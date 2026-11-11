"""Tests for paper_eval.tier_a, the HC-51 generate-check-run-repair driver.

These run the real checker and real Chez on five fixed HumanEval tasks with
canned programs, so no model is called.

Run from harness-checker/:
    python3 -m unittest discover -s paper_eval/tests -t .
"""

import io
import json
import os
import subprocess
import sys
import time
import unittest
from contextlib import redirect_stdout
from unittest.mock import MagicMock, patch

from paper_eval import tier_a

_HC_DIR = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

FIXED = {
    "HumanEval_0_has_close_elements": """
(define (has_close_elements numbers threshold)
  (let loop ((xs numbers))
    (cond ((null? xs) #f)
          ((let inner ((ys (cdr xs)))
             (cond ((null? ys) #f)
                   ((< (abs (- (car xs) (car ys))) threshold) #t)
                   (else (inner (cdr ys)))))
           #t)
          (else (loop (cdr xs))))))
""",
    "HumanEval_2_truncate_number": """
(define (truncate_number number)
  (- number (floor number)))
""",
    "HumanEval_22_filter_integers": """
(define (filter_integers values)
  (filter (lambda (v) (and (number? v) (exact? v) (integer? v))) values))
""",
    "HumanEval_27_flip_case": """
(define (flip_case string)
  (list->string
   (map (lambda (c)
          (cond ((char-upper-case? c) (char-downcase c))
                ((char-lower-case? c) (char-upcase c))
                (else c)))
        (string->list string))))
""",
    "HumanEval_111_histogram": """
(define (histogram test)
  (let ((counts (make-hashtable equal-hash equal?))
        (words (let split ((cs (string->list test)) (cur '()) (acc '()))
                 (cond ((null? cs)
                        (reverse (if (null? cur) acc
                                     (cons (list->string (reverse cur)) acc))))
                       ((char=? (car cs) #\\space)
                        (split (cdr cs) '()
                               (if (null? cur) acc
                                   (cons (list->string (reverse cur)) acc))))
                       (else (split (cdr cs) (cons (car cs) cur) acc))))))
    (for-each (lambda (w) (hashtable-update! counts w (lambda (n) (+ n 1)) 0))
              words)
    (let ((best (fold-left max 0 (vector->list (hashtable-values counts))))
          (out (make-hashtable equal-hash equal?)))
      (vector-for-each
       (lambda (k) (when (= (hashtable-ref counts k 0) best)
                     (hashtable-set! out k best)))
       (hashtable-keys counts))
      out)))
""",
}

WRONG_TRUNCATE = """
(define (truncate_number number)
  (+ number 1))
"""

UNSAFE_TRUNCATE = """
(define (truncate_number number)
  (eval (list '- number (list 'floor number))))
"""

LOOPING_TRUNCATE = """
(define (truncate_number number)
  (let loop ((n number)) (loop n)))
"""


def task(name):
    return tier_a.task_by_name(tier_a.load_tasks(), name)


class FakeModel:
    """Returns canned replies in order and records every message list it saw."""

    def __init__(self, replies):
        self.replies = list(replies)
        self.calls = []

    def __call__(self, messages):
        self.calls.append([dict(m) for m in messages])
        return self.replies.pop(0)


class TestTasks(unittest.TestCase):
    def test_loads_all_161_humaneval_rkt_tasks(self):
        tasks = tier_a.load_tasks()
        self.assertEqual(len(tasks), 161)
        self.assertEqual(len({t["name"] for t in tasks}), 161)

    def test_chez_prompt_drops_lang_line_and_keeps_signature(self):
        prompt = tier_a.chez_prompt(task("HumanEval_2_truncate_number"))
        self.assertNotIn("#lang racket", prompt)
        self.assertIn("(define (truncate_number number)", prompt)
        self.assertIn("Chez Scheme", prompt)

    def test_chez_tests_drop_rackunit_and_rewrite_hash_literals(self):
        tests = tier_a.chez_tests(task("HumanEval_111_histogram"))
        self.assertNotIn("require", tests)
        self.assertNotIn("#hash", tests)
        self.assertIn("(make-test-hash '((\"a\" .  2) (\"b\" .  2)))", tests)

    def test_hash_rewrite_skips_parens_inside_strings(self):
        self.assertEqual(
            tier_a.rewrite_hash_literals('(f #hash((")(" . 1)) "#hash(")'),
            "(f (make-test-hash '((\")(\" . 1))) \"#hash(\")",
        )

    def test_hash_rewrite_skips_a_hash_literal_inside_a_string(self):
        self.assertEqual(
            tier_a.rewrite_hash_literals('(f "a#hash((x . 1))")'),
            '(f "a#hash((x . 1))")',
        )

    def test_hash_rewrite_ends_a_string_after_an_escaped_backslash(self):
        self.assertEqual(
            tier_a.rewrite_hash_literals('(f "\\\\" #hash((a . 1)))'),
            '(f "\\\\" (make-test-hash \'((a . 1))))',
        )

    def test_hash_rewrite_keeps_an_unterminated_string(self):
        self.assertEqual(tier_a.rewrite_hash_literals('(f "abc'), '(f "abc')

    def test_hash_rewrite_reads_empty_and_escaped_string_keys(self):
        self.assertEqual(
            tier_a.rewrite_hash_literals('#hash(("" . ")"))'),
            "(make-test-hash '((\"\" . \")\")))",
        )
        self.assertEqual(
            tier_a.rewrite_hash_literals('#hash(("\\\\" . 1))'),
            "(make-test-hash '((\"\\\\\" . 1)))",
        )


def prelude_eval(expr):
    """Evaluate expr in Chez after loading prelude.ss; returns stdout or raises."""
    with open(tier_a.PRELUDE) as f:
        src = f.read() + f"\n(display {expr})\n"
    proc = subprocess.run(["scheme", "-q"], input=src, capture_output=True,
                          text=True, timeout=30)
    if "Exception" in proc.stdout + proc.stderr:
        raise AssertionError(proc.stdout + proc.stderr)
    return proc.stdout.strip().splitlines()[-1]


class TestPrelude(unittest.TestCase):
    def test_within_includes_the_epsilon_boundary(self):
        self.assertEqual(prelude_eval("(test-within? 1.5 1.0 0.5)"), "#t")

    def test_lists_compare_every_element(self):
        self.assertEqual(prelude_eval("(test-within? '(1 2) '(1 3) 0)"), "#f")

    def test_shape_mismatch_is_false_not_an_error(self):
        for actual, expected in [("'(1)", "5"), ("(vector 1)", "5"),
                                 ("(make-test-hash '((a . 1)))", "5")]:
            with self.subTest(actual=actual):
                self.assertEqual(
                    prelude_eval(f"(test-within? {actual} {expected} 0)"), "#f")

    def test_hashes_compare_values_not_only_keys(self):
        self.assertEqual(
            prelude_eval("(test-within? (make-test-hash '((a . 1)))"
                         " (make-test-hash '((a . 2))) 0)"),
            "#f")


class TestExtractCode(unittest.TestCase):
    def test_takes_last_fenced_block(self):
        text = "x\n```scheme\n(a)\n```\nthen\n```scheme\n(define (f) 1)\n```\n"
        self.assertEqual(tier_a.extract_code(text), "(define (f) 1)")

    def test_fence_tag_may_hold_a_dash_and_trailing_space(self):
        text = "Here:\n```scheme-r6rs \n(define (f) 1)\n```\n"
        self.assertEqual(tier_a.extract_code(text), "(define (f) 1)")

    def test_unfenced_reply_is_code(self):
        self.assertEqual(tier_a.extract_code("  (define (f) 1)\n"), "(define (f) 1)")


def fake_proc(returncode=0, out=""):
    return subprocess.CompletedProcess([], returncode, out, "")


class TestCaps(unittest.TestCase):
    # Values from the container-freeze rule and plans/hc-50-checker-paper-eval.md.
    def test_children_get_the_8gb_address_space_cap(self):
        proc = tier_a._capped(["bash", "-c", "ulimit -v"], timeout=10)
        self.assertEqual(proc.stdout.strip(), "8000000")

    def test_children_dump_no_core(self):
        # The checker runs here unsandboxed; its core would go to the host.
        proc = tier_a._capped(["bash", "-c", "ulimit -c"], timeout=10)
        self.assertEqual(proc.stdout.strip(), "0")

    def test_flooding_child_output_is_kept_as_a_bounded_tail(self):
        # An endless (display ...) loop must not grow the driver's memory.
        import tracemalloc
        tracemalloc.start()
        try:
            proc = tier_a._capped(
                ["bash", "-c", "head -c 200000000 /dev/zero | tr '\\0' a; echo -n END"],
                timeout=60)
            _, peak = tracemalloc.get_traced_memory()
        finally:
            tracemalloc.stop()
        self.assertEqual(proc.returncode, 0)
        self.assertTrue(proc.stdout.endswith("aaaEND"))
        self.assertEqual(len(proc.stdout), 65536)
        self.assertLess(peak, 4 * tier_a.OUTPUT_TAIL + 1000000)

    def test_grandchild_holding_the_pipe_costs_5s_then_dies(self):
        # A backgrounded grandchild keeps stdout open after the child exits.
        # The reader gets 5s to drain, then the child's process group dies.
        # One that left the group survives that; the driver waits 1s more,
        # then leaves the pipe to its daemon reader, which must not hold
        # the interpreter open. Both cases run at once to save 5s.
        def start(shell):
            script = (
                "import time\n"
                "from paper_eval import tier_a\n"
                "t = time.monotonic()\n"
                f"tier_a._capped(['bash', '-c', {shell!r}], timeout=10)\n"
                "print(time.monotonic() - t, flush=True)\n"
            )
            return subprocess.Popen([sys.executable, "-c", script], cwd=_HC_DIR,
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    text=True)

        start_time = time.monotonic()
        procs = {
            "in_group": start("sleep 20 & echo up"),
            "escaped": start("python3 -c 'import os, time; os.setsid(); "
                             "time.sleep(8)' & echo up"),
        }
        waited, total = {}, {}
        for name, proc in procs.items():
            out, err = proc.communicate(timeout=60)
            total[name] = time.monotonic() - start_time
            self.assertEqual(proc.returncode, 0, err)
            waited[name] = float(out.strip())
        self.assertGreater(waited["in_group"], 4.5)
        self.assertLess(waited["in_group"], 5.5)
        self.assertGreater(waited["escaped"], 5.5)
        self.assertLess(waited["escaped"], 6.5)
        for name in procs:
            self.assertLess(total[name], waited[name] + 2, name)

    def test_child_dies_with_a_killed_driver(self):
        # The child has its own session, so an outer timeout(1) killing the
        # driver's group misses it; the unsandboxed checker would run on.
        import signal, tempfile
        with tempfile.TemporaryDirectory() as d:
            pidfile = os.path.join(d, "pid")
            script = (
                "from paper_eval import tier_a\n"
                f"tier_a._capped(['bash', '-c', 'echo $$ > {pidfile}; exec sleep 30'], timeout=60)\n"
            )
            driver = subprocess.Popen([sys.executable, "-c", script], cwd=_HC_DIR)
            deadline = time.monotonic() + 10
            while not os.path.exists(pidfile) or not open(pidfile).read().strip():
                self.assertLess(time.monotonic(), deadline)
                time.sleep(0.05)
            child = int(open(pidfile).read())
            driver.send_signal(signal.SIGKILL)
            driver.wait()
            deadline = time.monotonic() + 2
            while time.monotonic() < deadline:
                try:
                    os.kill(child, 0)
                except ProcessLookupError:
                    break
                time.sleep(0.05)
            else:
                os.kill(child, signal.SIGKILL)
                self.fail("child outlived the driver")

    def test_stderr_is_captured_with_stdout(self):
        proc = tier_a._capped(["bash", "-c", "echo out; echo err >&2; exit 3"], timeout=10)
        self.assertEqual(proc.returncode, 3)
        self.assertEqual(proc.stdout, "out\nerr\n")

    def test_capped_timeout_returns_none(self):
        self.assertIsNone(tier_a._capped(["sleep", "5"], timeout=1))

    def test_run_and_check_default_timeouts(self):
        seen = []
        with patch.object(tier_a, "_capped",
                          lambda cmd, timeout, cwd=None: seen.append(timeout) or fake_proc()):
            tier_a.run_program(task("HumanEval_2_truncate_number"), "(x)")
            tier_a.check_program("(x)")
        self.assertEqual(seen, [10, 60])

    def test_elapsed_seconds_are_end_minus_start(self):
        for call in (lambda: tier_a.run_program(task("HumanEval_2_truncate_number"), "(x)"),
                     lambda: tier_a.check_program("(x)")):
            clock = MagicMock()
            clock.monotonic.side_effect = [100.0, 101.5]
            with patch.object(tier_a, "time", clock), \
                 patch.object(tier_a, "_capped", lambda *a, **k: fake_proc()):
                self.assertEqual(call()["seconds"], 1.5)

    def test_checker_timeout_is_not_an_acceptance(self):
        with patch.object(tier_a, "_capped", lambda *a, **k: None):
            verdict = tier_a.check_program("(x)")
        self.assertFalse(verdict["accepted"])
        self.assertEqual(verdict["status"], "timeout")


class TestRun(unittest.TestCase):
    def test_fixed_correct_programs_pass_their_tests(self):
        for name, code in FIXED.items():
            with self.subTest(name=name):
                result = tier_a.run_program(task(name), code)
                self.assertTrue(result["passed"], result["output"])
                self.assertFalse(result["timed_out"])

    def test_wrong_program_fails_with_check_within_message(self):
        result = tier_a.run_program(task("HumanEval_2_truncate_number"), WRONG_TRUNCATE)
        self.assertFalse(result["passed"])
        self.assertIn("check-within", result["output"])

    def test_check_within_compares_numbers_within_epsilon(self):
        close = "(define (truncate_number number) (+ (- number (floor number)) 0.0005))"
        far = "(define (truncate_number number) (+ (- number (floor number)) 0.002))"
        t = task("HumanEval_2_truncate_number")
        self.assertTrue(tier_a.run_program(t, close)["passed"])
        self.assertFalse(tier_a.run_program(t, far)["passed"])

    def test_hash_results_compare_by_contents(self):
        t = task("HumanEval_111_histogram")
        extra = FIXED["HumanEval_111_histogram"].replace(
            "      out)))", "      (hashtable-set! out \"zz\" 9)\n      out)))")
        self.assertNotEqual(extra, FIXED["HumanEval_111_histogram"])
        self.assertFalse(tier_a.run_program(t, extra)["passed"])

    def test_program_runs_sandboxed_without_writes_or_network(self):
        import os, tempfile
        with tempfile.TemporaryDirectory(dir=os.path.expanduser("~")) as d:
            marker = os.path.join(d, "escaped")
            code = (
                "(define (truncate_number number)\n"
                f"  (system \"touch {marker}; curl -s -m 3 https://example.com >> {marker}\")\n"
                "  (- number (floor number)))"
            )
            result = tier_a.run_program(task("HumanEval_2_truncate_number"), code)
            self.assertTrue(result["passed"], result["output"])
            self.assertFalse(os.path.exists(marker))

    @unittest.skipUnless(os.path.exists("/run/podman/podman.sock"),
                         "needs the container's podman socket")
    def test_sandbox_hides_the_podman_socket(self):
        # A visible socket is a connectable one: the reviewer reached the
        # podman API from inside the old --ro-bind / / sandbox.
        code = (
            "(define (truncate_number number)\n"
            "  (if (file-exists? \"/run/podman/podman.sock\") 99\n"
            "      (- number (floor number))))"
        )
        result = tier_a.run_program(task("HumanEval_2_truncate_number"), code)
        self.assertTrue(result["passed"], result["output"])

    def test_sandbox_shows_no_shell_to_a_program(self):
        code = (
            "(define (truncate_number number)\n"
            "  (if (file-exists? \"/bin/sh\") 99 (- number (floor number))))"
        )
        result = tier_a.run_program(task("HumanEval_2_truncate_number"), code)
        self.assertTrue(result["passed"], result["output"])

    def test_sandbox_has_no_network_even_through_libc(self):
        import socket
        with socket.socket() as srv:
            srv.bind(("127.0.0.1", 0))
            srv.listen(1)
            port = srv.getsockname()[1]
            # sockaddr_in: family 2 little-endian, port big-endian, 127.0.0.1.
            sockaddr = [2, 0, port >> 8, port & 255, 127, 0, 0, 1] + [0] * 8
            code = (
                "(load-shared-object \"libc.so.6\")\n"
                "(define c-socket (foreign-procedure \"socket\" (int int int) int))\n"
                "(define c-connect (foreign-procedure \"connect\" (int u8* int) int))\n"
                "(define (truncate_number number)\n"
                f"  (if (= 0 (c-connect (c-socket 2 1 0) (u8-list->bytevector '{tuple(sockaddr)}) 16))\n"
                "      99 (- number (floor number))))"
            ).replace(",", "")
            result = tier_a.run_program(task("HumanEval_2_truncate_number"), code)
        self.assertTrue(result["passed"], result["output"])

    def test_sandbox_tmp_is_size_capped(self):
        # tmpfs pages are not address space, so ulimit -v never sees them:
        # the reviewer filled 500MB of an uncapped /tmp in 0.2s.
        # 1MB files, each closed, stay under ulimit -f and -n: only the
        # tmpfs size stops 100 of them.
        code = (
            "(define (truncate_number number)\n"
            "  (if (guard (e (#t #f))\n"
            "        (do ((i 0 (+ i 1))) ((= i 100) #t)\n"
            "          (let ((p (open-file-output-port\n"
            "                    (string-append \"/tmp/fill\" (number->string i)))))\n"
            "            (put-bytevector p (make-bytevector 1048576 0))\n"
            "            (close-port p))))\n"
            "      99 (- number (floor number))))"
        )
        result = tier_a.run_program(task("HumanEval_2_truncate_number"), code)
        self.assertTrue(result["passed"], result["output"])

    def test_sandbox_root_and_dev_are_not_writable(self):
        for target in ("/fill", "/dev/fill", "/dev/shm/fill"):
            with self.subTest(target=target):
                code = (
                    "(define (truncate_number number)\n"
                    "  (if (guard (e (#t #f))\n"
                    f"        (let ((p (open-file-output-port \"{target}\")))\n"
                    "          (put-bytevector p (make-bytevector 16 0))\n"
                    "          (close-port p) #t))\n"
                    "      99 (- number (floor number))))"
                )
                result = tier_a.run_program(task("HumanEval_2_truncate_number"), code)
                self.assertTrue(result["passed"], result["output"])

    def test_sandbox_caps_memfd_size(self):
        # memfd pages are shmem, counted by neither ulimit -v nor /tmp's size.
        # SIGXFSZ is ignored so a refused write returns -1 instead of killing.
        code = (
            "(load-shared-object \"libc.so.6\")\n"
            "(define c-signal (foreign-procedure \"signal\" (int uptr) uptr))\n"
            "(define c-memfd (foreign-procedure \"memfd_create\" (string unsigned) int))\n"
            "(define c-write (foreign-procedure \"write\" (int u8* size_t) ssize_t))\n"
            "(c-signal 25 1)\n"
            "(define written\n"
            "  (let ((fd (c-memfd \"fill\" 0)) (chunk (make-bytevector 1048576 0)))\n"
            "    (let loop ((i 0) (n 0))\n"
            "      (if (= i 64) n\n"
            "          (let ((w (c-write fd chunk 1048576)))\n"
            "            (if (> w 0) (loop (+ i 1) (+ n w)) n))))))\n"
            "(define (truncate_number number)\n"
            "  (if (or (= written 0) (>= written (* 64 1048576))) 99\n"
            "      (- number (floor number))))"
        )
        result = tier_a.run_program(task("HumanEval_2_truncate_number"), code)
        self.assertTrue(result["passed"], result["output"])

    def test_sandbox_caps_each_process_below_the_driver_cap(self):
        # Every sandbox process may reach the run cap, so it must be small
        # enough that MAX_PROCS of them fit in RAM. Chez aborts on a refused
        # 2GB allocation; under the 8GB driver cap it would return 99.
        code = (
            "(define big (make-bytevector 2000000000))\n"
            "(define (truncate_number number) 99)"
        )
        result = tier_a.run_program(task("HumanEval_2_truncate_number"), code)
        self.assertFalse(result["passed"])
        self.assertIn("out of memory", result["output"])
        self.assertLessEqual(tier_a.MAX_PROCS * tier_a.RUN_MEM_LIMIT_KB, 8000000)

    def test_sandbox_dumps_no_core(self):
        # core_pattern pipes to the host's systemd-coredump, outside the
        # sandbox, and runaway recursion aborts Chez with SIGABRT.
        import os, shutil, tempfile
        bash = os.path.realpath(shutil.which("bash"))
        with tempfile.NamedTemporaryFile("w", suffix=".ss") as f:
            proc = tier_a._capped(
                tier_a._sandboxed([bash, "-c", "ulimit -c"], f.name), timeout=10)
        self.assertEqual(proc.stdout.strip(), "0")

    def test_sandbox_limits_are_the_planned_values(self):
        # 1GB per process, 4 processes, 16MiB files and /tmp, 32 open files:
        # about 4GB worst case, inside the 8GB driver cap.
        import os, shutil, tempfile
        bash = os.path.realpath(shutil.which("bash"))
        with tempfile.NamedTemporaryFile("w", suffix=".ss") as f:
            argv = tier_a._sandboxed(
                [bash, "-c", "ulimit -v; ulimit -u; ulimit -f; ulimit -n"], f.name)
            proc = tier_a._capped(argv, timeout=10)
        self.assertEqual(proc.stdout.split(), ["1000000", "4", "16384", "32"])
        self.assertEqual(argv[argv.index("--size") + 1], str(16 * 1024 * 1024))

    def test_sandbox_caps_process_count(self):
        # ulimit -v is per process, so each fork brings a fresh 8GB.
        code = (
            "(load-shared-object \"libc.so.6\")\n"
            "(define c-fork (foreign-procedure \"fork\" () int))\n"
            "(define c-exit (foreign-procedure \"_exit\" (int) void))\n"
            "(define forked\n"
            "  (let loop ((i 0) (n 0))\n"
            "    (if (= i 32) n\n"
            "        (let ((pid (c-fork)))\n"
            "          (when (= pid 0) (c-exit 0))\n"
            "          (loop (+ i 1) (if (> pid 0) (+ n 1) n))))))\n"
            "(define (truncate_number number)\n"
            "  (if (or (= forked 0) (= forked 32)) 99 (- number (floor number))))"
        )
        self.assertLess(tier_a.MAX_PROCS, 32)
        result = tier_a.run_program(task("HumanEval_2_truncate_number"), code)
        self.assertTrue(result["passed"], result["output"])

    def test_sandbox_sees_no_driver_environment(self):
        code = (
            "(define (truncate_number number)\n"
            "  (if (getenv \"TIER_A_LEAK\") 99 (- number (floor number))))"
        )
        with patch.dict("os.environ", {"TIER_A_LEAK": "secret"}):
            result = tier_a.run_program(task("HumanEval_2_truncate_number"), code)
        self.assertTrue(result["passed"], result["output"])

    def test_program_stdin_is_empty(self):
        code = (
            "(define (truncate_number number)\n"
            "  (if (eof-object? (read-char)) (- number (floor number)) 99))"
        )
        r, w = os.pipe()
        saved = os.dup(0)
        os.dup2(r, 0)
        try:
            result = tier_a.run_program(task("HumanEval_2_truncate_number"), code, timeout=5)
        finally:
            os.dup2(saved, 0)
            for fd in (r, w, saved):
                os.close(fd)
        self.assertTrue(result["passed"], result["output"])

    def test_scheme_found_through_a_symlink_outside_nix_still_runs(self):
        # The sandbox binds only /nix, so a PATH entry like ~/.nix-profile/bin
        # must be resolved to its store path before it goes in.
        import tempfile
        real_which = tier_a.shutil.which
        with tempfile.TemporaryDirectory(dir=os.path.expanduser("~")) as d:
            link = os.path.join(d, "scheme")
            os.symlink(os.path.realpath(real_which("scheme")), link)
            which = lambda name: link if name == "scheme" else real_which(name)
            with patch.object(tier_a.shutil, "which", which):
                result = tier_a.run_program(
                    task("HumanEval_2_truncate_number"),
                    FIXED["HumanEval_2_truncate_number"])
        self.assertTrue(result["passed"], result["output"])

    def test_run_records_the_return_code(self):
        with patch.object(tier_a, "_capped",
                          lambda cmd, timeout, cwd=None: fake_proc(3, "boom")):
            result = tier_a.run_program(task("HumanEval_2_truncate_number"), "(x)")
        self.assertEqual(result["returncode"], 3)
        timed_out = tier_a.run_program(
            task("HumanEval_2_truncate_number"), LOOPING_TRUNCATE, timeout=1)
        self.assertIsNone(timed_out["returncode"])

    def test_exit_zero_before_the_tests_does_not_pass(self):
        code = "(define (truncate_number number) 99)\n(exit 0)"
        result = tier_a.run_program(task("HumanEval_2_truncate_number"), code)
        self.assertFalse(result["passed"])

    def test_non_terminating_program_times_out(self):
        result = tier_a.run_program(
            task("HumanEval_2_truncate_number"), LOOPING_TRUNCATE, timeout=2)
        self.assertTrue(result["timed_out"])
        self.assertFalse(result["passed"])

    def test_output_keeps_the_last_2000_characters(self):
        out = "a" * 1000 + "b" * 2000
        with patch.object(tier_a, "_capped",
                          lambda cmd, timeout, cwd=None: fake_proc(1, out)):
            result = tier_a.run_program(task("HumanEval_2_truncate_number"), "(x)")
        self.assertEqual(result["output"], "b" * 2000)


class TestCheck(unittest.TestCase):
    def test_gate_accepts_safe_fixed_program(self):
        verdict = tier_a.check_program(FIXED["HumanEval_2_truncate_number"])
        self.assertTrue(verdict["accepted"], verdict["violations"])
        self.assertEqual(verdict["status"], "accepted")
        self.assertGreaterEqual(verdict["seconds"], 0)

    def test_gate_rejects_eval_with_violation_text(self):
        verdict = tier_a.check_program(UNSAFE_TRUNCATE)
        self.assertFalse(verdict["accepted"])
        self.assertEqual(verdict["status"], "rejected")
        self.assertIn("eval (unbound)", verdict["violations"])

    def test_gate_rejects_non_terminating_loop(self):
        verdict = tier_a.check_program(LOOPING_TRUNCATE)
        self.assertFalse(verdict["accepted"])
        self.assertEqual(verdict["status"], "rejected")

    def test_unreadable_program_is_an_error_not_a_rejection(self):
        verdict = tier_a.check_program("(define (f x) (+ x 1)")
        self.assertFalse(verdict["accepted"])
        self.assertEqual(verdict["status"], "error")
        self.assertIn("Exception in read", verdict["violations"])

    def test_checker_crash_is_an_error_not_a_rejection(self):
        with patch.dict("os.environ", {"PACKRAT": "/nonexistent"}):
            verdict = tier_a.check_program(FIXED["HumanEval_2_truncate_number"])
        self.assertEqual(verdict["status"], "error")


    def test_gate_uses_scheme_agents_termination_depth(self):
        # scheme-agent/src/scheme-agent/safety.ss passes 20; the paper
        # evaluates the gate as deployed.
        seen = []
        with patch.object(tier_a, "_capped",
                          lambda cmd, timeout, cwd=None: seen.append(cmd) or fake_proc(0)):
            tier_a.check_program("(define x 1)")
        cmd = seen[0]
        i = cmd.index("--termination-depth")
        self.assertEqual(cmd[i + 1], "20")
        self.assertLess(i, cmd.index("src/main.ss") + 2)


class TestSolve(unittest.TestCase):
    def test_accepted_first_attempt_stops_without_repair(self):
        model = FakeModel([f"```scheme\n{FIXED['HumanEval_2_truncate_number']}```"])
        record = tier_a.solve_task(task("HumanEval_2_truncate_number"), model, max_repairs=3)
        self.assertEqual(len(record["attempts"]), 1)
        self.assertTrue(record["attempts"][0]["accepted"])
        self.assertTrue(record["attempts"][0]["passed"])
        self.assertEqual(len(model.calls), 1)

    def test_rejection_sends_violations_back_and_repairs(self):
        model = FakeModel([UNSAFE_TRUNCATE, FIXED["HumanEval_2_truncate_number"]])
        record = tier_a.solve_task(task("HumanEval_2_truncate_number"), model, max_repairs=3)
        first, second = record["attempts"]
        self.assertFalse(first["accepted"])
        self.assertEqual(first["check_status"], "rejected")
        # Ungated ground truth is recorded even for a rejected program.
        self.assertTrue(first["passed"])
        self.assertEqual(first["run_returncode"], 0)
        self.assertTrue(second["accepted"] and second["passed"])
        self.assertEqual(second["turn"], 1)
        repair = model.calls[1]
        self.assertEqual(repair[-2]["role"], "assistant")
        self.assertIn(first["violations"], repair[-1]["content"])

    def test_repair_after_a_checker_error_does_not_claim_a_rejection(self):
        # Every program runs, and an unreadable one is an error, not a
        # rejection, so the repair turn must not tell the model otherwise.
        model = FakeModel(["(define (truncate_number", FIXED["HumanEval_2_truncate_number"]])
        record = tier_a.solve_task(task("HumanEval_2_truncate_number"), model, max_repairs=3)
        self.assertEqual(record["attempts"][0]["check_status"], "error")
        repair = model.calls[1][-1]["content"]
        self.assertIn("did not accept", repair)
        self.assertNotIn("rejected", repair)
        self.assertNotIn("not run", repair)

    def test_empty_program_is_a_model_error_not_an_accepted_attempt(self):
        # The checker accepts an empty program, which would score as a gated
        # failure and never get a repair turn.
        model = FakeModel(["```scheme\n```"])
        record = tier_a.solve_task(task("HumanEval_2_truncate_number"), model, max_repairs=3)
        self.assertEqual(record["attempts"], [])
        self.assertIn("empty", record["error"])

    def test_repairs_stop_at_the_limit(self):
        model = FakeModel([UNSAFE_TRUNCATE] * 5)
        record = tier_a.solve_task(task("HumanEval_2_truncate_number"), model, max_repairs=2)
        self.assertEqual([a["turn"] for a in record["attempts"]], [0, 1, 2])
        self.assertFalse(any(a["accepted"] for a in record["attempts"]))

    def test_default_allows_three_repairs(self):
        model = FakeModel(["(x)"] * 6)
        with patch.object(tier_a, "check_program", lambda code: {
                "accepted": False, "status": "rejected", "violations": "v", "seconds": 0}), \
             patch.object(tier_a, "run_program", lambda t, code: {
                "passed": False, "timed_out": False, "returncode": 1,
                "output": "", "seconds": 0}):
            record = tier_a.solve_task(task("HumanEval_2_truncate_number"), model)
        self.assertEqual([a["turn"] for a in record["attempts"]], [0, 1, 2, 3])

    def test_model_error_is_recorded_not_raised(self):
        def broken(messages):
            raise TimeoutError("proxy timed out")
        record = tier_a.solve_task(task("HumanEval_2_truncate_number"), broken, max_repairs=3)
        self.assertEqual(record["attempts"], [])
        self.assertIn("proxy timed out", record["error"])


class TestOllama(unittest.TestCase):
    def test_posts_chat_request_and_returns_content(self):
        seen = {}

        def fake_urlopen(req, timeout):
            seen["url"] = req.full_url
            seen["body"] = json.loads(req.data)
            return io.BytesIO(json.dumps({"message": {"content": "(x)"}}).encode())

        model = tier_a.OllamaModel("qwen3.5:latest", endpoint="http://h:1/")
        with patch("urllib.request.urlopen", fake_urlopen):
            reply = model([{"role": "user", "content": "hi"}])
        self.assertEqual(reply, "(x)")
        self.assertEqual(seen["url"], "http://h:1/api/chat")
        self.assertEqual(seen["body"]["model"], "qwen3.5:latest")
        self.assertFalse(seen["body"]["stream"])
        self.assertEqual(seen["body"]["messages"], [{"role": "user", "content": "hi"}])
        self.assertEqual(seen["body"]["options"], {"temperature": 0, "num_ctx": 32768})

    def _reply(self, payload):
        model = tier_a.OllamaModel("m")
        resp = lambda req, timeout: io.BytesIO(json.dumps(payload).encode())
        with patch("urllib.request.urlopen", resp):
            return model([{"role": "user", "content": "hi"}])

    def test_reply_cut_off_by_the_context_length_is_an_error(self):
        # qwen3.5's thinking filled Ollama's 4096-token default and left no
        # answer; a cut-off reply must be retried, not scored.
        for content in ("", "```scheme\n(define (f"):
            with self.subTest(content=content):
                with self.assertRaises(tier_a.ModelReplyError):
                    self._reply({"message": {"content": content}, "done_reason": "length"})

    def test_empty_reply_is_an_error(self):
        with self.assertRaises(tier_a.ModelReplyError):
            self._reply({"message": {"content": "  "}, "done_reason": "stop"})

    def test_complete_reply_is_returned(self):
        self.assertEqual(
            self._reply({"message": {"content": "(x)"}, "done_reason": "stop"}), "(x)")

    def test_default_request_timeout_is_ten_minutes(self):
        self.assertEqual(tier_a.OllamaModel("m").timeout, 600)


class TestRunAll(unittest.TestCase):
    def test_resumes_by_skipping_recorded_tasks_and_writes_marker(self):
        import tempfile, os
        tasks = [task("HumanEval_2_truncate_number"), task("HumanEval_27_flip_case")]
        with tempfile.TemporaryDirectory() as d:
            out = os.path.join(d, "r.jsonl")
            with open(out, "w") as f:
                f.write(json.dumps({"name": "HumanEval_2_truncate_number"}) + "\n")
            model = FakeModel([FIXED["HumanEval_27_flip_case"]])
            tier_a.run_all(tasks, model, out, max_repairs=0)
            with open(out) as f:
                names = [json.loads(l)["name"] for l in f]
            self.assertEqual(names, ["HumanEval_2_truncate_number", "HumanEval_27_flip_case"])
            self.assertTrue(os.path.exists(out + ".done"))


    def test_errored_record_is_retried_on_resume_and_replaced(self):
        import tempfile
        tasks = [task("HumanEval_2_truncate_number"), task("HumanEval_27_flip_case")]
        with tempfile.TemporaryDirectory() as d:
            out = os.path.join(d, "r.jsonl")
            with open(out, "w") as f:
                f.write(json.dumps({"name": "HumanEval_2_truncate_number",
                                    "attempts": [], "error": "TimeoutError: x"}) + "\n")
                f.write(json.dumps({"name": "HumanEval_27_flip_case",
                                    "attempts": [], "error": None}) + "\n")
            model = FakeModel([FIXED["HumanEval_2_truncate_number"]])
            tier_a.run_all(tasks, model, out, max_repairs=0)
            with open(out) as f:
                records = [json.loads(l) for l in f]
            self.assertEqual(len(model.calls), 1)
            self.assertEqual(sorted(r["name"] for r in records),
                             ["HumanEval_27_flip_case", "HumanEval_2_truncate_number"])
            self.assertTrue(all(r["error"] is None for r in records))
            self.assertTrue(os.path.exists(out + ".done"))

    def test_truncated_last_line_is_dropped_and_rerun(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            out = os.path.join(d, "r.jsonl")
            with open(out, "w") as f:
                f.write('{"name": "HumanEval_2_truncate_number", "attem')
            model = FakeModel([FIXED["HumanEval_2_truncate_number"]])
            tier_a.run_all([task("HumanEval_2_truncate_number")], model, out,
                           max_repairs=0)
            with open(out) as f:
                records = [json.loads(l) for l in f]
            self.assertEqual([r["name"] for r in records], ["HumanEval_2_truncate_number"])
            self.assertTrue(os.path.exists(out + ".done"))

    def test_no_done_marker_while_a_task_errored(self):
        import tempfile
        def broken(messages):
            raise TimeoutError("proxy timed out")
        with tempfile.TemporaryDirectory() as d:
            out = os.path.join(d, "r.jsonl")
            with open(out + ".done", "w") as f:
                f.write("stale\n")
            tier_a.run_all([task("HumanEval_2_truncate_number")], broken, out,
                           max_repairs=0)
            with open(out) as f:
                self.assertIn("proxy timed out", f.read())
            self.assertFalse(os.path.exists(out + ".done"))

    def test_default_allows_three_repairs(self):
        seen = []
        with patch.object(tier_a, "solve_task",
                          lambda t, m, max_repairs: seen.append(max_repairs) or {"name": t["name"], "error": None}):
            import tempfile
            with tempfile.TemporaryDirectory() as d:
                tier_a.run_all([task("HumanEval_2_truncate_number")], None,
                               os.path.join(d, "r.jsonl"))
        self.assertEqual(seen, [3])


class TestMain(unittest.TestCase):
    def test_model_and_out_are_required(self):
        for argv in ([], ["--model", "m"], ["--out", "o"]):
            with self.subTest(argv=argv), redirect_stdout(io.StringIO()), \
                 patch("sys.stderr", io.StringIO()), self.assertRaises(SystemExit):
                tier_a.main(argv)

    def test_help_names_the_driver(self):
        buf = io.StringIO()
        with redirect_stdout(buf), self.assertRaises(SystemExit):
            tier_a.main(["--help"])
        self.assertIn("Tier A driver", buf.getvalue())

    def test_cli_defaults_to_three_repairs(self):
        seen = {}
        with patch.object(tier_a, "run_all",
                          lambda tasks, model, out, max_repairs: seen.update(
                              n=len(tasks), out=out, max_repairs=max_repairs)):
            tier_a.main(["--model", "m", "--out", "o", "--limit", "2"])
        self.assertEqual(seen, {"n": 2, "out": "o", "max_repairs": 3})


if __name__ == "__main__":
    unittest.main()
