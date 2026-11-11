"""Tier A driver for the HC-50 checker evaluation (card HC-51).

Each MultiPL-E HumanEval task goes through generate, check, run and repair:
the model writes a Chez Scheme program, harness-checker gates it, the
program runs against the task's tests whether or not the gate accepted it,
and a rejection goes back to the model with the violation text. Running
every program gives the ungated ground truth that false-reject and
task-success numbers are measured against. The plan is
plans/hc-50-checker-paper-eval.md in the overlord vault.

data/humaneval-rkt.jsonl is nuprl/MultiPL-E's humaneval-rkt test split
(161 tasks), fields name, prompt, tests and stop_tokens, taken from
huggingface.co/datasets/nuprl/MultiPL-E humaneval-rkt/test-00000-of-00001.parquet
on 2026-11-11. Its Racket tests become Chez by loading prelude.ss and
rewriting #hash literals.

Usage, from harness-checker/:

    python3 -m paper_eval.tier_a --model qwen3.5:latest --out results.jsonl
"""

from __future__ import annotations

import argparse
import ctypes
import json
import os
import re
import shutil
import signal
import subprocess
import tempfile
import threading
import time
import urllib.request

_HERE = os.path.dirname(os.path.abspath(__file__))
_CHECKER_DIR = os.path.dirname(_HERE)
DATA = os.path.join(_HERE, "data", "humaneval-rkt.jsonl")
PRELUDE = os.path.join(_HERE, "prelude.ss")
WHITELIST = os.path.join(_CHECKER_DIR, "data", "minimal-safe.txt")
SIGNATURES = os.path.join(_CHECKER_DIR, "data", "type-signatures.scm")

# Every child runs under these caps (memory/project_container_freeze_oom.md).
MEM_LIMIT_KB = 8000000
RUN_TIMEOUT = 10
CHECK_TIMEOUT = 60
# ulimit -v is per process and misses tmpfs and memfd pages, so the
# sandbox sets its own caps. Its worst case is MAX_PROCS processes at
# RUN_MEM_LIMIT_KB each, about 4GB, plus the sized /tmp; / is read-only.
SANDBOX_TMP_BYTES = 16 * 1024 * 1024
RUN_MEM_LIMIT_KB = 1000000
MAX_PROCS = 4
MAX_FILES = 32
FILE_LIMIT_KB = 16384
# scheme-agent's gate limit (scheme-agent/src/scheme-agent/safety.ss).
TERMINATION_DEPTH = 20
TESTS_DONE = "tier-a-tests-done"
# Characters of child output kept; a printing loop must not fill memory.
OUTPUT_TAIL = 65536
# Ollama's 4096-token default is filled by a thinking model's reasoning
# before it answers.
NUM_CTX = 32768

INSTRUCTIONS = (
    "Complete the following function in Chez Scheme (R6RS). Reply with the "
    "complete definition, and any helpers it needs, in one ```scheme code "
    "block. Where the comments mention a hash, use an R6RS hashtable made "
    "with (make-hashtable equal-hash equal?).\n\n"
)

REPAIR = (
    "The safety checker did not accept that program. Its report:\n\n"
    "{violations}\n\nRewrite the program so the checker accepts it. Reply "
    "with the complete definition in one ```scheme code block."
)


def load_tasks(path: str = DATA) -> list[dict]:
    with open(path) as f:
        return [json.loads(line) for line in f if line.strip()]


def task_by_name(tasks: list[dict], name: str) -> dict:
    return next(t for t in tasks if t["name"] == name)


def chez_prompt(task: dict) -> str:
    body = re.sub(r"\A#lang racket\s*\n", "", task["prompt"])
    return INSTRUCTIONS + body


def rewrite_hash_literals(src: str) -> str:
    """Turn each #hash(...) into (make-test-hash '(...)), skipping strings."""
    out, i, n = [], 0, len(src)
    while i < n:
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append(src[i:j + 1])
            i = j + 1
        elif src.startswith("#hash(", i):
            start = i + len("#hash")
            end = _matching_paren(src, start)
            out.append("(make-test-hash '" + src[start:end + 1] + ")")
            i = end + 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def _matching_paren(src: str, open_at: int) -> int:
    depth, i = 0, open_at
    while True:
        c = src[i]
        if c == '"':
            i += 1
            while src[i] != '"':
                i += 2 if src[i] == "\\" else 1
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i
        i += 1


def chez_tests(task: dict) -> str:
    tests = task["tests"].replace("(require rackunit)", "")
    return rewrite_hash_literals(tests)


def extract_code(text: str) -> str:
    blocks = re.findall(r"```[^`\n]*\n(.*?)```", text, re.S)
    return (blocks[-1] if blocks else text).strip()


def _capped(cmd: list[str], timeout: int, cwd: str | None = None):
    """Run cmd under ulimit -v and a wall-clock timeout; None on timeout.

    Core dumps are off: core_pattern pipes them to the host's coredump
    handler, so an aborted child would ship its heap out of the container.

    stdin is empty and stderr joins stdout. Only the last OUTPUT_TAIL
    bytes are kept, read as they arrive, so a child printing in an endless
    loop costs the driver no more than that.
    """
    shell = f"ulimit -v {MEM_LIMIT_KB}; ulimit -c 0; exec \"$@\""
    proc = subprocess.Popen(
        ["bash", "-c", shell, "capped", *cmd], cwd=cwd,
        stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        start_new_session=True, preexec_fn=_die_with_parent,
    )
    tail = bytearray()

    def drain():
        while chunk := proc.stdout.read1(65536):
            tail.extend(chunk)
            del tail[:-OUTPUT_TAIL]

    reader = threading.Thread(target=drain, daemon=True)
    reader.start()
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        _kill_group(proc)
        proc.wait()
        return None
    finally:
        # A grandchild can hold the pipe open after the child exits.
        reader.join(timeout=5)
        if reader.is_alive():
            _kill_group(proc)
            reader.join(timeout=1)
        # close() would block on the reader's lock; a reader still blocked
        # here belongs to a grandchild that left the group, so leave it.
        if not reader.is_alive():
            proc.stdout.close()
    out = bytes(tail[-OUTPUT_TAIL:]).decode(errors="replace")
    return subprocess.CompletedProcess(cmd, proc.returncode, out, "")


def _die_with_parent():
    # Its own session hides the child from a group kill of the driver,
    # such as timeout(1)'s, so the kernel kills it when the driver dies.
    PR_SET_PDEATHSIG = 1
    ctypes.CDLL(None, use_errno=True).prctl(PR_SET_PDEATHSIG, signal.SIGKILL)


def _kill_group(proc):
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def _sandboxed(cmd: list[str], script: str) -> list[str]:
    """Wrap cmd in bubblewrap: only /nix and the script visible, no network.

    The run step executes every program, rejected ones included, so a
    model's (system ...) call must reach nothing. Binding only /nix leaves
    no /bin/sh, no home and no /run, whose podman socket is the host's API.
    --clearenv keeps the driver's tokens out of the program's reach.

    Only the sized /tmp is writable: / is remounted read-only and /dev holds
    just /dev/null and /dev/urandom. The ulimits are set inside the
    sandbox, where -u counts only the sandbox's own user namespace.
    """
    limits = (f"ulimit -v {RUN_MEM_LIMIT_KB}; ulimit -u {MAX_PROCS}; "
              f"ulimit -f {FILE_LIMIT_KB}; ulimit -n {MAX_FILES}; ulimit -c 0")
    bash = os.path.realpath(shutil.which("bash"))
    return [
        "bwrap", "--ro-bind", "/nix", "/nix",
        "--dev-bind", "/dev/null", "/dev/null",
        "--dev-bind", "/dev/urandom", "/dev/urandom",
        "--size", str(SANDBOX_TMP_BYTES), "--tmpfs", "/tmp",
        "--ro-bind", script, script, "--remount-ro", "/",
        "--unshare-all", "--die-with-parent", "--clearenv",
        bash, "-c", f"{limits}; exec \"$@\"", "sandboxed", *cmd,
    ]


def run_program(task: dict, code: str, timeout: int = RUN_TIMEOUT) -> dict:
    """Run code against the task's tests in a fresh, sandboxed Chez process."""
    with open(PRELUDE) as f:
        prelude = f.read()
    with tempfile.NamedTemporaryFile("w", suffix=".ss", delete=False) as f:
        f.write(prelude + "\n" + code + "\n" + chez_tests(task) + "\n"
                + f"(display \"{TESTS_DONE}\")\n")
        path = f.name
    try:
        start = time.monotonic()
        # --clearenv drops PATH and only /nix is bound, so the sandbox
        # needs scheme's resolved store path.
        scheme = os.path.realpath(shutil.which("scheme"))
        proc = _capped(_sandboxed([scheme, "--script", path], path), timeout)
        seconds = time.monotonic() - start
    finally:
        os.unlink(path)
    if proc is None:
        return {"passed": False, "timed_out": True, "returncode": None,
                "output": "", "seconds": seconds}
    return {
        # The sentinel proves the tests ran: (exit 0) before them is a fail.
        "passed": proc.returncode == 0 and TESTS_DONE in proc.stdout,
        "timed_out": False,
        "returncode": proc.returncode,
        "output": (proc.stdout + proc.stderr)[-2000:],
        "seconds": seconds,
    }


def _packrat() -> str:
    default = os.path.join(_CHECKER_DIR, os.pardir, os.pardir, "packrat-extended")
    return os.path.realpath(os.environ.get("PACKRAT", default))


def check_program(code: str, whitelist: str = WHITELIST) -> dict:
    """Gate code with harness-checker's CLI; exit 0 means accepted."""
    packrat = _packrat()
    libdirs = f"src:{packrat}:{packrat}/examples"
    with tempfile.NamedTemporaryFile("w", suffix=".ss", delete=False) as f:
        f.write(code + "\n")
        path = f.name
    try:
        start = time.monotonic()
        proc = _capped(
            ["scheme", "--libdirs", libdirs, "--program", "src/main.ss",
             "--termination-depth", str(TERMINATION_DEPTH),
             path, whitelist, SIGNATURES],
            CHECK_TIMEOUT, cwd=_CHECKER_DIR,
        )
        seconds = time.monotonic() - start
    finally:
        os.unlink(path)
    if proc is None:
        return {"accepted": False, "status": "timeout",
                "violations": "checker timed out", "seconds": seconds}
    # Exit 1 is the checker's violation report. Anything else non-zero is
    # Chez raising: unreadable model code, or the checker itself failing.
    # Neither is a rejection by a pass, so it must not count as a false reject.
    status = {0: "accepted", 1: "rejected"}.get(proc.returncode, "error")
    return {
        "accepted": status == "accepted",
        "status": status,
        "violations": "" if status == "accepted" else (proc.stdout + proc.stderr).strip(),
        "seconds": seconds,
    }


def solve_task(task: dict, model, max_repairs: int = 3) -> dict:
    """Generate, check and run, repairing after each rejection.

    Stops at the first accepted program or after max_repairs repair turns.
    A model error ends the task and is recorded rather than raised.
    """
    messages = [{"role": "user", "content": chez_prompt(task)}]
    record = {"name": task["name"], "attempts": [], "error": None}
    for turn in range(max_repairs + 1):
        try:
            reply = model(messages)
        except Exception as exc:  # the proxy rate-limits and times out
            record["error"] = f"{type(exc).__name__}: {exc}"
            break
        code = extract_code(reply)
        if not code:
            record["error"] = "ModelReplyError: empty program"
            break
        verdict = check_program(code)
        run = run_program(task, code)
        record["attempts"].append({
            "turn": turn,
            "reply": reply,
            "code": code,
            "accepted": verdict["accepted"],
            "violations": verdict["violations"],
            "check_status": verdict["status"],
            "check_seconds": verdict["seconds"],
            "passed": run["passed"],
            "timed_out": run["timed_out"],
            "run_returncode": run["returncode"],
            "run_output": run["output"],
            "run_seconds": run["seconds"],
        })
        if verdict["accepted"]:
            break
        messages = messages + [
            {"role": "assistant", "content": reply},
            {"role": "user", "content": REPAIR.format(violations=verdict["violations"])},
        ]
    return record


class ModelReplyError(RuntimeError):
    """A reply that is cut off or empty, so the task must be asked again."""


class OllamaModel:
    """Chat with one model through an Ollama endpoint, temperature 0."""

    def __init__(self, name: str, endpoint: str = "http://127.0.0.1:11434",
                 timeout: int = 600):
        self.name = name
        self.endpoint = endpoint.rstrip("/")
        self.timeout = timeout

    def __call__(self, messages: list[dict]) -> str:
        body = json.dumps({
            "model": self.name,
            "messages": messages,
            "stream": False,
            "options": {"temperature": 0, "num_ctx": NUM_CTX},
        }).encode()
        req = urllib.request.Request(
            self.endpoint + "/api/chat", data=body,
            headers={"Content-Type": "application/json"},
        )
        resp = json.load(urllib.request.urlopen(req, timeout=self.timeout))
        content = resp["message"]["content"]
        if resp.get("done_reason") == "length":
            raise ModelReplyError(f"reply cut off at num_ctx {NUM_CTX}")
        if not content.strip():
            raise ModelReplyError("empty reply")
        return content


def run_all(tasks: list[dict], model, out: str, max_repairs: int = 3) -> None:
    """Append one record per task to out, skipping tasks already finished.

    A record with a model error, or a line cut short by a kill, is not
    finished: resume drops it from out and runs the task again, so out
    keeps one record per task. out + ".done"
    is written only when every task has an error-free record, so a detached
    batch leaves a completion marker that a rate-limited pass cannot fake.
    """
    kept = []
    if os.path.exists(out):
        with open(out) as f:
            lines = [line for line in f if line.strip()]
        for line in lines:
            try:
                record = json.loads(line)
            except json.JSONDecodeError:  # a kill mid-append
                continue
            if record.get("error") is None:
                kept.append(record)
        if len(kept) != len(lines):
            with open(out + ".tmp", "w") as f:
                f.writelines(json.dumps(r) + "\n" for r in kept)
            os.replace(out + ".tmp", out)
    done = {r["name"] for r in kept}
    if os.path.exists(out + ".done"):
        os.unlink(out + ".done")
    errored = False
    for task in tasks:
        if task["name"] in done:
            continue
        record = solve_task(task, model, max_repairs=max_repairs)
        errored = errored or record["error"] is not None
        with open(out, "a") as f:
            f.write(json.dumps(record) + "\n")
    if not errored:
        with open(out + ".done", "w") as f:
            f.write(time.strftime("%Y-%m-%dT%H:%M:%S%z") + "\n")


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--model", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--endpoint", default="http://127.0.0.1:11434")
    p.add_argument("--max-repairs", type=int, default=3)
    p.add_argument("--limit", type=int, help="first N tasks only")
    args = p.parse_args(argv)
    tasks = load_tasks()[: args.limit]
    run_all(tasks, OllamaModel(args.model, args.endpoint), args.out,
            max_repairs=args.max_repairs)


if __name__ == "__main__":
    main()
