#!/bin/sh
# Run the BPMN checker's test suites; exit 1 if any fails.
cd "$(dirname "$0")" || exit 1
status=0
for t in test-xml.ss test-model.ss; do
  scheme --libdirs ../src --program "$t" || status=1
done
exit $status
