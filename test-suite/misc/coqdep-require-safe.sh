#!/usr/bin/env bash

set -e

cd misc/coqdep-require-safe

code=0
$coqdep -worker @ROCQWORKER@ -Q . 'Pfx' ./*.v > stdout 2> stderr || code=$?

diff -u stdout.ref stdout
diff -u stderr.ref stderr

exit $code
