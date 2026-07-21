#!/usr/bin/env bash
# A library compiled with [Require (safe) M] keeps M (and M's dependencies)
# safe for its downstream users: requiring such a library fully loads it but
# only safe-loads its safe dependencies.

set -e

export PATH=$BIN:$PATH

cd misc/safe-require-propagation
rm -rf _test
mkdir _test
cp A.v B.v C.v B.out C.out _test
cd _test

# A safe-requires CMorphisms (which depends on CRelationClasses).
rocq c -R . Top A.v

# Requiring A fully must keep CRelationClasses safe (no implicit arguments,
# and a plain require of it is still rejected).
rocq c -test-mode -R . Top B.v > B.real 2>&1
diff -u --strip-trailing-cr B.out B.real

# Control: fully requiring CRelationClasses first, then A, works and keeps
# CRelationClasses fully loaded.
rocq c -test-mode -R . Top C.v > C.real 2>&1
diff -u --strip-trailing-cr C.out C.real
