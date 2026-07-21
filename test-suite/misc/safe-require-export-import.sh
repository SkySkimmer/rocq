#!/usr/bin/env bash
# Integration of Require (safe) Import/Export support and safe-dependency
# propagation.  A does [Require (safe) Export CRelationClasses], so A both
# keeps CRelationClasses safe for its downstream users (propagation) and
# records the ExportObject that re-exports it (import/export support).  B
# requires A fully, then imports it: propagation keeps CRelationClasses safe
# in B, and [Import A] replays the ExportObject, whose import of the
# safe-loaded CRelationClasses exercises the safe branch of Declaremods'
# import machinery to push the short names.  Neither feature alone can make
# this work.

set -e

export PATH=$BIN:$PATH

cd misc/safe-require-export-import
rm -rf _test
mkdir _test
cp A.v B.v B.out _test
cd _test

# A re-exports the safe-required CRelationClasses.
rocq c -R . Top A.v

# Requiring A fully keeps CRelationClasses safe (short name FQN-only before
# import), [Import A] then exposes the short name, CRelationClasses stays safe
# (no implicit arguments), and a plain require of it is still rejected.
rocq c -test-mode -R . Top B.v > B.real 2>&1
diff -u --strip-trailing-cr B.out B.real
