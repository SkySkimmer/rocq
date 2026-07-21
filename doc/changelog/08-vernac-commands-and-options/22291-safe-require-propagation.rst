- **Added:**
  A library compiled with :cmd:`Require` :n:`(safe)` now keeps those safe
  dependencies safe for its downstream users: a plain :cmd:`Require` of such a
  library loads it fully but only safe-loads the dependencies it had itself
  safe-required (and, transitively, their dependencies). The set of
  safe-required direct dependencies is recorded in each ``.vo`` file
  (`#22291 <https://github.com/rocq-prover/rocq/pull/22291>`_,
  by Gaëtan Gilbert and Jason Gross).
