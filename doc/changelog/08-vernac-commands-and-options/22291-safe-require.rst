- **Added:**
  :cmd:`Require` :n:`(safe)` loads a library and its dependencies with only
  kernel-level content and fully-qualified names: no plugins, notations, hints,
  or flag settings are replayed. This is suitable for handling untrusted or
  heavyweight libraries. A later plain :cmd:`Require` of a safe-loaded library
  errors
  (`#22291 <https://github.com/rocq-prover/rocq/pull/22291>`_,
  by Gaëtan Gilbert).
