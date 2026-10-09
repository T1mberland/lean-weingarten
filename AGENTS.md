# Development instructions

This is a Lean 4.28 / Mathlib v4.28 project. Read README.md before extending it;
the arbitrary-order integration theorem is still conditional on spanning.

* Keep all mathematical statements faithful to actual Haar integration.
* Do not use `sorry`, `admit`, new axioms, or assumptions hidden in typeclasses to
  bypass a missing mathematical theorem.
* Keep the remaining spanning obligation explicit until it has been proved.
* Use `import Weingarten` as the public entry point. Put reusable additions in
  focused modules under `Weingarten/` and examples in `Weingarten/Examples.lean`.
* Run `scripts/check.sh` after changes and update README.md when the proved scope
  changes. Add meaningful API examples for substantial new results.
* Preserve the pinned toolchain and dependency manifest unless an upgrade is
  needed and verified. Do not commit `.lake/` or local cache symlinks.
* Make meaningful Git commits for verified increments.
