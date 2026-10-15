# Repository basics

- Lean 4 formalization; the main source and default build target is
  `AsymmetricTensor.lean`.
- `lean-toolchain` pins Lean; `lake-manifest.json` pins Mathlib and its
  dependencies. Preserve both unless explicitly updating dependencies.
- Use elan's `lean` and `lake`. With direnv's shell hook enabled, run
  `direnv allow` once per checkout; `.envrc` selects the pinned toolchain.
  Without direnv, put `${ELAN_HOME:-$HOME/.elan}/bin` on `PATH`.
- Initial setup: `lake exe cache get` to fetch prebuilt Mathlib artifacts.
  Do not build Mathlib from source or run `lake update` for routine setup.
- Validate changes with `lake build`. The main file can take several minutes
  to check; allow a long timeout. Existing module-system import warnings
  are not build failures.
- `.lake/` is generated and ignored. Do not commit build artifacts.
- Keep changes focused. Kernel checking verifies proofs relative to their
  axioms and hypotheses; it does not independently validate the physics.
