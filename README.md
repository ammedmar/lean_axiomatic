# lean_axiomatic

A Lean 4 / mathlib project for the axiomatic characterization of cup-i products.

The first file is `LeanAxiomatic/W.lean`. It defines the chain complex W over
F₂, using the basis e, T e in every nonnegative degree, and proves that its
boundary squares to zero.

Open this folder in VSCodium and open `LeanAxiomatic/W.lean`. The Lean 4
extension is required. Use **Lean 4: Toggle Infoview** from the Command Palette
to see the proof state, then place the cursor on each line of `boundary_sq`.

To check the project from a terminal in this folder:

```sh
lake build
```

Lean and mathlib are both pinned to version 4.34.1 (see `lean-toolchain` and `lakefile.toml`).

Dependencies (mathlib and its own dependencies) are not stored in this
project. They live in the shared folder `../.lean-packages`, set by
`packagesDir` in `lakefile.toml`, and are used by every Lean project in
the parent `lean/` folder. All those projects must therefore use the same
mathlib version, and should be upgraded together. A project that needs a
different version should be given its own `packagesDir`.
