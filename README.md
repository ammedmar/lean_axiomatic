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

-

## Paper version

The formalization follows the manuscript *An axiomatic characterization of
Steenrod's cup-i products* at commit `d35c41b` ("Sent to PEMS", tag
`arXiv6`) of its own repository. References to sections, lemmas, and
equations in this project are to that version. Update this line, and the
references, whenever a later version is adopted.

## Proof policy

- Every completed theorem is checked with `#print axioms`; it may depend only
  on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- `native_decide` is not used: it trusts the compiler rather than Lean's
  kernel.
- `sorry` is allowed during development only for statements listed as open in
  the progress ledger. Before a milestone is declared complete, the build
  must pass with no warnings.

Parts of this project were developed with the assistance of Claude and ChatGPT.
