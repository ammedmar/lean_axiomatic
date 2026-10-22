# Progress ledger

Each row links a result of the paper (version recorded in `README.md`) to its
Lean declaration. Status is one of: **open** (not stated), **stated**
(statement compiles, proof is `sorry`), **proved** (no `sorry`; axioms
checked with `#print axioms`).

| Paper reference | Content | Lean declaration | File | Status |
| --- | --- | --- | --- | --- |
| `sec/statement.tex` (s:statement), display defining W | The chain complex W over F₂ with basis e, Te | `LeanAxiomatic.W` | `LeanAxiomatic/W.lean` | proved |
| `sec/statement.tex` | Boundary of W squares to zero | `LeanAxiomatic.boundary_sq` | `LeanAxiomatic/W.lean` | proved |
| Corollary `c:free_zero` (`sec/freeness.tex`) | A free chain z with (1+T)z = 0 is zero | — | — | open |
