import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Prod

/-!
# The chain complex W

In every nonnegative degree, W has basis e and T e over the field F₂.
We use coordinates (a, b) for a e + b T e. The action of T exchanges
these coordinates, so the boundary 1 + T sends (a, b) to (a + b, a + b).

This file constructs the underlying chain complex of F₂-vector spaces.
-/

open CategoryTheory

namespace LeanAxiomatic

/-- The field with two elements. -/
abbrev F2 := ZMod 2

/-- A copy of F₂[C₂], written in the basis e, T e. -/
abbrev WModule := ModuleCat.of F2 (F2 × F2)

/-- The boundary 1 + T, in coordinates. -/
def boundary : WModule ⟶ WModule :=
  ModuleCat.ofHom
    ((LinearMap.fst F2 F2 F2 + LinearMap.snd F2 F2 F2).prod
      (LinearMap.fst F2 F2 F2 + LinearMap.snd F2 F2 F2))

/-- Applying the boundary twice gives zero, since x + x = 0 in F₂. -/
lemma boundary_sq : boundary ≫ boundary = 0 := by
  ext <;> simp [boundary, CharTwo.add_self_eq_zero]

/-- W is concentrated in nonnegative degrees, with boundary 1 + T. -/
def W : ChainComplex (ModuleCat F2) ℕ :=
  ChainComplex.of (fun _ => WModule) (fun _ => boundary) (fun _ => boundary_sq)

end LeanAxiomatic
