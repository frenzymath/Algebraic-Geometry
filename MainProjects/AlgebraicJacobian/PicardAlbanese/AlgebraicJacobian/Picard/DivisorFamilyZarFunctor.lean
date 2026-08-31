/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZarSheaf

/-!
# The divisor functor (DD-2 S6b)

The one-screen functor packaging of the locally certified divisor vehicle
(`informal/spec-dd-2.md` §6, spelling (A) of I-0222, co-signed by the DD-R lane):

* `AlgebraicGeometry.divFunctor`: `(Over (Spec k))ᵒᵖ ⥤ Type u`, with object values
  `divFamZar C π n T` and action `divFamZar.map` — the `picEtFunctor` house pattern.
  Type-valued: degree-`n` divisor families carry no group structure.

This is the functor `divRep` is stated against (`informal/spec-dd-r.md` §3 item 8,
Addendum 1).  The sheaf halves are consumed as-is from
`AlgebraicJacobian.Picard.DivisorFamilyZarSheaf` (`ext_of_le_cover` /
`existsUnique_glue_of_le_cover`), the pic0/01JJ precedent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (π : C.left ⟶ P1 k) [IsAffineHom π] (n : ℕ)

/-- **The divisor functor** (DD-2 S6b, the pinned name): the locally certified
degree-`n` divisor families as a presheaf of types on the slice over `Spec k`,
with the glued restriction `divFamZar.map` along arbitrary test morphisms — the
`picDegLayerFunctor` house pattern. -/
noncomputable def divFunctor : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u where
  obj T := divFamZar C π n T.unop
  map g := ↾divFamZar.map C π n g.unop
  map_id T := by
    ext s U
    exact congrArg (fun z : divFamZar C π n T.unop => z.1 U) (divFamZar.map_id C π n s)
  map_comp {T T' T''} g h := by
    ext s U
    exact congrArg (fun z : divFamZar C π n T''.unop => z.1 U)
      (divFamZar.map_comp C π n g.unop h.unop s)

@[simp]
lemma divFunctor_obj (T : (Over (Spec (.of k)))ᵒᵖ) :
    (divFunctor C π n).obj T = divFamZar C π n T.unop :=
  rfl

@[simp]
lemma divFunctor_map {T T' : (Over (Spec (.of k)))ᵒᵖ} (g : T ⟶ T')
    (s : divFamZar C π n T.unop) :
    (divFunctor C π n).map g s = divFamZar.map C π n g.unop s :=
  rfl

end AlgebraicGeometry
