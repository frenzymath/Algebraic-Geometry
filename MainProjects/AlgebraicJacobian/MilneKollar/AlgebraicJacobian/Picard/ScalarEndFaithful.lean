/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.GrassmannianQuot

/-!
# Faithfulness of scalar endomorphisms of `𝒪_X`

The scalar-endomorphism map `scalarEnd : Γ(X, ⊤) → End(𝒪_X)` of `Picard/GrassmannianQuot.lean`
(multiplication by a global function on the structure sheaf, viewed as a module over itself)
is **injective**, and `scalarEnd a` is the identity exactly when `a = 1`. This is the
"automorphisms of the structure sheaf are (a faithful image of) global functions" fact — the
algebraic half of Kleiman's automorphism-rigidity lemma (`lm:aut`): once one knows an
endomorphism `χ` of an invertible sheaf is `scalarEnd u` for a global function `u`, triviality
of `χ` reduces to `u = 1`.

Combined with the ring-level `lm:aut`
(`StructureSheafPushforward.eq_one_of_section_of_restrict_eq_one_of_gate`: `σ.appTop u = 1 ⟹ u = 1`
for a section `σ` of the projection over a proper geometrically integral curve) and the
rigidification API of `Picard/RigidifiedPic.lean`, these are the ingredients for the geometric
`lm:aut` (an automorphism of a rigidified relative-Picard bundle that restricts to the identity
along the `x₀`-section is the identity).

**Surjectivity note (next-session target).** The complementary fact
`χ = scalarEnd (χ.val.app (op ⊤) 1)` (every endomorphism of `𝒪_X` is scalar) — which upgrades the
below to a full ring bijection `Γ(X, ⊤) ≃ End(𝒪_X)` and is what the geometric `lm:aut` consumes —
reduces to `PresheafOfModules.naturality_apply` + `PresheafOfModules.unit_map_one`, but currently
stalls on the `SheafOfModules.unit R .val` vs `PresheafOfModules.unit R.obj`
coercion/dependent-motive wall in Lean v4.31 (`rw` cannot rewrite `(unit R).val` under the
`ConcreteCategory.hom` wrapper of
`χ.val.app`; the motive is not type-correct). A `conv`/`simp`-with-`@[congr]` route or a
`SheafOfModules`-level `unit_map_one` restatement is the way through.
-/

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Grassmannian

variable {X : Scheme.{u}}

/-- **`scalarEnd` is injective.** A scalar endomorphism of `𝒪_X` determines its scalar: the
scalar is recovered by evaluating the endomorphism at the unit section `1` over the whole space. -/
lemma scalarEnd_injective : Function.Injective (scalarEnd (X := X)) := by
  intro a b h
  have hval : (SheafOfModules.Hom.val (scalarEnd a)).app (op ⊤)
        (1 : X.ringCatSheaf.obj.obj (op ⊤))
      = (SheafOfModules.Hom.val (scalarEnd b)).app (op ⊤)
        (1 : X.ringCatSheaf.obj.obj (op ⊤)) := by rw [h]
  rw [scalarEnd_val_app_one, scalarEnd_val_app_one,
    Subsingleton.elim ((homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op) (𝟙 (op (⊤ : X.Opens))),
    CategoryTheory.Functor.map_id, CategoryTheory.ConcreteCategory.id_apply,
    CategoryTheory.ConcreteCategory.id_apply] at hval
  exact hval

/-- **`scalarEnd a` is the identity iff `a = 1`.** The identity-rigidity criterion feeding the
geometric automorphism-freeness lemma. -/
lemma scalarEnd_eq_one_iff (a : Γ(X, ⊤)) :
    scalarEnd a = 𝟙 (SheafOfModules.unit X.ringCatSheaf) ↔ a = 1 := by
  rw [← scalarEnd_one (X := X)]
  exact ⟨fun h => scalarEnd_injective h, fun h => congrArg scalarEnd h⟩

end AlgebraicGeometry.Grassmannian
