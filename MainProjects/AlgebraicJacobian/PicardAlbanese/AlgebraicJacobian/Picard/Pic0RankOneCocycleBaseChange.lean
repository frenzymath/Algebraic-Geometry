/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveH0
import AlgebraicJacobian.Picard.DivisorFamilyWindowBaseChange

/-!
# Tower coherence for cocycle sections

Comparison of sections of a base-changed cocycle datum is transitive along arbitrary affine
coefficient towers.  The codomain is transported by the canonical equality between the iterated
and direct base-changed datum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace BasicOpenCocycleDatum

section Tower

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R']
  [IsScalarTower k R R']
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]

private lemma cast_appLE_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g)
    {U : Y.Opens} {W W' : X.Opens} (hW : W = W')
    (e : W ≤ f ⁻¹ᵁ U) (e' : W' ≤ g ⁻¹ᵁ U) (s : Γ(Y, U)) :
    cast (congrArg (fun V : X.Opens => ↑(Γ(X, V))) hW) ((f.appLE U W e).hom s) =
      (g.appLE U W' e').hom s := by
  subst hf
  subst hW
  rfl

private lemma cast_gluedSubmodule_eq_of_val_heq
    {S : Type u} [CommRing S] [Algebra k S]
    {D₁ D₂ : BasicOpenCocycleDatum C S pi} {W : (relCurve C S).Opens}
    (hD : D₁ = D₂)
    (x : ↑(gluedSubmodule S D₁.pieces D₁.unit W))
    (y : ↑(gluedSubmodule S D₂.pieces D₂.unit W))
    (hval : HEq x.val y.val) :
    cast (congrArg (fun E : BasicOpenCocycleDatum C S pi =>
      ↑(gluedSubmodule S E.pieces E.unit W)) hD) x = y := by
  subst D₂
  exact Subtype.ext (eq_of_heq hval)

/-- Comparing glued sections in two stages agrees with direct comparison after transport by the
canonical equality of the two base-changed cocycle data. -/
theorem sectionsMap_tower (D : BasicOpenCocycleDatum C R pi)
    (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R'']
    {W : (relCurve C R).Opens} {W' : (relCurve C R').Opens}
    {W'' : (relCurve C R'').Opens}
    (hW' : W' ≤ relCurveMap C R R' ⁻¹ᵁ W)
    (hW'' : W'' ≤ relCurveMap C R' R'' ⁻¹ᵁ W')
    (s : ↑(gluedSubmodule R D.pieces D.unit W)) :
    let hD : (D.baseChange R').baseChange R'' = D.baseChange R'' :=
      D.baseChange_baseChange C R R' R''
    let hcomp : W'' ≤ relCurveMap C R R'' ⁻¹ᵁ W := by
      rw [← relCurveMap_comp (C := C) (R := R) (R' := R') (R'' := R''),
        Scheme.Hom.comp_preimage]
      exact hW''.trans (Scheme.Hom.preimage_mono _ hW')
    cast (congrArg (fun E : BasicOpenCocycleDatum C R'' pi =>
      ↑(gluedSubmodule R'' E.pieces E.unit W'')) hD)
        ((D.baseChange R').sectionsMap R'' hW'' (D.sectionsMap R' hW' s)) =
      D.sectionsMap R'' hcomp s := by
  let hD : (D.baseChange R').baseChange R'' = D.baseChange R'' :=
    D.baseChange_baseChange C R R' R''
  let hcomp : W'' ≤ relCurveMap C R R'' ⁻¹ᵁ W := by
    rw [← relCurveMap_comp (C := C) (R := R) (R' := R') (R'' := R''),
      Scheme.Hom.comp_preimage]
    exact hW''.trans (Scheme.Hom.preimage_mono _ hW')
  change cast (congrArg (fun E : BasicOpenCocycleDatum C R'' pi =>
      ↑(gluedSubmodule R'' E.pieces E.unit W'')) hD)
        ((D.baseChange R').sectionsMap R'' hW'' (D.sectionsMap R' hW' s)) =
      D.sectionsMap R'' hcomp s
  apply cast_gluedSubmodule_eq_of_val_heq C hD
  apply Function.hfunext rfl
  intro j j' hj
  cases hj
  let hopen : W'' ⊓ ((D.baseChange R').baseChange R'').pieces j =
      W'' ⊓ (D.baseChange R'').pieces j :=
    congrArg (fun V : (relCurve C R'').Opens => W'' ⊓ V)
      (D.toBasicOpenCoverData.pieces_tower C R R' R'' j)
  apply (Equiv.cast_eq_iff_heq
    (congrArg (fun V : (relCurve C R'').Opens => ↑(Γ(relCurve C R'', V))) hopen)).mp
  simp only [BasicOpenCocycleDatum.sectionsMap_coe]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact cast_appLE_congr
    (relCurveMap_comp (C := C) (R := R) (R' := R') (R'' := R'')) hopen _ _ (s.val j)

/-- Global glued-section comparison is transitive along an arbitrary coefficient tower. -/
theorem sectionsMapTop_tower (D : BasicOpenCocycleDatum C R pi)
    (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R'']
    (s : ↑(gluedSubmodule R D.pieces D.unit ⊤)) :
    let hD : (D.baseChange R').baseChange R'' = D.baseChange R'' :=
      D.baseChange_baseChange C R R' R''
    cast (congrArg (fun E : BasicOpenCocycleDatum C R'' pi =>
      ↑(gluedSubmodule R'' E.pieces E.unit ⊤)) hD)
        ((D.baseChange R').sectionsMapTop R'' (D.sectionsMapTop R' s)) =
      D.sectionsMapTop R'' s := by
  let hW' : (⊤ : (relCurve C R').Opens) ≤
      relCurveMap C R R' ⁻¹ᵁ (⊤ : (relCurve C R).Opens) := by
    rw [Scheme.Hom.preimage_top]
  let hW'' : (⊤ : (relCurve C R'').Opens) ≤
      relCurveMap C R' R'' ⁻¹ᵁ (⊤ : (relCurve C R').Opens) := by
    rw [Scheme.Hom.preimage_top]
  simpa only [BasicOpenCocycleDatum.sectionsMapTop] using
    sectionsMap_tower C R R' D R'' hW' hW'' s

end Tower

end BasicOpenCocycleDatum

end AlgebraicGeometry
