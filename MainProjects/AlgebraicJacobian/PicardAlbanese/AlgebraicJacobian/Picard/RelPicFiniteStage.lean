/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.CechPicFiniteStage
import AlgebraicJacobian.Picard.RelPicPi

/-!
# Relative Picard classes descend to finite subextensions

Every relative Picard class over an algebraic field extension is defined over a finite
intermediate extension.  This follows by choosing a Cech representative, descending that
representative, and applying naturality of the quotient map.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Every relative Picard class over an algebraic field extension is pulled back from a
finite subextension. -/
theorem exists_finSubext_relPic_model
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] (π : C.left ⟶ P1 k) [IsFinite π]
    (q : relPic C (overSpec k K)) :
    ∃ L : DatG0.FinSubext k K, ∃ qL : relPic C (overSpec k L.1),
      relPicAlgMap C (IsScalarTower.toAlgHom k L.1 K) qL = q := by
  obtain ⟨c, hc⟩ := relPicMk_surjective C (overSpec k K) q
  obtain ⟨L, cL, hcL⟩ := exists_finSubext_cechPic_model C π c
  refine ⟨L, relPicMk C (overSpec k L.1) cL, ?_⟩
  rw [relPicAlgMap_mk]
  have hcurve : (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k L.1 K)).left =
      relCurveMap C L.1 K := by
    refine congrArg (fun g : overSpec k K ⟶ overSpec k L.1 => (C ◁ g).left) ?_
    exact Over.OverMorphism.ext rfl
  rw [hcurve]
  exact (congrArg (relPicMk C (overSpec k K)) hcL).trans hc

end AlgebraicGeometry
