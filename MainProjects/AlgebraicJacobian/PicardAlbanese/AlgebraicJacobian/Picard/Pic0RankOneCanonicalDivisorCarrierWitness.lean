/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorStageGlued

/-!
# The canonical divisor witness on a presentation carrier

A rank-one presentation descends to a finite Noetherian stage, where the canonical glued divisor
exists.  This module pushes that divisor back to the presentation's etale carrier and identifies
its Abel value with the plus class represented by the presentation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance carrierWitnessOverCleft :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

namespace PicRankOneLocalPresentation

variable {A : Type u} [CommRing A] [Algebra k A]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

/-- A rank-one presentation carries an Abel-correct divisor on its etale carrier. -/
theorem exists_carrier_divFamZarAff_abel
    (P : PicRankOneLocalPresentation pi lam)
    (hpi : pi ≫ P1.structureMap k = C.hom) :
    ∃ F : DivFamZarAff C P.cover.Carrier (genus C),
      abelDivAffPlus C P.cover.Carrier F =
        PicEtAff.mapAlg C ((Algebra.ofId A P.cover.Carrier).restrictScalars k)
          (picEtAffineEquiv C A lam.1) := by
  classical
  obtain ⟨S⟩ := P.nonempty_noetherianStage hpi
  obtain ⟨F, hFrel⟩ := S.exists_glued_divFamZarAff hpi
  set F' : DivFamZarAff C P.cover.Carrier (genus C) :=
    DivFamZarAff.mapAlgHom (IsScalarTower.toAlgHom k S.A0 P.cover.Carrier) F with hF'def
  have hF'pic : F'.picClass =
      Scheme.CechPic.map (relCurveMap C S.A0 P.cover.Carrier) F.picClass := by
    rw [hF'def, DivFamZarAff.mapAlgHom_eq_mapAlg
      (IsScalarTower.toAlgHom k S.A0 P.cover.Carrier) (fun _ => rfl),
      DivFamZarAff.picClass_mapAlg]
  have hcurveB :
      (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k S.A0 P.cover.Carrier)).left =
        relCurveMap C S.A0 P.cover.Carrier := by
    refine congrArg
      (fun t : overSpec k P.cover.Carrier ⟶ overSpec k S.A0 => (C ◁ t).left) ?_
    exact Over.OverMorphism.ext rfl
  have hclassB : P.datum.cechPicClass =
      Scheme.CechPic.map (relCurveMap C S.A0 P.cover.Carrier)
        (S.D0.baseChange S.A0).cechPicClass := by
    rw [← S.hbase]
    exact (S.D0.baseChange S.A0).cechPicClass_baseChange P.cover.Carrier
  have hrelB : relPicMk C (overSpec k P.cover.Carrier) F'.picClass =
      relPicMk C (overSpec k P.cover.Carrier) P.datum.cechPicClass := by
    have h := congrArg
      (relPicAlgMap C (IsScalarTower.toAlgHom k S.A0 P.cover.Carrier)) hFrel
    rw [relPicAlgMap_mk, relPicAlgMap_mk, hcurveB] at h
    rw [hF'pic, hclassB]
    exact h
  have htarget :
      PicEtAff.mapAlg C ((Algebra.ofId A P.cover.Carrier).restrictScalars k)
          (picEtAffineEquiv C A lam.1) =
        PicEtAff.unit C P.cover.Carrier
          (P.representative : relPic C (overSpec k P.cover.Carrier)) := by
    rw [← P.represents, PicEtAff.mapAlg_mk_eq_unit_self]
  refine ⟨F', ?_⟩
  calc abelDivAffPlus C P.cover.Carrier F'
      = PicEtAff.unit C P.cover.Carrier
          (relPicMk C (overSpec k P.cover.Carrier) F'.picClass) := rfl
    _ = PicEtAff.unit C P.cover.Carrier
          (relPicMk C (overSpec k P.cover.Carrier) P.datum.cechPicClass) := by
        rw [hrelB]
    _ = PicEtAff.unit C P.cover.Carrier
          (P.representative : relPic C (overSpec k P.cover.Carrier)) := by
        rw [← P.datum_class]
    _ = PicEtAff.mapAlg C ((Algebra.ofId A P.cover.Carrier).restrictScalars k)
          (picEtAffineEquiv C A lam.1) := htarget.symm

end PicRankOneLocalPresentation

end AlgebraicGeometry
