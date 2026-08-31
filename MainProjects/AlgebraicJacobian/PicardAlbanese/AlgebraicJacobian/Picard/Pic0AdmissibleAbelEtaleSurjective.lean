/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveSpreadDescent
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveCover
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveHonest

/-!
# Etale-local surjectivity of the admissible Abel transformation

Every point of the degree-zero relative Picard sheaf admits, after an etale cover,
a lift to the widened divisor family at the admissible parameter.  The cover is
assembled from pointwise etale neighbourhoods on which the admissible chart twist
is represented by an effective divisor family.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

noncomputable section

variable {k : Type u} [Field k]

noncomputable local instance instIntegralSurj
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothSurj
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQuasiCompactSurj
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instFiniteH0Surj
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFiniteH1Surj
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option maxHeartbeats 1000000 in
-- The affine callback combines honestification, pointwise spreading, and Sigma evaluation.
/-- The admissible widened Abel transformation is locally surjective for the etale topology. -/
theorem isLocallySurjective_abelSigmaChartAffAdmissible
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] :
    Presheaf.IsLocallySurjective Scheme.etaleTopology
      (abelSigmaChartAffAdmissible C) := by
  classical
  let m := admissibleAbelChartIndex C
  let Z := admissibleAbelChartDivisor C
  let hdeg := admissibleAbelChartDivisor_degree C
  refine isLocallySurjective_etale_of_affine _ ?_
  intro Y hY s
  rcases s with ⟨a, lam⟩
  let T : Over (Spec (.of k)) := Over.mk a
  letI : IsAffine T.left := by
    change IsAffine Y
    exact hY
  let U : T.left.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let A : Type u := Γ(T.left, U.1)
  let e : overSpec k A ⟶ T := Over.fromSpecAffine T U
  let lamA : pic0Subgroup C (overSpec k A) := pic0Map C e lam
  obtain ⟨E, c, D, hpic, hD, hvan⟩ :=
    exists_admissibleAbelDatum_of_affine (C := C) lamA
  let gE : overSpec k E.Carrier ⟶ overSpec k A :=
    Over.overSpecMap ((Algebra.ofId A E.Carrier).restrictScalars k)
  have hdegD : ∀ (L : Type u) [Field L] [Algebra k L]
      [Algebra E.Carrier L] [IsScalarTower k E.Carrier L],
      classDeg L (Scheme.CechPic.map (relCurveMap C E.Carrier L)
        D.cechPicClass) = (divRepAffAdmissibleParameter C : ℤ) := by
    intro L _ _ _ _
    exact classDeg_eq_of_eq_twistedClass lamA gE c
      D.cechPicClass hpic m Z hdeg hD L
  have hspread := fun p : PrimeSpectrum E.Carrier ↦
    D.exists_etale_divFamZarAff_of_admissible_fibre
      (divRepAffP1Map_comp C) (divRepAffAdmissibleParameter C)
      (genus C) (chi_moduleKSheaf C)
      (genus_le_divRepAffAdmissibleParameter C) hdegD p (hvan p)
  choose S instComm instAlgk instAlgE instTower instEtale q hq F hF using hspread
  letI : ∀ p, CommRing (S p) := instComm
  letI : ∀ p, Algebra k (S p) := instAlgk
  letI : ∀ p, Algebra E.Carrier (S p) := instAlgE
  letI : ∀ p, IsScalarTower k E.Carrier (S p) := instTower
  letI : ∀ p, Algebra.Etale E.Carrier (S p) := instEtale
  let cover := etalePrimeLiftCover T U E S rfl q hq
  refine ⟨cover, ?_⟩
  intro p
  change PrimeSpectrum E.Carrier at p
  let gS : overSpec k (S p) ⟶ overSpec k E.Carrier :=
    Over.overSpecMap (IsScalarTower.toAlgHom k E.Carrier (S p))
  let g : overSpec k (S p) ⟶ T :=
    etalePrimeLiftOverHom T U E S p
  let cS : (relCurve C (S p)).CechPic :=
    Scheme.CechPic.map (relCurveMap C E.Carrier (S p)) c
  have hpicS : picEtMap C g lam.1 =
      relPicToPicEt C (overSpec k (S p))
        (relPicMk C (overSpec k (S p)) cS) := by
    have hg : g = gS ≫ (gE ≫ e) := by
      apply Over.OverMorphism.ext
      rfl
    have hcurveS : (C ◁ gS).left =
        relCurveMap C E.Carrier (S p) := by
      refine congrArg
        (fun q : overSpec k (S p) ⟶ overSpec k E.Carrier ↦
          (C ◁ q).left) ?_
      exact Over.OverMorphism.ext rfl
    calc
      picEtMap C g lam.1 =
          picEtMap C gS (picEtMap C gE (picEtMap C e lam.1)) := by
        rw [hg, picEtMap_comp C (gE ≫ e) gS,
          picEtMap_comp C e gE]
      _ = picEtMap C gS (picEtMap C gE lamA.1) := by rfl
      _ = picEtMap C gS
          (relPicToPicEt C (overSpec k E.Carrier)
            (relPicMk C (overSpec k E.Carrier) c)) := by
        rw [hpic]
      _ = relPicToPicEt C (overSpec k (S p))
          (relPicMk C (overSpec k (S p)) cS) := by
        rw [picEtMap_relPicToPicEt, relPicMap_mk, hcurveS]
        rfl
  have hFtarget : (F p).picClass =
      cS * Scheme.CechPic.map (relCurveMap C k (S p))
        (chartTwistClass C m Z) := by
    rw [hF p, hD, map_mul]
    dsimp only [cS]
    congr 1
    rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
      relCurveMap_comp]
  let sF : divFamZarAff C (divRepAffAdmissibleParameter C)
      (overSpec k (S p)) :=
    (divFamZarAffAffineEquiv C (divRepAffAdmissibleParameter C)
      (S p)).symm (F p)
  let z := (divFunctorAff_admissible_representableBy C).homEquiv.symm sF
  refine ⟨z.left, ?_⟩
  rw [abelSigmaChartAffAdmissible_eq_sigmaExtension_admissibleAbelTrans C]
  have hcoverf : cover.f p = g.left := by
    dsimp only [cover, g]
    exact etalePrimeLiftCover_f T U E S rfl q hq p
  rw [hcoverf]
  change
    (((Functor.RepresentableBy.yoneda
        (divRepAffAdmissibleScheme C)).toSigmaExtension ≫
      Over.sigmaExtensionNat (admissibleAbelTrans C)).app
        (op (Spec (.of (S p))))) z.left =
      (pic0SigmaSheaf C).1.map g.left.op ⟨a, lam⟩
  have hrep :
      (((Functor.RepresentableBy.yoneda
          (divRepAffAdmissibleScheme C)).toSigmaExtension ≫
        Over.sigmaExtensionNat (admissibleAbelTrans C)).app
          (op (Spec (.of (S p))))) z.left =
        (abelSigmaChartAff C (divRepAffAdmissibleParameter C)
          (divFunctorAff_admissible_representableBy C)
          m Z hdeg).app (op (Spec (.of (S p)))) z.left := by
    rfl
  refine Eq.trans ?_ (Over.sigmaExtension_map_left_mk g lam).symm
  calc
    _ = (abelSigmaChartAff C (divRepAffAdmissibleParameter C)
          (divFunctorAff_admissible_representableBy C)
          m Z hdeg).app (op (Spec (.of (S p)))) z.left := hrep
    _ = (⟨(overSpec k (S p)).hom,
        (chartValueAffTrans C (divRepAffAdmissibleParameter C)
          m Z hdeg).app (op (overSpec k (S p))) sF⟩ :
        (pic0SigmaSheaf C).1.obj (op (Spec (.of (S p))))) := by
      exact abelSigmaChartAff_app_homEquiv_symm
        (divFunctorAff_admissible_representableBy C)
        m Z hdeg (overSpec k (S p)).hom sF
    _ = (⟨(overSpec k (S p)).hom, pic0Map C g lam⟩ :
        (pic0SigmaSheaf C).1.obj (op (Spec (.of (S p))))) := by
      rw [show sF =
          (divFamZarAffAffineEquiv C
            (divRepAffAdmissibleParameter C) (S p)).symm (F p) from rfl,
        chartValueAffTrans_app_eq_of_picClass_eq
          lam g cS hpicS m Z hdeg (F p) hFtarget]

end

end AlgebraicGeometry
