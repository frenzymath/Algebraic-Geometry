/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.Pic0RankOneTranslatedCoverGeneral
import AlgebraicJacobian.Picard.DegreeAtBaseField

/-!
# The translated cover in the genus-degree layer

The separably closed translated-drop producer already supplies an exact lambda-tied
`IsSplitWitness`.  This file records the additional degree calculation needed to place that
translated class in the native `picDegLayer C (genus C)` carrier.  The calculation uses the
actual residual class `W₀ - S`, its base subtraction, and the presenting equation for the original
input class; it does not replace the input by a fieldwise existential.

The arbitrary-affine `PicRankOneLocalPresentation` family remains a separate integration
obligation.  Consequently this file stops at the exact ambient layer consumed by `PicRankOneOpen`
and does not assert locus membership without that protected presentation producer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! A field point of `overSpec k K` is induced by its structure-field map, so degree at that
point agrees with degree at the identity.  Keeping this local avoids enlarging the base-change
API for a fact used only by the layer bridge. -/
private theorem degAt_eq_degAt_id_of_overSpec
    {K K' : Type u} [Field K] [Algebra k K] [Field K'] [Algebra k K']
    (lam : picEt C (overSpec k K))
    (t : overSpec k K' ⟶ overSpec k K) :
    degAt lam t = degAt lam (𝟙 (overSpec k K)) := by
  let phiRing : K →+* K' := (Spec.preimage t.left).hom
  have hw : t.left ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K')) := by
    change t.left ≫ (overSpec k K).hom = (overSpec k K').hom
    exact Over.w t
  have hcat :
      CommRingCat.ofHom (algebraMap k K) ≫ Spec.preimage t.left =
        CommRingCat.ofHom (algebraMap k K') := by
    calc
      _ = Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
          Spec.preimage t.left := by rw [Spec.preimage_map]
      _ = Spec.preimage
          (t.left ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
        (Spec.preimage_comp t.left
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).symm
      _ = Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap k K'))) :=
        congrArg Spec.preimage hw
      _ = _ := Spec.preimage_map _
  have hcomm : ∀ x : k,
      phiRing (algebraMap k K x) = algebraMap k K' x := by
    intro x
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcat) x
  let phi : K →ₐ[k] K' := AlgHom.mk phiRing hcomm
  have ht : Over.overSpecMap phi = t := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom phi.toRingHom) = t.left
    rw [show CommRingCat.ofHom phi.toRingHom = Spec.preimage t.left from rfl,
      Spec.map_preimage]
  rw [← ht]
  calc
    degAt lam (Over.overSpecMap phi) =
        degAt lam (Over.overSpecMap phi ≫ 𝟙 (overSpec k K)) := by
      rw [Category.comp_id]
    _ = degAt lam (𝟙 (overSpec k K)) :=
      degAt_overSpecMap lam phi (𝟙 (overSpec k K))

section Layer

variable {K L : Type u} [Field K] [Algebra k K] [Field L] [Algebra k L]
  [Algebra K L] [IsScalarTower k K L]

/-- The exact degree-genus-layer object carried by a translated-drop result.

The underlying class is the result's translated input, and the subtype proof is computed from
the residual class `W₀ - S`.  Thus the output is directly an element of the `picDegLayer` target
used by `PicRankOneOpen`, rather than a parallel existential carrier. -/
noncomputable def SepClosedTranslatedDropResult.rankOneLayer
    (mu : picEt C (overSpec k K))
    (d : SepClosedTranslatedDropData (C := C) (L := L) mu)
    (r : SepClosedTranslatedDropResult (C := C) (L := L) mu d) :
    picDegLayer C (genus C : ℤ) (overSpec k K) := by
  let translated : picEt C (overSpec k K) := mu * thetaFamily C
    (chartTwistClass C d.m r.Z) (overSpec k K)
  have hgenusInt : (d.genusValue : ℤ) = (genus C : ℤ) := by
    have hchiC := chi_moduleKSheaf C
    linarith [d.hχ]
  have hW₀ := d.hW₀
  have hSZ := r.baseClass
  have hW :
      Scheme.CurveDivisor.picClass L (d.W₀ - r.S) =
        d.M₀ * Scheme.CechPic.map (relCurveMap C k L)
          (chartTwistClass C d.m r.Z) := by
    unfold relCurveMap relCurve at hW₀ hSZ ⊢
    rw [sub_eq_add_neg, Scheme.CurveDivisor.picClass_add,
      Scheme.picClass_neg, hW₀, hSZ]
    simp only [map_inv, inv_inv]
    rw [mul_assoc, ← map_mul]
    simp only [chartTwistClass, Scheme.CurveDivisor.picClass_zero,
      inv_one, mul_one, pow_zero, one_mul]
  have hpresentation :=
    picEtAffineEquiv_map_chartTwistFactor_eq_unit
      C mu d.M₀ d.hM₀ d.m r.Z
  have hdegreeAtId :
      degAt translated (𝟙 (overSpec k K)) = (genus C : ℤ) := by
    unfold translated degAt
    rw [picEtMap_id]
    rw [← classDeg_presenting_eq_degAff C L _ _ hpresentation]
    rw [← hW, classDeg_picClass, Scheme.CurveDivisor.deg_sub' L, d.hdeg,
      r.degree, hgenusInt]
    ring
  refine ⟨translated, ?_⟩
  intro K' _ _ t
  rw [degAt_eq_degAt_id_of_overSpec]
  exact hdegreeAtId

@[simp]
theorem SepClosedTranslatedDropResult.rankOneLayer_coe
    (mu : picEt C (overSpec k K))
    (d : SepClosedTranslatedDropData (C := C) (L := L) mu)
    (r : SepClosedTranslatedDropResult (C := C) (L := L) mu d) :
    (r.rankOneLayer mu d).1 =
      mu * thetaFamily C (chartTwistClass C d.m r.Z) (overSpec k K) := by
  rfl

theorem SepClosedTranslatedDropResult.rankOneLayer_isSplitWitness
    (mu : picEt C (overSpec k K))
    (d : SepClosedTranslatedDropData (C := C) (L := L) mu)
    (r : SepClosedTranslatedDropResult (C := C) (L := L) mu d) :
    IsSplitWitness C (r.rankOneLayer mu d).1 := by
  rw [SepClosedTranslatedDropResult.rankOneLayer_coe]
  exact r.translated

end Layer

section GeneralConsumer

variable [IsSepClosed k]
variable {K : Type u} [Field K] [Algebra k K]

/-- The general per-`K`/per-`mu` producer, now with its translated witness in the native
genus-degree layer.  The final arbitrary-affine presentation family is intentionally not hidden:
the returned subtype is the exact input that a later `PicRankOneOpen` producer must present. -/
theorem exists_sepClosedTranslatedRankOneLayer_general
    (mu : picEt C (overSpec k K)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra K L)
        (_ : IsScalarTower k K L) (_ : Module.Finite K L)
        (_ : Algebra.IsSeparable K L)
        (d : SepClosedTranslatedDropData (C := C) (L := L) mu)
        (r : SepClosedTranslatedDropResult (C := C) (L := L) mu d),
      IsSplitWitness C (r.rankOneLayer mu d).1 := by
  obtain ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, d, ⟨r⟩⟩ :=
    exists_sepClosedTranslatedDropResult_general (C := C) mu
  letI := hLfield
  letI := hkL
  letI := hKL
  letI := htow
  letI := hfin
  letI := hsep
  exact ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, d, r,
    r.rankOneLayer_isSplitWitness mu d⟩

end GeneralConsumer

end

end AlgebraicGeometry
