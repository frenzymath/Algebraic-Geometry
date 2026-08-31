/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneFibrePresentedProducer
import AlgebraicJacobian.Picard.Pic0RankOneUniquenessDischarge
import AlgebraicJacobian.Picard.Pic0RigidityAffineReduction
import AlgebraicJacobian.Picard.DivisorFamilyAffClassDegree

/-!
# The Abel inverse of the canonical evaluation divisor, unconditionally

`rankOneDivisorUniqueness` (`Pic0RankOneUniquenessDischarge.lean`) settles, over every affine
test whose plus class lies in the rank-one locus, that at most one widened locally certified
divisor class of degree `genus C` has a prescribed Abel value.  This file upgrades that affine
statement into the second inverse law of the rank-one Abel/evaluation pair on the big site: every
`E : PicRankOneEvaluationDivisorData pi` automatically satisfies `E.AbelInverse`, so its
`evaluationIso` is available with no extra hypothesis.

The upgrade is genuinely local-to-global on the base, and it reuses only landed material:

* **The vehicle collapse along an affine open** (`divFamZarAffAffineEquiv_map_fromSpecAffine`):
  restricting a widened vehicle section along `Over.fromSpecAffine T U` and collapsing through the
  affine comparison recovers the section's value at the affine open `U`.  This is the `mapVal`
  no-gluing computation followed by the `Spec`-`Γ` bookkeeping identity
  `fromSpecAffine_ΓTop_comp_appLEAlgHom`.
* **Arbitrary-test uniqueness** (`divFamZarAff_eq_of_rankOne`): two widened vehicle sections over
  an arbitrary test whose Abel values agree, one of whose Abel classes lies in the rank-one locus,
  are equal.  Two sections of the widened vehicle agree iff they agree on affine opens
  (`divFamZarAff.ext`); on each affine open the pulled-back rank-one class (via
  `picRankOneOpen_map_mem` along `Over.fromSpecAffine T U`) feeds the affine
  `rankOneDivisorUniqueness`, with the affine Abel value identified through
  `picEtMap_abelDivAff'`, `picEtAffineEquiv_abelDivAff'`, and the vehicle collapse above.
* **Monomorphy of the restricted Abel map** (`rankOneAbelSigma_app_injective`): arbitrary-test
  uniqueness gives injectivity of the represented Abel map on every slice object, and the
  `Σ`-extension preserves it componentwise.

Given a right inverse (`E.divisor_abel`) and injectivity of `rankOneAbelSigma pi`, the standard
cancellation yields the left inverse `E.AbelInverse`, hence the packaged `rankOneAbelIso`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

noncomputable section

/-! ## The vehicle collapse along an affine open -/

omit [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] in
/-- Restricting a widened vehicle section along the affine-open test object `Over.fromSpecAffine
T U` and collapsing through the affine comparison recovers the section's value at `U`.  The
`mapVal` no-gluing computation and the `Spec`-`Γ` bookkeeping identity
`fromSpecAffine_ΓTop_comp_appLEAlgHom`. -/
theorem divFamZarAffAffineEquiv_map_fromSpecAffine (n : ℕ) (T : Over (Spec (.of k)))
    (s : divFamZarAff C n T) (U : T.left.affineOpens) :
    divFamZarAffAffineEquiv C n Γ(T.left, U.1)
        (divFamZarAff.map C n (Over.fromSpecAffine T U) s)
      = s.1 U := by
  rw [divFamZarAffAffineEquiv_apply, divFamZarAff.map_val,
    divFamZarAff.mapVal_eq_mapAlgHom C n (Over.fromSpecAffine T U) s
      (top_le_preimage_fromSpecAffine T U),
    ← DivFamZarAff.mapAlgHom_comp, fromSpecAffine_ΓTop_comp_appLEAlgHom T U,
    DivFamZarAff.mapAlgHom_id]

/-! ## Arbitrary-test uniqueness of the widened Abel map on the rank-one locus -/

/-- **Arbitrary-test rank-one uniqueness**: two widened vehicle sections over an arbitrary test
`T` whose widened Abel values agree, one of whose Abel classes lies in the rank-one locus, are
equal.  The vehicle is separated by affine opens, and on each affine open the pulled-back rank-one
class feeds the affine `rankOneDivisorUniqueness`. -/
theorem divFamZarAff_eq_of_rankOne (T : Over (Spec (.of k)))
    (s₁ s₂ : divFamZarAff C (genus C) T)
    (hs₁ : (abelDivAffTrans C (genus C)).app (op T) s₁ ∈ (PicRankOneOpen pi).obj (op T))
    (habel : abelDivAff' C (genus C) T s₁ = abelDivAff' C (genus C) T s₂) :
    s₁ = s₂ := by
  refine divFamZarAff.ext fun U => ?_
  -- pull the rank-one class back along the affine-open test object
  have hmem : (picDegLayerFunctor C (genus C : ℤ)).map (Over.fromSpecAffine T U).op
        ((abelDivAffTrans C (genus C)).app (op T) s₁)
      ∈ (PicRankOneOpen pi).obj (op (overSpec k Γ(T.left, U.1))) :=
    picRankOneOpen_map_mem pi (Over.fromSpecAffine T U).op hs₁
  -- the pulled-back Abel value is the affine Abel value of `s₁.1 U`
  have hval : abelDivAffPlus C Γ(T.left, U.1) (s₁.1 U)
      = picEtAffineEquiv C Γ(T.left, U.1)
          ((picDegLayerFunctor C (genus C : ℤ)).map (Over.fromSpecAffine T U).op
            ((abelDivAffTrans C (genus C)).app (op T) s₁)).1 := by
    have h1 : ((picDegLayerFunctor C (genus C : ℤ)).map (Over.fromSpecAffine T U).op
          ((abelDivAffTrans C (genus C)).app (op T) s₁)).1
        = picEtMap C (Over.fromSpecAffine T U) (abelDivAff' C (genus C) T s₁) := rfl
    rw [h1, picEtMap_abelDivAff', picEtAffineEquiv_abelDivAff',
      divFamZarAffAffineEquiv_map_fromSpecAffine]
  -- the two affine Abel values agree, from equality of the vehicle Abel values
  have hU := congrArg (fun w : picEt C T => w.1 U) habel
  rw [abelDivAff'_val, abelDivAff'_val] at hU
  exact rankOneDivisorUniqueness pi Γ(T.left, U.1) _ hmem (s₁.1 U) (s₂.1 U) hval
    (hU.symm.trans hval)

/-! ## Monomorphy of the restricted Abel map -/

/-- The represented Abel map is injective on every slice object: this is arbitrary-test
uniqueness read through the subfunctor preimage plumbing. -/
theorem rankOneAbelRepresented_app_injective (Z : Over (Spec (.of k))) :
    Function.Injective ((rankOneAbelRepresented pi).app (op Z)) := by
  intro x y h
  have hinj : Function.Injective
      ((divFunctorAff_genus_representableBy C).toIso.hom.app (op Z)) :=
    Function.LeftInverse.injective fun a =>
      (divFunctorAff_genus_representableBy C).toIso.hom_inv_id_app_apply (op Z) a
  set sx := (divFunctorAff_genus_representableBy C).toIso.hom.app (op Z) x.val with hsx
  set sy := (divFunctorAff_genus_representableBy C).toIso.hom.app (op Z) y.val with hsy
  -- the underlying widened Abel values agree
  have happ : ∀ w : (divRankOnePresentationPreimageRepresenter pi).toFunctor.obj (op Z),
      ((rankOneAbelRepresented pi).app (op Z) w).val
        = (abelDivAffTrans C (genus C)).app (op Z)
            ((divFunctorAff_genus_representableBy C).toIso.hom.app (op Z) w.val) := fun _ => rfl
  have hval : (abelDivAffTrans C (genus C)).app (op Z) sx
      = (abelDivAffTrans C (genus C)).app (op Z) sy := by
    have := congrArg Subtype.val h
    rwa [happ, happ] at this
  have habel : abelDivAff' C (genus C) Z sx = abelDivAff' C (genus C) Z sy := by
    have := congrArg Subtype.val hval
    rwa [abelDivAffTrans_app_coe, abelDivAffTrans_app_coe] at this
  -- membership of the rank-one class of `sx`
  have hmem : (abelDivAffTrans C (genus C)).app (op Z) sx
      ∈ (PicRankOneOpen pi).obj (op Z) := x.property
  -- arbitrary-test uniqueness forces the vehicle sections to agree
  have hsxy : sx = sy := divFamZarAff_eq_of_rankOne pi Z sx sy hmem habel
  exact Subtype.ext (hinj (hsx ▸ hsy ▸ hsxy))

/-- Componentwise injectivity of the restricted represented Abel map on the big site: the
`Σ`-extension preserves the slicewise injectivity of `rankOneAbelRepresented`. -/
theorem rankOneAbelSigma_app_injective (Y : Schemeᵒᵖ) :
    Function.Injective ((rankOneAbelSigma pi).app Y) := by
  rintro ⟨a, ξ⟩ ⟨b, η⟩ h
  have ha : (⟨a, (rankOneAbelRepresented pi).app (op (Over.mk a)) ξ⟩ :
        Σ c : Y.unop ⟶ Spec (.of k),
          (PicRankOneOpen pi).toFunctor.obj (op (Over.mk c)))
      = ⟨b, (rankOneAbelRepresented pi).app (op (Over.mk b)) η⟩ := h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp ha
  simp only [heq_eq_eq] at h2
  obtain rfl := rankOneAbelRepresented_app_injective pi (Over.mk a) h2
  rfl

/-! ## The Abel inverse and the packaged iso -/

namespace PicRankOneEvaluationDivisorData

/-- **The Abel inverse law holds automatically**: every canonical evaluation-divisor classifier
of the rank-one locus is a two-sided inverse of the restricted Abel map.  From the right inverse
`E.divisor_abel` and injectivity of `rankOneAbelSigma pi`, the left inverse follows by
cancellation. -/
theorem abelInverse_of_uniqueness (E : PicRankOneEvaluationDivisorData pi) :
    E.AbelInverse := by
  have h : rankOneAbelSigma pi ≫ E.divisor
      = 𝟙 (rankOneDivisorLocus (C := C) (pi := pi)) := by
    ext Y d
    change E.divisor.app Y ((rankOneAbelSigma pi).app Y d) = d
    apply rankOneAbelSigma_app_injective pi Y
    exact E.divisor_abel_app pi Y.unop ((rankOneAbelSigma pi).app Y d)
  exact h

/-- The rank-one family isomorphism, with the Abel inverse discharged: the restricted Abel map
and the canonical evaluation divisor are mutually inverse on the big site. -/
noncomputable def rankOneAbelIso (E : PicRankOneEvaluationDivisorData pi) :
    rankOneDivisorLocus (C := C) (pi := pi) ≅ rankOneLocus (C := C) (pi := pi) :=
  E.evaluationIso pi (E.abelInverse_of_uniqueness pi)

end PicRankOneEvaluationDivisorData

end

end AlgebraicGeometry
