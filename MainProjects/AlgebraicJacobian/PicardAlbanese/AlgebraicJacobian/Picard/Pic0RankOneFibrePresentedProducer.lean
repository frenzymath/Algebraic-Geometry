/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlgebraicJacobian.Picard.DivRankOneOpen
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentation

/-!
# Assembly from a rank-one divisor-fibre pullback

This file isolates the last presheaf step in the arbitrary-scheme rank-one fibre construction.
Its input ties an open `W` to the displayed family, supplies native presentations on every
affine pullback, and supplies the canonical evaluation-divisor classifier.  The geometric input
to the assembly theorem is the genuine pullback square of that evaluation divisor along Abel.
The universal property of this stronger square produces, rather than assumes, the factorisation
field of `PicRankOneOpen.FibrePresented`.

The global construction of the canonical classifier and its represented pullbacks remains an
upstream obligation.  The endpoint here keeps that obligation in its geometric `IsPullback`
form and feeds the resulting arbitrary-scheme fibres immediately to
`picRankOneOpen_isOpen_of_fibrePresented`.

Thus this module is a conditional assembly interface, not the missing global producer: no
declaration below constructs the evaluator, the open family, or its pullback theorem.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
  CartesianMonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

noncomputable section

abbrev rankOneAmbient : Schemeᵒᵖ ⥤ Type u :=
  Over.sigmaExtension (Spec (.of k))
    (picDegLayerFunctor C (genus C : ℤ))

abbrev rankOneLocus : Schemeᵒᵖ ⥤ Type u :=
  Over.sigmaExtension (Spec (.of k)) (PicRankOneOpen pi).toFunctor

/-- The divisor families whose Abel class has a rank-one presentation, extended to the big site. -/
abbrev rankOneDivisorLocus : Schemeᵒᵖ ⥤ Type u :=
  Over.sigmaExtension (Spec (.of k))
    (divRankOnePresentationPreimageRepresenter pi).toFunctor

/-- The restricted represented Abel map on the big site. -/
def rankOneAbelSigma :
    rankOneDivisorLocus (C := C) (pi := pi) ⟶
      rankOneLocus (C := C) (pi := pi) :=
  Over.sigmaExtensionNat (rankOneAbelRepresented pi)

/-- The ambient class of a divisor already known to lie in the rank-one presentation preimage. -/
def rankOneDivisorToAmbient :
    rankOneDivisorLocus (C := C) (pi := pi) ⟶ rankOneAmbient (C := C) :=
  rankOneAbelSigma pi ≫ picRankOneOpenSigmaIncl pi

/-! ## The explicit geometric input -/

/-- The single canonical evaluation-divisor classifier used by every represented fibre.

Keeping this datum outside `PicRankOneFibrePresentationInput` prevents the classifier from
varying with the test scheme or displayed family. -/
structure PicRankOneEvaluationDivisorData where
  divisor : rankOneLocus (C := C) (pi := pi) ⟶
    rankOneDivisorLocus (C := C) (pi := pi)
  divisor_abel : divisor ≫ rankOneAbelSigma pi = 𝟙 _

namespace PicRankOneEvaluationDivisorData

/-- Applying restricted Abel to the canonical evaluation divisor recovers its rank-one class. -/
lemma divisor_abel_app (E : PicRankOneEvaluationDivisorData pi)
    (S : Scheme.{u}) (v : (rankOneLocus (C := C) (pi := pi)).obj (op S)) :
    (rankOneAbelSigma pi).app (op S) (E.divisor.app (op S) v) = v := by
  exact congrArg (fun q => q.app (op S) v) E.divisor_abel

/-- The canonical divisor has the original ambient Picard class. -/
lemma divisor_toAmbient (E : PicRankOneEvaluationDivisorData pi) :
    E.divisor ≫ rankOneDivisorToAmbient pi = picRankOneOpenSigmaIncl pi := by
  rw [rankOneDivisorToAmbient, ← Category.assoc, E.divisor_abel, Category.id_comp]

/-- The separate uniqueness obligation saying every divisor in the rank-one presentation
preimage is the canonical evaluation divisor of its Abel class. -/
def AbelInverse (E : PicRankOneEvaluationDivisorData pi) : Prop :=
  rankOneAbelSigma pi ≫ E.divisor = 𝟙 _

/-- Once divisor uniqueness is proved, restricted Abel and canonical evaluation form the
rank-one family isomorphism. -/
def evaluationIso (E : PicRankOneEvaluationDivisorData pi) (h : E.AbelInverse) :
    rankOneDivisorLocus (C := C) (pi := pi) ≅ rankOneLocus (C := C) (pi := pi) where
  hom := rankOneAbelSigma pi
  inv := E.divisor
  hom_inv_id := h
  inv_hom_id := E.divisor_abel

end PicRankOneEvaluationDivisorData

/--
The explicit data needed to assemble one arbitrary-scheme rank-one fibre.

`restrictedValue` is the restriction of the displayed ambient family to `W`, and
`nativePresentation` quantifies over every affine pullback of that value.  The parameter `E` is
the common evaluation-divisor classifier on the rank-one locus, with its Abel compatibility
kept explicit.  Divisor representability is deliberately not a field of this structure: it is
supplied separately as a pullback square to the assembly theorem.

In particular, no field-fibre dimension witness, unrelated line bundle, or pre-existing
`PicRankOneOpen.FibrePresented` is accepted by this contract.  Conversely, this structure is not
itself a producer: an inhabitant must still supply the arbitrary-affine native presentations.
-/
structure PicRankOneFibrePresentationInput
    (E : PicRankOneEvaluationDivisorData pi)
    {X : Scheme.{u}}
    (g : yoneda.obj X ⟶ rankOneAmbient (C := C)) where
  W : X.Opens
  restrictedValue : rankOneAmbient (C := C).obj (op (W : Scheme.{u}))
  restrictedValue_eq :
    restrictedValue =
      (yoneda.map W.ι ≫ g).app (op (W : Scheme.{u})) (𝟙 (W : Scheme.{u}))
  /-- The tied native presentation on every affine pullback of the restricted family value. -/
  nativePresentation :
    ∀ (A : Type u) [CommRing A] [Algebra k A]
      (t : overSpec k A ⟶ Over.mk restrictedValue.1),
      Nonempty (PicRankOneNativePresentation pi
        ((picDegLayerFunctor C (genus C : ℤ)).map t.op restrictedValue.2))

namespace PicRankOneFibrePresentationInput

variable {X : Scheme.{u}}
variable {g : yoneda.obj X ⟶ rankOneAmbient (C := C)}
variable {E : PicRankOneEvaluationDivisorData pi}

/-- The public-locus element carried by the restricted family value over `W`. -/
noncomputable def locusValue (F : PicRankOneFibrePresentationInput pi E g) :
    (rankOneLocus (C := C) (pi := pi)).obj (op (F.W : Scheme.{u})) :=
  ⟨F.restrictedValue.1, ⟨F.restrictedValue.2,
    mem_picRankOneOpen_of_nativePresentations pi
      (fun A _ _ t => F.nativePresentation A t)⟩⟩

/-- The map into the public locus is obtained from its universal element by Yoneda. -/
noncomputable def fst (F : PicRankOneFibrePresentationInput pi E g) :
    yoneda.obj (F.W : Scheme.{u}) ⟶ rankOneLocus (C := C) (pi := pi) :=
  yonedaEquiv.symm F.locusValue

/-- The canonical evaluation divisor of the restricted family value over `W`. -/
noncomputable def evaluationDivisor
    (F : PicRankOneFibrePresentationInput pi E g) :
    yoneda.obj (F.W : Scheme.{u}) ⟶ rankOneDivisorLocus (C := C) (pi := pi) :=
  F.fst ≫ E.divisor

/-- The factorisation clause required by `PicRankOneOpen.FibrePresented`, exposed as the target
of the represented evaluation-divisor argument below. -/
def FibreFactorizationClause
    (F : PicRankOneFibrePresentationInput pi E g) : Prop :=
  ∀ (S : Scheme.{u}) (v : (rankOneLocus (C := C) (pi := pi)).obj (op S)) (w : S ⟶ X),
    (picRankOneOpenSigmaIncl pi).app (op S) v =
      g.app (op S) w →
    ∃ u : S ⟶ (F.W : Scheme.{u}),
      F.fst.app (op S) u = v ∧ u ≫ F.W.ι = w

lemma fst_comp_incl (F : PicRankOneFibrePresentationInput pi E g) :
    F.fst ≫ picRankOneOpenSigmaIncl pi = yoneda.map F.W.ι ≫ g := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, fst, Equiv.apply_symm_apply, yonedaEquiv_apply,
    ← F.restrictedValue_eq]
  dsimp [locusValue, picRankOneOpenSigmaIncl,
    CategoryTheory.Over.sigmaExtensionNat]
  rfl

/-- The family evaluation divisor has the displayed family as its Abel class. -/
lemma evaluationDivisor_abel
    (F : PicRankOneFibrePresentationInput pi E g) :
    F.evaluationDivisor ≫ rankOneDivisorToAmbient pi =
      yoneda.map F.W.ι ≫ g := by
  rw [evaluationDivisor, Category.assoc, E.divisor_toAmbient]
  exact F.fst_comp_incl

/-! ## The represented rank-one-divisor fibre square -/

/-- The open `W` represents the pullback of the restricted divisor-class map along the displayed
family, with its top map fixed by the canonical evaluation divisor.  This is stronger than the
factorisation clause for the public rank-one locus: it is a categorical pullback against the
entire restricted rank-one divisor presheaf. -/
def EvaluationDivisorPullback
    (F : PicRankOneFibrePresentationInput pi E g) : Prop :=
  IsPullback
    F.evaluationDivisor
    (yoneda.map F.W.ι)
    (rankOneDivisorToAmbient pi)
    g

/-- The represented evaluation-divisor square produces the public-locus factorisation on every
test scheme. -/
lemma fibreFactorizationClause_of_evaluationDivisorPullback
    (F : PicRankOneFibrePresentationInput pi E g)
    (hpb : F.EvaluationDivisorPullback) :
    F.FibreFactorizationClause := by
  intro S v w hvw
  have hS := (IsPullback.iff_app.mp hpb) (op S)
  rw [Types.isPullback_iff] at hS
  have hcompat :
      (rankOneDivisorToAmbient pi).app (op S)
          (E.divisor.app (op S) v) =
        g.app (op S) w := by
    have h := congrArg
      (fun q => q.app (op S) v) E.divisor_toAmbient
    change
      (rankOneDivisorToAmbient pi).app (op S)
          (E.divisor.app (op S) v) =
        (picRankOneOpenSigmaIncl pi).app (op S) v at h
    rw [h]
    exact hvw
  obtain ⟨u, huDivisor, huW⟩ :=
    hS.2.2 (E.divisor.app (op S) v) w hcompat
  change E.divisor.app (op S) (F.fst.app (op S) u) =
    E.divisor.app (op S) v at huDivisor
  change u ≫ F.W.ι = w at huW
  refine ⟨u, ?_, huW⟩
  calc
    F.fst.app (op S) u =
        (rankOneAbelSigma pi).app (op S)
          (E.divisor.app (op S) (F.fst.app (op S) u)) :=
      (E.divisor_abel_app pi S (F.fst.app (op S) u)).symm
    _ = (rankOneAbelSigma pi).app (op S) (E.divisor.app (op S) v) :=
      congrArg _ huDivisor
    _ = v := E.divisor_abel_app pi S v

/-! ## Assembly of the stronger fibre datum -/

/-- Assemble the public fibre presentation from the represented canonical evaluation-divisor
square.  Its `exists_factor` field is derived from the pullback universal property. -/
noncomputable def toFibrePresented_of_evaluationDivisorPullback
    (F : PicRankOneFibrePresentationInput pi E g)
    (hpb : F.EvaluationDivisorPullback) :
    PicRankOneOpen.FibrePresented pi g where
  W := F.W
  fst := F.fst
  sq := F.fst_comp_incl
  exists_factor := by
    simpa only [FibreFactorizationClause] using
      F.fibreFactorizationClause_of_evaluationDivisorPullback pi hpb

@[simp]
lemma toFibrePresented_of_evaluationDivisorPullback_W
    (F : PicRankOneFibrePresentationInput pi E g)
    (hpb : F.EvaluationDivisorPullback) :
    (F.toFibrePresented_of_evaluationDivisorPullback pi hpb).W = F.W :=
  rfl

lemma toFibrePresented_of_evaluationDivisorPullback_isPullback
    (F : PicRankOneFibrePresentationInput pi E g)
    (hpb : F.EvaluationDivisorPullback) :
    IsPullback F.fst (yoneda.map F.W.ι) (picRankOneOpenSigmaIncl pi) g :=
  (F.toFibrePresented_of_evaluationDivisorPullback pi hpb).isPullback

/-! ## Immediate openness consumer -/

theorem picRankOneOpen_isOpen_of_evaluationDivisorPullbackFamilies
    (E : PicRankOneEvaluationDivisorData pi)
    (D : ∀ (X : Scheme.{u})
      (g : yoneda.obj X ⟶ rankOneAmbient (C := C)),
      PicRankOneFibrePresentationInput pi E g)
    (hpb : ∀ (X : Scheme.{u})
      (g : yoneda.obj X ⟶ rankOneAmbient (C := C)),
      (D X g).EvaluationDivisorPullback) :
    PicRankOneOpen.IsOpen pi := by
  apply picRankOneOpen_isOpen_of_fibrePresented pi
  intro X g
  exact (D X g).toFibrePresented_of_evaluationDivisorPullback pi (hpb X g)

end PicRankOneFibrePresentationInput

end
end AlgebraicGeometry
