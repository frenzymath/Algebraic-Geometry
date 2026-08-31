/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0EndgameContract
import AlgebraicJacobian.Picard.Pic0RankOnePresentation
import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# The presentation locus for the rank-one Abel map

`PicRankOneOpen` is the functorial locus in the degree-`genus C` Picard layer whose pullback to
every affine test admits a tied `PicRankOneLocalPresentation`.  Quantifying after every affine
pullback makes the condition intrinsic on arbitrary test schemes; stability under further
pullback is exactly `picEtMap_comp`.

The remaining declarations form the corresponding preimages in the widened divisor functor and
in its canonical representing Yoneda functor, together with the restricted Abel transformations.
These are logical subfunctors only.  In particular, this file does not assert that
`PicRankOneOpen` is represented by an open subscheme.  The relative-openness acceptance gate and
the conditional universal-divisor carrier contract are exposed separately in `DivRankOneOpen.lean`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

noncomputable section

/-- The rank-one presentation locus in the degree-`genus C` Picard layer.

Membership means that every affine pullback of the input plus class admits a local presentation
tied to that pullback.  This is the correct logical subfunctor underlying the future open Picard
locus; no openness or representability assertion is part of this definition. -/
def PicRankOneOpen :
    Subfunctor (picDegLayerFunctor C (genus C : ℤ)) where
  obj T := {lam | ∀ (A : Type u) [CommRing A] [Algebra k A]
      (t : overSpec k A ⟶ T.unop),
    Nonempty (PicRankOneLocalPresentation pi
      ((picDegLayerFunctor C (genus C : ℤ)).map t.op lam))}
  map {T T'} f lam hlam A _ _ t := by
    let F := picDegLayerFunctor C (genus C : ℤ)
    have e : F.map t.op (F.map f lam) = F.map (t ≫ f.unop).op lam := by
      apply Subtype.ext
      exact (picEtMap_comp C f.unop t lam.1).symm
    rw [e]
    exact hlam A (t ≫ f.unop)

/-! ## The public membership contract -/

/-- The exact producer predicate for the rank-one locus.

This is intentionally lambda-tied and quantifies over every affine pullback.  In particular, it
is stronger than a field-fibre `h⁰ = 1`/`H¹ = 0` statement: a producer must supply the complete
`PicRankOneLocalPresentation` structure for the pulled-back class. -/
def PicRankOneOpen.LocalPresentationCondition
    {T : (Over (Spec (.of k)))ᵒᵖ}
    (lam : (picDegLayerFunctor C (genus C : ℤ)).obj T) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A]
    (t : overSpec k A ⟶ T.unop),
    Nonempty (PicRankOneLocalPresentation pi
      ((picDegLayerFunctor C (genus C : ℤ)).map t.op lam))

/-- Unfolded membership in `PicRankOneOpen`, with the presentation tied to the pulled-back
Picard class.  Keeping this predicate named is important for producers in later lanes: a
field-level divisor or chart witness is not a substitute for this arbitrary-affine-pullback
contract. -/
theorem mem_picRankOneOpen_iff {T : (Over (Spec (.of k)))ᵒᵖ}
    (lam : (picDegLayerFunctor C (genus C : ℤ)).obj T) :
    lam ∈ (PicRankOneOpen pi).obj T ↔
      ∀ (A : Type u) [CommRing A] [Algebra k A]
        (t : overSpec k A ⟶ T.unop),
        Nonempty (PicRankOneLocalPresentation pi
          ((picDegLayerFunctor C (genus C : ℤ)).map t.op lam)) := by
  rfl

/-- Constructor for the exact lambda-tied arbitrary-affine-pullback presentation contract. -/
theorem mem_picRankOneOpen_of_localPresentations
    {T : (Over (Spec (.of k)))ᵒᵖ}
    {lam : (picDegLayerFunctor C (genus C : ℤ)).obj T}
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A]
        (t : overSpec k A ⟶ T.unop),
        Nonempty (PicRankOneLocalPresentation pi
          ((picDegLayerFunctor C (genus C : ℤ)).map t.op lam))) :
    lam ∈ (PicRankOneOpen pi).obj T :=
  (mem_picRankOneOpen_iff pi lam).mpr h

/-- Constructor using the named arbitrary-affine producer predicate. -/
theorem mem_picRankOneOpen_of_localPresentationCondition
    {T : (Over (Spec (.of k)))ᵒᵖ}
    {lam : (picDegLayerFunctor C (genus C : ℤ)).obj T}
    (h : PicRankOneOpen.LocalPresentationCondition pi lam) :
    lam ∈ (PicRankOneOpen pi).obj T := by
  exact mem_picRankOneOpen_of_localPresentations pi h

/-- The inclusion of the public rank-one locus into its degree-genus ambient functor. -/
def picRankOneOpenIncl :
    (PicRankOneOpen pi).toFunctor ⟶ picDegLayerFunctor C (genus C : ℤ) :=
  (PicRankOneOpen pi).ι

/-- The same inclusion after the slice-to-big-site `Σ` extension.

`IsOpenImmersion.presheaf` is a property of presheaves on schemes.  The rank-one functor is
defined on the slice over `Spec k`, so the `Σ` extension is the category-correct carrier for the
relative-open gate below. -/
def picRankOneOpenSigmaIncl :
    Over.sigmaExtension (Spec (.of k)) (PicRankOneOpen pi).toFunctor ⟶
      Over.sigmaExtension (Spec (.of k)) (picDegLayerFunctor C (genus C : ℤ)) :=
  Over.sigmaExtensionNat (PicRankOneOpen pi).ι

/-- Relative openness of the public locus, in Mathlib's presheaf sense.

This is a named acceptance gate rather than an unproved global assertion.  A future geometric
producer discharges it by supplying the represented open pullbacks; no arbitrary `Subfunctor` is
silently treated as an open subscheme. -/
def PicRankOneOpen.IsOpen : Prop :=
  IsOpenImmersion.presheaf (picRankOneOpenSigmaIncl pi)

/-! ## The explicit fibre producer contract -/

/-- A fibre of the rank-one locus over one test class, presented by an open of that test.

The `exists_factor` field is tied to the displayed class `g` and to an arbitrary source value `v`.
It is the family-level content needed for relative representability; the open immersion itself
supplies uniqueness of the factor.  Thus this structure cannot be inhabited by an unrelated open
or by a fieldwise dimension statement. -/
structure PicRankOneOpen.FibrePresented
    {X : Scheme.{u}}
    (g : yoneda.obj X ⟶
      Over.sigmaExtension (Spec (.of k)) (picDegLayerFunctor C (genus C : ℤ))) where
  W : X.Opens
  fst : yoneda.obj (W : Scheme.{u}) ⟶
    Over.sigmaExtension (Spec (.of k)) (PicRankOneOpen pi).toFunctor
  sq : fst ≫ picRankOneOpenSigmaIncl pi = yoneda.map W.ι ≫ g
  exists_factor : ∀ (S : Scheme.{u})
    (v : (Over.sigmaExtension (Spec (.of k)) (PicRankOneOpen pi).toFunctor).obj (Opposite.op S))
    (w : S ⟶ X),
    (picRankOneOpenSigmaIncl pi).app (Opposite.op S) v =
      g.app (Opposite.op S) w →
    ∃ u : S ⟶ (W : Scheme.{u}),
      fst.app (Opposite.op S) u = v ∧ u ≫ W.ι = w

namespace PicRankOneOpen.FibrePresented

variable {X : Scheme.{u}}
variable {g : yoneda.obj X ⟶
  Over.sigmaExtension (Spec (.of k)) (picDegLayerFunctor C (genus C : ℤ))}

/-- The fibre square supplied by `FibrePresented` is a pullback of presheaves. -/
theorem isPullback (D : PicRankOneOpen.FibrePresented pi g) :
    IsPullback D.fst (yoneda.map D.W.ι) (picRankOneOpenSigmaIncl pi) g := by
  refine IsPullback.of_forall_isPullback_app fun S => ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun φ : yoneda.obj (D.W : Scheme.{u}) ⟶
      Over.sigmaExtension (Spec (.of k)) (picDegLayerFunctor C (genus C : ℤ)) =>
      φ.app S) D.sq
  · rintro u₁ u₂ ⟨-, h₂⟩
    exact (cancel_mono D.W.ι).mp h₂
  · intro v w hvw
    obtain ⟨u, hu₁, hu₂⟩ := D.exists_factor S.unop v w hvw
    exact ⟨u, hu₁, hu₂⟩

end PicRankOneOpen.FibrePresented

/-- An arbitrary-test fibre producer discharges the relative openness gate. -/
theorem picRankOneOpen_isOpen_of_fibrePresented
    (D : ∀ (X : Scheme.{u})
      (g : yoneda.obj X ⟶
        Over.sigmaExtension (Spec (.of k)) (picDegLayerFunctor C (genus C : ℤ))),
      PicRankOneOpen.FibrePresented pi g) :
    PicRankOneOpen.IsOpen pi := by
  refine MorphismProperty.relative.of_exists ?_
  intro X g
  let d := D X g
  exact ⟨d.W, d.fst, d.W.ι, d.isPullback, inferInstance⟩

/-- Expose a supplied relative-open certificate without hiding it behind typeclass search. -/
theorem picRankOneOpen_isOpen_of_certificate
    (h : PicRankOneOpen.IsOpen pi) : PicRankOneOpen.IsOpen pi :=
  h

/-- Extract the open immersion supplied by the relative-openness certificate on an arbitrary
pullback.  This is the exact shape consumed by an eventual chart/fibre producer. -/
theorem picRankOneOpen_openPullback
    (h : PicRankOneOpen.IsOpen pi)
    {X Z : Scheme.{u}}
    (g : yoneda.obj X ⟶
      Over.sigmaExtension (Spec (.of k)) (picDegLayerFunctor C (genus C : ℤ)))
    (fst : yoneda.obj Z ⟶
      Over.sigmaExtension (Spec (.of k)) (PicRankOneOpen pi).toFunctor)
    (snd : Z ⟶ X)
    (hpb : IsPullback fst (yoneda.map snd) (picRankOneOpenSigmaIncl pi) g) :
    IsOpenImmersion snd :=
  h.property g fst snd hpb

/-- Pullback stability of the public rank-one locus, exposed independently of its definition. -/
theorem picRankOneOpen_map_mem {T T' : (Over (Spec (.of k)))ᵒᵖ}
    (f : T ⟶ T') {lam : (picDegLayerFunctor C (genus C : ℤ)).obj T}
    (h : lam ∈ (PicRankOneOpen pi).obj T) :
    (picDegLayerFunctor C (genus C : ℤ)).map f lam ∈ (PicRankOneOpen pi).obj T' :=
  (PicRankOneOpen pi).map f h

/-- Pullback stability of the public locus, with the base-change direction made explicit. -/
theorem picRankOneOpen_baseChange_mem {T T' : (Over (Spec (.of k)))ᵒᵖ}
    (f : T ⟶ T') {lam : (picDegLayerFunctor C (genus C : ℤ)).obj T}
    (h : lam ∈ (PicRankOneOpen pi).obj T) :
    (picDegLayerFunctor C (genus C : ℤ)).map f lam ∈ (PicRankOneOpen pi).obj T' :=
  picRankOneOpen_map_mem pi f h

/-- The inverse image of `PicRankOneOpen` under the affine widened Abel transformation.

This name deliberately records only a presentation-theoretic preimage.  It is not the future
open subscheme `DivRankOneOpen`. -/
def divRankOnePresentationPreimageAff :
    Subfunctor (divFunctorAff C (genus C)) :=
  (PicRankOneOpen pi).preimage (abelDivAffTrans C (genus C))

/-- The same presentation preimage on the Yoneda functor of the canonical genus divisor
representer. -/
def divRankOnePresentationPreimageRepresenter :
    Subfunctor (yoneda.obj (divRepAffGenusScheme C)) :=
  (divRankOnePresentationPreimageAff pi).preimage
    (divFunctorAff_genus_representableBy C).toIso.hom

/-- The affine Abel transformation restricted to the rank-one presentation preimage. -/
def rankOneAbelAff :
    (divRankOnePresentationPreimageAff pi).toFunctor ⟶
      (PicRankOneOpen pi).toFunctor :=
  (PicRankOneOpen pi).fromPreimage (abelDivAffTrans C (genus C))

/-- Restrict the canonical representation isomorphism to the rank-one presentation preimage. -/
def rankOneRepresenterRestriction :
    (divRankOnePresentationPreimageRepresenter pi).toFunctor ⟶
      (divRankOnePresentationPreimageAff pi).toFunctor :=
  (divRankOnePresentationPreimageAff pi).fromPreimage
    (divFunctorAff_genus_representableBy C).toIso.hom

/-- The represented genus Abel map restricted to the rank-one presentation preimage. -/
def rankOneAbelRepresented :
    (divRankOnePresentationPreimageRepresenter pi).toFunctor ⟶
      (PicRankOneOpen pi).toFunctor :=
  rankOneRepresenterRestriction pi ≫ rankOneAbelAff pi

/-- Immediate consumer theorem: the restricted represented Abel map lands in the public locus.
The stronger canonical inverse still needs the family-level divisor/evaluation producer; this
theorem records the exact target API that consumer lanes can use today. -/
theorem rankOneAbelRepresented_mem {T : (Over (Spec (.of k)))ᵒᵖ}
    (x : (divRankOnePresentationPreimageRepresenter pi).obj T) :
    ((rankOneAbelRepresented pi).app T x :
      (picDegLayerFunctor C (genus C : ℤ)).obj T) ∈ (PicRankOneOpen pi).obj T :=
  ((rankOneAbelRepresented pi).app T x).property

end

end AlgebraicGeometry
