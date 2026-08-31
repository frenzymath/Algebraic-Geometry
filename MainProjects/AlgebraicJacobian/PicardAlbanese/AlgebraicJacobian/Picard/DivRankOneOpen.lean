/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneLocus
import Mathlib.AlgebraicGeometry.Restrict

/-!
# The universal divisor rank-one open contract

The genus divisor representer is unconditional, while the rank-one restriction still needs a
family-level open-locus producer.  This file separates those two facts.  The predicate below is
the inverse image of `PicRankOneOpen` along the represented universal Abel map.  A
`DivRankOneOpenData` witness identifies that predicate with the range of one actual open of the
representer; only after that witness is supplied do we define the open subscheme.

This shape prevents a logical `Subfunctor` from being silently reinterpreted as a scheme.  It also
gives the canonical inverse lane a stable contract: it consumes the witness equality and can use
the resulting open inclusion and all of its pullbacks without choosing a generator.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

noncomputable section

/-- The universal genus-divisor predicate whose Abel class lies in `PicRankOneOpen`. -/
def divRankOneUniversalPredicate :
    Subfunctor (yoneda.obj (divRepAffGenusScheme C)) :=
  divRankOnePresentationPreimageRepresenter pi

/-- Evaluation of the represented genus Abel map on a slice point, with the base morphism
transported from the point in the divisor representer to its source. -/
theorem abelDivAffGenusSigma_app_left_rankOne
    {T : Over (Spec (.of k))}
    (q : T ⟶ divRepAffGenusScheme C) :
    (abelDivAffGenusSigma C).app (op T.left) q.left =
      (⟨T.hom,
        (abelDivAffTrans C (genus C)).app (op T)
          ((divFunctorAff_genus_representableBy C).homEquiv q)⟩ :
        (Over.sigmaExtension (Spec (.of k))
          (picDegLayerFunctor C (genus C : ℤ))).obj (op T.left)) := by
  change (⟨q.left ≫ (divRepAffGenusScheme C).hom, _⟩ :
      (Over.sigmaExtension (Spec (.of k))
        (picDegLayerFunctor C (genus C : ℤ))).obj (op T.left)) =
    ⟨T.hom,
      (abelDivAffTrans C (genus C)).app (op T)
        ((divFunctorAff_genus_representableBy C).homEquiv q)⟩
  refine Over.sigmaExtension_ext
    (picDegLayerFunctor C (genus C : ℤ)) q.w ?_
  let e : Over.mk (q.left ≫ (divRepAffGenusScheme C).hom) ⟶ T :=
    Over.mkCongr q.w
  let q' : Over.mk (q.left ≫ (divRepAffGenusScheme C).hom) ⟶
      divRepAffGenusScheme C :=
    Over.homMk q.left rfl
  have hq : e ≫ q = q' := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  change (picDegLayerFunctor C (genus C : ℤ)).map e.op
      ((abelDivAffTrans C (genus C)).app (op T)
        ((divFunctorAff_genus_representableBy C).homEquiv q)) =
    (abelDivAffTrans C (genus C)).app
      (op (Over.mk (q.left ≫ (divRepAffGenusScheme C).hom)))
      ((divFunctorAff_genus_representableBy C).homEquiv q')
  have hnat := ConcreteCategory.congr_hom
    ((abelDivAffTrans C (genus C)).naturality e.op)
      ((divFunctorAff_genus_representableBy C).homEquiv q)
  have hhom :
      (divFunctorAff_genus_representableBy C).homEquiv q' =
        (divFunctorAff C (genus C)).map e.op
          ((divFunctorAff_genus_representableBy C).homEquiv q) := by
    calc
      (divFunctorAff_genus_representableBy C).homEquiv q' =
          (divFunctorAff_genus_representableBy C).homEquiv (e ≫ q) := by
            rw [hq]
      _ = (divFunctorAff C (genus C)).map e.op
          ((divFunctorAff_genus_representableBy C).homEquiv q) :=
        (divFunctorAff_genus_representableBy C).homEquiv_comp e q
  rw [hhom]
  simpa only [ConcreteCategory.comp_apply] using hnat.symm

/-- A represented genus divisor lies in the universal predicate exactly when its Abel image
lifts through the single public rank-one Picard locus. -/
theorem divRankOneUniversalPredicate_mem_iff_sigma
    {T : (Over (Spec (.of k)))ᵒᵖ}
    (x : (yoneda.obj (divRepAffGenusScheme C)).obj T) :
    x ∈ (divRankOneUniversalPredicate pi).obj T ↔
      ∃ v : (Over.sigmaExtension (Spec (.of k))
          (PicRankOneOpen pi).toFunctor).obj (op T.unop.left),
        (picRankOneOpenSigmaIncl pi).app (op T.unop.left) v =
          (abelDivAffGenusSigma C).app (op T.unop.left) x.left := by
  simp only [divRankOneUniversalPredicate,
    divRankOnePresentationPreimageRepresenter,
    Subfunctor.preimage_obj, Set.mem_preimage]
  let p := (abelDivAffTrans C (genus C)).app T
    ((divFunctorAff_genus_representableBy C).homEquiv x)
  change p ∈ (PicRankOneOpen pi).obj T ↔ _
  have hleft :
      (abelDivAffGenusSigma C).app (op T.unop.left) x.left =
        (⟨T.unop.hom, p⟩ :
          (Over.sigmaExtension (Spec (.of k))
            (picDegLayerFunctor C (genus C : ℤ))).obj
              (op T.unop.left)) :=
    abelDivAffGenusSigma_app_left_rankOne x
  constructor
  · intro hp
    refine ⟨⟨T.unop.hom, ⟨p, hp⟩⟩, ?_⟩
    rw [hleft]
    rfl
  · rintro ⟨v, hv⟩
    rw [hleft] at hv
    dsimp [picRankOneOpenSigmaIncl,
      CategoryTheory.Over.sigmaExtensionNat] at hv
    rcases v with ⟨a, y⟩
    dsimp at hv
    have hfirst : a = T.unop.hom :=
      congrArg (fun z => z.1) hv
    cases hfirst
    have hinj := Sigma.mk.inj hv
    have heq :
        ConcreteCategory.hom
            ((PicRankOneOpen pi).ι.app
              (op (Over.mk T.unop.hom))) y = p :=
      eq_of_heq hinj.2
    change p ∈ (PicRankOneOpen pi).obj T
    rw [← heq]
    exact y.property

/-- The Yoneda map induced by the inclusion of an open of an object in the slice.  Naming this
map is useful to consumers which need the actual factorisation through the open, rather than only
the proposition that a point lies in its range. -/
def openSubfunctorMap (D : Over (Spec (.of k))) (U : D.left.Opens) :
    yoneda.obj (Over.mk (U.ι ≫ D.hom)) ⟶ yoneda.obj D :=
  yoneda.map (Over.homMk (U := Over.mk (U.ι ≫ D.hom)) U.ι)

/-- The subfunctor represented by an open `U` of an object `D` in the slice over `Spec k`.

Its values are precisely morphisms which factor through the open immersion `U.ι`; using the
Yoneda range keeps this definition independent of any chosen affine presentation of `U`. -/
def openSubfunctor (D : Over (Spec (.of k))) (U : D.left.Opens) :
    Subfunctor (yoneda.obj D) :=
  Subfunctor.range (openSubfunctorMap D U)

/-- Unpack range membership into the actual source point and its equality in the ambient Yoneda
functor.  This is the pointwise factorisation API used by inverse constructions. -/
theorem openSubfunctor_mem_iff
    (D : Over (Spec (.of k))) (U : D.left.Opens)
    {T : (Over (Spec (.of k)))ᵒᵖ}
    (x : (yoneda.obj D).obj T) :
    x ∈ (openSubfunctor D U).obj T ↔
      ∃ y : (yoneda.obj (Over.mk (U.ι ≫ D.hom))).obj T,
        (openSubfunctorMap D U).app T y = x := by
  rfl

/-- An explicit geometric certificate for the universal rank-one predicate.

The equality is the missing family-level producer/gluing statement: it identifies the logical
preimage with an actual open of the canonical genus representer.  No default or top-open witness
is manufactured here. -/
structure DivRankOneOpenData (pi : C.left ⟶ P1 k) [IsFinite pi] where
  carrier : (divRepAffGenusScheme C).left.Opens
  carrier_eq :
    openSubfunctor (divRepAffGenusScheme C) carrier =
      divRankOneUniversalPredicate pi

/-- Genuine relative openness of the public Picard rank-one locus produces the universal
divisor rank-one open.  The carrier is the open image of the represented pullback of the Abel
map, and the proof below identifies its Yoneda range with the defining predicate. -/
theorem divRankOneOpenData_of_picRankOneOpen_isOpen
    (h : PicRankOneOpen.IsOpen pi) :
    Nonempty (DivRankOneOpenData pi) := by
  obtain ⟨X, snd, fst, hpb⟩ := h.rep (abelDivAffGenusSigma C)
  letI : IsOpenImmersion snd :=
    h.property (abelDivAffGenusSigma C) fst snd hpb
  let U := snd.opensRange
  refine ⟨⟨U, ?_⟩⟩
  ext T x
  rw [openSubfunctor_mem_iff]
  rw [divRankOneUniversalPredicate_mem_iff_sigma]
  have hpbT := (IsPullback.iff_app.mp hpb) (op T.unop.left)
  rw [Types.isPullback_iff] at hpbT
  constructor
  · rintro ⟨y, hy⟩
    have hxy : x.left = y.left ≫ U.ι := by
      have hleft := congrArg Over.Hom.left hy
      exact hleft.symm
    have hrange : Set.range x.left.base ⊆ Set.range snd.base := by
      rw [← Scheme.Hom.coe_opensRange snd]
      rintro z ⟨t, rfl⟩
      rw [hxy, Scheme.Hom.comp_apply]
      change U.ι.base (y.left.base t) ∈ snd.opensRange
      change U.ι.base (y.left.base t) ∈ U
      exact (y.left.base t).property
    let u : T.unop.left ⟶ X :=
      IsOpenImmersion.lift snd x.left hrange
    have hu : u ≫ snd = x.left :=
      IsOpenImmersion.lift_fac _ _ _
    refine ⟨fst.app (op T.unop.left) u, ?_⟩
    have hcomm := congrArg
      (fun f => (ConcreteCategory.hom f) u) hpbT.1
    change (picRankOneOpenSigmaIncl pi).app (op T.unop.left)
        (fst.app (op T.unop.left) u) =
      (abelDivAffGenusSigma C).app (op T.unop.left) (u ≫ snd) at hcomm
    simpa only [hu] using hcomm
  · rintro ⟨v, hv⟩
    obtain ⟨u, hu₁, hu₂⟩ := hpbT.2.2 v x.left hv
    change u ≫ snd = x.left at hu₂
    have hrange : Set.range x.left.base ⊆ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      change Set.range x.left.base ⊆ snd.opensRange
      rw [Scheme.Hom.coe_opensRange]
      rintro z ⟨t, rfl⟩
      refine ⟨u.base t, ?_⟩
      have happ := congrArg (fun f => f.base t) hu₂
      simpa only [Scheme.Hom.comp_apply] using happ
    let V : Over (Spec (.of k)) :=
      Over.mk (U.ι ≫ (divRepAffGenusScheme C).hom)
    let j : V ⟶ divRepAffGenusScheme C :=
      Over.homMk (U := V) U.ι
    let e : U.toScheme = V.left := rfl
    let l : T.unop.left ⟶ U.toScheme :=
      IsOpenImmersion.lift U.ι x.left hrange
    let l' : T.unop.left ⟶ V.left := l ≫ eqToHom e
    have he : eqToHom e ≫ j.left = U.ι := by
      subst e
      rfl
    have hl : l' ≫ j.left = x.left := by
      dsimp only [l']
      rw [Category.assoc, he]
      dsimp only [l]
      exact IsOpenImmersion.lift_fac _ _ _
    have hlw : l' ≫ V.hom = T.unop.hom := by
      rw [← j.w, ← Category.assoc, hl]
      exact x.w
    let y : (yoneda.obj V).obj T := Over.homMk l' hlw
    refine ⟨y, ?_⟩
    change y ≫ j = x
    apply Over.OverMorphism.ext
    exact hl

/-- A named carrier choice for consumers which already possess the Picard openness theorem. -/
def divRankOneOpenDataOfPicRankOneOpen
    (h : PicRankOneOpen.IsOpen pi) : DivRankOneOpenData pi :=
  Classical.choice (divRankOneOpenData_of_picRankOneOpen_isOpen pi h)

/-- The open subscheme supplied by a `DivRankOneOpenData` witness. -/
def DivRankOneOpen (h : DivRankOneOpenData (C := C) pi) : Scheme :=
  h.carrier.toScheme

/-- The canonical open immersion into the genus divisor representer. -/
def divRankOneOpenMap (h : DivRankOneOpenData (C := C) pi) :
    DivRankOneOpen pi h ⟶ (divRepAffGenusScheme C).left :=
  h.carrier.ι

theorem divRankOneOpen_isOpenImmersion
    (h : DivRankOneOpenData (C := C) pi) :
    IsOpenImmersion (divRankOneOpenMap pi h) := by
  change IsOpenImmersion h.carrier.ι
  infer_instance

/- The scheme-level certificate also has the presheaf form consumed by relative-open inverse
   constructions.  This is conditional only on the explicit carrier witness above. -/
theorem divRankOneOpenMap_presheaf_isOpenImmersion
    (h : DivRankOneOpenData (C := C) pi) :
    IsOpenImmersion.presheaf (yoneda.map (divRankOneOpenMap pi h)) := by
  exact MorphismProperty.relative_map (divRankOneOpen_isOpenImmersion pi h)

/-- The open represented object, retained in the slice over `Spec k` for consumers of the affine
divisor functor. -/
def divRankOneOpenOver (h : DivRankOneOpenData (C := C) pi) :
    Over (Spec (.of k)) :=
  Over.mk (divRankOneOpenMap pi h ≫ (divRepAffGenusScheme C).hom)

/-- The inclusion of the certified open, as a morphism in the slice over `Spec k`.

This is the map whose Yoneda action is consumed by the canonical rank-one Abel inverse.  Naming
it separately keeps consumers independent of the implementation spelling of `divRankOneOpenOver`.
-/
def divRankOneOpenOverMap (h : DivRankOneOpenData (C := C) pi) :
    divRankOneOpenOver pi h ⟶ divRepAffGenusScheme C :=
  Over.homMk (divRankOneOpenMap pi h)

/-- Pull back the certified rank-one open along an arbitrary slice morphism. -/
def divRankOneOpenPullback
    (h : DivRankOneOpenData (C := C) pi)
    {T : Over (Spec (.of k))} (q : T ⟶ divRepAffGenusScheme C) : T.left.Opens :=
  q.left ⁻¹ᵁ h.carrier

theorem divRankOneOpenPullback_isOpenImmersion
    (h : DivRankOneOpenData (C := C) pi)
    {T : Over (Spec (.of k))} (q : T ⟶ divRepAffGenusScheme C) :
    IsOpenImmersion (divRankOneOpenPullback pi h q).ι := by
  infer_instance

/-- The arbitrary slice pullback remains an open immersion after passing to Yoneda. -/
theorem divRankOneOpenPullbackMap_presheaf_isOpenImmersion
    (h : DivRankOneOpenData (C := C) pi)
    {T : Over (Spec (.of k))} (q : T ⟶ divRepAffGenusScheme C) :
    IsOpenImmersion.presheaf
      (yoneda.map (divRankOneOpenPullback pi h q).ι) := by
  exact MorphismProperty.relative_map (divRankOneOpenPullback_isOpenImmersion pi h q)

/-- Pointwise form of arbitrary base-change compatibility for the certified open. -/
theorem mem_divRankOneOpenPullback_iff
    (h : DivRankOneOpenData (C := C) pi)
    {T : Over (Spec (.of k))} (q : T ⟶ divRepAffGenusScheme C)
    (x : T.left) :
    x ∈ divRankOneOpenPullback pi h q ↔ q.left.base x ∈ h.carrier := by
  rfl

/-- The universal predicate is exactly the represented preimage used by the Abel restriction. -/
theorem divRankOneUniversalPredicate_eq_preimage :
    divRankOneUniversalPredicate pi = divRankOnePresentationPreimageRepresenter pi :=
  rfl

/-- The certified open carrier has the universal rank-one predicate as its Yoneda range. -/
theorem divRankOneOpen_carrier_eq
    (h : DivRankOneOpenData (C := C) pi) :
    openSubfunctor (divRepAffGenusScheme C) h.carrier =
      divRankOneUniversalPredicate pi :=
  h.carrier_eq

/-- Pointwise form of the witness equality, exposing the exact contract consumed by an inverse.

The right-hand side is the range of the open immersion, so a consumer can use this theorem to
replace a rank-one predicate proof by a factorisation through `DivRankOneOpen pi h`. -/
theorem divRankOneOpen_mem_iff
    (h : DivRankOneOpenData (C := C) pi)
    {T : (Over (Spec (.of k)))ᵒᵖ}
    (x : (yoneda.obj (divRepAffGenusScheme C)).obj T) :
    x ∈ (divRankOneUniversalPredicate pi).obj T ↔
      x ∈ (openSubfunctor (divRepAffGenusScheme C) h.carrier).obj T := by
  rw [h.carrier_eq]

/-- A point of the universal rank-one predicate factors through the certified open immersion.

Unlike a bare range-membership proof, the conclusion exposes the source point and the equality
of its image with the given divisor point, which is the exact data needed by a canonical inverse. -/
theorem divRankOneOpen_mem_iff_factorization
    (h : DivRankOneOpenData (C := C) pi)
    {T : (Over (Spec (.of k)))ᵒᵖ}
    (x : (yoneda.obj (divRepAffGenusScheme C)).obj T) :
    x ∈ (divRankOneUniversalPredicate pi).obj T ↔
      ∃ y : (yoneda.obj (Over.mk
          (h.carrier.ι ≫ (divRepAffGenusScheme C).hom))).obj T,
        (openSubfunctorMap (divRepAffGenusScheme C) h.carrier).app T y = x := by
  rw [divRankOneOpen_mem_iff pi h x, openSubfunctor_mem_iff]

/-- The same factorisation contract with the named open object and slice inclusion.

The source in the preceding theorem is definitionally the slice object
`divRankOneOpenOver pi h`; this corollary gives the stable public names expected by inverse
consumers. -/
theorem divRankOneOpen_mem_iff_factorization_over
    (h : DivRankOneOpenData (C := C) pi)
    {T : (Over (Spec (.of k)))ᵒᵖ}
    (x : (yoneda.obj (divRepAffGenusScheme C)).obj T) :
    x ∈ (divRankOneUniversalPredicate pi).obj T ↔
      ∃ y : (yoneda.obj (divRankOneOpenOver pi h)).obj T,
        (yoneda.map (divRankOneOpenOverMap pi h)).app T y = x := by
  rw [divRankOneOpen_mem_iff_factorization pi h x]
  rfl

/-- The exact inverse-facing factorisation for a point of the represented rank-one preimage.

The source point is retained as a subtype, so its membership proof is tied to the same divisor
that is factored through `DivRankOneOpenOver`; no unrelated class or top-open witness can satisfy
this endpoint. -/
theorem rankOneRepresenterRestriction_factorization
    (h : DivRankOneOpenData (C := C) pi)
    {T : (Over (Spec (.of k)))ᵒᵖ}
    (x : (divRankOnePresentationPreimageRepresenter pi).obj T) :
    ∃ y : (yoneda.obj (divRankOneOpenOver pi h)).obj T,
      (yoneda.map (divRankOneOpenOverMap pi h)).app T y = x.1 := by
  apply (divRankOneOpen_mem_iff_factorization_over pi h x.1).mp
  exact x.2

/-- Immediate inverse-facing consumer of Picard rank-one openness: every point of the represented
rank-one divisor preimage factors through the open carrier extracted from that certificate. -/
theorem rankOneRepresenterRestriction_factorization_of_picRankOneOpen_isOpen
    (hPic : PicRankOneOpen.IsOpen pi)
    {T : (Over (Spec (.of k)))ᵒᵖ}
    (x : (divRankOnePresentationPreimageRepresenter pi).obj T) :
    ∃ y : (yoneda.obj (divRankOneOpenOver pi
        (divRankOneOpenDataOfPicRankOneOpen pi hPic))).obj T,
      (yoneda.map (divRankOneOpenOverMap pi
        (divRankOneOpenDataOfPicRankOneOpen pi hPic))).app T y = x.1 :=
  rankOneRepresenterRestriction_factorization pi
    (divRankOneOpenDataOfPicRankOneOpen pi hPic) x

/-- A point in the certified open carrier is a point of the universal rank-one predicate. -/
theorem divRankOneOpen_mem_of_carrier
    (h : DivRankOneOpenData (C := C) pi)
    {T : (Over (Spec (.of k)))ᵒᵖ}
    {x : (yoneda.obj (divRepAffGenusScheme C)).obj T}
    (hx : x ∈ (openSubfunctor (divRepAffGenusScheme C) h.carrier).obj T) :
    x ∈ (divRankOneUniversalPredicate pi).obj T := by
  exact (divRankOneOpen_mem_iff pi h x).mpr hx

/- The logical rank-one predicate remains stable under arbitrary pullback, independently of the
   geometric witness used to represent it by an open. -/
theorem divRankOneOpen_baseChange_mem
    {T T' : (Over (Spec (.of k)))ᵒᵖ}
    (f : T ⟶ T')
    {x : (yoneda.obj (divRepAffGenusScheme C)).obj T}
    (hx : x ∈ (divRankOneUniversalPredicate pi).obj T) :
    (yoneda.obj (divRepAffGenusScheme C)).map f x ∈
      (divRankOneUniversalPredicate pi).obj T' :=
  (divRankOneUniversalPredicate pi).map f hx

end

end AlgebraicGeometry
