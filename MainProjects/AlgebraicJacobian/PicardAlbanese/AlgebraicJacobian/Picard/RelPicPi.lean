/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.CechPicClopenGlue
import AlgebraicJacobian.Picard.ProjectionUnits
import AlgebraicJacobian.Picard.RelPicAlgebra

/-!
# The relative Picard group of a finite product of test algebras

For a finite family of `k`-algebras `B i` with product `P = Π i, B i`, the spectrum of
`P` is the disjoint union of the spectra of the factors, clopen-partitioned by the basic
opens of the coordinate idempotents; base-changing along the curve, the same holds for
the curve-products.  Through the clopen decomposition of the Čech Picard group
(`AlgebraicJacobian.Picard.CechPicClopenSep`, `CechPicClopenGlue`) this identifies the
relative Picard group of the product test with the product of the relative Picard
groups:

* `AlgebraicGeometry.relPic.eq_of_pi_proj_eq`: two relative Picard classes over `P`
  with equal restrictions to every factor are equal;
* `AlgebraicGeometry.relPic.exists_pi_lift`: every family of relative Picard classes
  over the factors is the family of restrictions of a class over `P`.

The Zariski sheaf property of the affine étale Picard functor
(`AlgebraicJacobian.Picard.PicEtAffZariski`) consumes exactly these two statements.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace

namespace AlgebraicGeometry

/-! ## The whisker-left pullback square -/

namespace Over

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable {T T' : Over (Spec (.of k))}

/-- Whiskering the curve over a morphism of test objects is the base change of the
morphism along the second projection: the square

```
(C ⊗ T').left --(C ◁ g).left--> (C ⊗ T).left
     |                               |
     ↓                               ↓
   T'.left --------g.left--------> T.left
```

is a pullback. -/
theorem isPullback_whiskerLeft (g : T' ⟶ T) :
    IsPullback (C ◁ g).left (snd C T').left (snd C T).left g.left := by
  have hfst : (C ◁ g).left ≫ (fst C T).left = (fst C T').left := by
    rw [← Over.comp_left _ _ _ (C ◁ g) (fst C T), whiskerLeft_fst]
  have hw : g.left ≫ T.hom = T'.hom := Over.w g
  have s := Over.isPullback_left C T'
  rw [← hfst, ← hw] at s
  exact IsPullback.of_right s (Over.snd_left_naturality C g) (Over.isPullback_left C T)

/-- Whiskering the curve over an open immersion of test objects is an open immersion. -/
instance isOpenImmersion_whiskerLeft (g : T' ⟶ T) [IsOpenImmersion g.left] :
    IsOpenImmersion (C ◁ g).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_whiskerLeft C g).flip inferInstance

/-- The range of the whiskered curve over an open immersion of test objects is the
preimage of the range under the second projection. -/
theorem range_whiskerLeft (g : T' ⟶ T) [IsOpenImmersion g.left] :
    Set.range ((C ◁ g).left).base
      = (snd C T).left.base ⁻¹' Set.range g.left.base := by
  have sq := isPullback_whiskerLeft C g
  have hcomp : (C ◁ g).left
      = sq.isoPullback.hom ≫ pullback.fst (snd C T).left g.left :=
    (sq.isoPullback_hom_fst).symm
  have hsurj : Function.Surjective sq.isoPullback.hom.base := fun q =>
    ⟨sq.isoPullback.inv.base q, by
      rw [← Scheme.Hom.comp_apply, sq.isoPullback.inv_hom_id]
      rfl⟩
  calc Set.range ((C ◁ g).left).base
      = Set.range ((sq.isoPullback.hom ≫ pullback.fst (snd C T).left g.left).base) :=
        congrArg (fun f : (C ⊗ T').left ⟶ (C ⊗ T).left => Set.range f.base) hcomp
    _ = Set.range ((pullback.fst (snd C T).left g.left).base) := by
        rw [Scheme.Hom.comp_base]
        exact Function.Surjective.range_comp hsurj _
    _ = (snd C T).left.base ⁻¹' Set.range g.left.base :=
        IsOpenImmersion.range_pullbackFst _ _

end Over

/-! ## The clopen partition of the spectrum of a finite product -/

section PiPartition

variable {ι : Type u} [DecidableEq ι] (B : ι → Type u) [∀ i, CommRing (B i)]

/-- The algebra structure of a factor of a finite product `P = Π i, B i` via the
coordinate projection.  A scoped auxiliary; activate with
`letI := piFactorAlgebra B i`. -/
@[reducible] noncomputable def piFactorAlgebra (i : ι) : Algebra (Π j, B j) (B i) :=
  (Pi.evalRingHom B i).toAlgebra

/-- Each factor of a finite product is the localization of the product away from the
corresponding coordinate idempotent. -/
lemma isLocalization_away_piFactor (i : ι) :
    letI := piFactorAlgebra B i
    IsLocalization.Away (Pi.single i 1 : Π j, B j) (B i) := by
  letI := piFactorAlgebra B i
  refine IsLocalization.away_of_isIdempotentElem_of_mul ?_ ?_ ?_
  · have h : (Pi.single i 1 : Π j, B j) * Pi.single i 1 = Pi.single i 1 := by
      rw [← Pi.single_mul, one_mul]
    exact h
  · intro x y
    constructor
    · intro h
      have h' : x i = y i := h
      ext j
      rcases eq_or_ne j i with hj | hj
      · subst hj
        simp [h']
      · simp [hj]
    · intro h
      exact show x i = y i by
        simpa [Pi.single_apply] using congrArg (fun z => z i) h
  · intro b
    exact ⟨Pi.single i b, Pi.single_eq_same i b⟩

end PiPartition

section PiPartitionInstance

variable {ι : Type u} (B : ι → Type u) [∀ i, CommRing (B i)]
variable {k : Type u} [Field k] [∀ i, Algebra k (B i)]

/-- The coordinate projections of the spectrum of a finite product are open
immersions. -/
instance isOpenImmersion_overSpecMap_evalAlgHom (i : ι) :
    IsOpenImmersion (Over.overSpecMap (Pi.evalAlgHom k B i)).left := by
  classical
  letI := piFactorAlgebra B i
  haveI := isLocalization_away_piFactor B i
  have h := IsOpenImmersion.of_isLocalization
    (S := B i) (Pi.single i 1 : Π j, B j)
  rw [Over.overSpecMap_left]
  exact h

end PiPartitionInstance

section PiPartition

variable {ι : Type u} [DecidableEq ι] (B : ι → Type u) [∀ i, CommRing (B i)]
variable {k : Type u} [Field k] [∀ i, Algebra k (B i)]

/-- Membership in the range of a coordinate projection of spectra is membership in the
basic open of the coordinate idempotent. -/
lemma mem_opensRange_overSpecMap_evalAlgHom {i : ι}
    (p : (overSpec k (Π j, B j)).left) :
    p ∈ Scheme.Hom.opensRange (Over.overSpecMap (Pi.evalAlgHom k B i)).left
      ↔ (show PrimeSpectrum (Π j, B j) from p)
          ∈ PrimeSpectrum.basicOpen (Pi.single i 1 : Π j, B j) := by
  letI := piFactorAlgebra B i
  haveI := isLocalization_away_piFactor B i
  have hrange := PrimeSpectrum.localization_away_comap_range (S := B i)
    (Pi.single i 1 : Π j, B j)
  constructor
  · rintro ⟨q, hq⟩
    have hq' : PrimeSpectrum.comap
        (algebraMap (Π j, B j) (B i)) (show PrimeSpectrum (B i) from q)
        = (show PrimeSpectrum (Π j, B j) from p) := hq
    have hmem : (show PrimeSpectrum (Π j, B j) from p)
        ∈ (↑(PrimeSpectrum.basicOpen (Pi.single i 1 : Π j, B j)) :
            Set (PrimeSpectrum (Π j, B j))) := hrange ▸ ⟨_, hq'⟩
    exact hmem
  · intro hp
    have hmem : (show PrimeSpectrum (Π j, B j) from p)
        ∈ Set.range (PrimeSpectrum.comap (algebraMap (Π j, B j) (B i))) := by
      rw [hrange]
      exact hp
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq⟩

/-- The basic opens of the coordinate idempotents are pairwise disjoint. -/
lemma basicOpen_single_disjoint {i j : ι} (hij : i ≠ j) :
    PrimeSpectrum.basicOpen (Pi.single i 1 : Π l, B l)
      ⊓ PrimeSpectrum.basicOpen (Pi.single j 1 : Π l, B l) = ⊥ := by
  rw [← PrimeSpectrum.basicOpen_mul]
  have hzero : (Pi.single i 1 : Π l, B l) * Pi.single j 1 = 0 := by
    ext l
    rcases eq_or_ne l i with hl | hl
    · subst hl
      simp [hij.symm]
    · simp [hl]
  rw [hzero]
  exact PrimeSpectrum.basicOpen_zero

/-- The basic opens of the coordinate idempotents cover the spectrum of the product. -/
lemma basicOpen_single_covers [Finite ι] (p : PrimeSpectrum (Π j, B j)) :
    ∃ i, p ∈ PrimeSpectrum.basicOpen (Pi.single i 1 : Π j, B j) := by
  by_contra hall
  haveI := Fintype.ofFinite ι
  have hmem : ∀ i, (Pi.single i 1 : Π j, B j) ∈ p.asIdeal := fun i =>
    of_not_not fun h => hall ⟨i, (PrimeSpectrum.mem_basicOpen _ _).mpr h⟩
  have hone : (1 : Π j, B j) ∈ p.asIdeal := by
    have hsum : ∑ i, (Pi.single i 1 : Π j, B j) = 1 := by
      ext j
      simp [Finset.sum_apply]
    rw [← hsum]
    exact Ideal.sum_mem _ fun i _ => hmem i
  exact p.asIdeal.ne_top_iff_one.mp p.isPrime.ne_top hone

omit [DecidableEq ι] in
/-- The ranges of the coordinate projections of spectra are pairwise disjoint. -/
lemma opensRange_overSpecMap_evalAlgHom_disjoint {i j : ι} (hij : i ≠ j) :
    Scheme.Hom.opensRange (Over.overSpecMap (Pi.evalAlgHom k B i)).left
      ⊓ Scheme.Hom.opensRange (Over.overSpecMap (Pi.evalAlgHom k B j)).left = ⊥ := by
  classical
  refine le_bot_iff.mp fun p hp => ?_
  have h1 := (mem_opensRange_overSpecMap_evalAlgHom B p).mp hp.1
  have h2 := (mem_opensRange_overSpecMap_evalAlgHom B p).mp hp.2
  have hmem : (show PrimeSpectrum (Π l, B l) from p)
      ∈ PrimeSpectrum.basicOpen (Pi.single i 1 : Π l, B l)
        ⊓ PrimeSpectrum.basicOpen (Pi.single j 1 : Π l, B l) := ⟨h1, h2⟩
  rw [basicOpen_single_disjoint B hij] at hmem
  exact hmem

omit [DecidableEq ι] in
/-- The ranges of the coordinate projections of spectra cover the spectrum of the
product. -/
lemma exists_mem_opensRange_overSpecMap_evalAlgHom [Finite ι]
    (p : (overSpec k (Π j, B j)).left) :
    ∃ i, p ∈ Scheme.Hom.opensRange (Over.overSpecMap (Pi.evalAlgHom k B i)).left := by
  classical
  obtain ⟨i, hi⟩ := basicOpen_single_covers B (show PrimeSpectrum (Π j, B j) from p)
  exact ⟨i, (mem_opensRange_overSpecMap_evalAlgHom B p).mpr hi⟩

end PiPartition

/-! ## The relative Picard group of a finite product -/

section RelPicPi

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable {ι : Type u} (B : ι → Type u) [∀ i, CommRing (B i)]
  [∀ i, Algebra k (B i)]

/-- Restriction of relative Picard classes along an algebra map, on Čech
representatives. -/
lemma relPicAlgMap_mk {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A']
    [Algebra k A'] (f : A →ₐ[k] A') (L : ((C ⊗ overSpec k A).left).CechPic) :
    relPicAlgMap C f (relPicMk C (overSpec k A) L)
      = relPicMk C (overSpec k A')
          (Scheme.CechPic.map (C ◁ Over.overSpecMap f).left L) :=
  relPicMap_mk C (Over.overSpecMap f) L

private lemma whisker_eval_disjoint {i j : ι} (hij : i ≠ j) :
    Scheme.Hom.opensRange (C ◁ Over.overSpecMap (Pi.evalAlgHom k B i)).left
      ⊓ Scheme.Hom.opensRange (C ◁ Over.overSpecMap (Pi.evalAlgHom k B j)).left
      = ⊥ := by
  classical
  refine le_bot_iff.mp fun x hx => ?_
  have h1 : (snd C (overSpec k (Π l, B l))).left.base x
      ∈ Set.range ((Over.overSpecMap (Pi.evalAlgHom k B i)).left).base := by
    have hx1 : x ∈ Set.range ((C ◁ Over.overSpecMap (Pi.evalAlgHom k B i)).left).base :=
      hx.1
    rw [Over.range_whiskerLeft C (Over.overSpecMap (Pi.evalAlgHom k B i))] at hx1
    exact hx1
  have h2 : (snd C (overSpec k (Π l, B l))).left.base x
      ∈ Set.range ((Over.overSpecMap (Pi.evalAlgHom k B j)).left).base := by
    have hx2 : x ∈ Set.range ((C ◁ Over.overSpecMap (Pi.evalAlgHom k B j)).left).base :=
      hx.2
    rw [Over.range_whiskerLeft C (Over.overSpecMap (Pi.evalAlgHom k B j))] at hx2
    exact hx2
  have hmem : (snd C (overSpec k (Π l, B l))).left.base x
      ∈ Scheme.Hom.opensRange (Over.overSpecMap (Pi.evalAlgHom k B i)).left
        ⊓ Scheme.Hom.opensRange (Over.overSpecMap (Pi.evalAlgHom k B j)).left :=
    ⟨h1, h2⟩
  rw [opensRange_overSpecMap_evalAlgHom_disjoint B hij] at hmem
  exact hmem

private lemma whisker_eval_covers [Finite ι] (x : (C ⊗ overSpec k (Π j, B j)).left) :
    ∃ i, x ∈ Scheme.Hom.opensRange
      (C ◁ Over.overSpecMap (Pi.evalAlgHom k B i)).left := by
  classical
  obtain ⟨i, hi⟩ := exists_mem_opensRange_overSpecMap_evalAlgHom B
    ((snd C (overSpec k (Π j, B j))).left.base x)
  refine ⟨i, ?_⟩
  change x ∈ Set.range ((C ◁ Over.overSpecMap (Pi.evalAlgHom k B i)).left).base
  rw [Over.range_whiskerLeft C (Over.overSpecMap (Pi.evalAlgHom k B i))]
  exact hi

/-- **Separation of relative Picard classes over a finite product of test algebras**:
two classes over `Π i, B i` with equal restrictions to every factor are equal. -/
theorem relPic.eq_of_pi_proj_eq [Finite ι] {ζ ζ' : relPic C (overSpec k (Π j, B j))}
    (h : ∀ i, relPicAlgMap C (Pi.evalAlgHom k B i) ζ
      = relPicAlgMap C (Pi.evalAlgHom k B i) ζ') :
    ζ = ζ' := by
  classical
  obtain ⟨L, rfl⟩ := relPicMk_surjective C (overSpec k (Π j, B j)) ζ
  obtain ⟨L', rfl⟩ := relPicMk_surjective C (overSpec k (Π j, B j)) ζ'
  rw [relPicMk_eq_relPicMk_iff]
  have h' : ∀ i, ∃ N, Scheme.CechPic.map (snd C (overSpec k (B i))).left N
      = Scheme.CechPic.map (C ◁ Over.overSpecMap (Pi.evalAlgHom k B i)).left (L / L') := by
    intro i
    have hi := h i
    rw [relPicAlgMap_mk, relPicAlgMap_mk, relPicMk_eq_relPicMk_iff] at hi
    obtain ⟨N, hN⟩ := hi
    exact ⟨N, by rw [hN, map_div]⟩
  choose N hN using h'
  obtain ⟨M, hM⟩ := Scheme.CechPic.exists_map_eq_of_clopen
    (fun i => (Over.overSpecMap (Pi.evalAlgHom k B i)).left)
    (fun i j hij => opensRange_overSpecMap_evalAlgHom_disjoint B hij)
    (fun p => exists_mem_opensRange_overSpecMap_evalAlgHom B p) N
  refine ⟨M, ?_⟩
  refine Scheme.CechPic.eq_of_map_eq_of_clopen
    (fun i => (C ◁ Over.overSpecMap (Pi.evalAlgHom k B i)).left)
    (fun i j hij => whisker_eval_disjoint C B hij)
    (fun x => whisker_eval_covers C B x) (fun i => ?_)
  calc Scheme.CechPic.map (C ◁ Over.overSpecMap (Pi.evalAlgHom k B i)).left
        (Scheme.CechPic.map (snd C (overSpec k (Π j, B j))).left M)
      = Scheme.CechPic.map ((C ◁ Over.overSpecMap (Pi.evalAlgHom k B i)).left
          ≫ (snd C (overSpec k (Π j, B j))).left) M := by
        rw [Scheme.CechPic.map_comp]
        rfl
    _ = Scheme.CechPic.map ((snd C (overSpec k (B i))).left
          ≫ (Over.overSpecMap (Pi.evalAlgHom k B i)).left) M := by
        rw [Over.snd_left_naturality]
    _ = Scheme.CechPic.map (snd C (overSpec k (B i))).left
          (Scheme.CechPic.map (Over.overSpecMap (Pi.evalAlgHom k B i)).left M) := by
        rw [Scheme.CechPic.map_comp]
        rfl
    _ = Scheme.CechPic.map (snd C (overSpec k (B i))).left (N i) := by rw [hM i]
    _ = Scheme.CechPic.map (C ◁ Over.overSpecMap (Pi.evalAlgHom k B i)).left (L / L') :=
        hN i

/-- **Gluing of relative Picard classes over a finite product of test algebras**: every
family of classes over the factors is the family of restrictions of a class over
`Π i, B i`. -/
theorem relPic.exists_pi_lift [Finite ι] (ξ : ∀ i, relPic C (overSpec k (B i))) :
    ∃ ζ : relPic C (overSpec k (Π j, B j)),
      ∀ i, relPicAlgMap C (Pi.evalAlgHom k B i) ζ = ξ i := by
  classical
  have hrep : ∀ i, ∃ L, relPicMk C (overSpec k (B i)) L = ξ i := fun i =>
    relPicMk_surjective C (overSpec k (B i)) (ξ i)
  choose L hL using hrep
  obtain ⟨M, hM⟩ := Scheme.CechPic.exists_map_eq_of_clopen
    (fun i => (C ◁ Over.overSpecMap (Pi.evalAlgHom k B i)).left)
    (fun i j hij => whisker_eval_disjoint C B hij)
    (fun x => whisker_eval_covers C B x) L
  refine ⟨relPicMk C (overSpec k (Π j, B j)) M, fun i => ?_⟩
  rw [relPicAlgMap_mk, hM i, hL i]

end RelPicPi

end AlgebraicGeometry
