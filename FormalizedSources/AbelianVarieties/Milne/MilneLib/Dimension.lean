/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology
import MilneLib.GroupScheme

/-!
# Dimension infrastructure

These lemmas isolate the commutative-algebra part of Milne's dimension
arguments.  The affine-scheme adapter is deliberately conditional; the
proper abelian-variety case still needs a separate global dimension theorem.
-/

set_option autoImplicit false

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  MorphismProperty
open AlgebraicGeometry

namespace MilneLib

/-- Passing to an open neighbourhood does not change the coheight of a point. -/
theorem coheight_eq_of_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    (z : X) (hz : z ∈ U) :
    @Order.coheight X (specializationPreorder X) z =
      @Order.coheight U (specializationPreorder U) ⟨z, hz⟩ := by
  letI : Preorder X := specializationPreorder X
  letI : Preorder U := specializationPreorder U
  have hmono : Monotone (Subtype.val : U → X) :=
    continuous_subtype_val.specialization_monotone
  have hstrict : StrictMono (Subtype.val : U → X) := by
    intro a b hab
    refine ⟨hmono hab.le, fun h => ?_⟩
    apply hab.not_ge
    change a ⤳ b
    exact (subtype_specializes_iff a b).mpr h
  apply le_antisymm
  · refine Order.coheight_le_iff'.mpr ?_
    intro p hphead
    have hmem : ∀ i, p i ∈ U := by
      intro i
      have hle : z ≤ p i := by
        have := p.head_le i
        rwa [hphead] at this
      exact Specializes.mem_open (show p i ⤳ z from hle) hU hz
    let q : LTSeries U :=
      { length := p.length
        toFun := fun i => ⟨p i, hmem i⟩
        step := by
          intro i
          have hlt : p i.castSucc < p i.succ := p.step i
          have hspec : p i.succ ⤳ p i.castSucc := hlt.le
          have hsub : (⟨p i.succ, hmem _⟩ : U) ⤳ ⟨p i.castSucc, hmem _⟩ :=
            (subtype_specializes_iff _ _).mpr hspec
          refine ⟨hsub, fun hbad => ?_⟩
          apply hlt.not_ge
          exact (subtype_specializes_iff _ _).mp hbad }
    have hqhead : q.head = ⟨z, hz⟩ := by
      apply Subtype.ext
      exact hphead
    have hbound := Order.length_le_coheight
      (x := (⟨z, hz⟩ : U)) (p := q) (by rw [hqhead])
    simpa using hbound
  · simpa using Order.coheight_le_coheight_apply_of_strictMono
      (Subtype.val : U → X) hstrict ⟨z, hz⟩

/-- Coheight in an affine scheme is height in its prime spectrum. -/
theorem coheight_spec_eq_height_primeSpectrum
    {R : CommRingCat} (p : Spec R) :
    Order.coheight (α := Spec R) p =
      Order.height (α := PrimeSpectrum R) ⟨p.asIdeal, p.isPrime⟩ := by
  let e : Spec R ≃o (PrimeSpectrum R)ᵒᵈ :=
    { toFun := fun q => OrderDual.toDual ⟨q.asIdeal, q.isPrime⟩
      invFun := fun q => (OrderDual.ofDual q : PrimeSpectrum R)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := by
        intro a b
        exact (AlgebraicGeometry.AffineSpace.spec_le_iff R a b).symm }
  have h : Order.coheight (α := (PrimeSpectrum R)ᵒᵈ) (e p) =
      Order.coheight (α := Spec R) p :=
    Order.coheight_orderIso e p
  rw [← h]
  rfl

/-- The Krull dimension of a scheme stalk is the coheight of its point. -/
theorem ringKrullDim_stalk_eq_coheight (X : Scheme.{u}) (z : X) :
    ringKrullDim (X.presheaf.stalk z) = Order.coheight z := by
  obtain ⟨U, hU, hzU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := z) (U := ⊤) (by trivial)
  set p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨z, hzU⟩ with hp
  letI : Algebra Γ(X, U) (X.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzU⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk z) p.asIdeal :=
    hU.isLocalization_stalk ⟨z, hzU⟩
  have hdim : ringKrullDim (X.presheaf.stalk z) =
      (Order.height (α := PrimeSpectrum Γ(X, U)) p : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height
          (R := Γ(X, U)) p.asIdeal (X.presheaf.stalk z),
      PrimeSpectrum.height_eq_orderHeight p]
  have hopen : Order.coheight (α := X) z =
      Order.coheight (α := U.toScheme) ⟨z, hzU⟩ :=
    coheight_eq_of_isOpenEmbedding (X := X) (U := U.1) U.isOpen z hzU
  let hHomeo : U.toScheme ≃ₜ Spec Γ(X, U) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso hU.isoSpec)
  let eOrder : U.toScheme ≃o Spec Γ(X, U) :=
    { toEquiv := hHomeo.toEquiv
      map_rel_iff' := by
        intro a b
        constructor
        · intro h
          have hsp : hHomeo b ⤳ hHomeo a := h
          have hsp' := hsp.map hHomeo.symm.continuous
          change hHomeo.symm (hHomeo b) ⤳ hHomeo.symm (hHomeo a) at hsp'
          rw [hHomeo.symm_apply_apply, hHomeo.symm_apply_apply] at hsp'
          exact (hsp' : a ≤ b)
        · intro h
          have hsp : b ⤳ a := h
          exact (hsp.map hHomeo.continuous : hHomeo a ≤ hHomeo b) }
  have hiso : Order.coheight (α := U.toScheme) ⟨z, hzU⟩ =
      Order.coheight (α := Spec Γ(X, U)) (eOrder ⟨z, hzU⟩) :=
    (Order.coheight_orderIso eOrder ⟨z, hzU⟩).symm
  have heq : eOrder ⟨z, hzU⟩ = p := rfl
  have haff : Order.coheight (α := Spec Γ(X, U)) p =
      Order.height (α := PrimeSpectrum Γ(X, U))
        ⟨p.asIdeal, p.isPrime⟩ :=
    coheight_spec_eq_height_primeSpectrum p
  have hp' : (⟨p.asIdeal, p.isPrime⟩ : PrimeSpectrum Γ(X, U)) = p := rfl
  rw [hdim, hopen, hiso, heq, haff, hp']

/-- The dimension of a local ring can only increase under specialization. -/
theorem ringKrullDim_stalk_le_of_specializes
    (X : Scheme.{u}) {x y : X} (hxy : x ⤳ y) :
    ringKrullDim (X.presheaf.stalk x) ≤
      ringKrullDim (X.presheaf.stalk y) := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Order.coheight_anti
    ((Scheme.le_iff_specializes).mpr hxy)

/-- The dimension of a scheme is the supremum of the dimensions of its stalks. -/
theorem topologicalKrullDim_eq_iSup_ringKrullDim_stalk (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ z : X, ringKrullDim (X.presheaf.stalk z) := by
  have h : topologicalKrullDim X =
      ⨆ z : X, (Order.coheight z : WithBot ℕ∞) := by
    unfold topologicalKrullDim
    rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact Order.krullDim_eq_iSup_coheight
  rw [h]
  exact iSup_congr fun z => (ringKrullDim_stalk_eq_coheight X z).symm

/-- Uniform upper bounds on stalk dimensions bound the scheme dimension. -/
theorem topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le
    (X : Scheme.{u}) (d : WithBot ℕ∞)
    (h : ∀ z : X, ringKrullDim (X.presheaf.stalk z) ≤ d) :
    topologicalKrullDim X ≤ d := by
  rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk X]
  exact iSup_le h

/-- The dimension of any stalk is bounded by the dimension of the scheme. -/
theorem ringKrullDim_stalk_le_topologicalKrullDim
    (X : Scheme.{u}) (z : X) :
    ringKrullDim (X.presheaf.stalk z) ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk X]
  exact le_iSup (fun z : X => ringKrullDim (X.presheaf.stalk z)) z

/-- A uniform upper bound and a matching stalk witness determine dimension. -/
theorem topologicalKrullDim_eq_of_le_of_exists_ge
    (X : Scheme.{u}) (d : WithBot ℕ∞)
    (hle : ∀ z : X, ringKrullDim (X.presheaf.stalk z) ≤ d)
    (z₀ : X) (hz₀ : d ≤ ringKrullDim (X.presheaf.stalk z₀)) :
    topologicalKrullDim X = d :=
  le_antisymm (topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le X d hle)
    (hz₀.trans (ringKrullDim_stalk_le_topologicalKrullDim X z₀))

/-- The Krull dimension of a Noetherian local ring is bounded by the dimension
of its cotangent space over the residue field. -/
theorem ringKrullDim_le_finrank_cotangentSpace
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤
      ((Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.CotangentSpace R) : ℕ) : WithBot ℕ∞) := by
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R]
  exact ringKrullDim_le_spanFinrank_maximalIdeal R

/-- At a point of a locally Noetherian scheme, the stalk dimension is bounded
by the dimension of its cotangent space. -/
theorem ringKrullDim_stalk_le_finrank_cotangentSpace
    (X : Scheme.{u}) [IsLocallyNoetherian X] (z : X) :
    ringKrullDim (X.presheaf.stalk z) ≤
      ((Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk z))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk z)) : ℕ) :
          WithBot ℕ∞) :=
  ringKrullDim_le_finrank_cotangentSpace _

/-- A uniform upper bound on cotangent-space dimensions bounds the dimension
of a locally Noetherian scheme. -/
theorem topologicalKrullDim_le_of_forall_finrank_cotangentSpace_le
    (X : Scheme.{u}) [IsLocallyNoetherian X] (d : ℕ)
    (h : ∀ z : X,
      Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk z))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk z)) ≤ d) :
    topologicalKrullDim X ≤ (d : WithBot ℕ∞) :=
  topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le X _ fun z =>
    le_trans (ringKrullDim_stalk_le_finrank_cotangentSpace X z)
      (by exact_mod_cast Nat.cast_le.mpr (h z))

/-- At a regular point, the cotangent-space dimension is a lower bound for the
dimension of the ambient scheme. -/
theorem le_topologicalKrullDim_of_finrank_cotangentSpace
    (X : Scheme.{u}) (d : ℕ) (z : X)
    (hreg : IsRegularLocalRing (X.presheaf.stalk z))
    (h : Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk z))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk z)) = d) :
    (d : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  haveI := hreg
  have hdim : ringKrullDim (X.presheaf.stalk z) =
      (d : WithBot ℕ∞) := by
    rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace
      (R := X.presheaf.stalk z)).mp hreg, h]
  rw [← hdim]
  exact ringKrullDim_stalk_le_topologicalKrullDim X z

/-- A uniform cotangent-space upper bound and one regular point attaining the
bound determine the dimension of a locally Noetherian scheme. -/
theorem topologicalKrullDim_eq_of_forall_finrank_cotangentSpace_le_of_regular
    (X : Scheme.{u}) [IsLocallyNoetherian X] (d : ℕ)
    (h : ∀ z : X,
      Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk z))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk z)) ≤ d)
    (z₀ : X) (hreg : IsRegularLocalRing (X.presheaf.stalk z₀))
    (hz₀ : Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk z₀))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk z₀)) = d) :
    topologicalKrullDim X = (d : WithBot ℕ∞) :=
  le_antisymm
    (topologicalKrullDim_le_of_forall_finrank_cotangentSpace_le X d h)
    (le_topologicalKrullDim_of_finrank_cotangentSpace X d z₀ hreg hz₀)

/-! ### Isomorphism invariance of local dimension data

The stalk map of a scheme isomorphism is a ring isomorphism.  We first record
the corresponding maximal-ideal generator count, then convert it to cotangent
dimension via the Noetherian Nakayama identity. -/

/-- An isomorphism of local rings preserves the span finrank of the maximal ideal. -/
theorem spanFinrank_maximalIdeal_eq_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) :
    (IsLocalRing.maximalIdeal A).spanFinrank =
      (IsLocalRing.maximalIdeal B).spanFinrank := by
  have hmap : (IsLocalRing.maximalIdeal A).map (e : A →+* B) =
      IsLocalRing.maximalIdeal B := by
    apply IsLocalRing.eq_maximalIdeal
    exact (IsLocalRing.maximalIdeal.isMaximal A).map_bijective _ e.bijective
  have h1 := Ideal.spanRank_map_le (e : A →+* B) (IsLocalRing.maximalIdeal A)
  have h2 := Ideal.spanRank_map_le (e.symm : B →+* A)
    ((IsLocalRing.maximalIdeal A).map (e : A →+* B))
  rw [Ideal.map_map] at h2
  rw [show ((e.symm : B →+* A).comp (e : A →+* B)) = RingHom.id A from by
    ext a
    simp, Ideal.map_id] at h2
  rw [← hmap]
  unfold Submodule.spanFinrank
  rw [le_antisymm h2 h1]

/-- The cotangent-space finrank is invariant under an isomorphism of local
rings. -/
theorem finrank_cotangentSpace_eq_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (e : A ≃+* B) :
    Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.CotangentSpace A) =
      Module.finrank (IsLocalRing.ResidueField B)
        (IsLocalRing.CotangentSpace B) := by
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    ← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact spanFinrank_maximalIdeal_eq_of_ringEquiv e

/-- Cotangent-space finrank is preserved by a scheme isomorphism, pointwise. -/
theorem finrank_cotangentSpace_stalk_eq_of_isIso
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsIso f] (x : X) :
    Module.finrank (IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)))
        (IsLocalRing.CotangentSpace (Y.presheaf.stalk (f.base x))) =
      Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) :=
  finrank_cotangentSpace_eq_of_ringEquiv
    ((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv)

/-- The Krull dimension of stalks is preserved by a scheme isomorphism. -/
theorem ringKrullDim_stalk_eq_of_isIso
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (x : X) :
    ringKrullDim (Y.presheaf.stalk (f.base x)) =
      ringKrullDim (X.presheaf.stalk x) :=
  ringKrullDim_eq_of_ringEquiv
    ((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv)

/-- An isomorphism of schemes preserves the global topological Krull dimension.

The pointwise stalk comparison is enough after expressing the dimension as the
supremum of stalk dimensions.  The reverse inequality uses the inverse scheme
isomorphism, avoiding any choice of a pointwise inverse for the underlying
homeomorphism.
-/
theorem topologicalKrullDim_eq_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk X,
      topologicalKrullDim_eq_iSup_ringKrullDim_stalk Y]
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [← ringKrullDim_stalk_eq_of_isIso f x]
    exact le_iSup (fun y : Y => ringKrullDim (Y.presheaf.stalk y)) (f.base x)
  · apply iSup_le
    intro y
    have hxy := ringKrullDim_stalk_eq_of_isIso (inv f) y
    rw [← hxy]
    exact le_iSup (fun x : X => ringKrullDim (X.presheaf.stalk x)) ((inv f).base y)

/-! Regularity is likewise invariant under the stalk isomorphism.  This is
useful when a dimension argument supplies regularity at one translated point. -/

/-- Regularity of local stalks is preserved by a scheme isomorphism. -/
theorem isRegularLocalRing_stalk_iff_of_isIso
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsIso f] (x : X) :
    IsRegularLocalRing (Y.presheaf.stalk (f.base x)) ↔
      IsRegularLocalRing (X.presheaf.stalk x) := by
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  constructor
  · intro h
    letI : IsRegularLocalRing (Y.presheaf.stalk (f.base x)) := h
    exact IsRegularLocalRing.of_ringEquiv e
  · intro h
    letI : IsRegularLocalRing (X.presheaf.stalk x) := h
    exact IsRegularLocalRing.of_ringEquiv e.symm

namespace GroupVariety

/-- A group-variety translation preserves the cotangent-space finrank at every
point of a locally Noetherian underlying scheme. -/
theorem finrank_cotangentSpace_eq_of_pointTranslation
    {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [IsLocallyNoetherian G.left]
    (x y : 𝟙_ (Over S) ⟶ G) (z : G.left) :
    Module.finrank
        (IsLocalRing.ResidueField
          (G.left.presheaf.stalk ((pointTranslationIso G x y).hom.base z)))
        (IsLocalRing.CotangentSpace
          (G.left.presheaf.stalk ((pointTranslationIso G x y).hom.base z))) =
      Module.finrank (IsLocalRing.ResidueField (G.left.presheaf.stalk z))
        (IsLocalRing.CotangentSpace (G.left.presheaf.stalk z)) :=
  finrank_cotangentSpace_stalk_eq_of_isIso
    ((pointTranslationIso G x y).hom) z

/-- A group-variety translation preserves the Krull dimension of local stalks. -/
theorem ringKrullDim_stalk_eq_of_pointTranslation
    {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (x y : 𝟙_ (Over S) ⟶ G) (z : G.left) :
    ringKrullDim
        (G.left.presheaf.stalk ((pointTranslationIso G x y).hom.base z)) =
      ringKrullDim (G.left.presheaf.stalk z) :=
  ringKrullDim_stalk_eq_of_isIso ((pointTranslationIso G x y).hom) z

/-- Regularity of a group-variety stalk is preserved by point translation. -/
theorem isRegularLocalRing_stalk_iff_of_pointTranslation
    {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [IsLocallyNoetherian G.left]
    (x y : 𝟙_ (Over S) ⟶ G) (z : G.left) :
    IsRegularLocalRing
        (G.left.presheaf.stalk ((pointTranslationIso G x y).hom.base z)) ↔
      IsRegularLocalRing (G.left.presheaf.stalk z) :=
  isRegularLocalRing_stalk_iff_of_isIso ((pointTranslationIso G x y).hom) z

section AlgebraicallyClosed

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Closed points of an abelian variety over an algebraically closed field have
the same cotangent-space finrank.  The two points are promoted to rational
sections and joined by the corresponding group translation. -/
theorem finrank_cotangentSpace_eq_of_closedPoints
    {G : Over (Spec (.of K))} [GrpObj G]
    (hG : IsAbelianVariety G)
    {x z : G.left} (hx : IsClosed {x}) (hz : IsClosed {z}) :
    Module.finrank
        (IsLocalRing.ResidueField (G.left.presheaf.stalk z))
        (IsLocalRing.CotangentSpace (G.left.presheaf.stalk z)) =
    Module.finrank
        (IsLocalRing.ResidueField (G.left.presheaf.stalk x))
        (IsLocalRing.CotangentSpace (G.left.presheaf.stalk x)) := by
  letI : LocallyOfFiniteType G.hom :=
    locallyOfFiniteType_of_isAbelianVariety G hG
  letI : IsLocallyNoetherian G.left :=
    isLocallyNoetherian_left_of_isAbelianVariety G hG
  let px : Spec (.of K) ⟶ G.left := pointOfClosedPoint G.hom x hx
  have hpx : px ≫ G.hom = 𝟙 _ := pointOfClosedPoint_comp G.hom x hx
  let xhat : 𝟙_ (Over (Spec (.of K))) ⟶ G := Over.homMk px hpx
  have hxhat : xhat.left (IsLocalRing.closedPoint K) = x := by
    exact pointOfClosedPoint_apply G.hom x hx _
  let pz : Spec (.of K) ⟶ G.left := pointOfClosedPoint G.hom z hz
  have hpz : pz ≫ G.hom = 𝟙 _ := pointOfClosedPoint_comp G.hom z hz
  let zhat : 𝟙_ (Over (Spec (.of K))) ⟶ G := Over.homMk pz hpz
  have hzhat : zhat.left (IsLocalRing.closedPoint K) = z := by
    exact pointOfClosedPoint_apply G.hom z hz _
  have h := finrank_cotangentSpace_eq_of_pointTranslation G xhat zhat x
  have htranslate : (pointTranslationIso G xhat zhat).hom.base x = z := by
    rw [← hxhat, pointTranslationIso_hom_apply, hzhat]
  rw [htranslate] at h
  exact h

/-- Closed points of an abelian variety over an algebraically closed field have
the same local Krull dimension. -/
theorem ringKrullDim_stalk_eq_of_closedPoints
    {G : Over (Spec (.of K))} [GrpObj G]
    (hG : IsAbelianVariety G)
    {x z : G.left} (hx : IsClosed {x}) (hz : IsClosed {z}) :
    ringKrullDim (G.left.presheaf.stalk z) =
      ringKrullDim (G.left.presheaf.stalk x) := by
  letI : LocallyOfFiniteType G.hom :=
    locallyOfFiniteType_of_isAbelianVariety G hG
  let px : Spec (.of K) ⟶ G.left := pointOfClosedPoint G.hom x hx
  have hpx : px ≫ G.hom = 𝟙 _ := pointOfClosedPoint_comp G.hom x hx
  let xhat : 𝟙_ (Over (Spec (.of K))) ⟶ G := Over.homMk px hpx
  have hxhat : xhat.left (IsLocalRing.closedPoint K) = x := by
    exact pointOfClosedPoint_apply G.hom x hx _
  let pz : Spec (.of K) ⟶ G.left := pointOfClosedPoint G.hom z hz
  have hpz : pz ≫ G.hom = 𝟙 _ := pointOfClosedPoint_comp G.hom z hz
  let zhat : 𝟙_ (Over (Spec (.of K))) ⟶ G := Over.homMk pz hpz
  have hzhat : zhat.left (IsLocalRing.closedPoint K) = z := by
    exact pointOfClosedPoint_apply G.hom z hz _
  have h := ringKrullDim_stalk_eq_of_pointTranslation G xhat zhat x
  have htranslate : (pointTranslationIso G xhat zhat).hom.base x = z := by
    rw [← hxhat, pointTranslationIso_hom_apply, hzhat]
  rw [htranslate] at h
  exact h

end AlgebraicallyClosed

end GroupVariety

/-! Jacobson spaces provide the closed specializations used by the global
dimension argument.  We keep this topological producer separate from the
cotangent-rank comparison, which needs additional geometric input. -/

/-- Every point of a Jacobson space has a closed specialization. -/
theorem exists_closed_specialization_of_jacobsonSpace
    {X : Type u} [TopologicalSpace X] [JacobsonSpace X]
    (x : X) : ∃ y : X, IsClosed ({y} : Set X) ∧ x ⤳ y := by
  have hloc : IsLocallyClosed (closure ({x} : Set X)) :=
    isClosed_closure.isLocallyClosed
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
    (Z := closure ({x} : Set X)) (Set.singleton_nonempty x).closure hloc
  refine ⟨y, hyc, ?_⟩
  exact specializes_iff_mem_closure.mpr hy

/-- Every point of an abelian variety over a field specializes to a closed
point.  This is the finite-type/Jacobson producer needed by later dimension
arguments. -/
theorem exists_closed_specialization_of_isAbelianVariety
    {K : Type u} [Field K]
    {G : Over (Spec (.of K))} [GrpObj G]
    (hG : IsAbelianVariety G) (x : G.left) :
    ∃ y : G.left, IsClosed ({y} : Set G.left) ∧ x ⤳ y := by
  letI : JacobsonSpace G.left :=
    jacobsonSpace_left_of_isAbelianVariety G hG
  exact exists_closed_specialization_of_jacobsonSpace x

/-- Over an algebraically closed field, the global dimension of an abelian
variety is the Krull dimension of the local ring at any closed point. -/
theorem topologicalKrullDim_eq_ringKrullDim_stalk_of_isAbelianVariety
    {K : Type u} [Field K] [IsAlgClosed K]
    {G : Over (Spec (.of K))} [GrpObj G]
    (hG : IsAbelianVariety G) (x₀ : G.left)
    (hx₀ : IsClosed ({x₀} : Set G.left)) :
    topologicalKrullDim G.left =
      ringKrullDim (G.left.presheaf.stalk x₀) := by
  rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk]
  apply le_antisymm
  · apply iSup_le
    intro z
    obtain ⟨c, hc, hzc⟩ :=
      exists_closed_specialization_of_isAbelianVariety hG z
    exact (ringKrullDim_stalk_le_of_specializes G.left hzc).trans_eq
      (GroupVariety.ringKrullDim_stalk_eq_of_closedPoints hG hx₀ hc)
  · exact le_iSup
      (fun z : G.left ↦ ringKrullDim (G.left.presheaf.stalk z)) x₀

/-! A global dimension consumer for the translation-invariant cotangent rank.

The specialization bound in the statement is the geometric input left to a
separate finite-type/Jacobson argument: every point is bounded by a closed
specialization.  The theorem then packages the abelian-variety translation
invariance proved above with the general cotangent-space dimension criterion.
-/

/-- If every point is bounded by a closed specialization, then a regular point
of an algebraically closed abelian variety whose cotangent space has rank `d`
determines the global Krull dimension. -/
theorem topologicalKrullDim_eq_of_closed_specialization_finrank
    {K : Type u} [Field K] [IsAlgClosed K]
    {G : Over (Spec (.of K))} [GrpObj G]
    (hG : IsAbelianVariety G) (d : ℕ) (x₀ : G.left)
    (hx₀ : IsClosed ({x₀} : Set G.left))
    (hreg : IsRegularLocalRing (G.left.presheaf.stalk x₀))
    (hfin : Module.finrank (IsLocalRing.ResidueField
      (G.left.presheaf.stalk x₀))
      (IsLocalRing.CotangentSpace (G.left.presheaf.stalk x₀)) = d)
    (hbound : ∀ z : G.left, ∃ c : G.left,
      IsClosed ({c} : Set G.left) ∧
        Module.finrank (IsLocalRing.ResidueField
          (G.left.presheaf.stalk z))
          (IsLocalRing.CotangentSpace (G.left.presheaf.stalk z)) ≤
        Module.finrank (IsLocalRing.ResidueField
          (G.left.presheaf.stalk c))
          (IsLocalRing.CotangentSpace (G.left.presheaf.stalk c))) :
    topologicalKrullDim G.left = (d : WithBot ℕ∞) := by
  letI : LocallyOfFiniteType G.hom :=
    locallyOfFiniteType_of_isAbelianVariety G hG
  letI : IsLocallyNoetherian G.left :=
    isLocallyNoetherian_left_of_isAbelianVariety G hG
  refine topologicalKrullDim_eq_of_forall_finrank_cotangentSpace_le_of_regular
    G.left d ?_ x₀ hreg hfin
  intro z
  obtain ⟨c, hc, hzc⟩ := hbound z
  have hz := GroupVariety.finrank_cotangentSpace_eq_of_closedPoints
    (G := G) hG hx₀ hc
  exact hzc.trans (le_of_eq (hz.trans hfin))

/-- An injective integral extension preserves Krull dimension. -/
theorem ringKrullDim_eq_of_isIntegral_of_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hfin : f.IsIntegral)
    (hinj : Function.Injective f) :
    ringKrullDim S = ringKrullDim R := by
  letI : Algebra R S := f.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hfin⟩
  let c : PrimeSpectrum S → PrimeSpectrum R := PrimeSpectrum.comap f
  have hc_strict : StrictMono c := by
    intro I J hIJ
    change I.asIdeal < J.asIdeal at hIJ
    change Ideal.comap f I.asIdeal < Ideal.comap f J.asIdeal
    exact Ideal.IsIntegral.comap_lt_comap hIJ
  have hcoheight (I : PrimeSpectrum S) :
      Order.coheight I = Order.coheight (c I) := by
    apply Order.coheight_eq_of_strictMono c hc_strict
    intro a b hab
    obtain ⟨Q, haQ, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
        b.asIdeal a.asIdeal hab.le
    let q : PrimeSpectrum S := ⟨Q, hQprime⟩
    refine ⟨q, ?_, ?_⟩
    · change a.asIdeal < Q
      refine lt_of_le_of_ne haQ ?_
      intro hEq
      have hcEq : c a = b := by
        apply PrimeSpectrum.ext
        change Ideal.comap f a.asIdeal = b.asIdeal
        simpa [hEq, RingHom.algebraMap_toAlgebra] using hQcomap
      exact (ne_of_lt hab) hcEq
    · apply PrimeSpectrum.ext
      change Ideal.comap f Q = b.asIdeal
      simpa only [RingHom.algebraMap_toAlgebra] using hQcomap
  change Order.krullDim (PrimeSpectrum S) =
    Order.krullDim (PrimeSpectrum R)
  apply le_antisymm
  · exact Order.krullDim_le_of_strictMono c hc_strict
  · rw [Order.krullDim_eq_iSup_coheight,
        Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro p
    obtain ⟨q, hq⟩ := hfin.comap_surjective hinj p
    rw [← hq, ← hcoheight q]
    exact le_iSup
      (fun q : PrimeSpectrum S =>
        (Order.coheight q : WithBot ℕ∞)) q

/-- A finite surjective morphism to an affine reduced scheme preserves
Krull dimension.  Finiteness makes the source affine, so the assertion is
reduced to the integral injective map on global sections. -/
theorem topologicalKrullDim_eq_of_isFinite_surjective_of_isAffineTarget
    {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] [IsReduced Y] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant f
  rw [IsHomeomorph.topologicalKrullDim_eq X.isoSpec.hom
        X.isoSpec.hom.homeomorph.isHomeomorph,
      IsHomeomorph.topologicalKrullDim_eq Y.isoSpec.hom
        Y.isoSpec.hom.homeomorph.isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum Γ(X, ⊤)) =
    topologicalKrullDim (PrimeSpectrum Γ(Y, ⊤))
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_eq_of_isIntegral_of_injective
    (f.appTop).hom f.finite_appTop.to_isIntegral (f.app_injective ⊤)

/-- Restricting a surjective scheme morphism to an open subscheme of its
target remains surjective. -/
theorem surjective_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] (U : Y.Opens) :
    Surjective (f ∣_ U) := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := f.surjective (U.ι y)
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change f x ∈ U
    rw [hx]
    exact y.2
  · apply Subtype.ext
    rw [morphismRestrict_base_coe]
    exact hx

/-- The dimension of a scheme is the supremum of the dimensions of the
members of any open cover. -/
theorem topologicalKrullDim_eq_iSup_of_iSup_eq_top
    {I : Type v} (X : Scheme.{u}) (U : I → X.Opens)
    (hU : ⨆ i, U i = ⊤) :
    topologicalKrullDim X =
      ⨆ i, topologicalKrullDim (U i).toScheme := by
  apply le_antisymm
  · rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk X]
    apply iSup_le
    intro x
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hU.ge (Set.mem_univ x))
    let xU : (U i).toScheme := ⟨x, hxi⟩
    have hstalk :
        ringKrullDim (X.presheaf.stalk ((U i).ι xU)) =
          ringKrullDim ((U i).toScheme.presheaf.stalk xU) :=
      ringKrullDim_eq_of_ringEquiv
        ((asIso ((U i).ι.stalkMap xU)).commRingCatIsoToRingEquiv)
    calc
      ringKrullDim (X.presheaf.stalk x) =
          ringKrullDim (X.presheaf.stalk ((U i).ι xU)) := by rfl
      _ = ringKrullDim ((U i).toScheme.presheaf.stalk xU) := hstalk
      _ ≤ topologicalKrullDim (U i).toScheme :=
        ringKrullDim_stalk_le_topologicalKrullDim (U i).toScheme xU
      _ ≤ ⨆ i, topologicalKrullDim (U i).toScheme :=
        le_iSup (fun i ↦ topologicalKrullDim (U i).toScheme) i
  · apply iSup_le
    intro i
    exact topologicalKrullDim_subspace_le X (U i)

/-- A finite surjective morphism to a reduced scheme preserves Krull
dimension. -/
theorem topologicalKrullDim_eq_of_isFinite_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] [IsReduced Y] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_iSup_of_iSup_eq_top X
      (fun U : Y.affineOpens ↦ f ⁻¹ᵁ (U : Y.Opens))
      (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y))]
  rw [topologicalKrullDim_eq_iSup_of_iSup_eq_top Y
      (fun U : Y.affineOpens ↦ (U : Y.Opens))
      (iSup_affineOpens_eq_top Y)]
  apply iSup_congr
  intro U
  letI : Surjective (f ∣_ (U : Y.Opens)) :=
    surjective_morphismRestrict f (U : Y.Opens)
  haveI : IsReduced (U : Y.Opens).toScheme :=
    isReduced_of_isOpenImmersion U.1.ι
  exact topologicalKrullDim_eq_of_isFinite_surjective_of_isAffineTarget
    (f ∣_ (U : Y.Opens))

end MilneLib
