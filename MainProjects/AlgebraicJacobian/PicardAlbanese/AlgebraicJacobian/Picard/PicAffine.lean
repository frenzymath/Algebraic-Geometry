/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicAffineCover
import AlgebraicJacobian.Picard.FamilyCoboundary

/-!
# The Čech–Picard dictionary for affine schemes: the descent homomorphism

For an affine scheme `X`, this file assembles the Picard classes of unit Čech cocycles
along basic refinements (`AlgebraicJacobian.Picard.PicAffineCover`) into an injective
group homomorphism

* `AlgebraicGeometry.Scheme.CechPic.toPic : X.CechPic →* CommRing.Pic Γ(X, ⊤)`

from the definitional Čech Picard group into mathlib's Picard group of the global
sections.  (Surjectivity — hence the full dictionary `X.CechPic ≃* CommRing.Pic Γ(X, ⊤)`
— is the invertible-module-trivialization direction, treated separately.)

The core is the **independence of the descent Picard class from every choice**
(`BasicRefinement.pic_congr`): representing cocycle of the `H¹` class, basic refinement,
and pointed cover.  All comparisons are routed through three elementary moves:

* `pic_res` — replacing the pointed cover by a finer one and restricting the cocycle
  does not change the refinement data nor the class (the restricted evaluations agree on
  the nose);
* `pic_eq_of_isCohomologous` — cohomologous cocycles give equal classes (the comparison
  restricts to an index-wise coboundary; coboundary invariance of the descended module);
* `pic_interFst` / `pic_inter` / `pic_interFst_eq_inter` — any two basic refinements of
  the same cover are dominated by their merge, on which the two point-selections differ
  by the index-wise coboundary of the cross evaluations `γ (pt i, pt' j)`; hence all
  refinements give the same class.

Injectivity is refinement injectivity: a trivial descent class makes the descent unit a
coboundary (`Module.IsDescentCocycle.picClass_eq_one_iff`), whose components glue back to
a coboundary on the pointed cover itself
(`AlgebraicGeometry.Scheme.unitsH1_eq_one_of_family`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Opposite TopologicalSpace CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

namespace Scheme

namespace PointedCover.BasicRefinement

variable {X : Scheme.{u}}

/-! ## Lifting refinements along cover refinement -/

/-- A basic refinement of a finer pointed cover is one of the coarser cover. -/
@[simps ι pt r]
def ofLE {𝒰 𝒱 : X.PointedCover} (h : 𝒱 ≤ 𝒰) (P : 𝒱.BasicRefinement) :
    𝒰.BasicRefinement where
  ι := P.ι
  pt := P.pt
  r := P.r
  basicOpen_le i := (P.basicOpen_le i).trans (h (P.pt i))
  iSup_eq := P.iSup_eq

/-- The merge of two basic refinements of the same cover, pointed by the **first**
factor.  Defined by updating the points of `inter`, so that the index family and the
sections are *definitionally those of `P.inter Q`*. -/
@[simps pt]
def interFst {𝒰 : X.PointedCover} (P Q : 𝒰.BasicRefinement) : 𝒰.BasicRefinement :=
  { P.inter Q with
    pt := fun p ↦ P.pt p.1
    basicOpen_le := fun p ↦
      ((X.basicOpen_mul _ _).trans_le inf_le_left).trans (P.basicOpen_le p.1) }

@[simp]
lemma interFst_r {𝒰 : X.PointedCover} (P Q : 𝒰.BasicRefinement) (p : P.ι × Q.ι) :
    (P.interFst Q).r p = P.r p.1 * Q.r p.2 :=
  rfl

section pic

variable [IsAffine X] {𝒰 𝒱 : X.PointedCover}

/-! ## Move 1: restriction along a refinement of pointed covers -/

/-- Restricting the cocycle to a finer pointed cover and lifting the basic refinement
back does not change the Picard class: the two cover cocycles agree on the nose. -/
theorem pic_ofLE (h : 𝒱 ≤ 𝒰) (P : 𝒱.BasicRefinement) (γ : X.unitsCocycle 𝒰) :
    (P.ofLE h).pic γ = P.pic (γ.res fun x ↦ homOfLE (h x)) := by
  -- Both sides are `picClass` of `isDescentCocycle_cocycleUnit` for the same data:
  -- `coverCocycle` of the restricted cocycle is the composed restriction of the same
  -- evaluations.
  have hcc : (P.ofLE h).coverCocycle γ = P.coverCocycle (γ.res fun x ↦ homOfLE (h x)) := by
    funext i j
    rw [coverCocycle, coverCocycle, res_unitsEvInf h γ, unitsRestrict_unitsRestrict]
    rfl
  haveI := (P.ofLE h).faithfullyFlat
  haveI := P.faithfullyFlat
  exact Module.IsDescentCocycle.picClass_congr _ _ (congrArg _ hcc)

/-! ## Move 2: cohomologous cocycles -/


/-- Cohomologous unit cocycles have the same Picard class along any basic refinement. -/
theorem pic_eq_of_isCohomologous (P : 𝒰.BasicRefinement) {γ γ' : X.unitsCocycle 𝒰}
    (h : γ.IsCohomologous γ') : P.pic γ = P.pic γ' := by
  letI := P.faithfullyFlat
  obtain ⟨α, hα⟩ := (OneCocycle.isCohomologous_iff_evInf _ _).mp h
  -- restate the comparison through the `Γ`-typed interface
  have hα' : ∀ z w : X,
      X.unitsRestrict (inf_le_left : 𝒰.opens z ⊓ 𝒰.opens w ≤ 𝒰.opens z) (α z)
          * unitsEvInf γ z w
        = unitsEvInf γ' z w
          * X.unitsRestrict (inf_le_right : 𝒰.opens z ⊓ 𝒰.opens w ≤ 𝒰.opens w) (α w) :=
    fun z w ↦ hα z w
  have hrel : ∀ i j, (P.coverCocycle γ i j).val
      = IsLocalization.AwayCover.inclLeft (A := Γ(X, ⊤)) (f := P.r)
          (S := fun i ↦ Γ(X, X.basicOpen (P.r i)))
          (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j))) i j
          ((X.unitsRestrict (P.basicOpen_le i) (α (P.pt i)))⁻¹ : _).val
        * ((P.coverCocycle γ' i j).val
          * IsLocalization.AwayCover.inclRight (A := Γ(X, ⊤)) (f := P.r)
              (S := fun i ↦ Γ(X, X.basicOpen (P.r i)))
              (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j))) i j
              ((((X.unitsRestrict (P.basicOpen_le j) (α (P.pt j)))⁻¹)⁻¹ : _).val)) := by
    intro i j
    rw [P.inclLeft_eq_basicRes, P.inclRight_eq_basicRes, inv_inv]
    -- units-level form of the component relation
    have e := congrArg (X.unitsRestrict (P.overlap_le i j)) (hα' (P.pt i) (P.pt j))
    rw [map_mul, map_mul] at e
    have key : P.coverCocycle γ i j
        = X.unitsRestrict (P.mul_le_left i j)
            ((X.unitsRestrict (P.basicOpen_le i) (α (P.pt i)))⁻¹)
          * (P.coverCocycle γ' i j
            * X.unitsRestrict (P.mul_le_right i j)
                ((X.unitsRestrict (P.basicOpen_le j) (α (P.pt j))))) := by
      rw [map_inv, unitsRestrict_unitsRestrict, unitsRestrict_unitsRestrict]
      rw [coverCocycle, coverCocycle]
      rw [show X.unitsRestrict ((P.mul_le_left i j).trans (P.basicOpen_le i)) (α (P.pt i))
          = X.unitsRestrict (P.overlap_le i j)
              (X.unitsRestrict (inf_le_left : 𝒰.opens (P.pt i) ⊓ 𝒰.opens (P.pt j)
                ≤ 𝒰.opens (P.pt i)) (α (P.pt i)))
        from (unitsRestrict_unitsRestrict _ _ _).symm,
        show X.unitsRestrict ((P.mul_le_right i j).trans (P.basicOpen_le j)) (α (P.pt j))
          = X.unitsRestrict (P.overlap_le i j)
              (X.unitsRestrict (inf_le_right : 𝒰.opens (P.pt i) ⊓ 𝒰.opens (P.pt j)
                ≤ 𝒰.opens (P.pt j)) (α (P.pt j)))
        from (unitsRestrict_unitsRestrict _ _ _).symm]
      rw [← e]
      group
    have hval := congrArg Units.val key
    simpa only [Units.val_mul, coe_unitsRestrict_basicOpen] using hval
  rw [P.pic_eq_picClass γ, P.pic_eq_picClass γ']
  exact IsLocalization.AwayCover.picClass_eq_of_coboundary (A := Γ(X, ⊤)) (f := P.r)
    (S := fun i ↦ Γ(X, X.basicOpen (P.r i)))
    (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j)))
    (W := fun i j k ↦ Γ(X, X.basicOpen (P.r i * (P.r j * P.r k))))
    (P.isCoverCocycle γ') (P.isCoverCocycle γ)
    (fun i ↦ (X.unitsRestrict (P.basicOpen_le i) (α (P.pt i)))⁻¹) hrel

/-! ## Move 3: change of basic refinement -/

/-- Refine-compare along the first projection: the merge pointed by `P` has the same
Picard class as `P`. -/
theorem pic_interFst (P Q : 𝒰.BasicRefinement)
    (γ : X.unitsCocycle 𝒰) : (P.interFst Q).pic γ = P.pic γ := by
  letI := P.faithfullyFlat
  letI := (P.interFst Q).faithfullyFlat
  have hτ : ∀ p : P.ι × Q.ι,
      IsUnit (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen ((P.interFst Q).r p)) (P.r p.1)) :=
    fun p ↦ IsLocalization.Away.isUnit_of_dvd ((P.interFst Q).r p)
      (⟨Q.r p.2, rfl⟩ : P.r p.1 ∣ (P.interFst Q).r p)
  have hτT : ∀ p q : P.ι × Q.ι,
      IsUnit (algebraMap Γ(X, ⊤)
        Γ(X, X.basicOpen ((P.interFst Q).r p * (P.interFst Q).r q))
        (P.r p.1 * P.r q.1)) :=
    fun p q ↦ IsLocalization.Away.isUnit_of_dvd ((P.interFst Q).r p * (P.interFst Q).r q)
      (⟨Q.r p.2 * Q.r q.2, by simp only [interFst_r]; ring⟩ :
        P.r p.1 * P.r q.1 ∣ (P.interFst Q).r p * (P.interFst Q).r q)
  have hrel : ∀ p q : P.ι × Q.ι, (P.interFst Q).coverCocycle γ p q
      = Units.map (IsLocalization.AwayCover.refineOverlapAlgHom (A := Γ(X, ⊤)) (f := P.r)
          (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j)))
          (T' := fun p q ↦ Γ(X, X.basicOpen ((P.interFst Q).r p * (P.interFst Q).r q)))
          Prod.fst hτT p q).toRingHom.toMonoidHom (P.coverCocycle γ p.1 q.1) := by
    intro p q
    have hle : X.basicOpen ((P.interFst Q).r p * (P.interFst Q).r q)
        ≤ X.basicOpen (P.r p.1 * P.r q.1) :=
      X.basicOpen_le_of_dvd ⟨Q.r p.2 * Q.r q.2, by simp only [interFst_r]; ring⟩
    have hro : IsLocalization.AwayCover.refineOverlapAlgHom (A := Γ(X, ⊤)) (f := P.r)
          (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j)))
          (T' := fun p q ↦ Γ(X, X.basicOpen ((P.interFst Q).r p * (P.interFst Q).r q)))
          Prod.fst hτT p q
        = X.basicRes _ _ hle :=
      X.basicOpen_algHom_ext _ _ _
    rw [hro]
    have hmap : Units.map ((X.basicRes _ _ hle)).toRingHom.toMonoidHom
          (P.coverCocycle γ p.1 q.1)
        = X.unitsRestrict hle (P.coverCocycle γ p.1 q.1) := rfl
    rw [hmap, coverCocycle, coverCocycle, unitsRestrict_unitsRestrict]
    rfl
  rw [pic_eq_picClass, pic_eq_picClass]
  exact IsLocalization.AwayCover.picClass_map_refine (A := Γ(X, ⊤)) (f := P.r)
    (S := fun i ↦ Γ(X, X.basicOpen (P.r i)))
    (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j)))
    (W := fun i j k ↦ Γ(X, X.basicOpen (P.r i * (P.r j * P.r k))))
    (f' := (P.interFst Q).r)
    (S' := fun p ↦ Γ(X, X.basicOpen ((P.interFst Q).r p)))
    (T' := fun p q ↦ Γ(X, X.basicOpen ((P.interFst Q).r p * (P.interFst Q).r q)))
    Prod.fst hτ hτT
    (W' := fun p q t ↦ Γ(X, X.basicOpen ((P.interFst Q).r p
      * ((P.interFst Q).r q * (P.interFst Q).r t))))
    (P.isCoverCocycle γ) ((P.interFst Q).isCoverCocycle γ) hrel

/-- Refine-compare along the second projection: the merge pointed by `Q` has the same
Picard class as `Q`. -/
theorem pic_inter (P : 𝒰.BasicRefinement) (Q : 𝒱.BasicRefinement)
    (γ : X.unitsCocycle 𝒱) : (P.inter Q).pic γ = Q.pic γ := by
  letI := Q.faithfullyFlat
  letI := (P.inter Q).faithfullyFlat
  have hτ : ∀ p : P.ι × Q.ι,
      IsUnit (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen ((P.inter Q).r p)) (Q.r p.2)) :=
    fun p ↦ IsLocalization.Away.isUnit_of_dvd ((P.inter Q).r p)
      (⟨P.r p.1, mul_comm _ _⟩ : Q.r p.2 ∣ (P.inter Q).r p)
  have hτT : ∀ p q : P.ι × Q.ι,
      IsUnit (algebraMap Γ(X, ⊤)
        Γ(X, X.basicOpen ((P.inter Q).r p * (P.inter Q).r q))
        (Q.r p.2 * Q.r q.2)) :=
    fun p q ↦ IsLocalization.Away.isUnit_of_dvd ((P.inter Q).r p * (P.inter Q).r q)
      (⟨P.r p.1 * P.r q.1, by simp only [inter_r]; ring⟩ :
        Q.r p.2 * Q.r q.2 ∣ (P.inter Q).r p * (P.inter Q).r q)
  have hrel : ∀ p q : P.ι × Q.ι, (P.inter Q).coverCocycle γ p q
      = Units.map (IsLocalization.AwayCover.refineOverlapAlgHom (A := Γ(X, ⊤)) (f := Q.r)
          (T := fun i j ↦ Γ(X, X.basicOpen (Q.r i * Q.r j)))
          (T' := fun p q ↦ Γ(X, X.basicOpen ((P.inter Q).r p * (P.inter Q).r q)))
          Prod.snd hτT p q).toRingHom.toMonoidHom (Q.coverCocycle γ p.2 q.2) := by
    intro p q
    have hle : X.basicOpen ((P.inter Q).r p * (P.inter Q).r q)
        ≤ X.basicOpen (Q.r p.2 * Q.r q.2) :=
      X.basicOpen_le_of_dvd ⟨P.r p.1 * P.r q.1, by simp only [inter_r]; ring⟩
    have hro : IsLocalization.AwayCover.refineOverlapAlgHom (A := Γ(X, ⊤)) (f := Q.r)
          (T := fun i j ↦ Γ(X, X.basicOpen (Q.r i * Q.r j)))
          (T' := fun p q ↦ Γ(X, X.basicOpen ((P.inter Q).r p * (P.inter Q).r q)))
          Prod.snd hτT p q
        = X.basicRes _ _ hle :=
      X.basicOpen_algHom_ext _ _ _
    rw [hro]
    have hmap : Units.map ((X.basicRes _ _ hle)).toRingHom.toMonoidHom
          (Q.coverCocycle γ p.2 q.2)
        = X.unitsRestrict hle (Q.coverCocycle γ p.2 q.2) := rfl
    rw [hmap, coverCocycle, coverCocycle, unitsRestrict_unitsRestrict]
    rfl
  rw [pic_eq_picClass, pic_eq_picClass]
  exact IsLocalization.AwayCover.picClass_map_refine (A := Γ(X, ⊤)) (f := Q.r)
    (S := fun i ↦ Γ(X, X.basicOpen (Q.r i)))
    (T := fun i j ↦ Γ(X, X.basicOpen (Q.r i * Q.r j)))
    (W := fun i j k ↦ Γ(X, X.basicOpen (Q.r i * (Q.r j * Q.r k))))
    (f' := (P.inter Q).r)
    (S' := fun p ↦ Γ(X, X.basicOpen ((P.inter Q).r p)))
    (T' := fun p q ↦ Γ(X, X.basicOpen ((P.inter Q).r p * (P.inter Q).r q)))
    Prod.snd hτ hτT
    (W' := fun p q t ↦ Γ(X, X.basicOpen ((P.inter Q).r p
      * ((P.inter Q).r q * (P.inter Q).r t))))
    (Q.isCoverCocycle γ) ((P.inter Q).isCoverCocycle γ) hrel

/-- The two point-selections on the merge of two refinements of the same cover give the
same Picard class: they differ by the index-wise coboundary of the cross evaluations
`γ (P.pt i, Q.pt j)`. -/
theorem pic_interFst_eq_inter (P Q : 𝒰.BasicRefinement) (γ : X.unitsCocycle 𝒰) :
    (P.interFst Q).pic γ = (P.inter Q).pic γ := by
  letI := (P.inter Q).faithfullyFlat
  letI := (P.interFst Q).faithfullyFlat
  have hβle : ∀ p : P.ι × Q.ι, X.basicOpen ((P.inter Q).r p)
      ≤ 𝒰.opens (P.pt p.1) ⊓ 𝒰.opens (Q.pt p.2) :=
    fun p ↦ (X.basicOpen_mul _ _).trans_le
      (inf_le_inf (P.basicOpen_le p.1) (Q.basicOpen_le p.2))
  have hrel : ∀ p q : P.ι × Q.ι, ((P.interFst Q).coverCocycle γ p q).val
      = IsLocalization.AwayCover.inclLeft (A := Γ(X, ⊤)) (f := (P.inter Q).r)
          (S := fun p ↦ Γ(X, X.basicOpen ((P.inter Q).r p)))
          (T := fun p q ↦ Γ(X, X.basicOpen ((P.inter Q).r p * (P.inter Q).r q))) p q
          ((X.unitsRestrict (hβle p) (unitsEvInf γ (P.pt p.1) (Q.pt p.2))).val)
        * (((P.inter Q).coverCocycle γ p q).val
          * IsLocalization.AwayCover.inclRight (A := Γ(X, ⊤)) (f := (P.inter Q).r)
              (S := fun p ↦ Γ(X, X.basicOpen ((P.inter Q).r p)))
              (T := fun p q ↦ Γ(X, X.basicOpen ((P.inter Q).r p * (P.inter Q).r q))) p q
              (((X.unitsRestrict (hβle q) (unitsEvInf γ (P.pt q.1) (Q.pt q.2)))⁻¹).val)) := by
    intro p q
    rw [(P.inter Q).inclLeft_eq_basicRes p q, (P.inter Q).inclRight_eq_basicRes p q]
    have key : (P.interFst Q).coverCocycle γ p q
        = X.unitsRestrict ((P.inter Q).mul_le_left p q)
            (X.unitsRestrict (hβle p) (unitsEvInf γ (P.pt p.1) (Q.pt p.2)))
          * ((P.inter Q).coverCocycle γ p q
            * X.unitsRestrict ((P.inter Q).mul_le_right p q)
                ((X.unitsRestrict (hβle q) (unitsEvInf γ (P.pt q.1) (Q.pt q.2)))⁻¹)) := by
      rw [coverCocycle, coverCocycle, map_inv, unitsRestrict_unitsRestrict,
        unitsRestrict_unitsRestrict]
      have e₁ := congrArg (X.unitsRestrict (le_inf
          (((P.inter Q).mul_le_left p q).trans (hβle p))
          (((P.inter Q).mul_le_right p q).trans ((hβle q).trans inf_le_right)) :
            X.basicOpen ((P.inter Q).r p * (P.inter Q).r q)
              ≤ 𝒰.opens (P.pt p.1) ⊓ 𝒰.opens (Q.pt p.2) ⊓ 𝒰.opens (Q.pt q.2)))
        (unitsEvInf_trans γ (P.pt p.1) (Q.pt p.2) (Q.pt q.2))
      have e₂ := congrArg (X.unitsRestrict (le_inf (le_inf
          (((P.inter Q).mul_le_left p q).trans ((hβle p).trans inf_le_left))
          (((P.inter Q).mul_le_right p q).trans ((hβle q).trans inf_le_left)))
          (((P.inter Q).mul_le_right p q).trans ((hβle q).trans inf_le_right)) :
            X.basicOpen ((P.inter Q).r p * (P.inter Q).r q)
              ≤ 𝒰.opens (P.pt p.1) ⊓ 𝒰.opens (P.pt q.1) ⊓ 𝒰.opens (Q.pt q.2)))
        (unitsEvInf_trans γ (P.pt p.1) (P.pt q.1) (Q.pt q.2))
      simp only [map_mul, unitsRestrict_unitsRestrict] at e₁ e₂
      rw [← mul_assoc]
      exact eq_mul_inv_iff_mul_eq.mpr (e₂.trans e₁.symm)
    have hval := congrArg Units.val key
    simpa only [Units.val_mul, coe_unitsRestrict_basicOpen] using hval
  rw [pic_eq_picClass, pic_eq_picClass]
  exact IsLocalization.AwayCover.picClass_eq_of_coboundary (A := Γ(X, ⊤))
    (f := (P.inter Q).r)
    (S := fun p ↦ Γ(X, X.basicOpen ((P.inter Q).r p)))
    (T := fun p q ↦ Γ(X, X.basicOpen ((P.inter Q).r p * (P.inter Q).r q)))
    (W := fun p q t ↦ Γ(X, X.basicOpen ((P.inter Q).r p
      * ((P.inter Q).r q * (P.inter Q).r t))))
    ((P.inter Q).isCoverCocycle γ) ((P.interFst Q).isCoverCocycle γ)
    (fun p ↦ X.unitsRestrict (hβle p) (unitsEvInf γ (P.pt p.1) (Q.pt p.2))) hrel

/-- **Any two basic refinements of the same pointed cover give the same Picard
class.** -/
theorem pic_eq_pic (P Q : 𝒰.BasicRefinement) (γ : X.unitsCocycle 𝒰) :
    P.pic γ = Q.pic γ :=
  ((pic_interFst P Q γ).symm.trans (pic_interFst_eq_inter P Q γ)).trans (pic_inter P Q γ)

/-! ## The master comparison -/

/-- **Full choice-independence of the descent Picard class**: if two cocycles on two
pointed covers restrict to cohomologous cocycles on a common refinement, their Picard
classes along arbitrary basic refinements agree. -/
theorem pic_congr {𝒲 : X.PointedCover} (h₁ : 𝒲 ≤ 𝒰) (h₂ : 𝒲 ≤ 𝒱)
    (P : 𝒰.BasicRefinement) (Q : 𝒱.BasicRefinement)
    {γ : X.unitsCocycle 𝒰} {γ' : X.unitsCocycle 𝒱}
    (h : (γ.res fun x ↦ homOfLE (h₁ x)).IsCohomologous (γ'.res fun x ↦ homOfLE (h₂ x))) :
    P.pic γ = Q.pic γ' := by
  obtain ⟨R⟩ := BasicRefinement.nonempty 𝒲
  calc
    P.pic γ = (R.ofLE h₁).pic γ := pic_eq_pic P (R.ofLE h₁) γ
    _ = R.pic (γ.res fun x ↦ homOfLE (h₁ x)) := pic_ofLE h₁ R γ
    _ = R.pic (γ'.res fun x ↦ homOfLE (h₂ x)) := pic_eq_of_isCohomologous R h
    _ = (R.ofLE h₂).pic γ' := (pic_ofLE h₂ R γ').symm
    _ = Q.pic γ' := pic_eq_pic (R.ofLE h₂) Q γ'

/-! ## Multiplicativity and normalization on a fixed refinement -/

/-- The Picard class of the trivial cocycle is trivial. -/
theorem pic_one (P : 𝒰.BasicRefinement) : P.pic (1 : X.unitsCocycle 𝒰) = 1 := by
  haveI := P.faithfullyFlat
  have hcov : P.coverCocycle (1 : X.unitsCocycle 𝒰) = fun _ _ ↦ 1 := by
    funext i j
    rw [coverCocycle, one_unitsEvInf, map_one]
  have hunit : IsLocalization.AwayCover.cocycleUnit P.r
      (fun i ↦ Γ(X, X.basicOpen (P.r i))) (fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j)))
      (P.coverCocycle (1 : X.unitsCocycle 𝒰)) = 1 := by
    rw [hcov]
    apply Units.ext
    rw [IsLocalization.AwayCover.cocycleUnit_val,
      show IsLocalization.AwayCover.piUnit
        (fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j))) (fun _ _ ↦ 1) = 1 from Units.ext rfl]
    exact map_one _
  exact (Module.IsDescentCocycle.picClass_congr _ Module.IsDescentCocycle.one hunit).trans
    Module.IsDescentCocycle.picClass_one

/-- The Picard class is multiplicative in the cocycle. -/
theorem pic_mul (P : 𝒰.BasicRefinement) (γ γ' : X.unitsCocycle 𝒰) :
    P.pic (γ * γ') = P.pic γ * P.pic γ' := by
  haveI := P.faithfullyFlat
  have hcov : P.coverCocycle (γ * γ')
      = fun i j ↦ P.coverCocycle γ i j * P.coverCocycle γ' i j := by
    funext i j
    rw [coverCocycle, coverCocycle, coverCocycle, mul_unitsEvInf, map_mul]
  refine (Module.IsDescentCocycle.picClass_congr _
      ((IsLocalization.AwayCover.isDescentCocycle_cocycleUnit _ _ _ _
          (P.isCoverCocycle γ)).mul
        (IsLocalization.AwayCover.isDescentCocycle_cocycleUnit _ _ _ _
          (P.isCoverCocycle γ'))) ?_).trans
    (Module.IsDescentCocycle.picClass_mul _ _)
  rw [hcov]
  exact IsLocalization.AwayCover.cocycleUnit_mul P.r _ _ _ _

/-! ## Triviality detection -/

/-- If the Picard class of a cocycle vanishes, the cocycle is a coboundary: its `H¹`
class is trivial. -/
theorem class_eq_one_of_pic_eq_one (P : 𝒰.BasicRefinement) (γ : X.unitsCocycle 𝒰)
    (h : P.pic γ = 1) : γ.class = (1 : X.unitsH1 𝒰) := by
  letI := P.faithfullyFlat
  rw [P.pic_eq_picClass γ] at h
  obtain ⟨β, hβ⟩ := (Module.IsDescentCocycle.picClass_eq_one_iff _).mp h
  have hcomp := IsLocalization.AwayCover.exists_units_of_cocycleUnit_eq_descentCoboundary
    P.r (fun i ↦ Γ(X, X.basicOpen (P.r i)))
    (fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j))) hβ
  -- per-index comparison units
  set α : ∀ i : P.ι, Γ(X, X.basicOpen (P.r i))ˣ :=
    fun i ↦ Units.map (Pi.evalMonoidHom (fun i ↦ Γ(X, X.basicOpen (P.r i))) i) β with hα
  -- units-level, on the double overlap `D(r i * r j)`
  have hcc : ∀ i j, P.coverCocycle γ i j
      = X.unitsRestrict (P.mul_le_right i j) (α j)
        * X.unitsRestrict (P.mul_le_left i j) ((α i)⁻¹) := by
    intro i j
    apply Units.ext
    have := hcomp i j
    rw [(P.inclRight_eq_basicRes i j), (P.inclLeft_eq_basicRes i j)] at this
    exact this
  refine unitsH1_eq_one_of_family γ P.pt (fun i ↦ X.basicOpen (P.r i)) P.basicOpen_le
    (fun x ↦ ?_) α (fun k l ↦ ?_)
  · exact Opens.mem_iSup.mp (P.iSup_eq.ge (trivial : x ∈ (⊤ : X.Opens)))
  · -- restrict the comparison from `D(r k * r l)` to `D(r k) ⊓ D(r l)`
    have e := congrArg
      (X.unitsRestrict ((X.basicOpen_mul (P.r k) (P.r l)).ge :
        X.basicOpen (P.r k) ⊓ X.basicOpen (P.r l) ≤ X.basicOpen (P.r k * P.r l)))
      (hcc k l)
    rw [coverCocycle, map_mul, unitsRestrict_unitsRestrict, unitsRestrict_unitsRestrict,
      unitsRestrict_unitsRestrict, map_inv] at e
    rw [show X.unitsRestrict
          (((X.basicOpen_mul (P.r k) (P.r l)).ge).trans (P.mul_le_right k l)) (α l)
        = X.unitsRestrict
          (inf_le_right : X.basicOpen (P.r k) ⊓ X.basicOpen (P.r l) ≤ X.basicOpen (P.r l))
          (α l) from rfl,
      show X.unitsRestrict
          (((X.basicOpen_mul (P.r k) (P.r l)).ge).trans (P.mul_le_left k l)) (α k)
        = X.unitsRestrict
          (inf_le_left : X.basicOpen (P.r k) ⊓ X.basicOpen (P.r l) ≤ X.basicOpen (P.r k))
          (α k) from rfl] at e
    rw [show X.unitsRestrict (inf_le_inf (P.basicOpen_le k) (P.basicOpen_le l))
          (unitsEvInf γ (P.pt k) (P.pt l))
        = X.unitsRestrict (((X.basicOpen_mul (P.r k) (P.r l)).ge).trans (P.overlap_le k l))
          (unitsEvInf γ (P.pt k) (P.pt l)) from rfl, e]
    rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]

end pic

end PointedCover.BasicRefinement


end Scheme

end AlgebraicGeometry
