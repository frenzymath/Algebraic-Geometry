/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.LocalizationCocycleRefine
import AlgebraicJacobian.Picard.SectionsAlgebra

/-!
# The Picard class of a unit Čech cocycle on an affine scheme

For an affine scheme `X`, a unit Čech cocycle `γ` on a pointed cover `𝒰` determines a
class in mathlib's Picard group `CommRing.Pic Γ(X, ⊤)`, by faithfully flat descent along
a finite basic refinement of `𝒰`:

* `Scheme.PointedCover.BasicRefinement`: finitely many points `pt i` and sections
  `r i : Γ(X, ⊤)` with `X.basicOpen (r i) ≤ 𝒰.opens (pt i)`, covering `X`.  Such data
  always exists (`BasicRefinement.nonempty`): basic opens form a basis of an affine
  scheme, which is quasi-compact.
* `BasicRefinement.coverCocycle γ`: the evaluations `γ (pt i, pt j)` restricted to the
  pairwise overlaps `X.basicOpen (r i * r j)` — a Čech cocycle of units on the finite
  localization cover `r` in the sense of `IsLocalization.AwayCover.IsCoverCocycle`
  (`BasicRefinement.isCoverCocycle`; the canonical algebra maps between localizations
  agree with restriction of sections by uniqueness, `Scheme.basicOpen_algHom_ext`).
* `BasicRefinement.pic γ : CommRing.Pic Γ(X, ⊤)`: the Picard class of the invertible
  module descended from the associated descent 1-cocycle
  (`AlgebraicJacobian.Descent.UnitDescent`) along the faithfully flat cover algebra
  `∀ i, Γ(X, X.basicOpen (r i))`.

The independence of `pic γ` from all choices, and the resulting group homomorphism
`X.CechPic →* CommRing.Pic Γ(X, ⊤)`, are established in
`AlgebraicJacobian.Picard.PicAffine`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

/-! ## Basic refinements of a pointed cover -/

/-- A finite basic refinement of a pointed cover of a scheme: finitely many points and
sections whose basic opens refine the cover at those points and still cover `X`.  The
index type is a field, so that refinements can be merged (`BasicRefinement.inter`). -/
structure PointedCover.BasicRefinement (𝒰 : X.PointedCover) : Type (u + 1) where
  /-- The index type of the refinement. -/
  ι : Type u
  /-- The index type is finite. -/
  [fintype : Fintype ι]
  /-- The index type has decidable equality. -/
  [decEq : DecidableEq ι]
  /-- The chosen points. -/
  pt : ι → X
  /-- The sections cutting out the basic opens. -/
  r : ι → Γ(X, ⊤)
  /-- Each basic open refines the cover at its point. -/
  basicOpen_le : ∀ i, X.basicOpen (r i) ≤ 𝒰.opens (pt i)
  /-- The basic opens cover `X`. -/
  iSup_eq : (⨆ i, X.basicOpen (r i)) = ⊤

namespace PointedCover.BasicRefinement

attribute [instance] fintype decEq

/-- Every pointed cover of an affine scheme admits a finite basic refinement: basic
opens form a basis and the space is quasi-compact. -/
theorem nonempty [IsAffine X] (𝒰 : X.PointedCover) : Nonempty 𝒰.BasicRefinement := by
  have hex : ∀ x : X, ∃ f : Γ(X, ⊤), X.basicOpen f ≤ 𝒰.opens x ∧ x ∈ X.basicOpen f :=
    fun x ↦ (isAffineOpen_top X).exists_basicOpen_le
      (⟨x, 𝒰.mem_opens x⟩ : (𝒰.opens x : TopologicalSpace.Opens X)) trivial
  choose f hf₁ hf₂ using hex
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover isCompact_univ
    (fun x : X ↦ (X.basicOpen (f x) : Set X)) (fun x ↦ (X.basicOpen (f x)).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hf₂ x⟩)
  letI : DecidableEq X := Classical.decEq X
  refine ⟨{ ι := ↥t, pt := fun y ↦ (y : X), r := fun y ↦ f (y : X),
            basicOpen_le := fun y ↦ hf₁ _, iSup_eq := ?_ }⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨⟨y, hy.1⟩, hy.2⟩

/-- Merging two basic refinements: the products of the sections, indexed by pairs, with
the points of the **second** refinement.  The result refines every pointed cover that the
second refinement refines. -/
@[simps]
def inter {𝒰 𝒱 : X.PointedCover} (P : 𝒰.BasicRefinement) (Q : 𝒱.BasicRefinement) :
    𝒱.BasicRefinement where
  ι := P.ι × Q.ι
  pt p := Q.pt p.2
  r p := P.r p.1 * Q.r p.2
  basicOpen_le p := ((X.basicOpen_mul _ _).trans_le inf_le_right).trans (Q.basicOpen_le p.2)
  iSup_eq := by
    rw [eq_top_iff]
    intro x _
    have hxP : x ∈ ⨆ i, X.basicOpen (P.r i) := P.iSup_eq.ge trivial
    have hxQ : x ∈ ⨆ j, X.basicOpen (Q.r j) := Q.iSup_eq.ge trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxP
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxQ
    exact Opens.mem_iSup.mpr ⟨(i, j), (X.basicOpen_mul _ _).ge ⟨hi, hj⟩⟩

variable {𝒰 : X.PointedCover} (P : 𝒰.BasicRefinement)

/-- The overlap of two members of the refinement is contained in the overlap of the
corresponding members of the pointed cover. -/
lemma overlap_le (i j : P.ι) :
    X.basicOpen (P.r i * P.r j) ≤ 𝒰.opens (P.pt i) ⊓ 𝒰.opens (P.pt j) :=
  (X.basicOpen_mul _ _).trans_le (inf_le_inf (P.basicOpen_le i) (P.basicOpen_le j))

lemma basicOpen_le_mul_self (i : P.ι) :
    X.basicOpen (P.r i) ≤ X.basicOpen (P.r i * P.r i) :=
  le_of_le_of_eq (le_inf le_rfl le_rfl) (X.basicOpen_mul _ _).symm

lemma _root_.AlgebraicGeometry.Scheme.basicOpen_le_of_dvd {f g : Γ(X, ⊤)} (h : f ∣ g) :
    X.basicOpen g ≤ X.basicOpen f := by
  obtain ⟨c, rfl⟩ := h
  exact (X.basicOpen_mul f c).trans_le inf_le_left

lemma mul_le_left (i j : P.ι) :
    X.basicOpen (P.r i * P.r j) ≤ X.basicOpen (P.r i) :=
  (X.basicOpen_mul _ _).trans_le inf_le_left

lemma mul_le_right (i j : P.ι) :
    X.basicOpen (P.r i * P.r j) ≤ X.basicOpen (P.r j) :=
  (X.basicOpen_mul _ _).trans_le inf_le_right

/-- The triple overlap is contained in each double overlap. -/
lemma triple_le₁₂ (i j k : P.ι) :
    X.basicOpen (P.r i * (P.r j * P.r k)) ≤ X.basicOpen (P.r i * P.r j) := by
  have h : P.r i * (P.r j * P.r k) = P.r i * P.r j * P.r k := (mul_assoc _ _ _).symm
  rw [h]
  exact (X.basicOpen_mul _ _).trans_le inf_le_left

lemma triple_le₂₃ (i j k : P.ι) :
    X.basicOpen (P.r i * (P.r j * P.r k)) ≤ X.basicOpen (P.r j * P.r k) :=
  (X.basicOpen_mul _ _).trans_le inf_le_right

lemma triple_le₁₃ (i j k : P.ι) :
    X.basicOpen (P.r i * (P.r j * P.r k)) ≤ X.basicOpen (P.r i * P.r k) := by
  have h : P.r i * (P.r j * P.r k) = P.r i * P.r k * P.r j := by ring
  rw [h]
  exact (X.basicOpen_mul _ _).trans_le inf_le_left

/-- The triple overlap is contained in the triple overlap of the pointed cover. -/
lemma triple_le (i j k : P.ι) :
    X.basicOpen (P.r i * (P.r j * P.r k))
      ≤ 𝒰.opens (P.pt i) ⊓ 𝒰.opens (P.pt j) ⊓ 𝒰.opens (P.pt k) :=
  le_inf ((P.triple_le₁₂ i j k).trans ((P.overlap_le i j).trans le_rfl))
    (((P.triple_le₂₃ i j k).trans (P.overlap_le j k)).trans inf_le_right)

/-! ## The cover cocycle of a unit Čech cocycle -/

/-- The Čech cocycle of units on the finite localization cover `P.r` obtained by
restricting the evaluations of a unit cocycle on the pointed cover. -/
noncomputable def coverCocycle (γ : X.unitsCocycle 𝒰) (i j : P.ι) :
    Γ(X, X.basicOpen (P.r i * P.r j))ˣ :=
  X.unitsRestrict (P.overlap_le i j) (unitsEvInf γ (P.pt i) (P.pt j))

section isCoverCocycle

variable [IsAffine X]

/-- The canonical algebra maps between localized section rings agree with restriction:
the diagonal map. -/
lemma diag_eq_basicRes (i : P.ι) :
    IsLocalization.AwayCover.diag (A := Γ(X, ⊤)) (f := P.r)
        (S := fun i ↦ Γ(X, X.basicOpen (P.r i)))
        (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j))) i
      = X.basicRes _ _ (P.basicOpen_le_mul_self i) :=
  X.basicOpen_algHom_ext _ _ _

lemma inclLeft_eq_basicRes (i j : P.ι) :
    IsLocalization.AwayCover.inclLeft (A := Γ(X, ⊤)) (f := P.r)
        (S := fun i ↦ Γ(X, X.basicOpen (P.r i)))
        (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j))) i j
      = X.basicRes _ _ (P.mul_le_left i j) :=
  X.basicOpen_algHom_ext _ _ _

lemma inclRight_eq_basicRes (i j : P.ι) :
    IsLocalization.AwayCover.inclRight (A := Γ(X, ⊤)) (f := P.r)
        (S := fun i ↦ Γ(X, X.basicOpen (P.r i)))
        (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j))) i j
      = X.basicRes _ _ (P.mul_le_right i j) :=
  X.basicOpen_algHom_ext _ _ _

lemma face₁₂_eq_basicRes (i j k : P.ι) :
    IsLocalization.AwayCover.face₁₂ (A := Γ(X, ⊤)) (f := P.r)
        (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j)))
        (W := fun i j k ↦ Γ(X, X.basicOpen (P.r i * (P.r j * P.r k)))) i j k
      = X.basicRes _ _ (P.triple_le₁₂ i j k) :=
  X.basicOpen_algHom_ext _ _ _

lemma face₁₃_eq_basicRes (i j k : P.ι) :
    IsLocalization.AwayCover.face₁₃ (A := Γ(X, ⊤)) (f := P.r)
        (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j)))
        (W := fun i j k ↦ Γ(X, X.basicOpen (P.r i * (P.r j * P.r k)))) i j k
      = X.basicRes _ _ (P.triple_le₁₃ i j k) :=
  X.basicOpen_algHom_ext _ _ _

lemma face₂₃_eq_basicRes (i j k : P.ι) :
    IsLocalization.AwayCover.face₂₃ (A := Γ(X, ⊤)) (f := P.r)
        (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j)))
        (W := fun i j k ↦ Γ(X, X.basicOpen (P.r i * (P.r j * P.r k)))) i j k
      = X.basicRes _ _ (P.triple_le₂₃ i j k) :=
  X.basicOpen_algHom_ext _ _ _

/-- The restricted evaluations of a unit Čech cocycle form a Čech cocycle on the finite
localization cover. -/
theorem isCoverCocycle (γ : X.unitsCocycle 𝒰) :
    IsLocalization.AwayCover.IsCoverCocycle (A := Γ(X, ⊤))
      (f := P.r)
      (S := fun i ↦ Γ(X, X.basicOpen (P.r i)))
      (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j)))
      (W := fun i j k ↦ Γ(X, X.basicOpen (P.r i * (P.r j * P.r k))))
      (P.coverCocycle γ) := by
  constructor
  · -- diagonal: `γ (x, x)` restricts to `1`
    intro i
    rw [diag_eq_basicRes]
    have h := congrArg Units.val
      (X.unitsRestrict_unitsEvInf_self γ (P.pt i) (P.basicOpen_le i))
    have hcomp :
        X.basicRes _ _ (P.basicOpen_le_mul_self i) (P.coverCocycle γ i i).val
          = (X.unitsRestrict (le_inf (P.basicOpen_le i) (P.basicOpen_le i))
              (unitsEvInf γ (P.pt i) (P.pt i))).val := by
      rw [coverCocycle, ← coe_unitsRestrict_basicOpen, unitsRestrict_unitsRestrict]
    rw [hcomp]
    exact h
  · -- cocycle identity: restrict `unitsEvInf_trans` to the triple overlap
    intro i j k
    rw [face₁₂_eq_basicRes, face₁₃_eq_basicRes, face₂₃_eq_basicRes]
    have e := congrArg (X.unitsRestrict (P.triple_le i j k))
      (unitsEvInf_trans γ (P.pt i) (P.pt j) (P.pt k))
    simp only [map_mul, unitsRestrict_unitsRestrict] at e
    have := congrArg Units.val e
    simp only [Units.val_mul] at this
    calc
      X.basicRes _ _ (P.triple_le₂₃ i j k) (P.coverCocycle γ j k).val
          * X.basicRes _ _ (P.triple_le₁₂ i j k) (P.coverCocycle γ i j).val
        = (X.unitsRestrict ((P.triple_le₂₃ i j k).trans (P.overlap_le j k))
              (unitsEvInf γ (P.pt j) (P.pt k))).val
            * (X.unitsRestrict ((P.triple_le₁₂ i j k).trans (P.overlap_le i j))
              (unitsEvInf γ (P.pt i) (P.pt j))).val := by
          rw [coverCocycle, coverCocycle, ← coe_unitsRestrict_basicOpen,
            ← coe_unitsRestrict_basicOpen, unitsRestrict_unitsRestrict,
            unitsRestrict_unitsRestrict]
      _ = (X.unitsRestrict ((P.triple_le₁₃ i j k).trans (P.overlap_le i k))
              (unitsEvInf γ (P.pt i) (P.pt k))).val :=
          (mul_comm _ _).trans this
      _ = X.basicRes _ _ (P.triple_le₁₃ i j k) (P.coverCocycle γ i k).val := by
          rw [coverCocycle, ← coe_unitsRestrict_basicOpen, unitsRestrict_unitsRestrict]

end isCoverCocycle

/-! ## The Picard class -/

/-- The sections of a basic refinement span the unit ideal. -/
theorem span_eq_top [IsAffine X] : Ideal.span (Set.range P.r) = ⊤ := by
  rw [← (isAffineOpen_top X).iSup_basicOpen_eq_self_iff]
  rw [iSup_range' (fun f ↦ X.basicOpen f) P.r]
  exact P.iSup_eq

/-- The cover algebra of a basic refinement is faithfully flat over the global
sections. -/
theorem faithfullyFlat [IsAffine X] :
    Module.FaithfullyFlat Γ(X, ⊤) (∀ i, Γ(X, X.basicOpen (P.r i))) :=
  Module.FaithfullyFlat.pi_of_span_eq_top P.r P.span_eq_top

/-- **The Picard class of a unit Čech cocycle along a basic refinement**: the class of
the invertible module obtained by faithfully flat descent of the associated descent
1-cocycle. -/
noncomputable def pic [IsAffine X] (γ : X.unitsCocycle 𝒰) : CommRing.Pic Γ(X, ⊤) :=
  haveI := P.faithfullyFlat
  (IsLocalization.AwayCover.isDescentCocycle_cocycleUnit (A := Γ(X, ⊤))
    (f := P.r) (S := fun i ↦ Γ(X, X.basicOpen (P.r i)))
    (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j)))
    (W := fun i j k ↦ Γ(X, X.basicOpen (P.r i * (P.r j * P.r k))))
    (P.isCoverCocycle γ)).picClass

/-- `pic` computes as the Picard class of the descent unit, with the faithful-flatness
instance made explicit — the interface used to apply the abstract `picClass` calculus. -/
lemma pic_eq_picClass [IsAffine X] (γ : X.unitsCocycle 𝒰) :
    P.pic γ
      = @Module.IsDescentCocycle.picClass _ _ _ _ _ P.faithfullyFlat _
          (IsLocalization.AwayCover.isDescentCocycle_cocycleUnit (A := Γ(X, ⊤))
            (f := P.r) (S := fun i ↦ Γ(X, X.basicOpen (P.r i)))
            (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j)))
            (W := fun i j k ↦ Γ(X, X.basicOpen (P.r i * (P.r j * P.r k))))
            (P.isCoverCocycle γ)) :=
  rfl

end PointedCover.BasicRefinement

end Scheme

end AlgebraicGeometry
