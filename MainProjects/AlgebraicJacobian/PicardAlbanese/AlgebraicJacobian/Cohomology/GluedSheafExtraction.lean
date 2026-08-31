/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafClass

/-!
# Presentation extraction: every Čech Picard class is a cocycle datum (DAT-1, stage 1f)

The extraction keystone of `informal/spec-dat-1.md` stage (1f) (worksheet §2.3.1, the
front half of V-rel-B): every `Scheme.CechPic` class on the relative curve `C_B`
refines to a pinned basic-open cocycle datum — a `Scheme.BasicOpenCocycleDatum C B π`
on **finite** basic-open families of the two pinned charts — with the same class.

* `Scheme.unitsEvInf_self` — the diagonal pair values of a unit cocycle are `1`.
* `Scheme.unitsEvInf_mul_res_of_le` — the cocycle identity for pair values, restricted
  to any open below the triple overlap (the `resHom` form the datum's cocycle law
  consumes).
* `Scheme.isGluingCocycle_unitsRestrict_evInf` — restricted pair values of a unit
  cocycle along an anchored family of opens form a gluing cocycle.
* `IsAffineOpen.exists_finite_basicOpen_refinement` — **the affine refinement step**:
  on an affine open `V` and for any pointed cover `𝒰`, there is a finite family of
  sections of `V` whose basic opens refine `𝒰` (each contained in the member at an
  anchor point) and which admit a partition of unity (`exists_basicOpen_le` per point,
  quasi-compactness of `V`, and `self_le_iSup_basicOpen_iff` for the span).
* `BasicOpenCocycleDatum.refinementCoverData` / `BasicOpenCocycleDatum.ofRefinement` —
  the cocycle datum assembled from chart refinements of a pointed cover carrying a
  unit cocycle: transition units are the restricted pair values of the cocycle.
* `BasicOpenCocycleDatum.cechPicClass_eq_of_anchor` — **the class comparison**: any
  datum whose transition units are restricted pair values of a cocycle `γ` on `𝒰`
  (along an anchor map) has `cechPicClass = CechPic.mk 𝒰 γ.class`.
* `BasicOpenCocycleDatum.exists_cechPicClass_eq` — **the extraction keystone**
  (stage 1f): `∀ c : (relCurve C B).CechPic, ∃ D, D.cechPicClass = c`.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C B, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k B).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

/-! ## Pair-value algebra of unit cocycles -/

section EvInf

variable {X : Scheme.{u}}

/-- The underlying section of a restricted unit is the restricted underlying section. -/
private lemma coe_unitsRestrict {W U₀ : X.Opens} (h : W ≤ U₀) (u : Γ(X, U₀)ˣ) :
    (X.unitsRestrict h u : Γ(X, W)) = X.resHom h (u : Γ(X, U₀)) :=
  rfl

/-- **The diagonal pair values of a unit cocycle are `1`**: the cocycle identity at
`(x, x, x)` forces idempotency, and restriction along the (equal-opens) triple overlap
is invertible. -/
lemma Scheme.unitsEvInf_self {𝒰 : X.PointedCover} (γ : X.unitsCocycle 𝒰) (x : X) :
    Scheme.unitsEvInf γ x x = 1 := by
  have h2 : X.unitsRestrict (inf_le_left :
        𝒰.opens x ⊓ 𝒰.opens x ⊓ 𝒰.opens x ≤ 𝒰.opens x ⊓ 𝒰.opens x)
        (Scheme.unitsEvInf γ x x) *
      X.unitsRestrict inf_le_left (Scheme.unitsEvInf γ x x) =
      X.unitsRestrict inf_le_left (Scheme.unitsEvInf γ x x) :=
    Scheme.unitsEvInf_trans γ x x x
  have h3 : X.unitsRestrict (inf_le_left :
      𝒰.opens x ⊓ 𝒰.opens x ⊓ 𝒰.opens x ≤ 𝒰.opens x ⊓ 𝒰.opens x)
      (Scheme.unitsEvInf γ x x) = 1 := mul_eq_right.mp h2
  refine Units.ext ?_
  have h4 := congrArg (fun u : Γ(X, 𝒰.opens x ⊓ 𝒰.opens x ⊓ 𝒰.opens x)ˣ =>
    X.resHom (le_inf le_rfl inf_le_left :
      𝒰.opens x ⊓ 𝒰.opens x ≤ 𝒰.opens x ⊓ 𝒰.opens x ⊓ 𝒰.opens x) (u : Γ(X, _))) h3
  simp only [coe_unitsRestrict, Scheme.resHom_resHom, Units.val_one, map_one] at h4
  rw [Units.val_one, ← Scheme.resHom_refl
    (Scheme.unitsEvInf γ x x : Γ(X, 𝒰.opens x ⊓ 𝒰.opens x))]
  exact h4

/-- **The cocycle identity for pair values on any sub-open of the triple overlap**, in
`resHom` form (the shape the datum's `mul_res` law consumes). -/
lemma Scheme.unitsEvInf_mul_res_of_le {𝒰 : X.PointedCover} (γ : X.unitsCocycle 𝒰)
    (x y z : X) {O : X.Opens} (hxy : O ≤ 𝒰.opens x ⊓ 𝒰.opens y)
    (hyz : O ≤ 𝒰.opens y ⊓ 𝒰.opens z) (hxz : O ≤ 𝒰.opens x ⊓ 𝒰.opens z) :
    X.resHom hxy (Scheme.unitsEvInf γ x y : Γ(X, 𝒰.opens x ⊓ 𝒰.opens y)) *
        X.resHom hyz (Scheme.unitsEvInf γ y z : Γ(X, 𝒰.opens y ⊓ 𝒰.opens z)) =
      X.resHom hxz (Scheme.unitsEvInf γ x z : Γ(X, 𝒰.opens x ⊓ 𝒰.opens z)) := by
  have hO : O ≤ 𝒰.opens x ⊓ 𝒰.opens y ⊓ 𝒰.opens z :=
    le_inf hxy (hyz.trans inf_le_right)
  have h := congrArg (fun u : Γ(X, 𝒰.opens x ⊓ 𝒰.opens y ⊓ 𝒰.opens z)ˣ =>
    X.resHom hO (u : Γ(X, _))) (Scheme.unitsEvInf_trans γ x y z)
  simp only [Units.val_mul, map_mul, coe_unitsRestrict, Scheme.resHom_resHom] at h
  exact h

/-- **Restricted pair values along an anchored family form a gluing cocycle**: for a
unit cocycle `γ` on a pointed cover `𝒰`, an arbitrary family of opens `U : J → X.Opens`
and anchor points with `U j ≤ 𝒰.opens (anchor j)`, the restrictions of the pair values
`γ.evInf (anchor i) (anchor j)` to the double overlaps satisfy the gluing cocycle
law. -/
lemma Scheme.isGluingCocycle_unitsRestrict_evInf {𝒰 : X.PointedCover}
    (γ : X.unitsCocycle 𝒰) {J : Type u} (U : J → X.Opens) (anchor : J → X)
    (hanch : ∀ j : J, U j ≤ 𝒰.opens (anchor j)) :
    Scheme.IsGluingCocycle U (fun i j =>
      X.unitsRestrict (inf_le_inf (hanch i) (hanch j))
        (Scheme.unitsEvInf γ (anchor i) (anchor j))) := by
  constructor
  · intro i
    rw [Scheme.unitsEvInf_self γ (anchor i), map_one, Units.val_one]
  · intro i j l
    simp only [coe_unitsRestrict, Scheme.resHom_resHom]
    exact Scheme.unitsEvInf_mul_res_of_le γ (anchor i) (anchor j) (anchor l) _ _ _

end EvInf

/-! ## The affine basic-open refinement of a pointed cover -/

/-- **Affine refinement of a pointed cover with a partition of unity**: on an affine
open `V`, any pointed cover `𝒰` refines to a finite family of basic opens `D(f i)`,
each contained in the cover member at an anchor point, whose sections admit a partition
of unity `∑ a i · f i = 1` in `Γ(X, V)`. -/
theorem IsAffineOpen.exists_finite_basicOpen_refinement {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) (𝒰 : X.PointedCover) :
    ∃ (ι : Type u) (_ : Fintype ι) (f : ι → Γ(X, V)) (anchor : ι → X)
      (a : ι → Γ(X, V)),
      (∀ i : ι, X.basicOpen (f i) ≤ 𝒰.opens (anchor i)) ∧ ∑ i : ι, a i * f i = 1 := by
  classical
  -- a basic open through every point of `V`, inside the cover member at that point
  have hpt : ∀ p : ↥V, ∃ f : Γ(X, V),
      X.basicOpen f ≤ 𝒰.opens (p : X) ⊓ V ∧ (p : X) ∈ X.basicOpen f := fun p =>
    hV.exists_basicOpen_le (V := 𝒰.opens (p : X) ⊓ V)
      (⟨(p : X), ⟨𝒰.mem_opens (p : X), p.2⟩⟩ : ↥(𝒰.opens (p : X) ⊓ V)) p.2
  choose f hfle hfmem using hpt
  -- a finite subfamily covering the quasi-compact `V`
  have hcov : (V : Set X) ⊆ ⋃ p : ↥V, (X.basicOpen (f p) : Set X) := fun q hq =>
    Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hfmem ⟨q, hq⟩⟩
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover
    (fun p : ↥V => (X.basicOpen (f p) : Set X))
    (fun p => (X.basicOpen (f p)).isOpen) hcov
  -- the finite subfamily, reindexed over the subcover
  have hle : V ≤ ⨆ x : (Set.range fun i : {p : ↥V // p ∈ t} => f (i : ↥V) :
      Set Γ(X, V)), X.basicOpen (x : Γ(X, V)) := by
    intro q hq
    obtain ⟨p, hpt', hpq⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨f p, Set.mem_range_self (⟨p, hpt'⟩ : {p : ↥V // p ∈ t})⟩, hpq⟩
  have hspan : Ideal.span
      (Set.range fun i : {p : ↥V // p ∈ t} => f (i : ↥V)) = ⊤ :=
    hV.self_le_iSup_basicOpen_iff.mp hle
  have hone : (1 : Γ(X, V)) ∈
      Ideal.span (Set.range fun i : {p : ↥V // p ∈ t} => f (i : ↥V)) :=
    (Ideal.eq_top_iff_one _).mp hspan
  rw [Ideal.mem_span_range_iff_exists_fun] at hone
  obtain ⟨a, ha⟩ := hone
  exact ⟨{p : ↥V // p ∈ t}, inferInstance, fun i => f (i : ↥V),
    fun i => ((i : ↥V) : X), a, fun i => (hfle (i : ↥V)).trans inf_le_left, ha⟩

/-! ## The datum of a refined pointed cover -/

section Datum

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

namespace BasicOpenCocycleDatum

variable (ι₀ ι₁ : Type u) [Fintype ι₀] [Fintype ι₁]
variable (f₀ a₀ : ι₀ → Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₀))
variable (f₁ a₁ : ι₁ → Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₁))

/-- The cover data of a chart refinement: the given finite basic-open families with
their partition witnesses. -/
noncomputable def refinementCoverData
    (hpart₀ : ∑ i : ι₀, a₀ i * f₀ i = 1) (hpart₁ : ∑ i : ι₁, a₁ i * f₁ i = 1) :
    BasicOpenCoverData C B π where
  J₀ := ι₀
  J₁ := ι₁
  fintype₀ := inferInstance
  fintype₁ := inferInstance
  h₀ := f₀
  h₁ := f₁
  a₀ := a₀
  a₁ := a₁
  partition₀ := hpart₀
  partition₁ := hpart₁

variable (𝒰 : (relCurve C B).PointedCover) (γ : (relCurve C B).unitsCocycle 𝒰)
variable (an₀ : ι₀ → relCurve C B) (an₁ : ι₁ → relCurve C B)
variable (hpart₀ : ∑ i : ι₀, a₀ i * f₀ i = 1) (hpart₁ : ∑ i : ι₁, a₁ i * f₁ i = 1)

/-- The pieces of the refinement cover data are subordinated to the pointed cover at
the anchor points. -/
lemma refinementCoverData_pieces_le
    (hsub₀ : ∀ i : ι₀, (relCurve C B).basicOpen (f₀ i) ≤ 𝒰.opens (an₀ i))
    (hsub₁ : ∀ i : ι₁, (relCurve C B).basicOpen (f₁ i) ≤ 𝒰.opens (an₁ i))
    (i : (refinementCoverData ι₀ ι₁ f₀ a₀ f₁ a₁ hpart₀ hpart₁).index) :
    (refinementCoverData ι₀ ι₁ f₀ a₀ f₁ a₁ hpart₀ hpart₁).pieces i ≤
      𝒰.opens (Sum.elim an₀ an₁ i) := by
  cases i with
  | inl i =>
    rw [BasicOpenCoverData.pieces_inl]
    exact hsub₀ i
  | inr i =>
    rw [BasicOpenCoverData.pieces_inr]
    exact hsub₁ i

/-- **The cocycle datum of a refined pointed cover** (stage 1f, the construction):
basic-open generators refining a pointed cover on both pinned charts, with transition
units the restricted pair values of a unit cocycle on the cover. -/
noncomputable def ofRefinement
    (hsub₀ : ∀ i : ι₀, (relCurve C B).basicOpen (f₀ i) ≤ 𝒰.opens (an₀ i))
    (hsub₁ : ∀ i : ι₁, (relCurve C B).basicOpen (f₁ i) ≤ 𝒰.opens (an₁ i)) :
    BasicOpenCocycleDatum C B π where
  toBasicOpenCoverData := refinementCoverData ι₀ ι₁ f₀ a₀ f₁ a₁ hpart₀ hpart₁
  unit i j := (relCurve C B).unitsRestrict
    (inf_le_inf
      (refinementCoverData_pieces_le ι₀ ι₁ f₀ a₀ f₁ a₁ 𝒰 an₀ an₁ hpart₀ hpart₁
        hsub₀ hsub₁ i)
      (refinementCoverData_pieces_le ι₀ ι₁ f₀ a₀ f₁ a₁ 𝒰 an₀ an₁ hpart₀ hpart₁
        hsub₀ hsub₁ j))
    (Scheme.unitsEvInf γ (Sum.elim an₀ an₁ i) (Sum.elim an₀ an₁ j))
  isGluingCocycle := Scheme.isGluingCocycle_unitsRestrict_evInf γ
    (refinementCoverData ι₀ ι₁ f₀ a₀ f₁ a₁ hpart₀ hpart₁).pieces (Sum.elim an₀ an₁)
    (refinementCoverData_pieces_le ι₀ ι₁ f₀ a₀ f₁ a₁ 𝒰 an₀ an₁ hpart₀ hpart₁
      hsub₀ hsub₁)

end BasicOpenCocycleDatum

/-! ## The class comparison and the extraction keystone -/

namespace BasicOpenCocycleDatum

/-- **The class of an anchored datum**: a datum whose transition units are the
restricted pair values of a unit cocycle `γ` on a pointed cover `𝒰` (along an anchor
map dominating the pieces) has Čech Picard class `CechPic.mk 𝒰 γ.class`. The
comparison runs on the pointed cover `x ↦ 𝒰.opens x ⊓ pieces (σ x)`, where the two
restricted cocycles are cohomologous through the `0`-cochain
`x ↦ γ.evInf x (anchor (σ x))`. -/
theorem cechPicClass_eq_of_anchor (D : BasicOpenCocycleDatum C B π)
    (𝒰 : (relCurve C B).PointedCover) (γ : (relCurve C B).unitsCocycle 𝒰)
    (anchor : D.index → relCurve C B)
    (hanch : ∀ j : D.index, D.pieces j ≤ 𝒰.opens (anchor j))
    (hunit : ∀ i j : D.index,
      ((D.unit i j : Γ(relCurve C B, D.pieces i ⊓ D.pieces j)ˣ) :
          Γ(relCurve C B, D.pieces i ⊓ D.pieces j)) =
        (relCurve C B).resHom (inf_le_inf (hanch i) (hanch j))
          (Scheme.unitsEvInf γ (anchor i) (anchor j) :
            Γ(relCurve C B, 𝒰.opens (anchor i) ⊓ 𝒰.opens (anchor j)))) :
    D.cechPicClass = Scheme.CechPic.mk 𝒰 γ.class := by
  set 𝒲 : (relCurve C B).PointedCover :=
    ⟨fun x => 𝒰.opens x ⊓ D.pieces (D.pieceIndex x),
      fun x => ⟨𝒰.mem_opens x, D.mem_pieces_pieceIndex x⟩⟩ with h𝒲
  have h𝒲𝒰 : 𝒲 ≤ 𝒰 := fun x => inf_le_left
  have hsub : ∀ x : relCurve C B, 𝒲.opens x ≤ D.pieces (D.pieceIndex x) :=
    fun x => inf_le_right
  -- the subordinated cocycle of the datum and the restricted `γ` are cohomologous
  have hcoh : (gluedSubordCocycle D.isGluingCocycle 𝒲 D.pieceIndex hsub).IsCohomologous
      (γ.res fun x => homOfLE (h𝒲𝒰 x)) := by
    refine Scheme.unitsCocycle_isCohomologous
      (fun x => (relCurve C B).unitsRestrict
        (le_inf inf_le_left (inf_le_right.trans (hanch (D.pieceIndex x))) :
          𝒲.opens x ≤ 𝒰.opens x ⊓ 𝒰.opens (anchor (D.pieceIndex x)))
        (Scheme.unitsEvInf γ x (anchor (D.pieceIndex x)))) (fun x y => ?_)
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, gluedSubordCocycle_evInf,
      Scheme.res_unitsEvInf h𝒲𝒰 γ x y]
    simp only [coe_unitsRestrict, gluedSubordUnit, Scheme.resHom_resHom]
    rw [hunit (D.pieceIndex x) (D.pieceIndex y), Scheme.resHom_resHom]
    have hL := Scheme.unitsEvInf_mul_res_of_le γ x (anchor (D.pieceIndex x))
      (anchor (D.pieceIndex y))
      (O := 𝒲.opens x ⊓ 𝒲.opens y)
      (le_inf (inf_le_left.trans inf_le_left)
        ((inf_le_left.trans inf_le_right).trans (hanch (D.pieceIndex x))))
      (le_inf ((inf_le_left.trans inf_le_right).trans (hanch (D.pieceIndex x)))
        ((inf_le_right.trans inf_le_right).trans (hanch (D.pieceIndex y))))
      (le_inf (inf_le_left.trans inf_le_left)
        ((inf_le_right.trans inf_le_right).trans (hanch (D.pieceIndex y))))
    have hR := Scheme.unitsEvInf_mul_res_of_le γ x y (anchor (D.pieceIndex y))
      (O := 𝒲.opens x ⊓ 𝒲.opens y)
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (le_inf (inf_le_right.trans inf_le_left)
        ((inf_le_right.trans inf_le_right).trans (hanch (D.pieceIndex y))))
      (le_inf (inf_le_left.trans inf_le_left)
        ((inf_le_right.trans inf_le_right).trans (hanch (D.pieceIndex y))))
    exact hL.trans hR.symm
  calc D.cechPicClass
      = Scheme.CechPic.mk 𝒲
          (gluedSubordCocycle D.isGluingCocycle 𝒲 D.pieceIndex hsub).class :=
        (D.cechPicClass_eq_mk 𝒲 D.pieceIndex hsub).symm
    _ = Scheme.CechPic.mk 𝒲 (γ.res fun x => homOfLE (h𝒲𝒰 x)).class :=
        congrArg (Scheme.CechPic.mk 𝒲) hcoh.class_eq
    _ = Scheme.CechPic.mk 𝒰 γ.class := Scheme.CechPic.mk_unitsRes h𝒲𝒰 γ.class

/-- **The extraction keystone** (stage 1f; worksheet §2.3.1): every Čech Picard class
on the relative curve refines to a pinned basic-open cocycle datum with the same
class — the DAT-1 constructor input shape, on finite basic-open families of the two
pinned charts. -/
theorem exists_cechPicClass_eq (c : (relCurve C B).CechPic) :
    ∃ D : BasicOpenCocycleDatum C B π, D.cechPicClass = c := by
  induction c using Scheme.CechPic.ind with | mk 𝒰 a =>
  induction a using Quot.ind with | _ γ =>
  obtain ⟨ι₀, hfin₀, f₀, an₀, a₀, hsub₀, hpart₀⟩ :=
    (relCover_isAffineOpen₀ C B (fiberTwoCover π)).exists_finite_basicOpen_refinement 𝒰
  obtain ⟨ι₁, hfin₁, f₁, an₁, a₁, hsub₁, hpart₁⟩ :=
    (relCover_isAffineOpen₁ C B (fiberTwoCover π)).exists_finite_basicOpen_refinement 𝒰
  refine ⟨ofRefinement ι₀ ι₁ f₀ a₀ f₁ a₁ 𝒰 γ an₀ an₁ hpart₀ hpart₁ hsub₀ hsub₁, ?_⟩
  exact cechPicClass_eq_of_anchor _ 𝒰 γ (Sum.elim an₀ an₁)
    (refinementCoverData_pieces_le ι₀ ι₁ f₀ a₀ f₁ a₁ 𝒰 an₀ an₁ hpart₀ hpart₁
      hsub₀ hsub₁)
    (fun i j => rfl)

end BasicOpenCocycleDatum

end Datum

end AlgebraicGeometry
