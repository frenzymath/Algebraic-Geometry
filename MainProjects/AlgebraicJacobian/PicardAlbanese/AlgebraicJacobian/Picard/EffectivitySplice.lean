/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EffectivityOverlap
import AlgebraicJacobian.Picard.SectionsDescent

/-!
# The refinement splice ((C2) effectivity, brick E4: the assembly)

**The effectivity theorem, from a covering family of flat pieces**: if every point of
the base curve `X_A` lies in an affine piece carrying a piece trivialization whose glued
comparison unit is `1` (a *flat* trivialization — produced from any covering family of
trivialized pieces by `Over.exists_flat_pieceTrivialization_of_le`), then the class
`L = mk 𝒩 γ.class` descends along the cover inclusion: `∃ M, cg^* M = L`.

The splice (worksheet decision D3, run in the constructive direction of the kernel
lemma's final assembly):

* on the overlap of two flat pieces, the two restricted trivializations differ by a
  glued unit `c` of the overlap piece (`Over.exists_ratio_unit`); both restrictions are
  still flat (`pieceComparisonUnit_res`), so the twist lemma forces the two coprojection
  pullbacks of `c` to the double piece to agree **on the nose**;
* faithfully flat descent of unit sections along `cg` (`Over.exists_unitsAppLE_eq`,
  brick D of the (C1) close) descends each `c` to a unit `m` of the overlap downstairs
  — the affine overlaps use separatedness of the curve product (`isAffineOpen_inf`);
* the descended units satisfy the Čech cocycle identity — their `cg`-pullbacks
  telescope through the trivializations, and `cg`-pullback is injective on sections
  (`appLE_whiskerLeft_injective`);
* `M` is the class of the resulting cocycle on the pointed cover by the pieces, and
  `cg^* M = L` holds by `mk`-calculus over the common refinement
  `(pieces pulled back) ⊓ 𝒩`, cobounded by the trivializations themselves.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]
variable (C : Over (Spec (.of k)))

set_option quotPrecheck false in
local notation "XA" => (C ⊗ overSpec k A).left
set_option quotPrecheck false in
local notation "XB" => (C ⊗ overSpec k B).left
set_option quotPrecheck false in
local notation "Xq" => (C ⊗ overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "u₁" => (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "u₂" => (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "cg" => (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "cgq" =>
  (C ◁ Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k)).left

namespace Over

/-- Cancellation core of the transition telescope: `a = b ⋅ c₁`, `b = d ⋅ c₂`,
`a = d ⋅ c₃` give `c₁ ⋅ c₂ = c₃`. -/
private lemma telescope_core {G : Type u} [CommGroup G] {a b d c₁ c₂ c₃ : G}
    (h₁ : a = b * c₁) (h₂ : b = d * c₂) (h₃ : a = d * c₃) : c₁ * c₂ = c₃ := by
  subst h₂
  rw [h₁, mul_assoc] at h₃
  rw [mul_comm]
  exact mul_left_cancel h₃

/-- Final-relation core: `t_x = t_y ⋅ c` and `t_y ⋅ γ = t_y'` give
`t_x⁻¹ ⋅ c = γ ⋅ (t_y')⁻¹`. -/
private lemma final_core {G : Type u} [CommGroup G] {tx ty ty' c γ : G}
    (h₁ : tx = ty * c) (h₂ : ty * γ = ty') : tx⁻¹ * c = γ * ty'⁻¹ := by
  subst h₁
  rw [← h₂, mul_inv, inv_mul_cancel_right, mul_inv, mul_comm ty⁻¹ γ⁻¹,
    mul_inv_cancel_left]

variable (σ : overSpec k A ⟶ C)
variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
variable [Module.FaithfullyFlat A B]

set_option maxHeartbeats 1600000 in
-- the concrete product towers exceed the default budget
omit [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom] in
/-- **The refinement splice** ((C2) effectivity, brick E4): given a covering family of
affine pieces with *flat* trivializations (comparison unit `1`), the represented class
descends along the cover inclusion `cg` on the curve product. -/
theorem exists_cechPic_map_whiskerLeft_eq_of_flat
    {𝒩 : (XB).PointedCover} {γ : (XB).unitsCocycle 𝒩}
    (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    (hcov : ∀ x : XA, ∃ (V : (XA).Opens) (_ : IsAffineOpen V), x ∈ V ∧
      ∃ T : PieceTrivialization C 𝒩 γ V, pieceComparisonUnit C σ W T = 1) :
    ∃ M : (XA).CechPic,
      Scheme.CechPic.map (cg) M = Scheme.CechPic.mk 𝒩 γ.class := by
  classical
  choose V hVaff hxV T hT using hcov
  -- ### the transition units on the overlap pieces, glued from the trivializations
  choose c hc using fun x y : XA =>
    exists_ratio_unit C ((T y).res C (inf_le_right : V x ⊓ V y ≤ V y))
      ((T x).res C (inf_le_left : V x ⊓ V y ≤ V x))
  -- restricted trivializations remain flat
  have hflat : ∀ (x : XA) {V' : (XA).Opens} (hle : V' ≤ V x),
      pieceComparisonUnit C σ W ((T x).res C hle) = 1 := by
    intro x V' hle
    rw [pieceComparisonUnit_res C σ W hle (T x), hT x, map_one]
  -- ### the two pullbacks of each transition unit agree on the double piece
  have hdesc : ∀ x y : XA, geomCoboundary C (c x y) = 1 := by
    intro x y
    have h := pieceComparisonUnit_eq_of_triv_eq C σ W
      ((T y).res C (inf_le_right : V x ⊓ V y ≤ V y))
      ((T x).res C (inf_le_left : V x ⊓ V y ≤ V x)) (c x y) (hc x y)
    rw [hflat x inf_le_left, hflat y inf_le_right, one_mul] at h
    exact h.symm
  -- ### descend the transition units along `cg`
  have hkey : ∀ x y : XA, ∃ s : Γ(XA, V x ⊓ V y)ˣ,
      (cg).unitsAppLE (V x ⊓ V y) ((cg) ⁻¹ᵁ (V x ⊓ V y)) le_rfl s = c x y := by
    intro x y
    refine Over.exists_unitsAppLE_eq (C := C) (isAffineOpen_inf C (hVaff x) (hVaff y))
      (c x y) ?_
    have h := hdesc x y
    rw [geomCoboundary_def, mul_inv_eq_one] at h
    exact h.symm
  choose m hm using hkey
  -- units-level injectivity of the `cg`-pullback over an open of the base curve
  have hinj : ∀ W' : (XA).Opens, Function.Injective
      ((cg).unitsAppLE W' ((cg) ⁻¹ᵁ W') le_rfl) := by
    intro W' a b hab
    exact Units.ext (appLE_whiskerLeft_injective (C := C) W'
      (congrArg Units.val hab))
  -- the `cg`-pullback of a descended transition unit, on any smaller cover open
  have hcgm : ∀ (x y : XA) (O : (XB).Opens) (hO : O ≤ (cg) ⁻¹ᵁ (V x ⊓ V y)),
      (cg).unitsAppLE (V x ⊓ V y) O hO (m x y)
        = (XB).unitsRestrict hO (c x y) := by
    intro x y O hO
    rw [← hm x y, Scheme.Hom.unitsAppLE_map]
  -- ### the cocycle identity for the descended transition units
  have hmcoc : ∀ x y z : XA,
      (XA).unitsRestrict (inf_le_left :
          V x ⊓ V y ⊓ V z ≤ V x ⊓ V y) (m x y)
        * (XA).unitsRestrict (inf_le_inf_right _ inf_le_right :
            V x ⊓ V y ⊓ V z ≤ V y ⊓ V z) (m y z)
      = (XA).unitsRestrict (inf_le_inf_right _ inf_le_left :
          V x ⊓ V y ⊓ V z ≤ V x ⊓ V z) (m x z) := by
    intro x y z
    apply hinj (V x ⊓ V y ⊓ V z)
    rw [map_mul]
    -- both sides in `c`-form on the cover piece
    have hf : ∀ (x' y' : XA) (h1 : V x ⊓ V y ⊓ V z ≤ V x' ⊓ V y'),
        (cg).unitsAppLE (V x ⊓ V y ⊓ V z) ((cg) ⁻¹ᵁ (V x ⊓ V y ⊓ V z)) le_rfl
          ((XA).unitsRestrict h1 (m x' y'))
        = (XB).unitsRestrict ((cg).preimage_mono h1) (c x' y') := by
      intro x' y' h1
      rw [Scheme.Hom.map_unitsAppLE, ← hm x' y', Scheme.Hom.unitsAppLE_map]
    rw [hf x y inf_le_left, hf y z (inf_le_inf_right _ inf_le_right),
      hf x z (inf_le_inf_right _ inf_le_left)]
    -- the telescope for the glued ratios, by the sheaf separation over the members
    refine Scheme.unitsRestrict_eq_of_locally_eq
      (W := fun b : XB => 𝒩.opens b ⊓ (cg) ⁻¹ᵁ (V x ⊓ V y ⊓ V z))
      (fun _ => inf_le_right)
      (fun v hv => Opens.mem_iSup.mpr ⟨v, ⟨𝒩.mem_opens v, hv⟩⟩) _ _ (fun b => ?_)
    simp only [map_mul, Scheme.unitsRestrict_unitsRestrict]
    -- the three ratio relations at the member `b`, restricted
    have hxy := congrArg ((XB).unitsRestrict (le_inf inf_le_left
        (inf_le_right.trans ((cg).preimage_mono inf_le_left)) :
        𝒩.opens b ⊓ (cg) ⁻¹ᵁ (V x ⊓ V y ⊓ V z)
          ≤ 𝒩.opens b ⊓ (cg) ⁻¹ᵁ (V x ⊓ V y))) (hc x y b)
    have hyz := congrArg ((XB).unitsRestrict (le_inf inf_le_left
        (inf_le_right.trans ((cg).preimage_mono (inf_le_inf_right _ inf_le_right))) :
        𝒩.opens b ⊓ (cg) ⁻¹ᵁ (V x ⊓ V y ⊓ V z)
          ≤ 𝒩.opens b ⊓ (cg) ⁻¹ᵁ (V y ⊓ V z))) (hc y z b)
    have hxz := congrArg ((XB).unitsRestrict (le_inf inf_le_left
        (inf_le_right.trans ((cg).preimage_mono (inf_le_inf_right _ inf_le_left))) :
        𝒩.opens b ⊓ (cg) ⁻¹ᵁ (V x ⊓ V y ⊓ V z)
          ≤ 𝒩.opens b ⊓ (cg) ⁻¹ᵁ (V x ⊓ V z))) (hc x z b)
    simp only [PieceTrivialization.res_triv, map_mul,
      Scheme.unitsRestrict_unitsRestrict] at hxy hyz hxz
    exact telescope_core hxy hyz hxz
  -- ### the pointed cover of the pieces and the descended cocycle
  set 𝒱 : (XA).PointedCover := ⟨fun x => V x, hxV⟩ with h𝒱
  set mcoc : (XA).unitsCocycle 𝒱 :=
    { ev := fun x y _ a b => (XA).unitsRestrict (le_inf a.le b.le) (m x y)
      ev_precomp := fun _ _ _ _ _ _ _ =>
        Scheme.unitsRestrict_unitsRestrict _ _ _
      ev_trans := fun x y z T' a b c' => by
        have h := congrArg ((XA).unitsRestrict
          (le_inf (le_inf a.le b.le) c'.le : T' ≤ V x ⊓ V y ⊓ V z)) (hmcoc x y z)
        rw [map_mul] at h
        simp only [Scheme.unitsRestrict_unitsRestrict] at h
        exact h } with hmcocdef
  refine ⟨Scheme.CechPic.mk 𝒱 mcoc.class, ?_⟩
  -- ### `cg^* M = L` over the common refinement, cobounded by the trivializations
  rw [Scheme.CechPic.map_mk, Scheme.Hom.pullbackUnitsH1_class]
  have h₁ : 𝒱.pullback (cg) ⊓ 𝒩 ≤ 𝒱.pullback (cg) := inf_le_left
  have h₂ : 𝒱.pullback (cg) ⊓ 𝒩 ≤ 𝒩 := inf_le_right
  refine Scheme.CechPic.mk_eq_mk_iff.mpr ⟨𝒱.pullback (cg) ⊓ 𝒩, h₁, h₂, ?_⟩
  refine OneCocycle.IsCohomologous.class_eq ?_
  set α : ∀ v : XB, Γ(XB, (𝒱.pullback (cg) ⊓ 𝒩).opens v)ˣ := fun v =>
    ((XB).unitsRestrict (le_inf inf_le_right inf_le_left :
        (𝒱.pullback (cg) ⊓ 𝒩).opens v
          ≤ 𝒩.opens v ⊓ (cg) ⁻¹ᵁ V ((cg).base v))
      ((T ((cg).base v)).triv v))⁻¹ with hα
  refine (OneCocycle.isCohomologous_iff_evInf _ _).mpr ⟨α, fun v v' => ?_⟩
  -- the pair value of the pulled-back cocycle on the refinement, in `c`-form
  have hOle : ∀ v v' : XB,
      (𝒱.pullback (cg) ⊓ 𝒩).opens v ⊓ (𝒱.pullback (cg) ⊓ 𝒩).opens v'
        ≤ (cg) ⁻¹ᵁ (V ((cg).base v) ⊓ V ((cg).base v')) := fun v v' =>
    (cg).le_preimage_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left)
  have e₁ : Scheme.unitsEvInf
      (((cg).pullbackUnitsCocycle mcoc).res fun p => homOfLE (h₁ p)) v v'
      = (XB).unitsRestrict (hOle v v') (c ((cg).base v) ((cg).base v')) := by
    rw [Scheme.res_unitsEvInf h₁ ((cg).pullbackUnitsCocycle mcoc) v v',
      Scheme.Hom.pullbackUnitsCocycle_unitsEvInf]
    have hev : Scheme.unitsEvInf mcoc ((cg).base v) ((cg).base v')
        = (XA).unitsRestrict (le_inf inf_le_left inf_le_right)
            (m ((cg).base v) ((cg).base v')) := rfl
    rw [hev, Scheme.Hom.map_unitsAppLE, Scheme.Hom.unitsAppLE_map,
      hcgm ((cg).base v) ((cg).base v') _ (hOle v v')]
  -- the pair value of the restricted representing cocycle
  have e₂ : Scheme.unitsEvInf (γ.res fun p => homOfLE (h₂ p)) v v'
      = (XB).unitsRestrict (inf_le_inf (h₂ v) (h₂ v'))
          (Scheme.unitsEvInf γ v v') :=
    Scheme.res_unitsEvInf h₂ γ v v'
  -- the transition value at the member `v`, restricted to the overlap
  have hcval := congrArg ((XB).unitsRestrict
    (le_inf (inf_le_left.trans inf_le_right) (hOle v v') :
      (𝒱.pullback (cg) ⊓ 𝒩).opens v ⊓ (𝒱.pullback (cg) ⊓ 𝒩).opens v'
        ≤ 𝒩.opens v ⊓ (cg) ⁻¹ᵁ (V ((cg).base v) ⊓ V ((cg).base v'))))
    (hc ((cg).base v) ((cg).base v') v)
  -- the trivializing relation of the `v'`-piece at the pair `(v, v')`
  have htriv := congrArg ((XB).unitsRestrict
    (le_inf (le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right))
      (inf_le_right.trans inf_le_left) :
      (𝒱.pullback (cg) ⊓ 𝒩).opens v ⊓ (𝒱.pullback (cg) ⊓ 𝒩).opens v'
        ≤ (𝒩.opens v ⊓ 𝒩.opens v') ⊓ (cg) ⁻¹ᵁ V ((cg).base v')))
    ((T ((cg).base v')).triv_rel v v')
  have key : (XB).unitsRestrict (inf_le_left :
        (𝒱.pullback (cg) ⊓ 𝒩).opens v ⊓ (𝒱.pullback (cg) ⊓ 𝒩).opens v'
          ≤ (𝒱.pullback (cg) ⊓ 𝒩).opens v) (α v)
      * Scheme.unitsEvInf
          (((cg).pullbackUnitsCocycle mcoc).res fun p => homOfLE (h₁ p)) v v'
    = Scheme.unitsEvInf (γ.res fun p => homOfLE (h₂ p)) v v'
      * (XB).unitsRestrict (inf_le_right) (α v') := by
    rw [e₁, e₂]
    simp only [hα, map_inv, Scheme.unitsRestrict_unitsRestrict]
    simp only [PieceTrivialization.res_triv, map_mul,
      Scheme.unitsRestrict_unitsRestrict] at hcval htriv
    exact final_core hcval htriv
  exact key

end Over

end AlgebraicGeometry
