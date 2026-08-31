/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EffectivityPieceDescent

/-!
# Twisting a piece trivialization by a global unit ((C2) effectivity, brick E4)

Two piece trivializations of the same representing cocycle on the same piece differ,
member by member, by the restrictions of a single global unit of the cover piece; this
file computes how the per-piece comparison unit and its descent data respond to such a
twist — the mechanism behind both the trivialization-independence of the descended
classes (brick E4 (B)) and the flattening of a trivialization along a coboundary
(brick E4 (C) preparation).

* `Over.PieceTrivialization.twist` — the trivialization with members multiplied by the
  restrictions of a global unit `e ∈ Γ(X_B, cg⁻¹ V)ˣ`.
* `Over.pieceComparisonUnit_eq_of_triv_eq` — **the twist lemma**: if `T'` and `T`
  differ by `e`, the glued comparison units differ by the geometric descent coboundary
  `u₂^♯ e ⋅ (u₁^♯ e)⁻¹` on the double piece.
* `Module.comparisonDescentUnit_coboundary` — the algebra seam: the descent-cocycle
  identification carries the base-changed coboundary of `β` to
  `Module.descentCoboundary` of `β`.
* `Over.map_pieceEquiv_geomCoboundary` — the geometric seam: the E0 identification
  carries the geometric coboundary of `e` to the base-changed coboundary of the
  identified unit — the master bridge at the two inclusions `descentIncl₁/₂`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace Module

open Algebra.TensorProduct

variable (A S B : Type u) [CommRing A] [CommRing S] [CommRing B] [Algebra A S]
  [Algebra A B]

/-! ## The algebra seam: the identification carries coboundaries to coboundaries -/

/-- The descent-cocycle identification on a left pure tensor is the base-changed
first inclusion. -/
lemma pieceDescentEquiv_tmul_one' (x : S ⊗[A] B) :
    pieceDescentEquiv A S B (x ⊗ₜ[S] 1)
      = Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentIncl₁ A B) x := by
  induction x with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul s b =>
    rw [show (1 : S ⊗[A] B) = (1 : S) ⊗ₜ[A] (1 : B) from rfl, pieceDescentEquiv_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, one_mul]
    rfl

/-- The descent-cocycle identification on a right pure tensor is the base-changed
second inclusion. -/
lemma pieceDescentEquiv_one_tmul' (x : S ⊗[A] B) :
    pieceDescentEquiv A S B ((1 : S ⊗[A] B) ⊗ₜ[S] x)
      = Algebra.TensorProduct.map (AlgHom.id S S) (Module.descentIncl₂ A B) x := by
  induction x with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul s b =>
    rw [show (1 : S ⊗[A] B) = (1 : S) ⊗ₜ[A] (1 : B) from rfl, pieceDescentEquiv_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, mul_one]
    rfl

/-- **The algebra seam**: the per-piece descent unit of the base-changed coboundary of
`β` is the descent coboundary of `β` over the piece ring. -/
theorem comparisonDescentUnit_coboundary (β : (S ⊗[A] B)ˣ) :
    Module.comparisonDescentUnit A S B
        (Units.map (Algebra.TensorProduct.map (AlgHom.id S S)
            (Module.descentIncl₂ A B)).toRingHom.toMonoidHom β
          * (Units.map (Algebra.TensorProduct.map (AlgHom.id S S)
              (Module.descentIncl₁ A B)).toRingHom.toMonoidHom β)⁻¹)
      = Module.descentCoboundary S (S ⊗[A] B) β := by
  refine Units.ext ?_
  apply (pieceDescentEquiv A S B).injective
  rw [pieceDescentEquiv_comparisonDescentUnit_val, Module.descentCoboundary_val,
    map_mul, pieceDescentEquiv_one_tmul', pieceDescentEquiv_tmul_one']
  rfl

end Module

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

/-- Multiplication core of the twist relation: `a ⋅ γ = b` gives `(a ⋅ c) ⋅ γ = b ⋅ c`. -/
private lemma twist_rel_core {G : Type u} [CommGroup G] {a b c γ : G}
    (h : a * γ = b) : a * c * γ = b * c := by
  rw [mul_right_comm, h]

/-- **The twist of a piece trivialization by a global unit of the cover piece**: each
member is multiplied by the restriction of `e ∈ Γ(X_B, cg⁻¹ V)ˣ`. -/
noncomputable def PieceTrivialization.twist {𝒩 : (XB).PointedCover}
    {γ : (XB).unitsCocycle 𝒩} {V : (XA).Opens} (T : PieceTrivialization C 𝒩 γ V)
    (e : Γ(XB, (cg) ⁻¹ᵁ V)ˣ) : PieceTrivialization C 𝒩 γ V where
  triv b := T.triv b * (XB).unitsRestrict (inf_le_right : 𝒩.opens b ⊓ (cg) ⁻¹ᵁ V ≤ _) e
  triv_rel b b' := by
    have h := T.triv_rel b b'
    simp only [map_mul, Scheme.unitsRestrict_unitsRestrict]
    exact twist_rel_core h

@[simp]
lemma PieceTrivialization.twist_triv {𝒩 : (XB).PointedCover}
    {γ : (XB).unitsCocycle 𝒩} {V : (XA).Opens} (T : PieceTrivialization C 𝒩 γ V)
    (e : Γ(XB, (cg) ⁻¹ᵁ V)ˣ) (b : XB) :
    (T.twist C e).triv b
      = T.triv b * (XB).unitsRestrict (inf_le_right : 𝒩.opens b ⊓ (cg) ⁻¹ᵁ V ≤ _) e :=
  rfl

variable (σ : overSpec k A ⟶ C)

/-- The geometric descent coboundary of a global unit of the cover piece: the ratio of
its two coprojection pullbacks on the double piece. -/
noncomputable def geomCoboundary {V : (XA).Opens} (e : Γ(XB, (cg) ⁻¹ᵁ V)ˣ) :
    Γ(Xq, (cgq) ⁻¹ᵁ V)ˣ :=
  (u₂).unitsAppLE ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V) (cgqPreimage_le_inr C V) e
    * ((u₁).unitsAppLE ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V) (cgqPreimage_le_inl C V) e)⁻¹

lemma geomCoboundary_def {V : (XA).Opens} (e : Γ(XB, (cg) ⁻¹ᵁ V)ˣ) :
    geomCoboundary C e
      = (u₂).unitsAppLE ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V) (cgqPreimage_le_inr C V) e
        * ((u₁).unitsAppLE ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V) (cgqPreimage_le_inl C V) e)⁻¹ :=
  rfl

/-- The geometric coboundary of an inverse is the inverse of the coboundary. -/
lemma geomCoboundary_inv {V : (XA).Opens} (e : Γ(XB, (cg) ⁻¹ᵁ V)ˣ) :
    geomCoboundary C e⁻¹ = (geomCoboundary C e)⁻¹ := by
  rw [geomCoboundary_def, geomCoboundary_def, map_inv, map_inv, mul_inv, inv_inv]

/-- Abelian core of the twist computation for the glued comparison unit. -/
private lemma twist_glued_core {G : Type u} [CommGroup G] {θ t₂ t₁ e₂ e₁ : G} :
    θ * (t₂ * e₂) * (t₁ * e₁)⁻¹ = θ * t₂ * t₁⁻¹ * (e₂ * e₁⁻¹) := by
  rw [mul_inv]
  ac_rfl

/-- **The twist lemma**: if two piece trivializations differ, member by member, by the
restrictions of a global unit `e` of the cover piece, their glued comparison units
differ by the geometric descent coboundary of `e`. -/
theorem pieceComparisonUnit_eq_of_triv_eq {𝒩 : (XB).PointedCover}
    {γ : (XB).unitsCocycle 𝒩} (W : NormalizedCechComparison k A B C σ 𝒩 γ)
    {V : (XA).Opens} (T T' : PieceTrivialization C 𝒩 γ V) (e : Γ(XB, (cg) ⁻¹ᵁ V)ˣ)
    (h : ∀ b : XB, T'.triv b
      = T.triv b * (XB).unitsRestrict (inf_le_right : 𝒩.opens b ⊓ (cg) ⁻¹ᵁ V ≤ _) e) :
    pieceComparisonUnit C σ W T' = pieceComparisonUnit C σ W T * geomCoboundary C e := by
  refine (pieceComparisonUnit_unique C σ W T' _ fun x => ?_).symm
  rw [map_mul, pieceComparisonUnit_spec C σ W T x, unitsTrivTwistCochain_def,
    unitsTrivTwistCochain_def, h ((u₂).base x), h ((u₁).base x)]
  simp only [map_mul, map_inv, geomCoboundary_def,
    Scheme.Hom.map_unitsAppLE, Scheme.Hom.unitsAppLE_map]
  exact (twist_glued_core).symm

/-! ## The geometric seam: the identification carries the coboundary -/

-- The base-piece `A`-algebra structure and the cover-piece `Γ(V)`-algebra structure.
attribute [local instance] Over.sectionsAlgebraA Over.pieceCoverAlgebra

/-- The whiskered map of the first inclusion is the first coprojection. -/
lemma whiskerLeft_descentIncl₁ :
    (C ◁ Over.overSpecMap ((Module.descentIncl₁ A B).restrictScalars k)).left = (u₁) := by
  have h : (Module.descentIncl₁ A B).restrictScalars k = tensorInl (A := A) (B := B) :=
    AlgHom.ext fun _ => rfl
  rw [h]

/-- The whiskered map of the second inclusion is the second coprojection. -/
lemma whiskerLeft_descentIncl₂ :
    (C ◁ Over.overSpecMap ((Module.descentIncl₂ A B).restrictScalars k)).left = (u₂) := by
  have h : (Module.descentIncl₂ A B).restrictScalars k = tensorInr (A := A) (B := B) :=
    AlgHom.ext fun _ => rfl
  rw [h]

/-- **The geometric seam**: through the E0 identifications, the geometric descent
coboundary of `e` is carried to the base-changed descent coboundary of the identified
unit — the master bridge at the two inclusions. -/
theorem map_pieceEquiv_geomCoboundary {V : (XA).Opens} (hV : IsAffineOpen V)
    (e : Γ(XB, (cg) ⁻¹ᵁ V)ˣ) :
    Units.map (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C
        hV).toAlgHom.toRingHom.toMonoidHom (geomCoboundary C e)
      = Units.map (Algebra.TensorProduct.map (AlgHom.id Γ(XA, V) Γ(XA, V))
            (Module.descentIncl₂ A B)).toRingHom.toMonoidHom
          (Units.map (Over.pieceEquiv (A := A) (B := B) C
            hV).toAlgHom.toRingHom.toMonoidHom e)
        * (Units.map (Algebra.TensorProduct.map (AlgHom.id Γ(XA, V) Γ(XA, V))
              (Module.descentIncl₁ A B)).toRingHom.toMonoidHom
            (Units.map (Over.pieceEquiv (A := A) (B := B) C
              hV).toAlgHom.toRingHom.toMonoidHom e))⁻¹ := by
  have h₂ : Units.map (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C
        hV).toAlgHom.toRingHom.toMonoidHom
        ((u₂).unitsAppLE ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V) (cgqPreimage_le_inr C V) e)
      = Units.map (Algebra.TensorProduct.map (AlgHom.id Γ(XA, V) Γ(XA, V))
            (Module.descentIncl₂ A B)).toRingHom.toMonoidHom
          (Units.map (Over.pieceEquiv (A := A) (B := B) C
            hV).toAlgHom.toRingHom.toMonoidHom e) := by
    refine Units.ext ?_
    change Over.pieceEquiv (A := A) (B := B ⊗[A] B) C hV
        (((u₂).unitsAppLE ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V) (cgqPreimage_le_inr C V) e).val)
      = Algebra.TensorProduct.map (AlgHom.id Γ(XA, V) Γ(XA, V)) (Module.descentIncl₂ A B)
          (Over.pieceEquiv (A := A) (B := B) C hV e.val)
    rw [Over.map_pieceEquiv_eq_pieceEquiv_whiskerLeft C (Module.descentIncl₂ A B) hV,
      Scheme.Hom.coe_unitsAppLE]
    exact (congrArg (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C hV)
      (Scheme.Hom.appLE_apply_congr_hom (whiskerLeft_descentIncl₂ C) _ _ e.val)).symm
  have h₁ : Units.map (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C
        hV).toAlgHom.toRingHom.toMonoidHom
        ((u₁).unitsAppLE ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V) (cgqPreimage_le_inl C V) e)
      = Units.map (Algebra.TensorProduct.map (AlgHom.id Γ(XA, V) Γ(XA, V))
            (Module.descentIncl₁ A B)).toRingHom.toMonoidHom
          (Units.map (Over.pieceEquiv (A := A) (B := B) C
            hV).toAlgHom.toRingHom.toMonoidHom e) := by
    refine Units.ext ?_
    change Over.pieceEquiv (A := A) (B := B ⊗[A] B) C hV
        (((u₁).unitsAppLE ((cg) ⁻¹ᵁ V) ((cgq) ⁻¹ᵁ V) (cgqPreimage_le_inl C V) e).val)
      = Algebra.TensorProduct.map (AlgHom.id Γ(XA, V) Γ(XA, V)) (Module.descentIncl₁ A B)
          (Over.pieceEquiv (A := A) (B := B) C hV e.val)
    rw [Over.map_pieceEquiv_eq_pieceEquiv_whiskerLeft C (Module.descentIncl₁ A B) hV,
      Scheme.Hom.coe_unitsAppLE]
    exact (congrArg (Over.pieceEquiv (A := A) (B := B ⊗[A] B) C hV)
      (Scheme.Hom.appLE_apply_congr_hom (whiskerLeft_descentIncl₁ C) _ _ e.val)).symm
  rw [geomCoboundary_def, map_mul, map_inv, h₁, h₂]

end Over

end AlgebraicGeometry
