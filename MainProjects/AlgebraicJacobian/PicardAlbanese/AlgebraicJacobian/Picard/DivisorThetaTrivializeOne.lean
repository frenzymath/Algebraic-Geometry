/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorThetaTrivializeZero

/-!
# DD-4 (Task 4, right exactness) — trivialization into the glued `𝒪(Θᵃ − d)`, chart 1

The chart-1 mirror of `AlgebraicJacobian.Picard.DivisorThetaTrivializeZero`: a section
`β` over `W ≤ V₁` vanishing along the divisor family `d` germwise divides into a glued
section of the theta-ideal sheaf (`DivisorAdaptation.idealToGlued₁`) — on chart-1 pieces
the cofactor `β/f_j`, on chart-0 pieces the factor `θᵃ` (the section `β` is read in the
chart-1 picture of the Θ-twisted pair, and the chart-0 picture is `θᵃ·β`).  The
characterizing equation is `eqn_mul_idealToGlued₁_inr`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R]
  [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} {A : DivisorAdaptation C R π d} {a : ℕ}

variable (A a) in
/-- **Trivialization over the chart `V₁`**: a section `β` over `W ≤ V₁` vanishing along
`d` germwise divides into a glued section of `𝒪(Θᵃ − d)` — on chart-1 pieces the
cofactor `β/f_j`, on chart-0 pieces `θᵃ·(β/f_i)` (the chart-1 picture of `β`). -/
noncomputable def idealToGlued₁ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z) :
    A.ThetaIdealSections a W :=
  ⟨fun p =>
    match p with
    | Sum.inl i =>
        (relCurve C R).resHom
            (le_inf (inf_le_right.trans (A.pieces_inl_le i.down))
              (inf_le_left.trans hW) :
              W ⊓ A.pieces (Sum.inl i.down) ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)
            ((relThetaCocycle C R π a :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁))
          * A.idealDiv (Sum.inl i.down) β hβ
    | Sum.inr j => A.idealDiv (Sum.inr j.down) β hβ, by
    intro p q
    rcases p with i | i <;> rcases q with q | q
    · -- (inl, inl)
      have h1 := eqn_mul_idealDiv_res (A := A) (Sum.inl i.down) β hβ
        (inf_le_left.trans inf_le_left :
          W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inl q.down) ≤ W)
        (inf_le_left.trans inf_le_right)
      have h2 := eqn_mul_idealDiv_res (A := A) (Sum.inl q.down) β hβ
        (inf_le_left.trans inf_le_left :
          W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inl q.down) ≤ W)
        inf_le_right
      have hratio := congrArg ((relCurve C R).resHom
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inl q.down)
            ≤ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inl q.down)))
        (A.eqn_mul_eqnRatio (Sum.inl i.down) (Sum.inl q.down))
      rw [map_mul] at hratio
      simp only [Scheme.resHom_resHom] at hratio
      have key : (relCurve C R).resHom
          (inf_le_left : W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inl q.down)
            ≤ W ⊓ A.pieces (Sum.inl i.down))
          ((relCurve C R).resHom
              (le_inf (inf_le_right.trans (A.pieces_inl_le i.down))
                (inf_le_left.trans hW))
              ((relThetaCocycle C R π a :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁))
            * A.idealDiv (Sum.inl i.down) β hβ)
          = (relCurve C R).resHom
              (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
                W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inl q.down)
                  ≤ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inl q.down))
              (((A.eqnRatio (Sum.inl i.down) (Sum.inl q.down) :
                Γ(relCurve C R, A.pieces (Sum.inl i.down) ⊓
                  A.pieces (Sum.inl q.down))ˣ) :
                Γ(relCurve C R, A.pieces (Sum.inl i.down) ⊓
                  A.pieces (Sum.inl q.down))) * 1)
            * (relCurve C R).resHom
                (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
                  W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inl q.down)
                    ≤ W ⊓ A.pieces (Sum.inl q.down))
                ((relCurve C R).resHom
                    (le_inf (inf_le_right.trans (A.pieces_inl_le q.down))
                      (inf_le_left.trans hW))
                    ((relThetaCocycle C R π a :
                      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                        (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                        (relCover C R (fiberTwoCover π)).V₁))
                  * A.idealDiv (Sum.inl q.down) β hβ) := by
        rw [mul_one, map_mul, map_mul]
        simp only [Scheme.resHom_resHom]
        refine A.eqn_res_cancel (Sum.inl i.down)
          (inf_le_left.trans inf_le_right :
            W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inl q.down)
              ≤ A.pieces (Sum.inl i.down)) ?_
        linear_combination (relCurve C R).resHom
            (le_inf ((inf_le_left.trans inf_le_right).trans (A.pieces_inl_le i.down))
              ((inf_le_left.trans inf_le_left).trans hW) :
              W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inl q.down)
                ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)
            ((relThetaCocycle C R π a :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)) * (h1 - h2)
          - (relCurve C R).resHom
              (le_inf ((inf_le_left.trans inf_le_right).trans (A.pieces_inl_le i.down))
                ((inf_le_left.trans inf_le_left).trans hW))
              ((relThetaCocycle C R π a :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁))
            * (relCurve C R).resHom
                (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
                (A.idealDiv (Sum.inl q.down) β hβ) * hratio
      exact key
    · -- (inl, inr)
      have h1 := eqn_mul_idealDiv_res (A := A) (Sum.inl i.down) β hβ
        (inf_le_left.trans inf_le_left :
          W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down) ≤ W)
        (inf_le_left.trans inf_le_right)
      have h2 := eqn_mul_idealDiv_res (A := A) (Sum.inr q.down) β hβ
        (inf_le_left.trans inf_le_left :
          W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down) ≤ W)
        inf_le_right
      have hratio := congrArg ((relCurve C R).resHom
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down)
            ≤ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down)))
        (A.eqn_mul_eqnRatio (Sum.inl i.down) (Sum.inr q.down))
      rw [map_mul] at hratio
      simp only [Scheme.resHom_resHom] at hratio
      have key : (relCurve C R).resHom
          (inf_le_left : W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down)
            ≤ W ⊓ A.pieces (Sum.inl i.down))
          ((relCurve C R).resHom
              (le_inf (inf_le_right.trans (A.pieces_inl_le i.down))
                (inf_le_left.trans hW))
              ((relThetaCocycle C R π a :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁))
            * A.idealDiv (Sum.inl i.down) β hβ)
          = (relCurve C R).resHom
              (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
                W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down)
                  ≤ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down))
              (((A.eqnRatio (Sum.inl i.down) (Sum.inr q.down) :
                Γ(relCurve C R, A.pieces (Sum.inl i.down) ⊓
                  A.pieces (Sum.inr q.down))ˣ) :
                Γ(relCurve C R, A.pieces (Sum.inl i.down) ⊓
                  A.pieces (Sum.inr q.down)))
                * (relCurve C R).resHom
                    (inf_le_inf (A.pieces_inl_le i.down) (A.pieces_inr_le q.down))
                    ((relThetaCocycle C R π a :
                      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                        (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                        (relCover C R (fiberTwoCover π)).V₁)))
            * (relCurve C R).resHom
                (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
                  W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down)
                    ≤ W ⊓ A.pieces (Sum.inr q.down))
                (A.idealDiv (Sum.inr q.down) β hβ) := by
        rw [map_mul, map_mul]
        simp only [Scheme.resHom_resHom]
        refine A.eqn_res_cancel (Sum.inl i.down)
          (inf_le_left.trans inf_le_right :
            W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down)
              ≤ A.pieces (Sum.inl i.down)) ?_
        linear_combination (relCurve C R).resHom
            (le_inf ((inf_le_left.trans inf_le_right).trans (A.pieces_inl_le i.down))
              ((inf_le_left.trans inf_le_left).trans hW) :
              W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down)
                ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)
            ((relThetaCocycle C R π a :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)) * (h1 - h2)
          - (relCurve C R).resHom
              (le_inf ((inf_le_left.trans inf_le_right).trans (A.pieces_inl_le i.down))
                ((inf_le_left.trans inf_le_left).trans hW))
              ((relThetaCocycle C R π a :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁))
            * (relCurve C R).resHom
                (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
                (A.idealDiv (Sum.inr q.down) β hβ) * hratio
      exact key
    · -- (inr, inl)
      have h1 := eqn_mul_idealDiv_res (A := A) (Sum.inr i.down) β hβ
        (inf_le_left.trans inf_le_left :
          W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down) ≤ W)
        (inf_le_left.trans inf_le_right)
      have h2 := eqn_mul_idealDiv_res (A := A) (Sum.inl q.down) β hβ
        (inf_le_left.trans inf_le_left :
          W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down) ≤ W)
        inf_le_right
      have hratio := congrArg ((relCurve C R).resHom
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down)
            ≤ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down)))
        (A.eqn_mul_eqnRatio (Sum.inr i.down) (Sum.inl q.down))
      rw [map_mul] at hratio
      simp only [Scheme.resHom_resHom] at hratio
      have hθ : (relCurve C R).resHom
          (le_inf (inf_le_right.trans (A.pieces_inl_le q.down))
            ((inf_le_left.trans inf_le_left).trans hW) :
            W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down)
              ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)
          (((relThetaCocycle C R π a)⁻¹ :
            Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
              (relCover C R (fiberTwoCover π)).V₁)ˣ) :
            Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
              (relCover C R (fiberTwoCover π)).V₁))
          * (relCurve C R).resHom
            (le_inf (inf_le_right.trans (A.pieces_inl_le q.down))
              ((inf_le_left.trans inf_le_left).trans hW))
            ((relThetaCocycle C R π a :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      have key : (relCurve C R).resHom
          (inf_le_left : W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down)
            ≤ W ⊓ A.pieces (Sum.inr i.down)) (A.idealDiv (Sum.inr i.down) β hβ)
          = (relCurve C R).resHom
              (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
                W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down)
                  ≤ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down))
              (((A.eqnRatio (Sum.inr i.down) (Sum.inl q.down) :
                Γ(relCurve C R, A.pieces (Sum.inr i.down) ⊓
                  A.pieces (Sum.inl q.down))ˣ) :
                Γ(relCurve C R, A.pieces (Sum.inr i.down) ⊓
                  A.pieces (Sum.inl q.down)))
                * (relCurve C R).resHom
                    (le_inf (inf_le_right.trans (A.pieces_inl_le q.down))
                      (inf_le_left.trans (A.pieces_inr_le i.down)))
                    (((relThetaCocycle C R π a)⁻¹ :
                      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                        (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                        (relCover C R (fiberTwoCover π)).V₁)))
            * (relCurve C R).resHom
                (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
                  W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down)
                    ≤ W ⊓ A.pieces (Sum.inl q.down))
                ((relCurve C R).resHom
                    (le_inf (inf_le_right.trans (A.pieces_inl_le q.down))
                      (inf_le_left.trans hW))
                    ((relThetaCocycle C R π a :
                      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                        (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                        (relCover C R (fiberTwoCover π)).V₁))
                  * A.idealDiv (Sum.inl q.down) β hβ) := by
        rw [map_mul, map_mul]
        simp only [Scheme.resHom_resHom]
        refine A.eqn_res_cancel (Sum.inr i.down)
          (inf_le_left.trans inf_le_right :
            W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down)
              ≤ A.pieces (Sum.inr i.down)) ?_
        linear_combination h1 - h2
          - (relCurve C R).resHom
              (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
              (A.idealDiv (Sum.inl q.down) β hβ) * hratio
          - (relCurve C R).resHom (inf_le_left.trans inf_le_right)
              (A.eqn (Sum.inr i.down))
            * (relCurve C R).resHom
                (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
                (((A.eqnRatio (Sum.inr i.down) (Sum.inl q.down) :
                  Γ(relCurve C R, A.pieces (Sum.inr i.down) ⊓
                    A.pieces (Sum.inl q.down))ˣ) :
                  Γ(relCurve C R, A.pieces (Sum.inr i.down) ⊓
                    A.pieces (Sum.inl q.down))))
            * (relCurve C R).resHom
                (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
                (A.idealDiv (Sum.inl q.down) β hβ) * hθ
      exact key
    · -- (inr, inr)
      have h1 := eqn_mul_idealDiv_res (A := A) (Sum.inr i.down) β hβ
        (inf_le_left.trans inf_le_left :
          W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inr q.down) ≤ W)
        (inf_le_left.trans inf_le_right)
      have h2 := eqn_mul_idealDiv_res (A := A) (Sum.inr q.down) β hβ
        (inf_le_left.trans inf_le_left :
          W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inr q.down) ≤ W)
        inf_le_right
      have hratio := congrArg ((relCurve C R).resHom
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inr q.down)
            ≤ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inr q.down)))
        (A.eqn_mul_eqnRatio (Sum.inr i.down) (Sum.inr q.down))
      rw [map_mul] at hratio
      simp only [Scheme.resHom_resHom] at hratio
      have key : (relCurve C R).resHom
          (inf_le_left : W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inr q.down)
            ≤ W ⊓ A.pieces (Sum.inr i.down)) (A.idealDiv (Sum.inr i.down) β hβ)
          = (relCurve C R).resHom
              (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
                W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inr q.down)
                  ≤ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inr q.down))
              (((A.eqnRatio (Sum.inr i.down) (Sum.inr q.down) :
                Γ(relCurve C R, A.pieces (Sum.inr i.down) ⊓
                  A.pieces (Sum.inr q.down))ˣ) :
                Γ(relCurve C R, A.pieces (Sum.inr i.down) ⊓
                  A.pieces (Sum.inr q.down))) * 1)
            * (relCurve C R).resHom
                (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
                  W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inr q.down)
                    ≤ W ⊓ A.pieces (Sum.inr q.down))
                (A.idealDiv (Sum.inr q.down) β hβ) := by
        rw [mul_one]
        refine A.eqn_res_cancel (Sum.inr i.down)
          (inf_le_left.trans inf_le_right :
            W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inr q.down)
              ≤ A.pieces (Sum.inr i.down)) ?_
        linear_combination h1 - h2
          - (relCurve C R).resHom
              (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
              (A.idealDiv (Sum.inr q.down) β hβ) * hratio
      exact key⟩

/-- The chart-1 component of the trivialization over `V₁` is the division by the
equation. -/
lemma idealToGlued₁_comp_inr {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z) (j : Fin A.m₁) :
    ((idealToGlued₁ A a hW β hβ).val (Sum.inr (ULift.up j)) :
        Γ(relCurve C R, W ⊓ A.pieces (Sum.inr j)))
      = A.idealDiv (Sum.inr j) β hβ := rfl

/-- The chart-1 characterizing equation of the trivialization:
`f_j · (idealToGlued₁ β)_j = β` on any open below `W ⊓ D(h_j)`. -/
lemma eqn_mul_idealToGlued₁_inr {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z) (j : Fin A.m₁)
    {O : (relCurve C R).Opens} (hOW : O ≤ W) (hOj : O ≤ A.pieces (Sum.inr j)) :
    (relCurve C R).resHom hOj (A.eqn (Sum.inr j))
        * (relCurve C R).resHom (le_inf hOW hOj)
            ((idealToGlued₁ A a hW β hβ).val (Sum.inr (ULift.up j)))
      = (relCurve C R).resHom hOW β :=
  eqn_mul_idealDiv_res (A := A) (Sum.inr j) β hβ hOW hOj

end DivisorAdaptation

end AlgebraicGeometry
