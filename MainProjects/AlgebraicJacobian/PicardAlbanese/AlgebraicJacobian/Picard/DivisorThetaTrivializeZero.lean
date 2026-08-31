/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorThetaBridge

/-!
# DD-4 (Task 4, right exactness) — trivialization into the glued `𝒪(Θᵃ − d)`, chart 0

The chart-0-oriented trivialization bridge: a section `β` over `W ≤ V₀` vanishing along
the divisor family `d` germwise divides by the adaptation equations into a glued section
of the theta-ideal sheaf (`DivisorAdaptation.idealToGlued₀`).  On chart-0 pieces the
component is the cofactor `β/f_i` (`DivisorAdaptation.idealDiv`); on chart-1 pieces it
carries the factor `θ^{-a}` — the section `β` is read in the chart-0 picture of the
Θ-twisted pair.  The characterizing equation is `eqn_mul_idealToGlued₀_inl`
(`f_i · (idealToGlued₀ β)_i = β`); each matching case is proved by cancellation against
the regular equation (`eqn_res_cancel`) after normalizing the transition unit.

The chart-1 mirror is `AlgebraicJacobian.Picard.DivisorThetaTrivializeOne`.
-/

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

/-! ## Trivialization: from ideal sections to glued sections -/

variable (A) in
/-- A section vanishing along `d` germwise restricts to a section vanishing along `d`
germwise on the part of a piece inside its home. -/
lemma res_germ_mem (i : A.index) {W : (relCurve C R).Opens}
    (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z) :
    ∀ (z : relCurve C R) (hz : z ∈ W ⊓ A.pieces i),
      ((relCurve C R).presheaf.germ (W ⊓ A.pieces i) z hz).hom
        ((relCurve C R).resHom (inf_le_left : W ⊓ A.pieces i ≤ W) β)
        ∈ d.stalkIdeal z := by
  intro z hz
  have hswap : ((relCurve C R).presheaf.germ (W ⊓ A.pieces i) z hz).hom
      ((relCurve C R).resHom (inf_le_left : W ⊓ A.pieces i ≤ W) β)
      = ((relCurve C R).presheaf.germ W z hz.1).hom β :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [hswap]
  exact hβ z hz.1

variable (A) in
/-- The division of a section vanishing along `d` by the equation of a piece, on the
part of the piece inside `W`. -/
noncomputable def idealDiv (i : A.index) {W : (relCurve C R).Opens}
    (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z) :
    Γ(relCurve C R, W ⊓ A.pieces i) :=
  A.eqnDiv i inf_le_right ((relCurve C R).resHom inf_le_left β)
    (res_germ_mem A i β hβ)

/-- The defining equation of the division, restricted to any open below the piece part:
`f_i · (β/f_i) = β` on `O`. -/
lemma eqn_mul_idealDiv_res (i : A.index) {W : (relCurve C R).Opens}
    (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z)
    {O : (relCurve C R).Opens} (hOW : O ≤ W) (hOi : O ≤ A.pieces i) :
    (relCurve C R).resHom hOi (A.eqn i)
        * (relCurve C R).resHom (le_inf hOW hOi) (A.idealDiv i β hβ)
      = (relCurve C R).resHom hOW β := by
  have key := congrArg ((relCurve C R).resHom
    (le_inf hOW hOi : O ≤ W ⊓ A.pieces i))
    (A.eqn_mul_eqnDiv i inf_le_right ((relCurve C R).resHom inf_le_left β)
      (res_germ_mem A i β hβ))
  rw [map_mul] at key
  simp only [Scheme.resHom_resHom] at key
  exact key

variable (A a) in
/-- **Trivialization over the chart `V₀`**: a section `β` over `W ≤ V₀` vanishing along
`d` germwise divides into a glued section of `𝒪(Θᵃ − d)` — on chart-0 pieces the
cofactor `β/f_i`, on chart-1 pieces `θ^{-a}·(β/f_j)` (the chart-0 picture of `β`). -/
noncomputable def idealToGlued₀ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z) :
    A.ThetaIdealSections a W :=
  ⟨fun p =>
    match p with
    | Sum.inl i => A.idealDiv (Sum.inl i.down) β hβ
    | Sum.inr j =>
        (relCurve C R).resHom
            (le_inf (inf_le_left.trans hW)
              (inf_le_right.trans (A.pieces_inr_le j.down)) :
              W ⊓ A.pieces (Sum.inr j.down) ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)
            (((relThetaCocycle C R π a)⁻¹ :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁))
          * A.idealDiv (Sum.inr j.down) β hβ, by
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
            ≤ W ⊓ A.pieces (Sum.inl i.down)) (A.idealDiv (Sum.inl i.down) β hβ)
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
                (A.idealDiv (Sum.inl q.down) β hβ) := by
        rw [mul_one]
        refine A.eqn_res_cancel (Sum.inl i.down)
          (inf_le_left.trans inf_le_right :
            W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inl q.down)
              ≤ A.pieces (Sum.inl i.down)) ?_
        linear_combination h1 - h2
          - (relCurve C R).resHom
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
      have hθ : (relCurve C R).resHom
          (le_inf ((inf_le_left.trans inf_le_left).trans hW)
            (inf_le_right.trans (A.pieces_inr_le q.down)) :
            W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down)
              ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)
          ((relThetaCocycle C R π a :
            Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
              (relCover C R (fiberTwoCover π)).V₁)ˣ) :
            Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
              (relCover C R (fiberTwoCover π)).V₁))
          * (relCurve C R).resHom
            (le_inf ((inf_le_left.trans inf_le_left).trans hW)
              (inf_le_right.trans (A.pieces_inr_le q.down)))
            (((relThetaCocycle C R π a)⁻¹ :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      have key : (relCurve C R).resHom
          (inf_le_left : W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down)
            ≤ W ⊓ A.pieces (Sum.inl i.down)) (A.idealDiv (Sum.inl i.down) β hβ)
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
                ((relCurve C R).resHom
                    (le_inf (inf_le_left.trans hW)
                      (inf_le_right.trans (A.pieces_inr_le q.down)))
                    (((relThetaCocycle C R π a)⁻¹ :
                      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                        (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                        (relCover C R (fiberTwoCover π)).V₁))
                  * A.idealDiv (Sum.inr q.down) β hβ) := by
        rw [map_mul, map_mul]
        simp only [Scheme.resHom_resHom]
        refine A.eqn_res_cancel (Sum.inl i.down)
          (inf_le_left.trans inf_le_right :
            W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr q.down)
              ≤ A.pieces (Sum.inl i.down)) ?_
        linear_combination h1 - h2
          - (relCurve C R).resHom
              (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
              (A.idealDiv (Sum.inr q.down) β hβ) * hratio
          - (relCurve C R).resHom (inf_le_left.trans inf_le_right)
              (A.eqn (Sum.inl i.down))
            * (relCurve C R).resHom
                (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
                (((A.eqnRatio (Sum.inl i.down) (Sum.inr q.down) :
                  Γ(relCurve C R, A.pieces (Sum.inl i.down) ⊓
                    A.pieces (Sum.inr q.down))ˣ) :
                  Γ(relCurve C R, A.pieces (Sum.inl i.down) ⊓
                    A.pieces (Sum.inr q.down))))
            * (relCurve C R).resHom
                (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
                (A.idealDiv (Sum.inr q.down) β hβ) * hθ
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
      have key : (relCurve C R).resHom
          (inf_le_left : W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down)
            ≤ W ⊓ A.pieces (Sum.inr i.down))
          ((relCurve C R).resHom
              (le_inf (inf_le_left.trans hW)
                (inf_le_right.trans (A.pieces_inr_le i.down)))
              (((relThetaCocycle C R π a)⁻¹ :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁))
            * A.idealDiv (Sum.inr i.down) β hβ)
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
                (A.idealDiv (Sum.inl q.down) β hβ) := by
        rw [map_mul, map_mul]
        simp only [Scheme.resHom_resHom]
        refine A.eqn_res_cancel (Sum.inr i.down)
          (inf_le_left.trans inf_le_right :
            W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down)
              ≤ A.pieces (Sum.inr i.down)) ?_
        linear_combination (relCurve C R).resHom
            (le_inf ((inf_le_left.trans inf_le_left).trans hW)
              ((inf_le_left.trans inf_le_right).trans (A.pieces_inr_le i.down)) :
              W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inl q.down)
                ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)
            (((relThetaCocycle C R π a)⁻¹ :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)) * (h1 - h2)
          - (relCurve C R).resHom
              (le_inf ((inf_le_left.trans inf_le_left).trans hW)
                ((inf_le_left.trans inf_le_right).trans (A.pieces_inr_le i.down)))
              (((relThetaCocycle C R π a)⁻¹ :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁))
            * (relCurve C R).resHom
                (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
                (A.idealDiv (Sum.inl q.down) β hβ) * hratio
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
            ≤ W ⊓ A.pieces (Sum.inr i.down))
          ((relCurve C R).resHom
              (le_inf (inf_le_left.trans hW)
                (inf_le_right.trans (A.pieces_inr_le i.down)))
              (((relThetaCocycle C R π a)⁻¹ :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁))
            * A.idealDiv (Sum.inr i.down) β hβ)
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
                ((relCurve C R).resHom
                    (le_inf (inf_le_left.trans hW)
                      (inf_le_right.trans (A.pieces_inr_le q.down)))
                    (((relThetaCocycle C R π a)⁻¹ :
                      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                        (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                        (relCover C R (fiberTwoCover π)).V₁))
                  * A.idealDiv (Sum.inr q.down) β hβ) := by
        rw [mul_one, map_mul, map_mul]
        simp only [Scheme.resHom_resHom]
        refine A.eqn_res_cancel (Sum.inr i.down)
          (inf_le_left.trans inf_le_right :
            W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inr q.down)
              ≤ A.pieces (Sum.inr i.down)) ?_
        linear_combination (relCurve C R).resHom
            (le_inf ((inf_le_left.trans inf_le_left).trans hW)
              ((inf_le_left.trans inf_le_right).trans (A.pieces_inr_le i.down)) :
              W ⊓ A.pieces (Sum.inr i.down) ⊓ A.pieces (Sum.inr q.down)
                ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)
            (((relThetaCocycle C R π a)⁻¹ :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)) * (h1 - h2)
          - (relCurve C R).resHom
              (le_inf ((inf_le_left.trans inf_le_left).trans hW)
                ((inf_le_left.trans inf_le_right).trans (A.pieces_inr_le i.down)))
              (((relThetaCocycle C R π a)⁻¹ :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁))
            * (relCurve C R).resHom
                (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
                (A.idealDiv (Sum.inr q.down) β hβ) * hratio
      exact key⟩

/-- The chart-0 component of the trivialization over `V₀` is the division by the
equation. -/
lemma idealToGlued₀_comp_inl {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z) (i : Fin A.m₀) :
    ((idealToGlued₀ A a hW β hβ).val (Sum.inl (ULift.up i)) :
        Γ(relCurve C R, W ⊓ A.pieces (Sum.inl i)))
      = A.idealDiv (Sum.inl i) β hβ := rfl

/-- The chart-0 characterizing equation of the trivialization:
`f_i · (idealToGlued₀ β)_i = β` on `W ⊓ D(h_i)`. -/
lemma eqn_mul_idealToGlued₀_inl {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z) (i : Fin A.m₀)
    {O : (relCurve C R).Opens} (hOW : O ≤ W) (hOi : O ≤ A.pieces (Sum.inl i)) :
    (relCurve C R).resHom hOi (A.eqn (Sum.inl i))
        * (relCurve C R).resHom (le_inf hOW hOi)
            ((idealToGlued₀ A a hW β hβ).val (Sum.inl (ULift.up i)))
      = (relCurve C R).resHom hOW β :=
  eqn_mul_idealDiv_res (A := A) (Sum.inl i) β hβ hOW hOi

end DivisorAdaptation

end AlgebraicGeometry
