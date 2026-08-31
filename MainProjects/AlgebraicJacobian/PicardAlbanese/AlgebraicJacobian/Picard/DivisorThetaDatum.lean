/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyTheta

/-!
# DD-4 (Task 4, right exactness) — the glued-sheaf datum of `𝒪(Θᵃ − d)`

The twisted ideal sheaf of a divisor family, presented as a pinned cocycle datum
(`AlgebraicGeometry.BasicOpenCocycleDatum`, DAT-1) on the pieces of a finite chart
adaptation `A` — the object on which the rigid engine fires the relative
`H¹(𝒪(Θᵃ − d)) = 0` of the section sequence's right exactness:

* `DivisorAdaptation.existsUnique_eqn_mul_eq` — **division by the equation**: on any
  open below a piece, a section vanishing along `d` germwise is a unique multiple of
  the restricted equation `f_i` (stalk-locality of the regular principal ideal
  `Scheme.mem_span_singleton_of_forall_germ` + regularity for uniqueness).  This is the
  workhorse of the trivialization bridges.
* `DivisorAdaptation.eqnRatio` — **the ratio units** `f_j/f_i ∈ Γ(D(h_i) ⊓ D(h_j))ˣ`:
  the unique cofactors of the two equations over each other; a gluing cocycle by
  uniqueness (`eqnRatio_self`, `eqnRatio_mul_res`).
* `FinCoverData.thetaOvlUnit_self`, `thetaOvlUnit_mul_res` — the four-case theta
  twisting unit of `AlgebraicJacobian.Picard.DivisorFamilyTheta` is a gluing cocycle
  (eight chart-case products collapsing to the unit laws of the theta cocycle).
* `DivisorAdaptation.thetaIdealUnit` — the transition units of `𝒪(Θᵃ − d)`:
  `eqnRatio · thetaOvlUnit`; a section of the glued sheaf is, on each piece, the
  cofactor `x/f_j` of an honest section `x` vanishing along `d`, in the chart picture
  of the piece — the matching `s_i = (f_j/f_i)·θ^{±a}·s_j` is exactly
  `f_i s_i = θ^{±a}·(f_j s_j)`.
* `DivisorAdaptation.thetaIdealDatum` — the datum: the adaptation's cover data
  (`ULift`-ed to the ambient universe — `FinCoverData` indices live in `Type 0`, the
  datum wants `Type u`) with the `thetaIdealUnit` transition cocycle.  Its glued sheaf
  carries the engine's quasi-coherence packagings and two-lattice pair for free
  (`BasicOpenCocycleDatum.instQcohOn₀/₁/Inf`, `BasicOpenCocycleDatum.pairData`).

The cocycle laws are stated as plain `∀`-lemmas at the adaptation index (`Type 0`;
`Scheme.IsGluingCocycle` pins its index to `Type u`) and assembled into the structure
at the `ULift`-ed datum index, where each constructor case is definitionally the
adaptation-level law.

The trivialization bridges (glued sections ↔ sections vanishing along `d`) and the
discharge of the surjectivity inputs of
`AlgebraicJacobian.Picard.DivisorFamilyThetaSurj` are the follow-on file.
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

/-! ## The theta twisting units form a cocycle -/

namespace FinCoverData

variable (D : FinCoverData C R π) (a : ℕ)

/-- The value of a restricted unit. -/
private lemma val_unitsRestrict {W U : (relCurve C R).Opens} (h : W ≤ U)
    (u : Γ(relCurve C R, U)ˣ) :
    (((relCurve C R).unitsRestrict h u : Γ(relCurve C R, W)ˣ) : Γ(relCurve C R, W))
      = (relCurve C R).resHom h (u : Γ(relCurve C R, U)) := rfl

/-- The value of the inverse of a restricted unit. -/
private lemma val_inv_unitsRestrict {W U : (relCurve C R).Opens} (h : W ≤ U)
    (u : Γ(relCurve C R, U)ˣ) :
    ((((relCurve C R).unitsRestrict h u)⁻¹ : Γ(relCurve C R, W)ˣ) :
        Γ(relCurve C R, W))
      = (relCurve C R).resHom h ((u⁻¹ : Γ(relCurve C R, U)ˣ) : Γ(relCurve C R, U)) :=
  rfl

/-- The theta twisting unit is `1` on the diagonal. -/
theorem thetaOvlUnit_self (i : D.index) :
    ((D.thetaOvlUnit a i i : Γ(relCurve C R, D.pieces i ⊓ D.pieces i)ˣ) :
      Γ(relCurve C R, D.pieces i ⊓ D.pieces i)) = 1 := by
  rcases i with i | i
  · rw [thetaOvlUnit_inl_inl, Units.val_one]
  · rw [thetaOvlUnit_inr_inr, Units.val_one]

/-- **The theta twisting units satisfy the cocycle identity** on every triple overlap:
the eight chart-case products collapse to the unit laws of the theta cocycle. -/
theorem thetaOvlUnit_mul_res (i j l : D.index) :
    (relCurve C R).resHom
        (inf_le_left : D.pieces i ⊓ D.pieces j ⊓ D.pieces l ≤ D.pieces i ⊓ D.pieces j)
        ((D.thetaOvlUnit a i j : Γ(relCurve C R, D.pieces i ⊓ D.pieces j)ˣ) :
          Γ(relCurve C R, D.pieces i ⊓ D.pieces j))
      * (relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            D.pieces i ⊓ D.pieces j ⊓ D.pieces l ≤ D.pieces j ⊓ D.pieces l)
          ((D.thetaOvlUnit a j l : Γ(relCurve C R, D.pieces j ⊓ D.pieces l)ˣ) :
            Γ(relCurve C R, D.pieces j ⊓ D.pieces l))
      = (relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            D.pieces i ⊓ D.pieces j ⊓ D.pieces l ≤ D.pieces i ⊓ D.pieces l)
          ((D.thetaOvlUnit a i l : Γ(relCurve C R, D.pieces i ⊓ D.pieces l)ˣ) :
            Γ(relCurve C R, D.pieces i ⊓ D.pieces l)) := by
  rcases i with i | i <;> rcases j with j | j <;> rcases l with l | l
  · -- (0,0,0): 1 · 1 = 1
    simp only [thetaOvlUnit_inl_inl, Units.val_one, map_one, one_mul]
  · -- (0,0,1): 1 · θ = θ
    rw [thetaOvlUnit_inl_inl, thetaOvlUnit_inl_inr, thetaOvlUnit_inl_inr,
      Units.val_one, map_one, one_mul, val_unitsRestrict, val_unitsRestrict,
      Scheme.resHom_resHom, Scheme.resHom_resHom]
  · -- (0,1,0): θ · θ⁻¹ = 1
    rw [thetaOvlUnit_inl_inr, thetaOvlUnit_inr_inl, thetaOvlUnit_inl_inl,
      val_unitsRestrict, val_inv_unitsRestrict, Units.val_one, map_one,
      Scheme.resHom_resHom, Scheme.resHom_resHom, ← map_mul, Units.mul_inv, map_one]
  · -- (0,1,1): θ · 1 = θ
    rw [thetaOvlUnit_inl_inr, thetaOvlUnit_inr_inr, thetaOvlUnit_inl_inr,
      Units.val_one, map_one, mul_one, val_unitsRestrict, val_unitsRestrict,
      Scheme.resHom_resHom, Scheme.resHom_resHom]
  · -- (1,0,0): θ⁻¹ · 1 = θ⁻¹
    rw [thetaOvlUnit_inr_inl, thetaOvlUnit_inl_inl, thetaOvlUnit_inr_inl,
      Units.val_one, map_one, mul_one, val_inv_unitsRestrict, val_inv_unitsRestrict,
      Scheme.resHom_resHom, Scheme.resHom_resHom]
  · -- (1,0,1): θ⁻¹ · θ = 1
    rw [thetaOvlUnit_inr_inl, thetaOvlUnit_inl_inr, thetaOvlUnit_inr_inr,
      val_inv_unitsRestrict, val_unitsRestrict, Units.val_one, map_one,
      Scheme.resHom_resHom, Scheme.resHom_resHom, ← map_mul, Units.inv_mul, map_one]
  · -- (1,1,0): 1 · θ⁻¹ = θ⁻¹
    rw [thetaOvlUnit_inr_inr, thetaOvlUnit_inr_inl, thetaOvlUnit_inr_inl,
      Units.val_one, map_one, one_mul, val_inv_unitsRestrict, val_inv_unitsRestrict,
      Scheme.resHom_resHom, Scheme.resHom_resHom]
  · -- (1,1,1): 1 · 1 = 1
    simp only [thetaOvlUnit_inr_inr, Units.val_one, map_one, one_mul]

end FinCoverData

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d)

/-! ## Division by the equation -/

/-- **Cancellation by the restricted equation**: the adaptation equations are regular on
every open below their piece. -/
lemma eqn_res_cancel (i : A.index) {W : (relCurve C R).Opens} (hW : W ≤ A.pieces i)
    {x y : Γ(relCurve C R, W)}
    (h : (relCurve C R).resHom hW (A.eqn i) * x
      = (relCurve C R).resHom hW (A.eqn i) * y) : x = y :=
  (mul_cancel_left_mem_nonZeroDivisors
    (Scheme.restriction_mem_nonZeroDivisors
      (fun z hz => A.eqn_regular i z hz) hW)).mp h

/-- The germ of a restricted equation lies in the stalk ideal of `d` at every point. -/
lemma germ_res_eqn_mem_stalkIdeal (i : A.index) {W : (relCurve C R).Opens}
    (hW : W ≤ A.pieces i) (z : relCurve C R) (hz : z ∈ W) :
    ((relCurve C R).presheaf.germ W z hz).hom
      ((relCurve C R).resHom hW (A.eqn i)) ∈ d.stalkIdeal z := by
  have hswap : ((relCurve C R).presheaf.germ W z hz).hom
      ((relCurve C R).resHom hW (A.eqn i))
      = ((relCurve C R).presheaf.germ (A.pieces i) z (hW hz)).hom (A.eqn i) :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [hswap, ← A.germ_eqn_span_eq_stalkIdeal i (hW hz)]
  exact Ideal.subset_span rfl

/-- **Division by the equation** (the trivialization workhorse): on any open below a
piece, a section vanishing along `d` germwise is a *unique* multiple of the restricted
equation — existence by stalk-locality of the regular principal ideal, uniqueness by
regularity. -/
theorem existsUnique_eqn_mul_eq (i : A.index) {W : (relCurve C R).Opens}
    (hW : W ≤ A.pieces i) {s : Γ(relCurve C R, W)}
    (hs : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom s ∈ d.stalkIdeal z) :
    ∃! c : Γ(relCurve C R, W), (relCurve C R).resHom hW (A.eqn i) * c = s := by
  have hb : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom
        ((relCurve C R).resHom hW (A.eqn i))
        ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk z) := by
    intro z hz
    have hswap : ((relCurve C R).presheaf.germ W z hz).hom
        ((relCurve C R).resHom hW (A.eqn i))
        = ((relCurve C R).presheaf.germ (A.pieces i) z (hW hz)).hom (A.eqn i) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hswap]
    exact A.eqn_regular i z (hW hz)
  have hmem : s ∈ Ideal.span {(relCurve C R).resHom hW (A.eqn i)} := by
    refine Scheme.mem_span_singleton_of_forall_germ hb (fun z hz => ?_)
    have hswap : ((relCurve C R).presheaf.germ W z hz).hom
        ((relCurve C R).resHom hW (A.eqn i))
        = ((relCurve C R).presheaf.germ (A.pieces i) z (hW hz)).hom (A.eqn i) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hswap, A.germ_eqn_span_eq_stalkIdeal i (hW hz)]
    exact hs z hz
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [mul_comm] at hc
  exact ⟨c, hc, fun y hy => A.eqn_res_cancel i hW (hy.trans hc.symm)⟩

/-- **The cofactor of a section vanishing along `d`** over the (restricted) equation of a
piece: the unique `c` with `f_i · c = s`. -/
noncomputable def eqnDiv (i : A.index) {W : (relCurve C R).Opens}
    (hW : W ≤ A.pieces i) (s : Γ(relCurve C R, W))
    (hs : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom s ∈ d.stalkIdeal z) :
    Γ(relCurve C R, W) :=
  (A.existsUnique_eqn_mul_eq i hW hs).choose

/-- The defining equation of the cofactor. -/
lemma eqn_mul_eqnDiv (i : A.index) {W : (relCurve C R).Opens}
    (hW : W ≤ A.pieces i) (s : Γ(relCurve C R, W))
    (hs : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom s ∈ d.stalkIdeal z) :
    (relCurve C R).resHom hW (A.eqn i) * A.eqnDiv i hW s hs = s :=
  (A.existsUnique_eqn_mul_eq i hW hs).choose_spec.1

/-- Uniqueness of the cofactor. -/
lemma eqnDiv_unique (i : A.index) {W : (relCurve C R).Opens}
    (hW : W ≤ A.pieces i) {s c : Γ(relCurve C R, W)}
    (hs : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom s ∈ d.stalkIdeal z)
    (hc : (relCurve C R).resHom hW (A.eqn i) * c = s) :
    c = A.eqnDiv i hW s hs :=
  (A.existsUnique_eqn_mul_eq i hW hs).choose_spec.2 c hc

/-! ## The ratio units `f_j / f_i` -/

/-- The restriction of the second equation to a piece overlap vanishes along `d`
germwise. -/
private lemma germ_res_eqn_right (i j : A.index) :
    ∀ (z : relCurve C R) (hz : z ∈ A.pieces i ⊓ A.pieces j),
      ((relCurve C R).presheaf.germ (A.pieces i ⊓ A.pieces j) z hz).hom
        ((relCurve C R).resHom (inf_le_right : A.pieces i ⊓ A.pieces j ≤ A.pieces j)
          (A.eqn j)) ∈ d.stalkIdeal z :=
  fun z hz => A.germ_res_eqn_mem_stalkIdeal j inf_le_right z hz

/-- The restriction of the first equation to a piece overlap vanishes along `d`
germwise. -/
private lemma germ_res_eqn_left (i j : A.index) :
    ∀ (z : relCurve C R) (hz : z ∈ A.pieces i ⊓ A.pieces j),
      ((relCurve C R).presheaf.germ (A.pieces i ⊓ A.pieces j) z hz).hom
        ((relCurve C R).resHom (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i)
          (A.eqn i)) ∈ d.stalkIdeal z :=
  fun z hz => A.germ_res_eqn_mem_stalkIdeal i inf_le_left z hz

/-- **The ratio unit `f_j / f_i`** on the piece overlap `D(h_i) ⊓ D(h_j)`: the unique
cofactor of `f_j` over `f_i`, a unit because the reverse cofactor inverts it (by
regularity).  These are the transition units of the ideal sheaf `𝒪(−d)` in the piece
trivializations. -/
noncomputable def eqnRatio (i j : A.index) :
    Γ(relCurve C R, A.pieces i ⊓ A.pieces j)ˣ :=
  Units.mkOfMulEqOne
    (A.existsUnique_eqn_mul_eq i inf_le_left (A.germ_res_eqn_right i j)).choose
    (A.existsUnique_eqn_mul_eq j inf_le_right (A.germ_res_eqn_left i j)).choose
    (by
      have h1 := (A.existsUnique_eqn_mul_eq i inf_le_left
        (A.germ_res_eqn_right i j)).choose_spec.1
      have h2 := (A.existsUnique_eqn_mul_eq j inf_le_right
        (A.germ_res_eqn_left i j)).choose_spec.1
      refine A.eqn_res_cancel i inf_le_left ?_
      rw [mul_one, ← mul_assoc, h1, h2])

/-- The defining equation of the ratio unit: `f_i · (f_j/f_i) = f_j` on the overlap. -/
lemma eqn_mul_eqnRatio (i j : A.index) :
    (relCurve C R).resHom (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i)
        (A.eqn i)
      * ((A.eqnRatio i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)ˣ) :
          Γ(relCurve C R, A.pieces i ⊓ A.pieces j))
      = (relCurve C R).resHom (inf_le_right : A.pieces i ⊓ A.pieces j ≤ A.pieces j)
          (A.eqn j) :=
  (A.existsUnique_eqn_mul_eq i inf_le_left (A.germ_res_eqn_right i j)).choose_spec.1

/-- The symmetric overlap ideal is already generated by the equation from the left
piece; the right equation differs from it by the overlap ratio unit. -/
theorem ovlIdeal_eq_span_left (i j : A.index) :
    A.ovlIdeal i j =
      Ideal.span {relResAlgHom C R
        (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i) (A.eqn i)} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.subset_span rfl
    · have hratio := A.eqn_mul_eqnRatio i j
      change relResAlgHom C R
          (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i) (A.eqn i) *
          (A.eqnRatio i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)) =
        relResAlgHom C R
          (inf_le_right : A.pieces i ⊓ A.pieces j ≤ A.pieces j) (A.eqn j) at hratio
      rw [← hratio]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · apply Ideal.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Ideal.subset_span (Set.mem_insert _ _)

/-- The ratio unit is `1` on the diagonal (by uniqueness of the cofactor). -/
theorem eqnRatio_self (i : A.index) :
    ((A.eqnRatio i i : Γ(relCurve C R, A.pieces i ⊓ A.pieces i)ˣ) :
      Γ(relCurve C R, A.pieces i ⊓ A.pieces i)) = 1 := by
  refine A.eqn_res_cancel i inf_le_left ?_
  rw [mul_one, A.eqn_mul_eqnRatio i i]

/-- **The ratio units satisfy the cocycle identity** (by uniqueness of cofactors over
the regular `f_i`). -/
theorem eqnRatio_mul_res (i j l : A.index) :
    (relCurve C R).resHom
        (inf_le_left : A.pieces i ⊓ A.pieces j ⊓ A.pieces l ≤ A.pieces i ⊓ A.pieces j)
        ((A.eqnRatio i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)ˣ) :
          Γ(relCurve C R, A.pieces i ⊓ A.pieces j))
      * (relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            A.pieces i ⊓ A.pieces j ⊓ A.pieces l ≤ A.pieces j ⊓ A.pieces l)
          ((A.eqnRatio j l : Γ(relCurve C R, A.pieces j ⊓ A.pieces l)ˣ) :
            Γ(relCurve C R, A.pieces j ⊓ A.pieces l))
      = (relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            A.pieces i ⊓ A.pieces j ⊓ A.pieces l ≤ A.pieces i ⊓ A.pieces l)
          ((A.eqnRatio i l : Γ(relCurve C R, A.pieces i ⊓ A.pieces l)ˣ) :
            Γ(relCurve C R, A.pieces i ⊓ A.pieces l)) := by
  refine A.eqn_res_cancel i
    ((inf_le_left.trans inf_le_left :
      A.pieces i ⊓ A.pieces j ⊓ A.pieces l ≤ A.pieces i)) ?_
  have h1 := congrArg ((relCurve C R).resHom
    (inf_le_left : A.pieces i ⊓ A.pieces j ⊓ A.pieces l ≤ A.pieces i ⊓ A.pieces j))
    (A.eqn_mul_eqnRatio i j)
  have h2 := congrArg ((relCurve C R).resHom
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      A.pieces i ⊓ A.pieces j ⊓ A.pieces l ≤ A.pieces j ⊓ A.pieces l))
    (A.eqn_mul_eqnRatio j l)
  have h3 := congrArg ((relCurve C R).resHom
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      A.pieces i ⊓ A.pieces j ⊓ A.pieces l ≤ A.pieces i ⊓ A.pieces l))
    (A.eqn_mul_eqnRatio i l)
  rw [map_mul] at h1 h2 h3
  simp only [Scheme.resHom_resHom] at h1 h2 h3
  rw [← mul_assoc, h1, h2, h3]

/-! ## The transition units of `𝒪(Θᵃ − d)` -/

variable (a : ℕ)

/-- **The transition units of the twisted ideal sheaf `𝒪(Θᵃ − d)`** on the piece
overlaps: the ratio unit times the theta twisting unit.  In the piece trivializations
"cofactor over `f_j` in the chart picture of the piece", the matching
`s_i = (f_j/f_i)·θ^{±a}·s_j` is exactly the twisted-pair matching
`f_i·s_i = θ^{±a}·(f_j·s_j)` of an honest section vanishing along `d`. -/
noncomputable def thetaIdealUnit (i j : A.index) :
    Γ(relCurve C R, A.pieces i ⊓ A.pieces j)ˣ :=
  A.eqnRatio i j * A.thetaOvlUnit a i j

/-- The ideal transition unit is `1` on the diagonal. -/
theorem thetaIdealUnit_self (i : A.index) :
    ((A.thetaIdealUnit a i i : Γ(relCurve C R, A.pieces i ⊓ A.pieces i)ˣ) :
      Γ(relCurve C R, A.pieces i ⊓ A.pieces i)) = 1 := by
  rw [thetaIdealUnit, Units.val_mul, A.eqnRatio_self i,
    A.toFinCoverData.thetaOvlUnit_self a i, one_mul]

/-- **The ideal transition units satisfy the cocycle identity** (product of the two
cocycle laws). -/
theorem thetaIdealUnit_mul_res (i j l : A.index) :
    (relCurve C R).resHom
        (inf_le_left : A.pieces i ⊓ A.pieces j ⊓ A.pieces l ≤ A.pieces i ⊓ A.pieces j)
        ((A.thetaIdealUnit a i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)ˣ) :
          Γ(relCurve C R, A.pieces i ⊓ A.pieces j))
      * (relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            A.pieces i ⊓ A.pieces j ⊓ A.pieces l ≤ A.pieces j ⊓ A.pieces l)
          ((A.thetaIdealUnit a j l : Γ(relCurve C R, A.pieces j ⊓ A.pieces l)ˣ) :
            Γ(relCurve C R, A.pieces j ⊓ A.pieces l))
      = (relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            A.pieces i ⊓ A.pieces j ⊓ A.pieces l ≤ A.pieces i ⊓ A.pieces l)
          ((A.thetaIdealUnit a i l : Γ(relCurve C R, A.pieces i ⊓ A.pieces l)ˣ) :
            Γ(relCurve C R, A.pieces i ⊓ A.pieces l)) := by
  simp only [thetaIdealUnit, Units.val_mul, map_mul]
  rw [mul_mul_mul_comm, A.eqnRatio_mul_res i j l,
    A.toFinCoverData.thetaOvlUnit_mul_res a i j l]

/-! ## The pinned cocycle datum of `𝒪(Θᵃ − d)` -/

/-- **The glued-sheaf datum of the twisted ideal sheaf `𝒪(Θᵃ − d)`**: the adaptation's
finite basic-open cover data of the two pinned charts (`ULift`-ed to the ambient
universe) with the `thetaIdealUnit` transition cocycle.  Its glued sheaf carries the
engine's quasi-coherence packagings and its two-lattice pair for free. -/
noncomputable def thetaIdealDatum : BasicOpenCocycleDatum C R π where
  J₀ := ULift.{u} (Fin A.m₀)
  J₁ := ULift.{u} (Fin A.m₁)
  fintype₀ := inferInstance
  fintype₁ := inferInstance
  h₀ := fun j => A.h₀ j.down
  h₁ := fun j => A.h₁ j.down
  a₀ := fun j => A.a₀ j.down
  a₁ := fun j => A.a₁ j.down
  partition₀ := by
    rw [← A.partition₀]
    exact Fintype.sum_equiv Equiv.ulift _ _ (fun j => rfl)
  partition₁ := by
    rw [← A.partition₁]
    exact Fintype.sum_equiv Equiv.ulift _ _ (fun j => rfl)
  unit := fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => A.thetaIdealUnit a (Sum.inl i.down) (Sum.inl j.down)
    | Sum.inl i, Sum.inr j => A.thetaIdealUnit a (Sum.inl i.down) (Sum.inr j.down)
    | Sum.inr i, Sum.inl j => A.thetaIdealUnit a (Sum.inr i.down) (Sum.inl j.down)
    | Sum.inr i, Sum.inr j => A.thetaIdealUnit a (Sum.inr i.down) (Sum.inr j.down)
  isGluingCocycle := by
    constructor
    · intro i
      rcases i with i | i
      · exact A.thetaIdealUnit_self a (Sum.inl i.down)
      · exact A.thetaIdealUnit_self a (Sum.inr i.down)
    · intro i j l
      rcases i with i | i <;> rcases j with j | j <;> rcases l with l | l
      · exact A.thetaIdealUnit_mul_res a (Sum.inl i.down) (Sum.inl j.down) (Sum.inl l.down)
      · exact A.thetaIdealUnit_mul_res a (Sum.inl i.down) (Sum.inl j.down) (Sum.inr l.down)
      · exact A.thetaIdealUnit_mul_res a (Sum.inl i.down) (Sum.inr j.down) (Sum.inl l.down)
      · exact A.thetaIdealUnit_mul_res a (Sum.inl i.down) (Sum.inr j.down) (Sum.inr l.down)
      · exact A.thetaIdealUnit_mul_res a (Sum.inr i.down) (Sum.inl j.down) (Sum.inl l.down)
      · exact A.thetaIdealUnit_mul_res a (Sum.inr i.down) (Sum.inl j.down) (Sum.inr l.down)
      · exact A.thetaIdealUnit_mul_res a (Sum.inr i.down) (Sum.inr j.down) (Sum.inl l.down)
      · exact A.thetaIdealUnit_mul_res a (Sum.inr i.down) (Sum.inr j.down) (Sum.inr l.down)

/-! ### The index and piece dictionary of the datum -/

/-- The datum index lowers to the adaptation index. -/
def lowerIndex : (A.thetaIdealDatum a).index → A.index :=
  Sum.map ULift.down ULift.down

@[simp]
lemma thetaIdealDatum_pieces_inl (i : ULift.{u} (Fin A.m₀)) :
    (A.thetaIdealDatum a).pieces (Sum.inl i) = A.pieces (Sum.inl i.down) := rfl

@[simp]
lemma thetaIdealDatum_pieces_inr (i : ULift.{u} (Fin A.m₁)) :
    (A.thetaIdealDatum a).pieces (Sum.inr i) = A.pieces (Sum.inr i.down) := rfl

lemma thetaIdealDatum_pieces (i : (A.thetaIdealDatum a).index) :
    (A.thetaIdealDatum a).pieces i = A.pieces (A.lowerIndex a i) := by
  rcases i with i | i <;> rfl

@[simp]
lemma thetaIdealDatum_unit_inl_inl (i j : ULift.{u} (Fin A.m₀)) :
    (A.thetaIdealDatum a).unit (Sum.inl i) (Sum.inl j)
      = A.thetaIdealUnit a (Sum.inl i.down) (Sum.inl j.down) := rfl

@[simp]
lemma thetaIdealDatum_unit_inl_inr (i : ULift.{u} (Fin A.m₀))
    (j : ULift.{u} (Fin A.m₁)) :
    (A.thetaIdealDatum a).unit (Sum.inl i) (Sum.inr j)
      = A.thetaIdealUnit a (Sum.inl i.down) (Sum.inr j.down) := rfl

@[simp]
lemma thetaIdealDatum_unit_inr_inl (i : ULift.{u} (Fin A.m₁))
    (j : ULift.{u} (Fin A.m₀)) :
    (A.thetaIdealDatum a).unit (Sum.inr i) (Sum.inl j)
      = A.thetaIdealUnit a (Sum.inr i.down) (Sum.inl j.down) := rfl

@[simp]
lemma thetaIdealDatum_unit_inr_inr (i j : ULift.{u} (Fin A.m₁)) :
    (A.thetaIdealDatum a).unit (Sum.inr i) (Sum.inr j)
      = A.thetaIdealUnit a (Sum.inr i.down) (Sum.inr j.down) := rfl

end DivisorAdaptation

end AlgebraicGeometry
