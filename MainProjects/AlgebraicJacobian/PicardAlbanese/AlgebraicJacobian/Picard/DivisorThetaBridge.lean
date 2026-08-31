/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorThetaDatum

/-!
# DD-4 (Task 4, right exactness) — the trivialization bridges for `𝒪(Θᵃ − d)`

The dictionary between sections of the glued theta-ideal sheaf
(`DivisorAdaptation.thetaIdealDatum`) and honest chart sections vanishing along the
divisor family `d`:

* `DivisorAdaptation.glued_cross` — **the cross-chart reading** of the glued matching:
  for a glued section `s` and pieces `i` (chart 0), `j` (chart 1), on any open below
  both, `f_i·s_i = θᵃ·(f_j·s_j)` — the transition units were built so that the piece
  pictures assemble to a Θ-twisted pair.
* `DivisorAdaptation.gluedSections_ext₀/₁` — a glued section over an open of a pinned
  chart is determined by its components on the pieces of that chart (the other chart's
  components are tied through `glued_cross` by regularity).
* `DivisorAdaptation.idealToGlued₀/₁` — **trivialization**: a section `β` over `W ≤ Vc`
  vanishing along `d` germwise divides by the equations into a glued section (the
  chart-`c` picture; the other chart's components carry the `θ^{∓a}` factor), with the
  characterizing equations `eqn_mul_idealToGlued₀_inl/inr` (and mirrors).
* `DivisorAdaptation.gluedToIdeal₀/₁` — **assembly**: the piece pictures `f_i·s_i` of a
  glued section over `W ≤ Vc` glue to a single section vanishing along `d`
  (`res_gluedToIdeal₀`, `germ_gluedToIdeal₀_mem`, and mirrors).

These four maps discharge the chart-lifting and overlap-correction inputs of
`AlgebraicJacobian.Picard.DivisorFamilyThetaSurj` in
`AlgebraicJacobian.Picard.DivisorThetaSurjectivity`.
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

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d) (a : ℕ)

/-- The sections of the glued theta-ideal sheaf `𝒪(Θᵃ − d)` over `W`. -/
noncomputable abbrev ThetaIdealSections (W : (relCurve C R).Opens) : Type u :=
  ↥(_root_.AlgebraicGeometry.gluedSubmodule R (A.thetaIdealDatum a).pieces
    (A.thetaIdealDatum a).unit W)

variable {A a}

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

/-- The value of the ideal transition unit. -/
private lemma val_thetaIdealUnit (i j : A.index) :
    ((A.thetaIdealUnit a i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)ˣ) :
        Γ(relCurve C R, A.pieces i ⊓ A.pieces j))
      = ((A.eqnRatio i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)ˣ) :
          Γ(relCurve C R, A.pieces i ⊓ A.pieces j))
        * ((A.thetaOvlUnit a i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)ˣ) :
            Γ(relCurve C R, A.pieces i ⊓ A.pieces j)) := rfl

/-! ## The matching of a glued section, read through the equations -/

/-- The glued matching at a pair of indices, restricted to any open below the double
overlap: `s_p = u_{pq} · s_q` on `O`. -/
private lemma glued_matching_res {W : (relCurve C R).Opens}
    (s : A.ThetaIdealSections a W) (p q : (A.thetaIdealDatum a).index)
    {O : (relCurve C R).Opens}
    (hOW : O ≤ W) (hOp : O ≤ (A.thetaIdealDatum a).pieces p)
    (hOq : O ≤ (A.thetaIdealDatum a).pieces q) :
    (relCurve C R).resHom (le_inf hOW hOp) (s.val p)
      = (relCurve C R).resHom (le_inf hOp hOq)
          (((A.thetaIdealDatum a).unit p q :
            Γ(relCurve C R, (A.thetaIdealDatum a).pieces p ⊓
              (A.thetaIdealDatum a).pieces q)ˣ) :
            Γ(relCurve C R, (A.thetaIdealDatum a).pieces p ⊓
              (A.thetaIdealDatum a).pieces q))
        * (relCurve C R).resHom (le_inf hOW hOq) (s.val q) := by
  have hmatch := (_root_.AlgebraicGeometry.mem_gluedSubmodule_iff R (A.thetaIdealDatum a).pieces
    (A.thetaIdealDatum a).unit s.val).mp s.property p q
  have key := congrArg ((relCurve C R).resHom
    (le_inf (le_inf hOW hOp) hOq :
      O ≤ W ⊓ (A.thetaIdealDatum a).pieces p ⊓ (A.thetaIdealDatum a).pieces q)) hmatch
  rw [map_mul] at key
  simp only [Scheme.resHom_resHom] at key
  exact key

/-- **The cross-chart reading of the glued matching**: for a chart-0 piece `i` and a
chart-1 piece `j`, on any open below `W` and both pieces,
`f_i·s_i = θᵃ·(f_j·s_j)` — the piece pictures of a glued section assemble to a
Θ-twisted pair. -/
lemma glued_cross {W : (relCurve C R).Opens} (s : A.ThetaIdealSections a W)
    (i : Fin A.m₀) (j : Fin A.m₁) {O : (relCurve C R).Opens}
    (hOW : O ≤ W) (hOi : O ≤ A.pieces (Sum.inl i)) (hOj : O ≤ A.pieces (Sum.inr j)) :
    (relCurve C R).resHom hOi (A.eqn (Sum.inl i))
        * (relCurve C R).resHom (le_inf hOW hOi) (s.val (Sum.inl (ULift.up i)))
      = (relCurve C R).resHom
            (le_inf (hOi.trans (A.pieces_inl_le i)) (hOj.trans (A.pieces_inr_le j)))
            ((relThetaCocycle C R π a :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁))
          * ((relCurve C R).resHom hOj (A.eqn (Sum.inr j))
            * (relCurve C R).resHom (le_inf hOW hOj) (s.val (Sum.inr (ULift.up j)))) := by
  have key : (relCurve C R).resHom (le_inf hOW hOi) (s.val (Sum.inl (ULift.up i)))
      = (relCurve C R).resHom (le_inf hOi hOj :
            O ≤ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j))
          (((A.eqnRatio (Sum.inl i) (Sum.inr j) :
              Γ(relCurve C R, A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j))ˣ) :
              Γ(relCurve C R, A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)))
            * (relCurve C R).resHom
                (inf_le_inf (A.pieces_inl_le i) (A.pieces_inr_le j))
                ((relThetaCocycle C R π a :
                  Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                    (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                  Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                    (relCover C R (fiberTwoCover π)).V₁)))
        * (relCurve C R).resHom (le_inf hOW hOj) (s.val (Sum.inr (ULift.up j))) :=
    glued_matching_res s (Sum.inl (ULift.up i)) (Sum.inr (ULift.up j)) hOW hOi hOj
  rw [map_mul, Scheme.resHom_resHom] at key
  have hratio := congrArg ((relCurve C R).resHom (le_inf hOi hOj :
      O ≤ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)))
    (A.eqn_mul_eqnRatio (Sum.inl i) (Sum.inr j))
  rw [map_mul] at hratio
  simp only [Scheme.resHom_resHom] at hratio
  rw [key, ← hratio]
  ring

/-- **Chart-0 determination**: a glued section over an open of the pinned chart `V₀` is
determined by its chart-0 components. -/
lemma gluedSections_ext₀ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) {s t : A.ThetaIdealSections a W}
    (h : ∀ i : Fin A.m₀, s.val (Sum.inl (ULift.up i)) = t.val (Sum.inl (ULift.up i))) :
    s = t := by
  refine Subtype.ext (funext fun p => ?_)
  rcases p with i | j
  · exact h i.down
  · -- the chart-1 components are tied through `glued_cross` on the chart-0 cover
    apply TopCat.Sheaf.eq_of_locally_eq' (relCurve C R).sheaf
      (fun i : Fin A.m₀ =>
        W ⊓ A.pieces (Sum.inr j.down) ⊓ A.pieces (Sum.inl i))
      (W ⊓ A.pieces (Sum.inr j.down))
      (fun i => homOfLE inf_le_left)
    · intro x hx
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (A.cover₀ (hW hx.1))
      exact Opens.mem_iSup.mpr ⟨i, ⟨hx, hi⟩⟩
    · intro i
      change (relCurve C R).resHom inf_le_left (s.val (Sum.inr j))
        = (relCurve C R).resHom inf_le_left (t.val (Sum.inr j))
      have hOW : W ⊓ A.pieces (Sum.inr j.down) ⊓ A.pieces (Sum.inl i) ≤ W :=
        inf_le_left.trans inf_le_left
      have hOi : W ⊓ A.pieces (Sum.inr j.down) ⊓ A.pieces (Sum.inl i)
          ≤ A.pieces (Sum.inl i) := inf_le_right
      have hOj : W ⊓ A.pieces (Sum.inr j.down) ⊓ A.pieces (Sum.inl i)
          ≤ A.pieces (Sum.inr j.down) := inf_le_left.trans inf_le_right
      have hs := glued_cross s i j.down hOW hOi hOj
      have ht := glued_cross t i j.down hOW hOi hOj
      rw [h i] at hs
      have hkey := hs.symm.trans ht
      -- cancel the theta unit and the regular equation `f_j`
      have hθ : IsUnit ((relCurve C R).resHom
          (le_inf (hOi.trans (A.pieces_inl_le i)) (hOj.trans (A.pieces_inr_le j.down)))
          ((relThetaCocycle C R π a :
            Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
              (relCover C R (fiberTwoCover π)).V₁)ˣ) :
            Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
              (relCover C R (fiberTwoCover π)).V₁))) :=
        (relThetaCocycle C R π a).isUnit.map _
      have hcancel := hθ.mul_left_cancel hkey
      have := A.eqn_res_cancel (Sum.inr j.down) hOj hcancel
      -- both sides are the two componentwise restrictions
      have hgoal : (relCurve C R).resHom (le_inf hOW hOj) (s.val (Sum.inr j))
          = (relCurve C R).resHom (le_inf hOW hOj) (t.val (Sum.inr j)) := this
      calc (relCurve C R).resHom inf_le_left (s.val (Sum.inr j))
          = (relCurve C R).resHom (le_inf hOW hOj) (s.val (Sum.inr j)) := rfl
        _ = (relCurve C R).resHom (le_inf hOW hOj) (t.val (Sum.inr j)) := hgoal
        _ = (relCurve C R).resHom inf_le_left (t.val (Sum.inr j)) := rfl

/-- **Chart-1 determination**: a glued section over an open of the pinned chart `V₁` is
determined by its chart-1 components. -/
lemma gluedSections_ext₁ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) {s t : A.ThetaIdealSections a W}
    (h : ∀ j : Fin A.m₁, s.val (Sum.inr (ULift.up j)) = t.val (Sum.inr (ULift.up j))) :
    s = t := by
  refine Subtype.ext (funext fun p => ?_)
  rcases p with i | j
  swap
  · exact h j.down
  · -- the chart-0 components are tied through `glued_cross` on the chart-1 cover
    apply TopCat.Sheaf.eq_of_locally_eq' (relCurve C R).sheaf
      (fun j : Fin A.m₁ =>
        W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr j))
      (W ⊓ A.pieces (Sum.inl i.down))
      (fun j => homOfLE inf_le_left)
    · intro x hx
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (A.cover₁ (hW hx.1))
      exact Opens.mem_iSup.mpr ⟨j, ⟨hx, hj⟩⟩
    · intro j
      change (relCurve C R).resHom inf_le_left (s.val (Sum.inl i))
        = (relCurve C R).resHom inf_le_left (t.val (Sum.inl i))
      have hOW : W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr j) ≤ W :=
        inf_le_left.trans inf_le_left
      have hOi : W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr j)
          ≤ A.pieces (Sum.inl i.down) := inf_le_left.trans inf_le_right
      have hOj : W ⊓ A.pieces (Sum.inl i.down) ⊓ A.pieces (Sum.inr j)
          ≤ A.pieces (Sum.inr j) := inf_le_right
      have hs := glued_cross s i.down j hOW hOi hOj
      have ht := glued_cross t i.down j hOW hOi hOj
      rw [h j] at hs
      have hkey := hs.trans ht.symm
      have := A.eqn_res_cancel (Sum.inl i.down) hOi hkey
      have hgoal : (relCurve C R).resHom (le_inf hOW hOi) (s.val (Sum.inl i))
          = (relCurve C R).resHom (le_inf hOW hOi) (t.val (Sum.inl i)) := this
      calc (relCurve C R).resHom inf_le_left (s.val (Sum.inl i))
          = (relCurve C R).resHom (le_inf hOW hOi) (s.val (Sum.inl i)) := rfl
        _ = (relCurve C R).resHom (le_inf hOW hOi) (t.val (Sum.inl i)) := hgoal
        _ = (relCurve C R).resHom inf_le_left (t.val (Sum.inl i)) := rfl

/-- **The same-chart reading of the glued matching** on chart 0: `f_i·s_i = f_{i'}·s_{i'}`
on any open below `W` and both pieces. -/
lemma glued_same₀ {W : (relCurve C R).Opens} (s : A.ThetaIdealSections a W)
    (i i' : Fin A.m₀) {O : (relCurve C R).Opens}
    (hOW : O ≤ W) (hOi : O ≤ A.pieces (Sum.inl i)) (hOi' : O ≤ A.pieces (Sum.inl i')) :
    (relCurve C R).resHom hOi (A.eqn (Sum.inl i))
        * (relCurve C R).resHom (le_inf hOW hOi) (s.val (Sum.inl (ULift.up i)))
      = (relCurve C R).resHom hOi' (A.eqn (Sum.inl i'))
        * (relCurve C R).resHom (le_inf hOW hOi') (s.val (Sum.inl (ULift.up i'))) := by
  have key : (relCurve C R).resHom (le_inf hOW hOi) (s.val (Sum.inl (ULift.up i)))
      = (relCurve C R).resHom (le_inf hOi hOi' :
            O ≤ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl i'))
          (((A.eqnRatio (Sum.inl i) (Sum.inl i') :
              Γ(relCurve C R, A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl i'))ˣ) :
              Γ(relCurve C R, A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl i')))
            * 1)
        * (relCurve C R).resHom (le_inf hOW hOi') (s.val (Sum.inl (ULift.up i'))) :=
    glued_matching_res s (Sum.inl (ULift.up i)) (Sum.inl (ULift.up i')) hOW hOi hOi'
  rw [mul_one] at key
  have hratio := congrArg ((relCurve C R).resHom (le_inf hOi hOi' :
      O ≤ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl i')))
    (A.eqn_mul_eqnRatio (Sum.inl i) (Sum.inl i'))
  rw [map_mul] at hratio
  simp only [Scheme.resHom_resHom] at hratio
  rw [key, ← hratio]
  ring

/-- **The same-chart reading of the glued matching** on chart 1. -/
lemma glued_same₁ {W : (relCurve C R).Opens} (s : A.ThetaIdealSections a W)
    (j j' : Fin A.m₁) {O : (relCurve C R).Opens}
    (hOW : O ≤ W) (hOj : O ≤ A.pieces (Sum.inr j)) (hOj' : O ≤ A.pieces (Sum.inr j')) :
    (relCurve C R).resHom hOj (A.eqn (Sum.inr j))
        * (relCurve C R).resHom (le_inf hOW hOj) (s.val (Sum.inr (ULift.up j)))
      = (relCurve C R).resHom hOj' (A.eqn (Sum.inr j'))
        * (relCurve C R).resHom (le_inf hOW hOj') (s.val (Sum.inr (ULift.up j'))) := by
  have key : (relCurve C R).resHom (le_inf hOW hOj) (s.val (Sum.inr (ULift.up j)))
      = (relCurve C R).resHom (le_inf hOj hOj' :
            O ≤ A.pieces (Sum.inr j) ⊓ A.pieces (Sum.inr j'))
          (((A.eqnRatio (Sum.inr j) (Sum.inr j') :
              Γ(relCurve C R, A.pieces (Sum.inr j) ⊓ A.pieces (Sum.inr j'))ˣ) :
              Γ(relCurve C R, A.pieces (Sum.inr j) ⊓ A.pieces (Sum.inr j')))
            * 1)
        * (relCurve C R).resHom (le_inf hOW hOj') (s.val (Sum.inr (ULift.up j'))) :=
    glued_matching_res s (Sum.inr (ULift.up j)) (Sum.inr (ULift.up j')) hOW hOj hOj'
  rw [mul_one] at key
  have hratio := congrArg ((relCurve C R).resHom (le_inf hOj hOj' :
      O ≤ A.pieces (Sum.inr j) ⊓ A.pieces (Sum.inr j')))
    (A.eqn_mul_eqnRatio (Sum.inr j) (Sum.inr j'))
  rw [map_mul] at hratio
  simp only [Scheme.resHom_resHom] at hratio
  rw [key, ← hratio]
  ring

end DivisorAdaptation

end AlgebraicGeometry
