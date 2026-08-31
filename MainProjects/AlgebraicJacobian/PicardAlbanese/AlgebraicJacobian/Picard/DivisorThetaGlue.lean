/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorThetaTrivializeOne

/-!
# DD-4 (Task 4, right exactness) — assembling glued `𝒪(Θᵃ − d)` sections into ideal sections

The assembly direction of the trivialization bridges: the piece pictures `f_i·s_i` of a
glued theta-ideal section `s` over an open `W` of a pinned chart agree on the piece
overlaps (`glued_same₀/₁`) and hence glue to a single chart section

* `DivisorAdaptation.gluedToIdeal₀/₁` — with the characterizing equations
  `res_gluedToIdeal₀/₁` (`(gluedToIdeal s)|_{W ⊓ D(h_i)} = f_i·s_i`) and uniqueness
  (`gluedToIdeal₀/₁_unique`);
* `DivisorAdaptation.germ_gluedToIdeal₀/₁_mem` — the assembled section vanishes along
  `d` germwise (each piece picture is a multiple of the equation);
* `DivisorAdaptation.gluedToIdeal₀_eq_theta_mul_gluedToIdeal₁` — **the two chart
  pictures differ by `θᵃ`** below the chart overlap (`glued_cross` on the double
  cover): the assembled sections are the two components of a Θ-twisted pair.
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

/-! ## The retyped components -/

variable (A) in
/-- The chart-0 component of a glued section, retyped at the adaptation's piece
(the `Scheme.overModule` seam: the datum's pieces are the adaptation's pieces only up
to unfolding, which instance search does not perform). -/
noncomputable def gluedComp₀ {W : (relCurve C R).Opens} (s : A.ThetaIdealSections a W)
    (i : Fin A.m₀) : Γ(relCurve C R, W ⊓ A.pieces (Sum.inl i)) :=
  s.val (Sum.inl (ULift.up i))

variable (A) in
/-- The chart-1 component of a glued section, retyped at the adaptation's piece. -/
noncomputable def gluedComp₁ {W : (relCurve C R).Opens} (s : A.ThetaIdealSections a W)
    (j : Fin A.m₁) : Γ(relCurve C R, W ⊓ A.pieces (Sum.inr j)) :=
  s.val (Sum.inr (ULift.up j))

/-! ## Assembly over the chart `V₀` -/

/-- The piece pictures `f_i·s_i` of a glued section over `W ≤ V₀` glue uniquely to a
section of `W`. -/
private lemma existsUnique_gluedToIdeal₀ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (s : A.ThetaIdealSections a W) :
    ∃! β : Γ(relCurve C R, W), ∀ i : Fin A.m₀,
      (relCurve C R).resHom (inf_le_left : W ⊓ A.pieces (Sum.inl i) ≤ W) β
        = (relCurve C R).resHom
            (inf_le_right : W ⊓ A.pieces (Sum.inl i) ≤ A.pieces (Sum.inl i))
            (A.eqn (Sum.inl i)) * A.gluedComp₀ s i := by
  have hcompat : ∀ i j : Fin A.m₀,
      (relCurve C R).resHom
          (inf_le_left : (W ⊓ A.pieces (Sum.inl i)) ⊓ (W ⊓ A.pieces (Sum.inl j))
            ≤ W ⊓ A.pieces (Sum.inl i))
          ((relCurve C R).resHom inf_le_right (A.eqn (Sum.inl i)) * A.gluedComp₀ s i)
        = (relCurve C R).resHom
            (inf_le_right : (W ⊓ A.pieces (Sum.inl i)) ⊓ (W ⊓ A.pieces (Sum.inl j))
              ≤ W ⊓ A.pieces (Sum.inl j))
            ((relCurve C R).resHom inf_le_right (A.eqn (Sum.inl j))
              * A.gluedComp₀ s j) := by
    intro i j
    have hOW : (W ⊓ A.pieces (Sum.inl i)) ⊓ (W ⊓ A.pieces (Sum.inl j)) ≤ W :=
      inf_le_left.trans inf_le_left
    have hOi : (W ⊓ A.pieces (Sum.inl i)) ⊓ (W ⊓ A.pieces (Sum.inl j))
        ≤ A.pieces (Sum.inl i) := inf_le_left.trans inf_le_right
    have hOj : (W ⊓ A.pieces (Sum.inl i)) ⊓ (W ⊓ A.pieces (Sum.inl j))
        ≤ A.pieces (Sum.inl j) := inf_le_right.trans inf_le_right
    have key := glued_same₀ s i j hOW hOi hOj
    rw [map_mul, map_mul]
    simp only [Scheme.resHom_resHom]
    exact key
  obtain ⟨β, hβ, huniq⟩ := TopCat.Sheaf.existsUnique_gluing' (relCurve C R).sheaf
    (fun i : Fin A.m₀ => W ⊓ A.pieces (Sum.inl i)) W
    (fun i => homOfLE inf_le_left)
    (fun x hx => by
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (A.cover₀ (hW hx))
      exact Opens.mem_iSup.mpr ⟨i, ⟨hx, hi⟩⟩)
    (fun i => (relCurve C R).resHom inf_le_right (A.eqn (Sum.inl i))
      * A.gluedComp₀ s i)
    (fun i j => hcompat i j)
  exact ⟨β, fun i => hβ i, fun y hy => huniq y fun i => hy i⟩

variable (A a) in
/-- **Assembly over the chart `V₀`**: the piece pictures `f_i·s_i` of a glued
theta-ideal section over `W ≤ V₀` glue to a single section of `W` — the chart-0
component of the Θ-twisted pair presented by `s`. -/
noncomputable def gluedToIdeal₀ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (s : A.ThetaIdealSections a W) :
    Γ(relCurve C R, W) :=
  (existsUnique_gluedToIdeal₀ hW s).choose

/-- The characterizing equations of the assembly. -/
lemma res_gluedToIdeal₀ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (s : A.ThetaIdealSections a W)
    (i : Fin A.m₀) :
    (relCurve C R).resHom (inf_le_left : W ⊓ A.pieces (Sum.inl i) ≤ W)
        (gluedToIdeal₀ A a hW s)
      = (relCurve C R).resHom
          (inf_le_right : W ⊓ A.pieces (Sum.inl i) ≤ A.pieces (Sum.inl i))
          (A.eqn (Sum.inl i)) * A.gluedComp₀ s i :=
  (existsUnique_gluedToIdeal₀ hW s).choose_spec.1 i

/-- Uniqueness of the assembly. -/
lemma gluedToIdeal₀_unique {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (s : A.ThetaIdealSections a W)
    {β : Γ(relCurve C R, W)}
    (hβ : ∀ i : Fin A.m₀,
      (relCurve C R).resHom (inf_le_left : W ⊓ A.pieces (Sum.inl i) ≤ W) β
        = (relCurve C R).resHom
            (inf_le_right : W ⊓ A.pieces (Sum.inl i) ≤ A.pieces (Sum.inl i))
            (A.eqn (Sum.inl i)) * A.gluedComp₀ s i) :
    β = gluedToIdeal₀ A a hW s :=
  (existsUnique_gluedToIdeal₀ hW s).choose_spec.2 β hβ

/-- The assembled section vanishes along `d` germwise. -/
lemma germ_gluedToIdeal₀_mem {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (s : A.ThetaIdealSections a W)
    (z : relCurve C R) (hz : z ∈ W) :
    ((relCurve C R).presheaf.germ W z hz).hom (gluedToIdeal₀ A a hW s)
      ∈ d.stalkIdeal z := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (A.cover₀ (hW hz))
  have hswap : ((relCurve C R).presheaf.germ (W ⊓ A.pieces (Sum.inl i)) z
      ⟨hz, hi⟩).hom ((relCurve C R).resHom
        (inf_le_left : W ⊓ A.pieces (Sum.inl i) ≤ W) (gluedToIdeal₀ A a hW s))
      = ((relCurve C R).presheaf.germ W z hz).hom (gluedToIdeal₀ A a hW s) :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [← hswap, res_gluedToIdeal₀ hW s i, map_mul]
  exact Ideal.mul_mem_right _ _
    (A.germ_res_eqn_mem_stalkIdeal (Sum.inl i) inf_le_right z ⟨hz, hi⟩)

/-! ## Assembly over the chart `V₁` -/

/-- The piece pictures `f_j·s_j` of a glued section over `W ≤ V₁` glue uniquely. -/
private lemma existsUnique_gluedToIdeal₁ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (s : A.ThetaIdealSections a W) :
    ∃! β : Γ(relCurve C R, W), ∀ j : Fin A.m₁,
      (relCurve C R).resHom (inf_le_left : W ⊓ A.pieces (Sum.inr j) ≤ W) β
        = (relCurve C R).resHom
            (inf_le_right : W ⊓ A.pieces (Sum.inr j) ≤ A.pieces (Sum.inr j))
            (A.eqn (Sum.inr j)) * A.gluedComp₁ s j := by
  have hcompat : ∀ i j : Fin A.m₁,
      (relCurve C R).resHom
          (inf_le_left : (W ⊓ A.pieces (Sum.inr i)) ⊓ (W ⊓ A.pieces (Sum.inr j))
            ≤ W ⊓ A.pieces (Sum.inr i))
          ((relCurve C R).resHom inf_le_right (A.eqn (Sum.inr i)) * A.gluedComp₁ s i)
        = (relCurve C R).resHom
            (inf_le_right : (W ⊓ A.pieces (Sum.inr i)) ⊓ (W ⊓ A.pieces (Sum.inr j))
              ≤ W ⊓ A.pieces (Sum.inr j))
            ((relCurve C R).resHom inf_le_right (A.eqn (Sum.inr j))
              * A.gluedComp₁ s j) := by
    intro i j
    have hOW : (W ⊓ A.pieces (Sum.inr i)) ⊓ (W ⊓ A.pieces (Sum.inr j)) ≤ W :=
      inf_le_left.trans inf_le_left
    have hOi : (W ⊓ A.pieces (Sum.inr i)) ⊓ (W ⊓ A.pieces (Sum.inr j))
        ≤ A.pieces (Sum.inr i) := inf_le_left.trans inf_le_right
    have hOj : (W ⊓ A.pieces (Sum.inr i)) ⊓ (W ⊓ A.pieces (Sum.inr j))
        ≤ A.pieces (Sum.inr j) := inf_le_right.trans inf_le_right
    have key := glued_same₁ s i j hOW hOi hOj
    rw [map_mul, map_mul]
    simp only [Scheme.resHom_resHom]
    exact key
  obtain ⟨β, hβ, huniq⟩ := TopCat.Sheaf.existsUnique_gluing' (relCurve C R).sheaf
    (fun j : Fin A.m₁ => W ⊓ A.pieces (Sum.inr j)) W
    (fun j => homOfLE inf_le_left)
    (fun x hx => by
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (A.cover₁ (hW hx))
      exact Opens.mem_iSup.mpr ⟨j, ⟨hx, hj⟩⟩)
    (fun j => (relCurve C R).resHom inf_le_right (A.eqn (Sum.inr j))
      * A.gluedComp₁ s j)
    (fun i j => hcompat i j)
  exact ⟨β, fun j => hβ j, fun y hy => huniq y fun j => hy j⟩

variable (A a) in
/-- **Assembly over the chart `V₁`**. -/
noncomputable def gluedToIdeal₁ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (s : A.ThetaIdealSections a W) :
    Γ(relCurve C R, W) :=
  (existsUnique_gluedToIdeal₁ hW s).choose

/-- The characterizing equations of the assembly. -/
lemma res_gluedToIdeal₁ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (s : A.ThetaIdealSections a W)
    (j : Fin A.m₁) :
    (relCurve C R).resHom (inf_le_left : W ⊓ A.pieces (Sum.inr j) ≤ W)
        (gluedToIdeal₁ A a hW s)
      = (relCurve C R).resHom
          (inf_le_right : W ⊓ A.pieces (Sum.inr j) ≤ A.pieces (Sum.inr j))
          (A.eqn (Sum.inr j)) * A.gluedComp₁ s j :=
  (existsUnique_gluedToIdeal₁ hW s).choose_spec.1 j

/-- Uniqueness of the assembly. -/
lemma gluedToIdeal₁_unique {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (s : A.ThetaIdealSections a W)
    {β : Γ(relCurve C R, W)}
    (hβ : ∀ j : Fin A.m₁,
      (relCurve C R).resHom (inf_le_left : W ⊓ A.pieces (Sum.inr j) ≤ W) β
        = (relCurve C R).resHom
            (inf_le_right : W ⊓ A.pieces (Sum.inr j) ≤ A.pieces (Sum.inr j))
            (A.eqn (Sum.inr j)) * A.gluedComp₁ s j) :
    β = gluedToIdeal₁ A a hW s :=
  (existsUnique_gluedToIdeal₁ hW s).choose_spec.2 β hβ

/-- The assembled section vanishes along `d` germwise. -/
lemma germ_gluedToIdeal₁_mem {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (s : A.ThetaIdealSections a W)
    (z : relCurve C R) (hz : z ∈ W) :
    ((relCurve C R).presheaf.germ W z hz).hom (gluedToIdeal₁ A a hW s)
      ∈ d.stalkIdeal z := by
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (A.cover₁ (hW hz))
  have hswap : ((relCurve C R).presheaf.germ (W ⊓ A.pieces (Sum.inr j)) z
      ⟨hz, hj⟩).hom ((relCurve C R).resHom
        (inf_le_left : W ⊓ A.pieces (Sum.inr j) ≤ W) (gluedToIdeal₁ A a hW s))
      = ((relCurve C R).presheaf.germ W z hz).hom (gluedToIdeal₁ A a hW s) :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [← hswap, res_gluedToIdeal₁ hW s j, map_mul]
  exact Ideal.mul_mem_right _ _
    (A.germ_res_eqn_mem_stalkIdeal (Sum.inr j) inf_le_right z ⟨hz, hj⟩)

/-! ## Algebra of the assemblies -/

/-- Restriction of scheme sections commutes with the `R`-action. -/
private lemma resHom_smul {V W : (relCurve C R).Opens} (h : V ≤ W) (r : R)
    (s : Γ(relCurve C R, W)) :
    (relCurve C R).resHom h (r • s) = r • (relCurve C R).resHom h s := by
  rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
  congr 1
  exact (relCurve C R).overAlgebraMap_apply_res R (homOfLE h).op r

/-- Additivity of the chart-zero assembly. -/
lemma gluedToIdeal₀_add {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (s t : A.ThetaIdealSections a W) :
    gluedToIdeal₀ A a hW (s + t) =
      gluedToIdeal₀ A a hW s + gluedToIdeal₀ A a hW t := by
  refine (gluedToIdeal₀_unique hW (s + t) (fun i => ?_)).symm
  rw [map_add, res_gluedToIdeal₀ hW s i, res_gluedToIdeal₀ hW t i, ← mul_add]
  rfl

/-- Additivity of the chart-one assembly. -/
lemma gluedToIdeal₁_add {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (s t : A.ThetaIdealSections a W) :
    gluedToIdeal₁ A a hW (s + t) =
      gluedToIdeal₁ A a hW s + gluedToIdeal₁ A a hW t := by
  refine (gluedToIdeal₁_unique hW (s + t) (fun j => ?_)).symm
  rw [map_add, res_gluedToIdeal₁ hW s j, res_gluedToIdeal₁ hW t j, ← mul_add]
  rfl

/-- The chart-zero assembly commutes with the `R`-action. -/
lemma gluedToIdeal₀_smul {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (r : R)
    (s : A.ThetaIdealSections a W) :
    gluedToIdeal₀ A a hW (r • s) = r • gluedToIdeal₀ A a hW s := by
  refine (gluedToIdeal₀_unique hW (r • s) (fun i => ?_)).symm
  rw [resHom_smul, res_gluedToIdeal₀ hW s i,
    show A.gluedComp₀ (r • s) i = r • A.gluedComp₀ s i from rfl]
  simp only [Scheme.overModule_smul_def]
  ring

/-- The chart-one assembly commutes with the `R`-action. -/
lemma gluedToIdeal₁_smul {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (r : R)
    (s : A.ThetaIdealSections a W) :
    gluedToIdeal₁ A a hW (r • s) = r • gluedToIdeal₁ A a hW s := by
  refine (gluedToIdeal₁_unique hW (r • s) (fun j => ?_)).symm
  rw [resHom_smul, res_gluedToIdeal₁ hW s j,
    show A.gluedComp₁ (r • s) j = r • A.gluedComp₁ s j from rfl]
  simp only [Scheme.overModule_smul_def]
  ring

/-- The assembly is additive in the glued section (differences). -/
lemma gluedToIdeal₀_sub {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (s t : A.ThetaIdealSections a W) :
    gluedToIdeal₀ A a hW (s - t)
      = gluedToIdeal₀ A a hW s - gluedToIdeal₀ A a hW t := by
  refine (gluedToIdeal₀_unique hW (s - t) (fun i => ?_)).symm
  rw [map_sub, res_gluedToIdeal₀ hW s i, res_gluedToIdeal₀ hW t i, ← mul_sub]
  rfl

/-- The chart-1 mirror. -/
lemma gluedToIdeal₁_sub {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (s t : A.ThetaIdealSections a W) :
    gluedToIdeal₁ A a hW (s - t)
      = gluedToIdeal₁ A a hW s - gluedToIdeal₁ A a hW t := by
  refine (gluedToIdeal₁_unique hW (s - t) (fun j => ?_)).symm
  rw [map_sub, res_gluedToIdeal₁ hW s j, res_gluedToIdeal₁ hW t j, ← mul_sub]
  rfl

/-- The assembly commutes with restriction of the glued section. -/
lemma gluedToIdeal₀_secRes {W' W : (relCurve C R).Opens} (h : W' ≤ W)
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (s : A.ThetaIdealSections a W) :
    gluedToIdeal₀ A a (h.trans hW) (secRes ((A.thetaIdealDatum a).sheaf) h s)
      = (relCurve C R).resHom h (gluedToIdeal₀ A a hW s) := by
  refine (gluedToIdeal₀_unique (h.trans hW) _ (fun i => ?_)).symm
  have key := congrArg ((relCurve C R).resHom
    (inf_le_inf_right (A.pieces (Sum.inl i)) h :
      W' ⊓ A.pieces (Sum.inl i) ≤ W ⊓ A.pieces (Sum.inl i)))
    (res_gluedToIdeal₀ hW s i)
  rw [map_mul] at key
  simp only [Scheme.resHom_resHom] at key ⊢
  exact key

/-- The chart-1 mirror. -/
lemma gluedToIdeal₁_secRes {W' W : (relCurve C R).Opens} (h : W' ≤ W)
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (s : A.ThetaIdealSections a W) :
    gluedToIdeal₁ A a (h.trans hW) (secRes ((A.thetaIdealDatum a).sheaf) h s)
      = (relCurve C R).resHom h (gluedToIdeal₁ A a hW s) := by
  refine (gluedToIdeal₁_unique (h.trans hW) _ (fun j => ?_)).symm
  have key := congrArg ((relCurve C R).resHom
    (inf_le_inf_right (A.pieces (Sum.inr j)) h :
      W' ⊓ A.pieces (Sum.inr j) ≤ W ⊓ A.pieces (Sum.inr j)))
    (res_gluedToIdeal₁ hW s j)
  rw [map_mul] at key
  simp only [Scheme.resHom_resHom] at key ⊢
  exact key

/-- **Roundtrip**: assembling the chart-0 trivialization of an ideal section returns
the section. -/
lemma gluedToIdeal₀_idealToGlued₀ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀) (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z) :
    gluedToIdeal₀ A a hW (idealToGlued₀ A a hW β hβ) = β := by
  refine (gluedToIdeal₀_unique hW _ (fun i => ?_)).symm
  have key := eqn_mul_idealToGlued₀_inl (A := A) (a := a) hW β hβ i
    (inf_le_left : W ⊓ A.pieces (Sum.inl i) ≤ W) inf_le_right
  rw [Scheme.resHom_self] at key
  exact key.symm

/-- The chart-1 mirror. -/
lemma gluedToIdeal₁_idealToGlued₁ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₁) (β : Γ(relCurve C R, W))
    (hβ : ∀ (z : relCurve C R) (hz : z ∈ W),
      ((relCurve C R).presheaf.germ W z hz).hom β ∈ d.stalkIdeal z) :
    gluedToIdeal₁ A a hW (idealToGlued₁ A a hW β hβ) = β := by
  refine (gluedToIdeal₁_unique hW _ (fun j => ?_)).symm
  have key := eqn_mul_idealToGlued₁_inr (A := A) (a := a) hW β hβ j
    (inf_le_left : W ⊓ A.pieces (Sum.inr j) ≤ W) inf_le_right
  rw [Scheme.resHom_self] at key
  exact key.symm

/-! ## The two chart pictures differ by `θᵃ` -/

/-- **The theta comparison of the two assemblies** below the chart overlap: the chart-0
picture of a glued section is `θᵃ` times its chart-1 picture — the assembled sections
are the two components of a Θ-twisted pair (`glued_cross` on the double cover). -/
theorem gluedToIdeal₀_eq_theta_mul_gluedToIdeal₁ {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)
    (s : A.ThetaIdealSections a W) :
    gluedToIdeal₀ A a (hW.trans inf_le_left) s
      = (relCurve C R).resHom hW
          ((relThetaCocycle C R π a :
            Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
              (relCover C R (fiberTwoCover π)).V₁)ˣ) :
            Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
              (relCover C R (fiberTwoCover π)).V₁))
        * gluedToIdeal₁ A a (hW.trans inf_le_right) s := by
  apply TopCat.Sheaf.eq_of_locally_eq' (relCurve C R).sheaf
    (fun p : Fin A.m₀ × Fin A.m₁ =>
      W ⊓ A.pieces (Sum.inl p.1) ⊓ A.pieces (Sum.inr p.2)) W
    (fun p => homOfLE (inf_le_left.trans inf_le_left))
  · intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (A.cover₀ ((hW hx).1))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (A.cover₁ ((hW hx).2))
    exact Opens.mem_iSup.mpr ⟨(i, j), ⟨⟨hx, hi⟩, hj⟩⟩
  · rintro ⟨i, j⟩
    have hOW : W ⊓ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j) ≤ W :=
      inf_le_left.trans inf_le_left
    have hOi : W ⊓ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)
        ≤ A.pieces (Sum.inl i) := inf_le_left.trans inf_le_right
    have hOj : W ⊓ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)
        ≤ A.pieces (Sum.inr j) := inf_le_right
    change (relCurve C R).resHom hOW (gluedToIdeal₀ A a (hW.trans inf_le_left) s)
      = (relCurve C R).resHom hOW
          ((relCurve C R).resHom hW
            ((relThetaCocycle C R π a :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁))
            * gluedToIdeal₁ A a (hW.trans inf_le_right) s)
    have h₀ := congrArg ((relCurve C R).resHom
      (le_inf hOW hOi : W ⊓ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)
        ≤ W ⊓ A.pieces (Sum.inl i)))
      (res_gluedToIdeal₀ (hW.trans inf_le_left) s i)
    have h₁ := congrArg ((relCurve C R).resHom
      (le_inf hOW hOj : W ⊓ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)
        ≤ W ⊓ A.pieces (Sum.inr j)))
      (res_gluedToIdeal₁ (hW.trans inf_le_right) s j)
    rw [map_mul] at h₀ h₁
    simp only [Scheme.resHom_resHom] at h₀ h₁
    have hcross := glued_cross s i j hOW hOi hOj
    rw [map_mul]
    simp only [Scheme.resHom_resHom]
    rw [h₀, h₁]
    exact hcross

end DivisorAdaptation

end AlgebraicGeometry
