/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyTheta

/-!
# DD-4 (Task 4, right exactness) — the surjectivity assembly for `thetaGluedEval`

The **assembly step** of the right exactness of the section sequence
(`informal/dat-d-worksheet.md` §2.3 step 2): the Θ-twisted colength evaluation
`thetaGluedEval : H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}` of `AlgebraicJacobian.Picard.DivisorFamilyTheta`
is surjective, GIVEN the two cohomological inputs in section-level form:

* **chart lifting** (`DivisorAdaptation.LiftsOnChart₀/₁`): every Θ-twisted glued colength
  family lifts, on each pinned chart separately, to a chart section reducing to it on
  every piece — the vanishing of `H¹` of the twisted ideal sheaf `𝒪(Θᵃ − d)` on the
  affine pinned chart (Serre, quasi-coherent Čech on the basic-open pieces);
* **overlap correction** (`relThetaOverlapCorrection`): every section of the chart
  overlap all of whose germs lie in the stalk ideals of `d` splits as a Θ-twisted
  difference of chart sections vanishing along `d` — the two-chart Čech
  `H¹(𝒪(Θᵃ − d)) = 0` (relative; fired by the engine at fibre degree
  `a·δ − deg d ≥ b`, DAT-0a).

Given these, the preimage of a glued family `w` is assembled as follows: lift `w` on
each chart (`σ₀`, `σ₁`), observe that the mismatch `τ = σ₀ − θᵃ·σ₁` on the chart overlap
vanishes along `d` germwise (the Θ-twisted matching of `w` on the piece overlaps),
correct by the overlap input (`τ = α₀ − θᵃ·α₁` with `αᵢ` vanishing along `d`), and check
that `(σ₀ − α₀, σ₁ − α₁)` is a global twisted section evaluating to `w` — the correction
disappears in every colength because a section vanishing along `d` germwise lies in the
regular principal ideal `(f_j)` of each piece
(`Scheme.mem_span_singleton_of_forall_germ`).

The discharge of the two inputs from the glued-sheaf datum of `𝒪(Θᵃ − d)` and the rigid
engine is the follow-on brick (`AlgebraicJacobian.Picard.DivisorThetaDatum`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R]
  [Algebra k R]

/-! ## The overlap-correction input -/

section Correction

variable (π : C.left ⟶ P1 k) [IsFinite π]

/-- **Overlap correction input** (the two-chart Čech `H¹(𝒪(Θᵃ − d)) = 0` in
section-level form): every section of the chart overlap vanishing along `d` germwise is
a Θ-twisted difference of chart sections vanishing along `d`.  Depends only on the
divisor family `d` and the twist `a`, not on any chart adaptation. -/
def relThetaOverlapCorrection (d : (relCurve C R).LocalEquations) (a : ℕ) : Prop :=
  ∀ τ : Γ(relCurve C R,
      (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁),
    (∀ (z : relCurve C R) (hz : z ∈ (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁),
      ((relCurve C R).presheaf.germ _ z hz).hom τ ∈ d.stalkIdeal z) →
    ∃ (α₀ : Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀))
      (α₁ : Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₁)),
      (∀ (z : relCurve C R) (hz : z ∈ (relCover C R (fiberTwoCover π)).V₀),
        ((relCurve C R).presheaf.germ _ z hz).hom α₀ ∈ d.stalkIdeal z) ∧
      (∀ (z : relCurve C R) (hz : z ∈ (relCover C R (fiberTwoCover π)).V₁),
        ((relCurve C R).presheaf.germ _ z hz).hom α₁ ∈ d.stalkIdeal z) ∧
      τ = (relCurve C R).resHom inf_le_left α₀
        - ((relThetaCocycle C R π a :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
            Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
              (relCover C R (fiberTwoCover π)).V₁))
          * (relCurve C R).resHom inf_le_right α₁

end Correction

variable {π : C.left ⟶ P1 k} [IsFinite π]

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d) (a : ℕ)

/-! ## The chart-lifting inputs -/

/-- **Chart-0 lifting input** for the right exactness of the section sequence: every
Θ-twisted glued colength family is, on the pinned chart `V₀`, the reduction of a single
chart section.  This is the vanishing of `H¹` of the ideal sheaf `𝒪(Θᵃ − d)` on the
affine chart, in Čech-free form. -/
def LiftsOnChart₀ : Prop :=
  ∀ w : A.chartProd, w ∈ A.thetaGluedSubmodule a →
    ∃ σ : Γ(relCurve C R, ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀),
      ∀ j : Fin A.m₀,
        Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inl j)})
          ((relCurve C R).resHom (le_inf le_top (A.pieces_inl_le j)) σ) = w (Sum.inl j)

/-- **Chart-1 lifting input**. -/
def LiftsOnChart₁ : Prop :=
  ∀ w : A.chartProd, w ∈ A.thetaGluedSubmodule a →
    ∃ σ : Γ(relCurve C R, ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁),
      ∀ j : Fin A.m₁,
        Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inr j)})
          ((relCurve C R).resHom (le_inf le_top (A.pieces_inr_le j)) σ) = w (Sum.inr j)

variable {A a}

/-! ## Vanishing along `d` kills every colength -/

/-- A chart section all of whose germs lie in the stalk ideals of `d` restricts into the
regular principal ideal `(f_j)` of every chart-0 piece (the
`Scheme.mem_span_singleton_of_forall_germ` pattern of the kernel bridge). -/
lemma res_mem_span_eqn_inl_of_forall_germ
    {α : Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀)}
    (hα : ∀ (z : relCurve C R) (hz : z ∈ (relCover C R (fiberTwoCover π)).V₀),
      ((relCurve C R).presheaf.germ _ z hz).hom α ∈ d.stalkIdeal z) (j : Fin A.m₀) :
    (relCurve C R).resHom (A.pieces_inl_le j) α
      ∈ Ideal.span {A.eqn (Sum.inl j)} := by
  refine Scheme.mem_span_singleton_of_forall_germ
    (fun z hz => A.eqn_regular (Sum.inl j) z hz) (fun z hz => ?_)
  have hswap : ((relCurve C R).presheaf.germ (A.pieces (Sum.inl j)) z hz).hom
      ((relCurve C R).resHom (A.pieces_inl_le j) α)
      = ((relCurve C R).presheaf.germ ((relCover C R (fiberTwoCover π)).V₀) z
          (A.pieces_inl_le j hz)).hom α :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [hswap, A.germ_eqn_span_eq_stalkIdeal (Sum.inl j) hz]
  exact hα z _

/-- The chart-1 mirror. -/
lemma res_mem_span_eqn_inr_of_forall_germ
    {α : Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₁)}
    (hα : ∀ (z : relCurve C R) (hz : z ∈ (relCover C R (fiberTwoCover π)).V₁),
      ((relCurve C R).presheaf.germ _ z hz).hom α ∈ d.stalkIdeal z) (j : Fin A.m₁) :
    (relCurve C R).resHom (A.pieces_inr_le j) α
      ∈ Ideal.span {A.eqn (Sum.inr j)} := by
  refine Scheme.mem_span_singleton_of_forall_germ
    (fun z hz => A.eqn_regular (Sum.inr j) z hz) (fun z hz => ?_)
  have hswap : ((relCurve C R).presheaf.germ (A.pieces (Sum.inr j)) z hz).hom
      ((relCurve C R).resHom (A.pieces_inr_le j) α)
      = ((relCurve C R).presheaf.germ ((relCover C R (fiberTwoCover π)).V₁) z
          (A.pieces_inr_le j hz)).hom α :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [hswap, A.germ_eqn_span_eq_stalkIdeal (Sum.inr j) hz]
  exact hα z _

/-! ## Germs of the overlap ideal lie in the stalk ideals -/

/-- Every germ of an element of the overlap ideal `(f_i, f_j)` lies in the stalk ideal
of `d`. -/
lemma germ_mem_stalkIdeal_of_mem_ovlIdeal {i j : A.index}
    {t : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)} (ht : t ∈ A.ovlIdeal i j)
    (z : relCurve C R) (hz : z ∈ A.pieces i ⊓ A.pieces j) :
    ((relCurve C R).presheaf.germ (A.pieces i ⊓ A.pieces j) z hz).hom t
      ∈ d.stalkIdeal z := by
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp ht
  have hgerm := congrArg
    ((relCurve C R).presheaf.germ (A.pieces i ⊓ A.pieces j) z hz).hom huv
  rw [map_add, map_mul, map_mul] at hgerm
  rw [← hgerm]
  have hi : ((relCurve C R).presheaf.germ (A.pieces i ⊓ A.pieces j) z hz).hom
      (relResAlgHom C R (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i) (A.eqn i))
      ∈ d.stalkIdeal z := by
    have hswap : ((relCurve C R).presheaf.germ (A.pieces i ⊓ A.pieces j) z hz).hom
        (relResAlgHom C R (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i)
          (A.eqn i))
        = ((relCurve C R).presheaf.germ (A.pieces i) z hz.1).hom (A.eqn i) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hswap, ← A.germ_eqn_span_eq_stalkIdeal i hz.1]
    exact Ideal.subset_span rfl
  have hj : ((relCurve C R).presheaf.germ (A.pieces i ⊓ A.pieces j) z hz).hom
      (relResAlgHom C R (inf_le_right : A.pieces i ⊓ A.pieces j ≤ A.pieces j) (A.eqn j))
      ∈ d.stalkIdeal z := by
    have hswap : ((relCurve C R).presheaf.germ (A.pieces i ⊓ A.pieces j) z hz).hom
        (relResAlgHom C R (inf_le_right : A.pieces i ⊓ A.pieces j ≤ A.pieces j)
          (A.eqn j))
        = ((relCurve C R).presheaf.germ (A.pieces j) z hz.2).hom (A.eqn j) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hswap, ← A.germ_eqn_span_eq_stalkIdeal j hz.2]
    exact Ideal.subset_span rfl
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hi) (Ideal.mul_mem_left _ _ hj)

/-! ## The assembly -/

/-- **Right exactness of the section sequence, assembly form** (worksheet §2.3 step 2):
given the chart-lifting inputs and the overlap-correction input, the Θ-twisted colength
evaluation `thetaGluedEval : H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}` is surjective. -/
theorem thetaGluedEval_surjective_of_liftsOnChart_of_correction
    (hlift₀ : A.LiftsOnChart₀ a) (hlift₁ : A.LiftsOnChart₁ a)
    (hcorr : relThetaOverlapCorrection π d a) :
    Function.Surjective (A.thetaGluedEval a) := by
  rintro ⟨w, hw⟩
  obtain ⟨σ₀, hσ₀⟩ := hlift₀ w hw
  obtain ⟨σ₁, hσ₁⟩ := hlift₁ w hw
  -- the mismatch of the chart lifts on the chart overlap
  obtain ⟨τ, hτdef⟩ : ∃ τ : Γ(relCurve C R,
      (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁),
      τ = (relCurve C R).resHom (le_inf le_top inf_le_left) σ₀
        - ((relThetaCocycle C R π a :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
            Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
              (relCover C R (fiberTwoCover π)).V₁))
          * (relCurve C R).resHom (le_inf le_top inf_le_right) σ₁ := ⟨_, rfl⟩
  -- the mismatch vanishes along `d` germwise: read the Θ-twisted matching of `w`
  -- on a piece overlap through each point
  have hτ : ∀ (z : relCurve C R) (hz : z ∈ (relCover C R (fiberTwoCover π)).V₀ ⊓
      (relCover C R (fiberTwoCover π)).V₁),
      ((relCurve C R).presheaf.germ _ z hz).hom τ ∈ d.stalkIdeal z := by
    intro z hz
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (A.cover₀ hz.1)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (A.cover₁ hz.2)
    have hzij : z ∈ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j) := ⟨hi, hj⟩
    -- the Θ-twisted matching of `w` at the pair `(inl i, inr j)`,
    -- as a membership in the overlap ideal
    have hmatch := (A.mem_thetaGluedSubmodule_iff a w).mp hw (Sum.inl i, Sum.inr j)
    dsimp only at hmatch
    rw [← hσ₀ i, ← hσ₁ j, toOvlLeft_mk, toOvlRight_mk,
      FinCoverData.thetaOvlUnit_inl_inr, Scheme.resHom_resHom, Scheme.resHom_resHom,
      ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at hmatch
    have hker := germ_mem_stalkIdeal_of_mem_ovlIdeal hmatch z hzij
    rw [map_sub, map_mul] at hker
    -- collapse germs of restrictions to germs of the ambient sections
    have hswap₀ : ((relCurve C R).presheaf.germ
        (A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)) z hzij).hom
        ((relCurve C R).resHom
          (((inf_le_left : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)
              ≤ A.pieces (Sum.inl i))).trans (le_inf le_top (A.pieces_inl_le i))) σ₀)
        = ((relCurve C R).presheaf.germ
            (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) z
            ⟨trivial, hz.1⟩).hom σ₀ :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    have hswap₁ : ((relCurve C R).presheaf.germ
        (A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)) z hzij).hom
        ((relCurve C R).resHom
          (((inf_le_right : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)
              ≤ A.pieces (Sum.inr j))).trans (le_inf le_top (A.pieces_inr_le j))) σ₁)
        = ((relCurve C R).presheaf.germ
            (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) z
            ⟨trivial, hz.2⟩).hom σ₁ :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    have hswapθ : ((relCurve C R).presheaf.germ
        (A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)) z hzij).hom
        (((relCurve C R).unitsRestrict
            (inf_le_inf (A.pieces_inl_le i) (A.pieces_inr_le j))
            (relThetaCocycle C R π a) :
          Γ(relCurve C R, A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j))ˣ) :
          Γ(relCurve C R, A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)))
        = ((relCurve C R).presheaf.germ
            ((relCover C R (fiberTwoCover π)).V₀ ⊓
              (relCover C R (fiberTwoCover π)).V₁) z hz).hom
            ((relThetaCocycle C R π a :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)) :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hswap₀, hswap₁, hswapθ] at hker
    -- the germ of the mismatch is the same stalk element
    have hgermτ : ((relCurve C R).presheaf.germ
        ((relCover C R (fiberTwoCover π)).V₀ ⊓
          (relCover C R (fiberTwoCover π)).V₁) z hz).hom τ
        = ((relCurve C R).presheaf.germ
            (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) z ⟨trivial, hz.1⟩).hom σ₀
          - ((relCurve C R).presheaf.germ
              ((relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁) z hz).hom
              ((relThetaCocycle C R π a :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁)ˣ) :
                Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                  (relCover C R (fiberTwoCover π)).V₁))
            * ((relCurve C R).presheaf.germ
                (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) z ⟨trivial, hz.2⟩).hom σ₁ := by
      have hs₀ : ((relCurve C R).presheaf.germ
          ((relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁) z hz).hom
          ((relCurve C R).resHom (le_inf le_top inf_le_left) σ₀)
          = ((relCurve C R).presheaf.germ
              (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) z ⟨trivial, hz.1⟩).hom σ₀ :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      have hs₁ : ((relCurve C R).presheaf.germ
          ((relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁) z hz).hom
          ((relCurve C R).resHom (le_inf le_top inf_le_right) σ₁)
          = ((relCurve C R).presheaf.germ
              (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) z ⟨trivial, hz.2⟩).hom σ₁ :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      rw [hτdef, map_sub, map_mul, hs₀, hs₁]
    rw [hgermτ]
    exact hker
  -- correct the mismatch by sections vanishing along `d`
  obtain ⟨α₀, α₁, hα₀, hα₁, hsplit⟩ := hcorr τ hτ
  -- the corrected pair is a global twisted section
  have hmem : ((σ₀ - (relCurve C R).resHom inf_le_right α₀,
      σ₁ - (relCurve C R).resHom inf_le_right α₁) :
        Γ(relCurve C R, ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀)
          × Γ(relCurve C R, ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁))
      ∈ twistSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) ⊤ := by
    rw [mem_twistSubmodule_iff]
    have hres := congrArg ((relCurve C R).resHom
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ⊓
          (relCover C R (fiberTwoCover π)).V₁ : (relCurve C R).Opens)
          ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁)) hsplit
    rw [hτdef, map_sub, map_sub, map_mul, map_mul] at hres
    simp only [Scheme.resHom_resHom] at hres
    rw [map_sub, map_sub, mul_sub]
    simp only [Scheme.resHom_resHom]
    linear_combination hres
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  rw [thetaGluedEval_coe]
  funext p
  rcases p with i | i
  · rw [thetaEval_apply_inl]
    dsimp only
    rw [map_sub, map_sub, Scheme.resHom_resHom, hσ₀ i, sub_eq_self,
      Ideal.Quotient.eq_zero_iff_mem]
    exact res_mem_span_eqn_inl_of_forall_germ hα₀ i
  · rw [thetaEval_apply_inr]
    dsimp only
    rw [map_sub, map_sub, Scheme.resHom_resHom, hσ₁ i, sub_eq_self,
      Ideal.Quotient.eq_zero_iff_mem]
    exact res_mem_span_eqn_inr_of_forall_germ hα₁ i

end DivisorAdaptation

end AlgebraicGeometry
