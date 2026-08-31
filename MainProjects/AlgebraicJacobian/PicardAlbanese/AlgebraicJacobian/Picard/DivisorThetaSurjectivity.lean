/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyThetaSurj
import AlgebraicJacobian.Picard.DivisorThetaGlue
import AlgebraicJacobian.Cohomology.GluedSheafEngine

/-!
# DD-4 (Task 4) — right exactness of the section sequence

The surjectivity of the Θ-twisted colength evaluation
`thetaGluedEval : H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}` (`informal/dat-d-worksheet.md` §2.3 step 2),
by discharging the two inputs of the assembly
(`AlgebraicJacobian.Picard.DivisorFamilyThetaSurj`) through the glued-sheaf datum of
`𝒪(Θᵃ − d)` (`DivisorAdaptation.thetaIdealDatum`) and its trivialization bridges:

* `DivisorAdaptation.liftsOnChart₀/₁` — **the chart lifting inputs hold
  unconditionally**: on the affine pinned chart, the Čech 1-cocycle of piece-overlap
  defects of any Θ-twisted glued colength family cobounds in the quasi-coherently
  packaged theta-ideal sheaf (`IsAffineOpen.exists_cech_cobounding_of_qcoh` — Serre's
  affine vanishing), and the corrected representatives glue to a chart section.
* `DivisorAdaptation.relThetaOverlapCorrection_of_subsingleton_h1` — the overlap
  correction input follows from the vanishing of `H¹` of the two-lattice pair of the
  theta-ideal datum: an overlap section vanishing along `d` is a glued section of
  `𝒪(Θᵃ − d)`, and `H¹(pair) = 0` splits it as a difference of chart sections, whose
  assembled ideal sections differ by exactly the Θ-twist.
* `DivisorAdaptation.thetaGluedEval_surjective_of_subsingleton_h1` — **right
  exactness** given `Subsingleton (datumPair (thetaIdealDatum)).H1`.
* `DivisorAdaptation.thetaGluedEval_surjective` — **the engine-fired form**: the same
  under the complex-form fibrewise hypothesis of the rigid engine
  (`datum_subsingleton_pairH1`, Noetherian-free).  The discharge of the fibrewise
  hypothesis from DAT-0a at fibre degree `a·δ − deg d ≥ b` is the W6-full
  fibre-restriction seam (`informal/spec-dat-1.md` 1d-ii second half) — the remaining
  open brick.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R]
  [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations}

/-! ## The chart-lifting inputs hold unconditionally -/

/-- The basic opens of the chart-0 generators cover the pinned chart. -/
private lemma iSup_basicOpen_h₀ (A : DivisorAdaptation C R π d) :
    ⨆ i, (relCurve C R).basicOpen (A.h₀ i) = (relCover C R (fiberTwoCover π)).V₀ :=
  le_antisymm (iSup_le fun i => (relCurve C R).basicOpen_le (A.h₀ i)) A.cover₀

/-- The basic opens of the chart-1 generators cover the pinned chart. -/
private lemma iSup_basicOpen_h₁ (A : DivisorAdaptation C R π d) :
    ⨆ j, (relCurve C R).basicOpen (A.h₁ j) = (relCover C R (fiberTwoCover π)).V₁ :=
  le_antisymm (iSup_le fun j => (relCurve C R).basicOpen_le (A.h₁ j)) A.cover₁

/-- **The chart-0 lifting input holds unconditionally** (Serre's affine vanishing for
the quasi-coherently packaged theta-ideal sheaf): every Θ-twisted glued colength family
lifts on the pinned chart `V₀`. -/
theorem liftsOnChart₀ (A : DivisorAdaptation C R π d) (a : ℕ) : A.LiftsOnChart₀ a := by
  intro w hw
  -- representatives of the colength classes
  choose r hr using fun i : Fin A.m₀ => Ideal.Quotient.mk_surjective (w (Sum.inl i))
  -- the piece-overlap defects lie in the overlap ideals (the matching of `w`)
  have hdiff : ∀ i j : Fin A.m₀,
      (relCurve C R).resHom
          (inf_le_left : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)
            ≤ A.pieces (Sum.inl i)) (r i)
        - (relCurve C R).resHom inf_le_right (r j)
        ∈ A.ovlIdeal (Sum.inl i) (Sum.inl j) := by
    intro i j
    have hmatch := (A.mem_thetaGluedSubmodule_iff a w).mp hw (Sum.inl i, Sum.inl j)
    dsimp only at hmatch
    rw [← hr i, ← hr j, toOvlLeft_mk, toOvlRight_mk,
      FinCoverData.thetaOvlUnit_inl_inl, Units.val_one, map_one, one_mul,
      ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at hmatch
    exact hmatch
  have hgerm : ∀ (i j : Fin A.m₀) (z : relCurve C R)
      (hz : z ∈ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)),
      ((relCurve C R).presheaf.germ (A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j))
        z hz).hom
        ((relCurve C R).resHom
            (inf_le_left : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)
              ≤ A.pieces (Sum.inl i)) (r i)
          - (relCurve C R).resHom inf_le_right (r j)) ∈ d.stalkIdeal z :=
    fun i j z hz => germ_mem_stalkIdeal_of_mem_ovlIdeal (hdiff i j) z hz
  -- the piece-overlap inclusion into the chart
  have hV : ∀ i j : Fin A.m₀,
      A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)
        ≤ (relCover C R (fiberTwoCover π)).V₀ :=
    fun i j => inf_le_left.trans (A.pieces_inl_le i)
  -- the cocycle condition for the trivialized defects
  have hc : ∀ i j l : Fin A.m₀,
      secRes ((A.thetaIdealDatum a).sheaf)
          (inf_le_inf_right ((relCurve C R).basicOpen (A.h₀ l)) inf_le_left)
          (idealToGlued₀ A a (hV i l) _ (hgerm i l))
        = secRes ((A.thetaIdealDatum a).sheaf) inf_le_left
            (idealToGlued₀ A a (hV i j) _ (hgerm i j))
          + secRes ((A.thetaIdealDatum a).sheaf)
              (inf_le_inf_right ((relCurve C R).basicOpen (A.h₀ l)) inf_le_right)
              (idealToGlued₀ A a (hV j l) _ (hgerm j l)) := by
    intro i j l
    refine gluedSections_ext₀
      ((inf_le_left.trans inf_le_left).trans (A.pieces_inl_le i) :
        A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j) ⊓ A.pieces (Sum.inl l)
          ≤ (relCover C R (fiberTwoCover π)).V₀) (fun i' => ?_)
    have hOi' : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j) ⊓ A.pieces (Sum.inl l)
        ⊓ A.pieces (Sum.inl i') ≤ A.pieces (Sum.inl i') := inf_le_right
    have e_il := eqn_mul_idealToGlued₀_inl (A := A) (a := a) (hV i l) _ (hgerm i l) i'
      (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_left.trans inf_le_right) :
        A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j) ⊓ A.pieces (Sum.inl l)
          ⊓ A.pieces (Sum.inl i')
          ≤ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl l)) hOi'
    have e_ij := eqn_mul_idealToGlued₀_inl (A := A) (a := a) (hV i j) _ (hgerm i j) i'
      (inf_le_left.trans inf_le_left :
        A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j) ⊓ A.pieces (Sum.inl l)
          ⊓ A.pieces (Sum.inl i')
          ≤ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)) hOi'
    have e_jl := eqn_mul_idealToGlued₀_inl (A := A) (a := a) (hV j l) _ (hgerm j l) i'
      (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (inf_le_left.trans inf_le_right) :
        A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j) ⊓ A.pieces (Sum.inl l)
          ⊓ A.pieces (Sum.inl i')
          ≤ A.pieces (Sum.inl j) ⊓ A.pieces (Sum.inl l)) hOi'
    rw [map_sub] at e_il e_ij e_jl
    simp only [Scheme.resHom_resHom] at e_il e_ij e_jl
    have key : (relCurve C R).resHom
        (le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
          (inf_le_left.trans inf_le_right)) hOi')
        ((idealToGlued₀ A a (hV i l) _ (hgerm i l)).val (Sum.inl (ULift.up i')))
        = (relCurve C R).resHom
            (le_inf (inf_le_left.trans inf_le_left) hOi')
            ((idealToGlued₀ A a (hV i j) _ (hgerm i j)).val (Sum.inl (ULift.up i')))
          + (relCurve C R).resHom
              (le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
                (inf_le_left.trans inf_le_right)) hOi')
              ((idealToGlued₀ A a (hV j l) _ (hgerm j l)).val
                (Sum.inl (ULift.up i'))) := by
      refine A.eqn_res_cancel (Sum.inl i') hOi' ?_
      rw [mul_add]
      linear_combination e_il - e_ij - e_jl
    exact key
  -- fire the Čech cobounding on the theta-ideal sheaf over the affine chart
  obtain ⟨b, hb⟩ := IsAffineOpen.exists_cech_cobounding_of_qcoh
    (F := (A.thetaIdealDatum a).sheaf)
    (relCover_isAffineOpen₀ C R (fiberTwoCover π)) A.h₀ (iSup_basicOpen_h₀ A)
    (fun i j => idealToGlued₀ A a (hV i j) _ (hgerm i j)) hc
  -- convert the cobounding back to ideal sections and correct the representatives
  have hkey : ∀ i j : Fin A.m₀,
      (relCurve C R).resHom
          (inf_le_left : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)
            ≤ A.pieces (Sum.inl i)) (r i)
        - (relCurve C R).resHom inf_le_right (r j)
        = (relCurve C R).resHom inf_le_left
            (gluedToIdeal₀ A a (A.pieces_inl_le i) (b i))
          - (relCurve C R).resHom inf_le_right
              (gluedToIdeal₀ A a (A.pieces_inl_le j) (b j)) := by
    intro i j
    have hnat_i : gluedToIdeal₀ A a (hV i j)
        (secRes ((A.thetaIdealDatum a).sheaf)
          (inf_le_left : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)
            ≤ A.pieces (Sum.inl i)) (b i))
        = (relCurve C R).resHom inf_le_left
            (gluedToIdeal₀ A a (A.pieces_inl_le i) (b i)) :=
      gluedToIdeal₀_secRes inf_le_left (A.pieces_inl_le i) (b i)
    have hnat_j : gluedToIdeal₀ A a (hV i j)
        (secRes ((A.thetaIdealDatum a).sheaf)
          (inf_le_right : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)
            ≤ A.pieces (Sum.inl j)) (b j))
        = (relCurve C R).resHom inf_le_right
            (gluedToIdeal₀ A a (A.pieces_inl_le j) (b j)) :=
      gluedToIdeal₀_secRes inf_le_right (A.pieces_inl_le j) (b j)
    calc (relCurve C R).resHom
          (inf_le_left : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)
            ≤ A.pieces (Sum.inl i)) (r i)
        - (relCurve C R).resHom inf_le_right (r j)
        = gluedToIdeal₀ A a (hV i j)
            (idealToGlued₀ A a (hV i j) _ (hgerm i j)) :=
          (gluedToIdeal₀_idealToGlued₀ (hV i j) _ (hgerm i j)).symm
      _ = gluedToIdeal₀ A a (hV i j)
            (secRes ((A.thetaIdealDatum a).sheaf)
              (inf_le_left : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)
                ≤ A.pieces (Sum.inl i)) (b i)
              - secRes ((A.thetaIdealDatum a).sheaf)
                (inf_le_right : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)
                  ≤ A.pieces (Sum.inl j)) (b j)) :=
          congrArg (gluedToIdeal₀ A a (hV i j)) (hb i j)
      _ = gluedToIdeal₀ A a (hV i j)
            (secRes ((A.thetaIdealDatum a).sheaf)
              (inf_le_left : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)
                ≤ A.pieces (Sum.inl i)) (b i))
          - gluedToIdeal₀ A a (hV i j)
              (secRes ((A.thetaIdealDatum a).sheaf)
                (inf_le_right : A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)
                  ≤ A.pieces (Sum.inl j)) (b j)) :=
          gluedToIdeal₀_sub (hV i j) _ _
      _ = (relCurve C R).resHom inf_le_left
            (gluedToIdeal₀ A a (A.pieces_inl_le i) (b i))
          - (relCurve C R).resHom inf_le_right
              (gluedToIdeal₀ A a (A.pieces_inl_le j) (b j)) := by
          rw [hnat_i, hnat_j]
  -- glue the corrected representatives to a chart section
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' (relCurve C R).sheaf
    (fun i : Fin A.m₀ => A.pieces (Sum.inl i))
    (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀)
    (fun i => homOfLE (le_inf le_top (A.pieces_inl_le i)))
    (fun x hx => by
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (A.cover₀ hx.2)
      exact Opens.mem_iSup.mpr ⟨i, hi⟩)
    (fun i => r i - gluedToIdeal₀ A a (A.pieces_inl_le i) (b i))
    (fun i j => by
      change (relCurve C R).resHom inf_le_left
          (r i - gluedToIdeal₀ A a (A.pieces_inl_le i) (b i))
        = (relCurve C R).resHom inf_le_right
            (r j - gluedToIdeal₀ A a (A.pieces_inl_le j) (b j))
      rw [map_sub, map_sub]
      linear_combination hkey i j)
  obtain ⟨σ', hσ'⟩ : ∃ σ' : Γ(relCurve C R, ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀),
      ∀ i : Fin A.m₀, (relCurve C R).resHom (le_inf le_top (A.pieces_inl_le i)) σ'
        = r i - gluedToIdeal₀ A a (A.pieces_inl_le i) (b i) :=
    ⟨σ, fun i => hσ i⟩
  refine ⟨σ', fun i => ?_⟩
  rw [hσ' i, map_sub, hr i, sub_eq_self, Ideal.Quotient.eq_zero_iff_mem]
  exact Scheme.mem_span_singleton_of_forall_germ
    (fun z hz => A.eqn_regular (Sum.inl i) z hz)
    (fun z hz => by
      rw [A.germ_eqn_span_eq_stalkIdeal (Sum.inl i) hz]
      exact germ_gluedToIdeal₀_mem (A.pieces_inl_le i) (b i) z hz)

/-- **The chart-1 lifting input holds unconditionally**. -/
theorem liftsOnChart₁ (A : DivisorAdaptation C R π d) (a : ℕ) : A.LiftsOnChart₁ a := by
  intro w hw
  choose r hr using fun j : Fin A.m₁ => Ideal.Quotient.mk_surjective (w (Sum.inr j))
  have hdiff : ∀ i j : Fin A.m₁,
      (relCurve C R).resHom
          (inf_le_left : A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)
            ≤ A.pieces (Sum.inr i)) (r i)
        - (relCurve C R).resHom inf_le_right (r j)
        ∈ A.ovlIdeal (Sum.inr i) (Sum.inr j) := by
    intro i j
    have hmatch := (A.mem_thetaGluedSubmodule_iff a w).mp hw (Sum.inr i, Sum.inr j)
    dsimp only at hmatch
    rw [← hr i, ← hr j, toOvlLeft_mk, toOvlRight_mk,
      FinCoverData.thetaOvlUnit_inr_inr, Units.val_one, map_one, one_mul,
      ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at hmatch
    exact hmatch
  have hgerm : ∀ (i j : Fin A.m₁) (z : relCurve C R)
      (hz : z ∈ A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)),
      ((relCurve C R).presheaf.germ (A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j))
        z hz).hom
        ((relCurve C R).resHom
            (inf_le_left : A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)
              ≤ A.pieces (Sum.inr i)) (r i)
          - (relCurve C R).resHom inf_le_right (r j)) ∈ d.stalkIdeal z :=
    fun i j z hz => germ_mem_stalkIdeal_of_mem_ovlIdeal (hdiff i j) z hz
  have hV : ∀ i j : Fin A.m₁,
      A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)
        ≤ (relCover C R (fiberTwoCover π)).V₁ :=
    fun i j => inf_le_left.trans (A.pieces_inr_le i)
  have hc : ∀ i j l : Fin A.m₁,
      secRes ((A.thetaIdealDatum a).sheaf)
          (inf_le_inf_right ((relCurve C R).basicOpen (A.h₁ l)) inf_le_left)
          (idealToGlued₁ A a (hV i l) _ (hgerm i l))
        = secRes ((A.thetaIdealDatum a).sheaf) inf_le_left
            (idealToGlued₁ A a (hV i j) _ (hgerm i j))
          + secRes ((A.thetaIdealDatum a).sheaf)
              (inf_le_inf_right ((relCurve C R).basicOpen (A.h₁ l)) inf_le_right)
              (idealToGlued₁ A a (hV j l) _ (hgerm j l)) := by
    intro i j l
    refine gluedSections_ext₁
      ((inf_le_left.trans inf_le_left).trans (A.pieces_inr_le i) :
        A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j) ⊓ A.pieces (Sum.inr l)
          ≤ (relCover C R (fiberTwoCover π)).V₁) (fun j' => ?_)
    have hOj' : A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j) ⊓ A.pieces (Sum.inr l)
        ⊓ A.pieces (Sum.inr j') ≤ A.pieces (Sum.inr j') := inf_le_right
    have e_il := eqn_mul_idealToGlued₁_inr (A := A) (a := a) (hV i l) _ (hgerm i l) j'
      (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_left.trans inf_le_right) :
        A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j) ⊓ A.pieces (Sum.inr l)
          ⊓ A.pieces (Sum.inr j')
          ≤ A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr l)) hOj'
    have e_ij := eqn_mul_idealToGlued₁_inr (A := A) (a := a) (hV i j) _ (hgerm i j) j'
      (inf_le_left.trans inf_le_left :
        A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j) ⊓ A.pieces (Sum.inr l)
          ⊓ A.pieces (Sum.inr j')
          ≤ A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)) hOj'
    have e_jl := eqn_mul_idealToGlued₁_inr (A := A) (a := a) (hV j l) _ (hgerm j l) j'
      (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (inf_le_left.trans inf_le_right) :
        A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j) ⊓ A.pieces (Sum.inr l)
          ⊓ A.pieces (Sum.inr j')
          ≤ A.pieces (Sum.inr j) ⊓ A.pieces (Sum.inr l)) hOj'
    rw [map_sub] at e_il e_ij e_jl
    simp only [Scheme.resHom_resHom] at e_il e_ij e_jl
    have key : (relCurve C R).resHom
        (le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
          (inf_le_left.trans inf_le_right)) hOj')
        ((idealToGlued₁ A a (hV i l) _ (hgerm i l)).val (Sum.inr (ULift.up j')))
        = (relCurve C R).resHom
            (le_inf (inf_le_left.trans inf_le_left) hOj')
            ((idealToGlued₁ A a (hV i j) _ (hgerm i j)).val (Sum.inr (ULift.up j')))
          + (relCurve C R).resHom
              (le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
                (inf_le_left.trans inf_le_right)) hOj')
              ((idealToGlued₁ A a (hV j l) _ (hgerm j l)).val
                (Sum.inr (ULift.up j'))) := by
      refine A.eqn_res_cancel (Sum.inr j') hOj' ?_
      rw [mul_add]
      linear_combination e_il - e_ij - e_jl
    exact key
  obtain ⟨b, hb⟩ := IsAffineOpen.exists_cech_cobounding_of_qcoh
    (F := (A.thetaIdealDatum a).sheaf)
    (relCover_isAffineOpen₁ C R (fiberTwoCover π)) A.h₁ (iSup_basicOpen_h₁ A)
    (fun i j => idealToGlued₁ A a (hV i j) _ (hgerm i j)) hc
  have hkey : ∀ i j : Fin A.m₁,
      (relCurve C R).resHom
          (inf_le_left : A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)
            ≤ A.pieces (Sum.inr i)) (r i)
        - (relCurve C R).resHom inf_le_right (r j)
        = (relCurve C R).resHom inf_le_left
            (gluedToIdeal₁ A a (A.pieces_inr_le i) (b i))
          - (relCurve C R).resHom inf_le_right
              (gluedToIdeal₁ A a (A.pieces_inr_le j) (b j)) := by
    intro i j
    have hnat_i : gluedToIdeal₁ A a (hV i j)
        (secRes ((A.thetaIdealDatum a).sheaf)
          (inf_le_left : A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)
            ≤ A.pieces (Sum.inr i)) (b i))
        = (relCurve C R).resHom inf_le_left
            (gluedToIdeal₁ A a (A.pieces_inr_le i) (b i)) :=
      gluedToIdeal₁_secRes inf_le_left (A.pieces_inr_le i) (b i)
    have hnat_j : gluedToIdeal₁ A a (hV i j)
        (secRes ((A.thetaIdealDatum a).sheaf)
          (inf_le_right : A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)
            ≤ A.pieces (Sum.inr j)) (b j))
        = (relCurve C R).resHom inf_le_right
            (gluedToIdeal₁ A a (A.pieces_inr_le j) (b j)) :=
      gluedToIdeal₁_secRes inf_le_right (A.pieces_inr_le j) (b j)
    calc (relCurve C R).resHom
          (inf_le_left : A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)
            ≤ A.pieces (Sum.inr i)) (r i)
        - (relCurve C R).resHom inf_le_right (r j)
        = gluedToIdeal₁ A a (hV i j)
            (idealToGlued₁ A a (hV i j) _ (hgerm i j)) :=
          (gluedToIdeal₁_idealToGlued₁ (hV i j) _ (hgerm i j)).symm
      _ = gluedToIdeal₁ A a (hV i j)
            (secRes ((A.thetaIdealDatum a).sheaf)
              (inf_le_left : A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)
                ≤ A.pieces (Sum.inr i)) (b i)
              - secRes ((A.thetaIdealDatum a).sheaf)
                (inf_le_right : A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)
                  ≤ A.pieces (Sum.inr j)) (b j)) :=
          congrArg (gluedToIdeal₁ A a (hV i j)) (hb i j)
      _ = gluedToIdeal₁ A a (hV i j)
            (secRes ((A.thetaIdealDatum a).sheaf)
              (inf_le_left : A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)
                ≤ A.pieces (Sum.inr i)) (b i))
          - gluedToIdeal₁ A a (hV i j)
              (secRes ((A.thetaIdealDatum a).sheaf)
                (inf_le_right : A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)
                  ≤ A.pieces (Sum.inr j)) (b j)) :=
          gluedToIdeal₁_sub (hV i j) _ _
      _ = (relCurve C R).resHom inf_le_left
            (gluedToIdeal₁ A a (A.pieces_inr_le i) (b i))
          - (relCurve C R).resHom inf_le_right
              (gluedToIdeal₁ A a (A.pieces_inr_le j) (b j)) := by
          rw [hnat_i, hnat_j]
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' (relCurve C R).sheaf
    (fun j : Fin A.m₁ => A.pieces (Sum.inr j))
    (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁)
    (fun j => homOfLE (le_inf le_top (A.pieces_inr_le j)))
    (fun x hx => by
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (A.cover₁ hx.2)
      exact Opens.mem_iSup.mpr ⟨j, hj⟩)
    (fun j => r j - gluedToIdeal₁ A a (A.pieces_inr_le j) (b j))
    (fun i j => by
      change (relCurve C R).resHom inf_le_left
          (r i - gluedToIdeal₁ A a (A.pieces_inr_le i) (b i))
        = (relCurve C R).resHom inf_le_right
            (r j - gluedToIdeal₁ A a (A.pieces_inr_le j) (b j))
      rw [map_sub, map_sub]
      linear_combination hkey i j)
  obtain ⟨σ', hσ'⟩ : ∃ σ' : Γ(relCurve C R, ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁),
      ∀ j : Fin A.m₁, (relCurve C R).resHom (le_inf le_top (A.pieces_inr_le j)) σ'
        = r j - gluedToIdeal₁ A a (A.pieces_inr_le j) (b j) :=
    ⟨σ, fun j => hσ j⟩
  refine ⟨σ', fun j => ?_⟩
  rw [hσ' j, map_sub, hr j, sub_eq_self, Ideal.Quotient.eq_zero_iff_mem]
  exact Scheme.mem_span_singleton_of_forall_germ
    (fun z hz => A.eqn_regular (Sum.inr j) z hz)
    (fun z hz => by
      rw [A.germ_eqn_span_eq_stalkIdeal (Sum.inr j) hz]
      exact germ_gluedToIdeal₁_mem (A.pieces_inr_le j) (b j) z hz)

/-! ## The overlap correction from `H¹` of the datum pair -/

/-- **The overlap-correction input from the vanishing of `H¹` of the theta-ideal
datum's two-lattice pair**: an overlap section vanishing along `d` trivializes into a
glued section of `𝒪(Θᵃ − d)`, splits as a difference of chart sections by the `H¹`
hypothesis, and the assembled ideal sections realize the Θ-twisted splitting. -/
theorem relThetaOverlapCorrection_of_subsingleton_h1 (A : DivisorAdaptation C R π d)
    (a : ℕ) (hH1 : Subsingleton (datumPair (A.thetaIdealDatum a)).H1) :
    relThetaOverlapCorrection π d a := by
  intro τ hτ
  -- the trivialized overlap section
  have himg : (datumPair (A.thetaIdealDatum a)).imageLattice = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hH1
  have hn : idealToGlued₀ A a
      (inf_le_left : (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁ ≤ (relCover C R (fiberTwoCover π)).V₀)
      τ hτ ∈ LinearMap.range (datumPair (A.thetaIdealDatum a)).diff := by
    rw [TwoLatticePair.range_diff_eq, himg]
    trivial
  obtain ⟨⟨x, y⟩, hxy⟩ := hn
  rw [TwoLatticePair.diff_apply] at hxy
  refine ⟨gluedToIdeal₀ A a le_rfl x, gluedToIdeal₁ A a le_rfl y,
    fun z hz => germ_gluedToIdeal₀_mem le_rfl x z hz,
    fun z hz => germ_gluedToIdeal₁_mem le_rfl y z hz, ?_⟩
  -- read the splitting through the assemblies
  have h0 := congrArg (gluedToIdeal₀ A a
    (inf_le_left : (relCover C R (fiberTwoCover π)).V₀ ⊓
      (relCover C R (fiberTwoCover π)).V₁ ≤ (relCover C R (fiberTwoCover π)).V₀)) hxy
  rw [gluedToIdeal₀_sub, gluedToIdeal₀_idealToGlued₀] at h0
  -- the first summand: naturality of the chart-0 assembly
  have h₀ : gluedToIdeal₀ A a
      (inf_le_left : (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁ ≤ (relCover C R (fiberTwoCover π)).V₀)
      ((datumPair (A.thetaIdealDatum a)).ι₀ x)
      = (relCurve C R).resHom inf_le_left (gluedToIdeal₀ A a le_rfl x) :=
    gluedToIdeal₀_secRes inf_le_left le_rfl x
  -- the second summand: the theta comparison and naturality of the chart-1 assembly
  have h₁ : gluedToIdeal₀ A a
      (inf_le_left : (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁ ≤ (relCover C R (fiberTwoCover π)).V₀)
      ((datumPair (A.thetaIdealDatum a)).ι₁ y)
      = ((relThetaCocycle C R π a :
          Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁)ˣ) :
          Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁))
        * (relCurve C R).resHom inf_le_right (gluedToIdeal₁ A a le_rfl y) := by
    have hcmp := gluedToIdeal₀_eq_theta_mul_gluedToIdeal₁
      (le_rfl : (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁ ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓
          (relCover C R (fiberTwoCover π)).V₁)
      (secRes ((A.thetaIdealDatum a).sheaf) inf_le_right y)
    rw [Scheme.resHom_self,
      gluedToIdeal₁_secRes inf_le_right le_rfl y] at hcmp
    exact hcmp
  rw [h₀, h₁] at h0
  exact h0.symm

/-! ## Right exactness -/

variable {A : DivisorAdaptation C R π d} {a : ℕ}

/-- **Right exactness of the section sequence** (worksheet §2.3 step 2), given the
vanishing of `H¹` of the theta-ideal datum's two-lattice pair: the Θ-twisted colength
evaluation `thetaGluedEval : H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}` is surjective. -/
theorem thetaGluedEval_surjective_of_subsingleton_h1
    (hH1 : Subsingleton (datumPair (A.thetaIdealDatum a)).H1) :
    Function.Surjective (A.thetaGluedEval a) :=
  thetaGluedEval_surjective_of_liftsOnChart_of_correction
    (liftsOnChart₀ A a) (liftsOnChart₁ A a)
    (relThetaOverlapCorrection_of_subsingleton_h1 A a hH1)

/-- **Right exactness of the section sequence, engine form**: surjectivity of the
Θ-twisted colength evaluation under the complex-form fibrewise `H¹`-vanishing
hypothesis of the rigid engine (`datum_subsingleton_pairH1`, Noetherian-free).  The
discharge of `hfib` from DAT-0a at fibre degree `a·δ − deg d ≥ b` is the W6-full
fibre-restriction seam — the remaining open brick of Task 4 (a). -/
theorem thetaGluedEval_surjective (hπ : π ≫ P1.structureMap k = C.hom)
    (hfib : ∀ p : PrimeSpectrum R,
      Subsingleton ((datumPair (A.thetaIdealDatum a)).H1 ⊗[R]
        p.asIdeal.ResidueField)) :
    Function.Surjective (A.thetaGluedEval a) :=
  thetaGluedEval_surjective_of_subsingleton_h1
    (datum_subsingleton_pairH1 (A.thetaIdealDatum a) hπ hfib)

end DivisorAdaptation

end AlgebraicGeometry
