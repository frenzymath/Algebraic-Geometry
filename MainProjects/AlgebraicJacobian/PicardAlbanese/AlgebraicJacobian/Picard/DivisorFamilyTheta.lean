/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorStalkIdeal
import AlgebraicJacobian.Cohomology.RelThetaTwist

/-!
# DD-4 (Task 4) — the Θ-twisted colength module and the section evaluation

The section sequence of the DAT-D worksheet §2.3 step 2, definitional layer: for a
divisor family `d` with finite chart adaptation `A` on the relative curve `C_R` and a
twist exponent `a`, the global sections of the relative theta twist `𝒪(Θᵃ)`
(`relThetaSections`) evaluate into the **Θ-twisted colength module** `W(d)^{Θᵃ}`:

* `AlgebraicGeometry.FinCoverData.thetaOvlUnit` — the four-case twisting unit on the
  pairwise piece overlaps: `1` between pieces of the same pinned chart, the theta
  cocycle `relThetaCocycle C R π a` (resp. its inverse) across the charts.
* `DivisorAdaptation.thetaGluedSubmodule` — `W(d)^{Θᵃ}`: the equalizer-style submodule
  of `∏_j Γ(D(h_j))/(f_j)` cut by the Θ-twisted matching `s_i = θ_{ij} · s_j` on the
  overlap colengths (kernel of `deltaLeft − thetaDeltaRight`, the `FlatCokernel` shape);
  with all twisting units `1` this is the certificate module `gluedSubmodule` of DD-1.
* `DivisorAdaptation.thetaGluedEval` — **the evaluation** `H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}`:
  trivialize on each piece through the pinned chart component and reduce mod `(f_j)`;
  the twisted matching of global sections restricts to the twisted matching of the
  colengths (`thetaEval_mem`).
* `DivisorAdaptation.ker_thetaGluedEval` — **the kernel bridge (left exactness)**: the
  kernel of the evaluation is exactly the cover-independent vanishing submodule
  `d.vanishingSubmodule` of `AlgebraicJacobian.Picard.DivisorStalkIdeal` — the DD-4
  spelling of `0 → H⁰(𝒪(Θᵃ − d)) → H⁰(𝒪(Θᵃ))`.  The `⊇` direction is the stalk-locality
  of regular principal ideals (`Scheme.mem_span_singleton_of_forall_germ`), the `⊆`
  direction is the germ reading of the adaptation equations
  (`germ_eqn_span_eq_stalkIdeal`).

Exactness on the *right* (surjectivity of the evaluation — the engine fired at fibre
degree `d_M − g ≥ b` through DAT-1's `H⁰`/`H¹` clauses) is NOT proved here; it is the
remaining cohomological heart of Task 4 and is consumed as a hypothesis by the window
bookkeeping of `AlgebraicJacobian.Picard.DivisorFamilyWindow`.
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

/-- The global sections of the relative theta twist `𝒪(Θᵃ)` on `C_R`, in two-cover pair
form: pairs on the pinned charts matching through the theta cocycle. -/
noncomputable abbrev relThetaSections (C : Over (Spec (.of k))) (R : Type u) [CommRing R]
    [Algebra k R] (π : C.left ⟶ P1 k) [IsFinite π] (a : ℕ) : Type u :=
  ↥(twistSubmodule R (relCover C R (fiberTwoCover π)).V₀
    (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) ⊤)

/-! ## The components of a global theta section -/

section Components

variable (a : ℕ)

/-- **Chart-0 component of a global theta section**, restricted into `W ≤ ⊤ ⊓ V₀`, as an
`R`-linear map (the junction between the `Scheme.overModule` structure of the twisted
pair and the section-ring structures — hand-rolled so the two smul structures are
compared through `overAlgebraMap`). -/
noncomputable def relThetaResFst {W : (relCurve C R).Opens}
    (hW : W ≤ ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) :
    relThetaSections C R π a →ₗ[R] Γ(relCurve C R, W) where
  toFun x := (relCurve C R).resHom hW x.val.1
  map_add' x y := by rw [Submodule.coe_add, Prod.fst_add, map_add]
  map_smul' r x := by
    rw [RingHom.id_apply, Submodule.coe_smul, Prod.smul_fst,
      Scheme.overModule_smul_def, map_mul, Scheme.resHom,
      (relCurve C R).overAlgebraMap_apply_res R (homOfLE hW).op r]
    rfl

@[simp]
lemma relThetaResFst_apply {W : (relCurve C R).Opens}
    (hW : W ≤ ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) (x : relThetaSections C R π a) :
    relThetaResFst a hW x = (relCurve C R).resHom hW x.val.1 := rfl

/-- **Chart-1 component of a global theta section**, restricted into `W ≤ ⊤ ⊓ V₁`. -/
noncomputable def relThetaResSnd {W : (relCurve C R).Opens}
    (hW : W ≤ ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) :
    relThetaSections C R π a →ₗ[R] Γ(relCurve C R, W) where
  toFun x := (relCurve C R).resHom hW x.val.2
  map_add' x y := by rw [Submodule.coe_add, Prod.snd_add, map_add]
  map_smul' r x := by
    rw [RingHom.id_apply, Submodule.coe_smul, Prod.smul_snd,
      Scheme.overModule_smul_def, map_mul, Scheme.resHom,
      (relCurve C R).overAlgebraMap_apply_res R (homOfLE hW).op r]
    rfl

@[simp]
lemma relThetaResSnd_apply {W : (relCurve C R).Opens}
    (hW : W ≤ ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) (x : relThetaSections C R π a) :
    relThetaResSnd a hW x = (relCurve C R).resHom hW x.val.2 := rfl

/-- **The global theta matching, restricted below the chart overlap**: for `W ≤ V₀ ⊓ V₁`
the two components of a global theta section match through the restricted theta
cocycle. -/
lemma relThetaSections_matching (x : relThetaSections C R π a) {W : (relCurve C R).Opens}
    (hW : W ≤ (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁) :
    (relCurve C R).resHom (le_inf le_top (hW.trans inf_le_left)) x.val.1
      = (relCurve C R).resHom hW
          ((relThetaCocycle C R π a : Γ(relCurve C R,
            (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)))
        * (relCurve C R).resHom (le_inf le_top (hW.trans inf_le_right)) x.val.2 := by
  have hx := (mem_twistSubmodule_iff R (relCover C R (fiberTwoCover π)).V₀
    (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) x.val).mp x.property
  have key := congrArg ((relCurve C R).resHom
    (le_inf (le_inf le_top (hW.trans inf_le_left)) (hW.trans inf_le_right) :
      W ≤ ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁))
    hx
  rw [map_mul] at key
  simpa only [Scheme.resHom_resHom] using key

end Components

/-! ## The piece inclusions and the theta overlap units -/

namespace FinCoverData

variable (D : FinCoverData C R π)

/-- The chart-0 pieces sit inside the pinned chart `V₀ᴿ`. -/
lemma pieces_inl_le (j : Fin D.m₀) :
    D.pieces (Sum.inl j) ≤ (relCover C R (fiberTwoCover π)).V₀ := by
  rw [pieces_inl]
  exact (relCurve C R).basicOpen_le (D.h₀ j)

/-- The chart-1 pieces sit inside the pinned chart `V₁ᴿ`. -/
lemma pieces_inr_le (j : Fin D.m₁) :
    D.pieces (Sum.inr j) ≤ (relCover C R (fiberTwoCover π)).V₁ := by
  rw [pieces_inr]
  exact (relCurve C R).basicOpen_le (D.h₁ j)

/-- **The theta twisting unit of an ordered pair of pieces**: `1` between pieces of the
same pinned chart, the theta cocycle restricted to the overlap from chart 0 to chart 1,
its inverse from chart 1 to chart 0. -/
noncomputable def thetaOvlUnit (a : ℕ) :
    ∀ i j : D.index, Γ(relCurve C R, D.pieces i ⊓ D.pieces j)ˣ
  | Sum.inl _, Sum.inl _ => 1
  | Sum.inl j₀, Sum.inr j₁ =>
      (relCurve C R).unitsRestrict
        (inf_le_inf (D.pieces_inl_le j₀) (D.pieces_inr_le j₁)) (relThetaCocycle C R π a)
  | Sum.inr j₁, Sum.inl j₀ =>
      ((relCurve C R).unitsRestrict
        (le_inf (inf_le_right.trans (D.pieces_inl_le j₀))
          (inf_le_left.trans (D.pieces_inr_le j₁))) (relThetaCocycle C R π a))⁻¹
  | Sum.inr _, Sum.inr _ => 1

@[simp]
lemma thetaOvlUnit_inl_inl (a : ℕ) (i j : Fin D.m₀) :
    D.thetaOvlUnit a (Sum.inl i) (Sum.inl j) = 1 := rfl

@[simp]
lemma thetaOvlUnit_inr_inr (a : ℕ) (i j : Fin D.m₁) :
    D.thetaOvlUnit a (Sum.inr i) (Sum.inr j) = 1 := rfl

lemma thetaOvlUnit_inl_inr (a : ℕ) (j₀ : Fin D.m₀) (j₁ : Fin D.m₁) :
    D.thetaOvlUnit a (Sum.inl j₀) (Sum.inr j₁)
      = (relCurve C R).unitsRestrict
          (inf_le_inf (D.pieces_inl_le j₀) (D.pieces_inr_le j₁))
          (relThetaCocycle C R π a) := rfl

lemma thetaOvlUnit_inr_inl (a : ℕ) (j₁ : Fin D.m₁) (j₀ : Fin D.m₀) :
    D.thetaOvlUnit a (Sum.inr j₁) (Sum.inl j₀)
      = ((relCurve C R).unitsRestrict
          (le_inf (inf_le_right.trans (D.pieces_inl_le j₀))
            (inf_le_left.trans (D.pieces_inr_le j₁))) (relThetaCocycle C R π a))⁻¹ := rfl

end FinCoverData

/-! ## The Θ-twisted glued colength module `W(d)^{Θᵃ}` -/

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d) (a : ℕ)

/-- The underlying section of a restricted unit is the restriction of the underlying
section. -/
private lemma val_unitsRestrict {W U : (relCurve C R).Opens} (h : W ≤ U)
    (u : Γ(relCurve C R, U)ˣ) :
    (((relCurve C R).unitsRestrict h u : Γ(relCurve C R, W)ˣ) : Γ(relCurve C R, W))
      = (relCurve C R).resHom h (u : Γ(relCurve C R, U)) := rfl

/-- `relResAlgHom` is `resHom` on elements. -/
private lemma relRes_eq {W U : (relCurve C R).Opens} (h : W ≤ U)
    (s : Γ(relCurve C R, U)) :
    relResAlgHom C R h s = (relCurve C R).resHom h s := rfl

/-- **The Θ-twisted right overlap arrow**: restrict the `p.2` component to each overlap
and multiply by the theta twisting unit of the pair. -/
noncomputable def thetaDeltaRight : A.chartProd →ₗ[R] A.ovlProd :=
  LinearMap.pi (fun p : A.index × A.index =>
    LinearMap.mulLeft R (Ideal.Quotient.mk (A.ovlIdeal p.1 p.2)
        ((A.thetaOvlUnit a p.1 p.2 :
          Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2)ˣ) :
          Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2))) ∘ₗ
      (A.toOvlRight p.1 p.2).toLinearMap ∘ₗ LinearMap.proj p.2)

/-- **The Θ-twisted glued colength module `W(d)^{Θᵃ}`** (worksheet §2.3 step 2): the
submodule of the product of chart-local colengths cut by the Θ-twisted matching on the
overlap colengths, spelled as a kernel so the `FlatCokernel` base-change shapes apply. -/
noncomputable def thetaGluedSubmodule : Submodule R A.chartProd :=
  LinearMap.ker (A.deltaLeft - A.thetaDeltaRight a)

/-- The twisted-equalizer description of `W(d)^{Θᵃ}`. -/
lemma mem_thetaGluedSubmodule_iff (s : A.chartProd) :
    s ∈ A.thetaGluedSubmodule a ↔ ∀ p : A.index × A.index,
      A.toOvlLeft p.1 p.2 (s p.1)
        = Ideal.Quotient.mk (A.ovlIdeal p.1 p.2)
            ((A.thetaOvlUnit a p.1 p.2 :
              Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2)ˣ) :
              Γ(relCurve C R, A.pieces p.1 ⊓ A.pieces p.2))
          * A.toOvlRight p.1 p.2 (s p.2) := by
  simp only [thetaGluedSubmodule, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    funext_iff, deltaLeft, thetaDeltaRight, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply,
    LinearMap.mulLeft_apply]

/-- The Θ-twisted glued colength module, as a type. -/
noncomputable abbrev ThetaGlued : Type u := ↥(A.thetaGluedSubmodule a)

/-! ## The evaluation `H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}` -/

/-- The per-piece evaluation of a global theta section: restrict the pinned chart
component to the piece and reduce mod `(f_j)`. -/
noncomputable def thetaPieceEval :
    ∀ j : A.index, relThetaSections C R π a →ₗ[R] A.colength j
  | Sum.inl j₀ =>
      (Ideal.Quotient.mkₐ R (Ideal.span {A.eqn (Sum.inl j₀)})).toLinearMap ∘ₗ
        relThetaResFst a (le_inf le_top (A.pieces_inl_le j₀))
  | Sum.inr j₁ =>
      (Ideal.Quotient.mkₐ R (Ideal.span {A.eqn (Sum.inr j₁)})).toLinearMap ∘ₗ
        relThetaResSnd a (le_inf le_top (A.pieces_inr_le j₁))

/-- **The section evaluation into the chart product**. -/
noncomputable def thetaEval : relThetaSections C R π a →ₗ[R] A.chartProd :=
  LinearMap.pi (A.thetaPieceEval a)

@[simp]
lemma thetaEval_apply_inl (x : relThetaSections C R π a) (j₀ : Fin A.m₀) :
    A.thetaEval a x (Sum.inl j₀)
      = Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inl j₀)})
          ((relCurve C R).resHom (le_inf le_top (A.pieces_inl_le j₀)) x.val.1) := rfl

@[simp]
lemma thetaEval_apply_inr (x : relThetaSections C R π a) (j₁ : Fin A.m₁) :
    A.thetaEval a x (Sum.inr j₁)
      = Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inr j₁)})
          ((relCurve C R).resHom (le_inf le_top (A.pieces_inr_le j₁)) x.val.2) := rfl

/-- The overlap arrows on a reduced section: `toOvlLeft` restricts into the overlap. -/
lemma toOvlLeft_mk (i j : A.index) (s : Γ(relCurve C R, A.pieces i)) :
    A.toOvlLeft i j (Ideal.Quotient.mk (Ideal.span {A.eqn i}) s)
      = Ideal.Quotient.mk (A.ovlIdeal i j)
          ((relCurve C R).resHom inf_le_left s) := rfl

/-- The overlap arrows on a reduced section: `toOvlRight` restricts into the overlap. -/
lemma toOvlRight_mk (i j : A.index) (s : Γ(relCurve C R, A.pieces j)) :
    A.toOvlRight i j (Ideal.Quotient.mk (Ideal.span {A.eqn j}) s)
      = Ideal.Quotient.mk (A.ovlIdeal i j)
          ((relCurve C R).resHom inf_le_right s) := rfl

/-- **The evaluation lands in the Θ-twisted glued module**: the global matching through
the theta cocycle restricts, on each pairwise piece overlap, to the Θ-twisted matching
of the colengths. -/
theorem thetaEval_mem (x : relThetaSections C R π a) :
    A.thetaEval a x ∈ A.thetaGluedSubmodule a := by
  rw [mem_thetaGluedSubmodule_iff]
  rintro ⟨i, j⟩
  rcases i with j₀ | j₁ <;> rcases j with i₀ | i₁
  · -- chart 0 / chart 0: both components restrict from `x.val.1`
    rw [thetaEval_apply_inl, thetaEval_apply_inl, toOvlLeft_mk, toOvlRight_mk,
      FinCoverData.thetaOvlUnit_inl_inl, Units.val_one, map_one, one_mul,
      Scheme.resHom_resHom, Scheme.resHom_resHom]
  · -- chart 0 / chart 1: the theta matching restricted to the overlap
    rw [thetaEval_apply_inl, thetaEval_apply_inr, toOvlLeft_mk, toOvlRight_mk,
      FinCoverData.thetaOvlUnit_inl_inr, val_unitsRestrict,
      Scheme.resHom_resHom, Scheme.resHom_resHom, ← map_mul]
    exact congrArg _ (relThetaSections_matching a x
      (inf_le_inf (A.pieces_inl_le j₀) (A.pieces_inr_le i₁)))
  · -- chart 1 / chart 0: the inverse matching
    rw [thetaEval_apply_inr, thetaEval_apply_inl, toOvlLeft_mk, toOvlRight_mk,
      FinCoverData.thetaOvlUnit_inr_inl,
      Scheme.resHom_resHom, Scheme.resHom_resHom, ← map_mul]
    refine congrArg _ ?_
    have key := relThetaSections_matching a x
      (le_inf (inf_le_right.trans (A.pieces_inl_le i₀))
        (inf_le_left.trans (A.pieces_inr_le j₁)))
    rw [← val_unitsRestrict] at key
    rw [key, ← mul_assoc, Units.inv_mul, one_mul]
  · -- chart 1 / chart 1: both components restrict from `x.val.2`
    rw [thetaEval_apply_inr, thetaEval_apply_inr, toOvlLeft_mk, toOvlRight_mk,
      FinCoverData.thetaOvlUnit_inr_inr, Units.val_one, map_one, one_mul,
      Scheme.resHom_resHom, Scheme.resHom_resHom]

/-- **The evaluation `H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ}`** (worksheet §2.3 step 2, the middle-right
arrow of the section sequence).  Surjectivity — exactness on the right, the engine at
fibre degree `d_M − g ≥ b` — is the open cohomological heart of Task 4. -/
noncomputable def thetaGluedEval : relThetaSections C R π a →ₗ[R] A.ThetaGlued a :=
  LinearMap.codRestrict (A.thetaGluedSubmodule a) (A.thetaEval a) (A.thetaEval_mem a)

lemma thetaGluedEval_coe (x : relThetaSections C R π a) :
    (A.thetaGluedEval a x : A.chartProd) = A.thetaEval a x := rfl

/-! ## The kernel bridge: left exactness of the section sequence -/

/-- **The germ of an adaptation equation spans the stalk ideal of the family**: through
the pointwise clause `eqn_rel j z` at the point `z` itself, `germ_z f_j` and
`germ_z (d.eqn z)` are associated at every `z` in the piece. -/
theorem germ_eqn_span_eq_stalkIdeal (j : A.index) {z : relCurve C R}
    (hz : z ∈ A.pieces j) :
    Ideal.span {((relCurve C R).presheaf.germ (A.pieces j) z hz).hom (A.eqn j)}
      = d.stalkIdeal z := by
  obtain ⟨u, hu⟩ := A.eqn_rel j z
  have hzW : z ∈ A.pieces j ⊓ d.cover.opens z := ⟨hz, d.cover.mem_opens z⟩
  have hgerm : ((relCurve C R).presheaf.germ (A.pieces j) z hz).hom (A.eqn j)
      = ((relCurve C R).presheaf.germ (A.pieces j ⊓ d.cover.opens z) z hzW).hom
          (u : Γ(relCurve C R, A.pieces j ⊓ d.cover.opens z))
        * ((relCurve C R).presheaf.germ (d.cover.opens z) z
            (d.cover.mem_opens z)).hom (d.eqn z) := by
    have h := congrArg ((relCurve C R).presheaf.germ
      (A.pieces j ⊓ d.cover.opens z) z hzW).hom hu
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
    exact h
  rw [hgerm, Ideal.span_singleton_mul_left_unit (u.isUnit.map
    ((relCurve C R).presheaf.germ (A.pieces j ⊓ d.cover.opens z) z hzW).hom)]
  exact d.germ_eqn_span_eq z z (d.cover.mem_opens z)

/-- The kernel of the corestricted evaluation is the kernel of the evaluation. -/
lemma ker_thetaGluedEval_eq_ker :
    LinearMap.ker (A.thetaGluedEval a) = LinearMap.ker (A.thetaEval a) :=
  LinearMap.ker_codRestrict _ _ _

/-- **The kernel bridge (Task 4, left exactness)**: the kernel of the Θ-twisted colength
evaluation is exactly the cover-independent vanishing submodule of the family — the
DD-4 spelling of `H⁰(𝒪(Θᵃ − d)) = ker (H⁰(𝒪(Θᵃ)) → W(d)^{Θᵃ})`.  In particular the
kernel does not depend on the adaptation, only on the divisor of `d`. -/
theorem ker_thetaGluedEval :
    LinearMap.ker (A.thetaGluedEval a)
      = d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
          (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) := by
  rw [ker_thetaGluedEval_eq_ker]
  ext x
  rw [LinearMap.mem_ker, Scheme.LocalEquations.mem_vanishingSubmodule_iff, funext_iff]
  constructor
  · -- evaluation zero ⟹ all germs in the stalk ideals
    intro hker
    constructor
    · intro z hz
      obtain ⟨j₀, hj₀⟩ := Opens.mem_iSup.mp (A.cover₀ hz.2)
      have hres : (relCurve C R).resHom (le_inf le_top (A.pieces_inl_le j₀)) x.val.1
          ∈ Ideal.span {A.eqn (Sum.inl j₀)} := by
        have := hker (Sum.inl j₀)
        rw [thetaEval_apply_inl, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at this
        exact this
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hres
      have hgerm := congrArg
        ((relCurve C R).presheaf.germ (A.pieces (Sum.inl j₀)) z hj₀).hom hc
      rw [map_mul] at hgerm
      have hswap : ((relCurve C R).presheaf.germ (A.pieces (Sum.inl j₀)) z hj₀).hom
          ((relCurve C R).resHom (le_inf le_top (A.pieces_inl_le j₀)) x.val.1)
          = ((relCurve C R).presheaf.germ
              (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) z hz).hom x.val.1 :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      rw [hswap] at hgerm
      rw [← A.germ_eqn_span_eq_stalkIdeal (Sum.inl j₀) hj₀, hgerm]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · intro z hz
      obtain ⟨j₁, hj₁⟩ := Opens.mem_iSup.mp (A.cover₁ hz.2)
      have hres : (relCurve C R).resHom (le_inf le_top (A.pieces_inr_le j₁)) x.val.2
          ∈ Ideal.span {A.eqn (Sum.inr j₁)} := by
        have := hker (Sum.inr j₁)
        rw [thetaEval_apply_inr, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at this
        exact this
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hres
      have hgerm := congrArg
        ((relCurve C R).presheaf.germ (A.pieces (Sum.inr j₁)) z hj₁).hom hc
      rw [map_mul] at hgerm
      have hswap : ((relCurve C R).presheaf.germ (A.pieces (Sum.inr j₁)) z hj₁).hom
          ((relCurve C R).resHom (le_inf le_top (A.pieces_inr_le j₁)) x.val.2)
          = ((relCurve C R).presheaf.germ
              (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) z hz).hom x.val.2 :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      rw [hswap] at hgerm
      rw [← A.germ_eqn_span_eq_stalkIdeal (Sum.inr j₁) hj₁, hgerm]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · -- all germs in the stalk ideals ⟹ evaluation zero, by stalk-locality of `(f_j)`
    rintro ⟨h₀, h₁⟩ j
    rcases j with j₀ | j₁
    · rw [thetaEval_apply_inl, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
      refine Scheme.mem_span_singleton_of_forall_germ
        (fun z hz => A.eqn_regular (Sum.inl j₀) z hz) (fun z hz => ?_)
      have hswap : ((relCurve C R).presheaf.germ (A.pieces (Sum.inl j₀)) z hz).hom
          ((relCurve C R).resHom (le_inf le_top (A.pieces_inl_le j₀)) x.val.1)
          = ((relCurve C R).presheaf.germ
              (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀) z
              (le_inf le_top (A.pieces_inl_le j₀) hz)).hom x.val.1 :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      rw [hswap, A.germ_eqn_span_eq_stalkIdeal (Sum.inl j₀) hz]
      exact h₀ z _
    · rw [thetaEval_apply_inr, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
      refine Scheme.mem_span_singleton_of_forall_germ
        (fun z hz => A.eqn_regular (Sum.inr j₁) z hz) (fun z hz => ?_)
      have hswap : ((relCurve C R).presheaf.germ (A.pieces (Sum.inr j₁)) z hz).hom
          ((relCurve C R).resHom (le_inf le_top (A.pieces_inr_le j₁)) x.val.2)
          = ((relCurve C R).presheaf.germ
              (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁) z
              (le_inf le_top (A.pieces_inr_le j₁) hz)).hom x.val.2 :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      rw [hswap, A.germ_eqn_span_eq_stalkIdeal (Sum.inr j₁) hz]
      exact h₁ z _

end DivisorAdaptation

end AlgebraicGeometry
