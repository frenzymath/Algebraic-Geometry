/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafDatum
import AlgebraicJacobian.Picard.LocalEquationsPullback
import AlgebraicJacobian.RiemannRoch.ChartColength
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Certified divisor families: the DD-1 carrier (`informal/spec-dd-1.md` §1)

The Wave-4 DAT-D divisor functor's object data over an affine test `R`, the worksheet's
(D1) pin (`informal/dat-d-worksheet.md` §1.1): a `LocalEquations` system `d` on the
relative curve `C_R = relCurve C R`, a **finite chart adaptation** refining it — finitely
many basic opens `D(h_j)` of the two pinned charts with partition witnesses, carrying
regular equations `f_j` that agree with `d`'s equations up to units — and the **colength
certificate**: the chart-local colength modules `Γ(D(h_j))/(f_j)` are finite projective
over `R`, and the glued equalizer module `W(d)` is finite projective of constant fibre
rank `n` (`Module.rankAtStalk`), with the two flat-cokernel clauses (c3)/(c4) that make
certificates base-change (`AlgebraicJacobian.Picard.FlatCokernel`).

* `AlgebraicGeometry.FinCoverData` — the `Fin`-indexed basic-open cover data (`Type u`;
  DAT-1's `BasicOpenCoverData` shape is `Type (u+1)`, unusable inside a functor value).
* `AlgebraicGeometry.DivisorAdaptation` — the adaptation: equations + the pointwise
  refinement-up-to-units clause `eqn_rel` (point-free, so it pulls back along arbitrary
  morphisms), with the anchored constructor `DivisorAdaptation.ofAnchors`.
* `DivisorAdaptation.gluedSubmodule` — the glued colength module
  `W(d) = ker (δ⁻ − δ⁺) ⊆ Π_j Γ(D(h_j))/(f_j)`, with the equalizer description
  `mem_gluedSubmodule_iff` (the worksheet's `eq(∏_j ⇉ ∏_{j,j'})`).
* `DivisorAdaptation.IsCertified` — the certificate (c1)–(c4).
* `AlgebraicGeometry.Scheme.LocalEquations.DivEq` — divisor equality of local-equation
  systems: on a common refinement the equations agree up to units (refinement +
  rescaling in one move), an equivalence relation with
  `picClass_eq_of_divEq` (the class laws `picClass_restrict`/`picClass_rescale`).
* `AlgebraicGeometry.CertifiedDivisorFamily`, `AlgebraicGeometry.DivFam` — the certified
  family and the setoid quotient `DivFam C π n R : Type u`, the divisor functor's value
  on the affine test `R`, with `DivFam.picClass`.

The `R`-algebra structure on section rings is `Scheme.overSectionsAlgebra` through
`relCurve.instOver` (LOCAL instances, house rule) — consumers must activate the same
instances.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## Divisor equality of local-equation systems (the setoid relation)

Generic in the scheme; this is pure `DivisorClass`-level material. -/

namespace Scheme.LocalEquations

variable {X : Scheme.{u}}

/-- Restriction of a section along `W ≤ V ≤ U` composes to restriction along `W ≤ U`. -/
private lemma res_res {W V U : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s)
      = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- **Divisor equality** of two local-equation systems: on a common refinement of the
two covers, the equations agree up to a unit at every point — common refinement plus
unit rescaling in a single move (the `CechPic`-pattern setoid of the DD-1 spec). -/
def DivEq (d₁ d₂ : X.LocalEquations) : Prop :=
  ∃ (𝒲 : X.PointedCover) (h₁ : 𝒲 ≤ d₁.cover) (h₂ : 𝒲 ≤ d₂.cover),
    ∀ x : X, ∃ u : Γ(X, 𝒲.opens x)ˣ,
      (X.presheaf.map (homOfLE (h₁ x)).op).hom (d₁.eqn x)
        = (u : Γ(X, 𝒲.opens x))
          * (X.presheaf.map (homOfLE (h₂ x)).op).hom (d₂.eqn x)

lemma divEq_refl (d : X.LocalEquations) : DivEq d d :=
  ⟨d.cover, le_rfl, le_rfl, fun _ => ⟨1, by rw [Units.val_one, one_mul]⟩⟩

lemma DivEq.symm {d₁ d₂ : X.LocalEquations} (h : DivEq d₁ d₂) : DivEq d₂ d₁ := by
  obtain ⟨𝒲, h₁, h₂, H⟩ := h
  refine ⟨𝒲, h₂, h₁, fun x => ?_⟩
  obtain ⟨u, hu⟩ := H x
  exact ⟨u⁻¹, by
    rw [hu, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]⟩

lemma DivEq.trans {d₁ d₂ d₃ : X.LocalEquations} (h : DivEq d₁ d₂) (h' : DivEq d₂ d₃) :
    DivEq d₁ d₃ := by
  obtain ⟨𝒲, h₁, h₂, H⟩ := h
  obtain ⟨𝒱, k₂, k₃, K⟩ := h'
  refine ⟨𝒲 ⊓ 𝒱, fun x => (inf_le_left (b := 𝒱.opens x)).trans (h₁ x),
    fun x => (inf_le_right (a := 𝒲.opens x)).trans (k₃ x), fun x => ?_⟩
  obtain ⟨u, hu⟩ := H x
  obtain ⟨v, hv⟩ := K x
  have E1 := congrArg (X.presheaf.map (homOfLE
    (inf_le_left : 𝒲.opens x ⊓ 𝒱.opens x ≤ 𝒲.opens x)).op).hom hu
  rw [map_mul, res_res, res_res] at E1
  have E2 := congrArg (X.presheaf.map (homOfLE
    (inf_le_right : 𝒲.opens x ⊓ 𝒱.opens x ≤ 𝒱.opens x)).op).hom hv
  rw [map_mul, res_res, res_res] at E2
  refine ⟨X.unitsRestrict inf_le_left u * X.unitsRestrict inf_le_right v, ?_⟩
  have hcast : ∀ (w : Γ(X, 𝒲.opens x ⊓ 𝒱.opens x)ˣ), (w : Γ(X, 𝒲.opens x ⊓ 𝒱.opens x))
      = w.val := fun _ => rfl
  rw [Units.val_mul]
  calc (X.presheaf.map (homOfLE _).op).hom (d₁.eqn x)
      = (X.unitsRestrict inf_le_left u).val
        * (X.presheaf.map (homOfLE ((inf_le_right).trans (k₂ x))).op).hom (d₂.eqn x) := by
        rw [show (X.unitsRestrict (inf_le_left :
            𝒲.opens x ⊓ 𝒱.opens x ≤ 𝒲.opens x) u).val
            = (X.presheaf.map (homOfLE (inf_le_left :
                𝒲.opens x ⊓ 𝒱.opens x ≤ 𝒲.opens x)).op).hom u.val from rfl]
        exact E1
    _ = (X.unitsRestrict inf_le_left u).val * ((X.unitsRestrict inf_le_right v).val
        * (X.presheaf.map (homOfLE ((inf_le_right).trans (k₃ x))).op).hom (d₃.eqn x)) := by
        rw [show (X.unitsRestrict (inf_le_right :
            𝒲.opens x ⊓ 𝒱.opens x ≤ 𝒱.opens x) v).val
            = (X.presheaf.map (homOfLE (inf_le_right :
                𝒲.opens x ⊓ 𝒱.opens x ≤ 𝒱.opens x)).op).hom v.val from rfl]
        rw [E2]
    _ = (X.unitsRestrict inf_le_left u).val * (X.unitsRestrict inf_le_right v).val
        * (X.presheaf.map (homOfLE _).op).hom (d₃.eqn x) := by
        rw [mul_assoc]

/-- Structure extensionality for local-equation systems: the two `Prop` fields are
proof-irrelevant, so a system is determined by its cover and equations. -/
private lemma ext_eqn {d e : X.LocalEquations} (hcov : d.cover = e.cover)
    (heqn : d.eqn ≍ e.eqn) : d = e := by
  cases d; cases e
  cases hcov; cases heqn
  rfl

/-- **Divisor equality preserves the Picard class** (`𝒪(D)` depends only on the divisor):
restrict both systems to the common refinement (`picClass_restrict`), where they differ
by a unit rescaling (`picClass_rescale`). -/
theorem picClass_eq_of_divEq {d₁ d₂ : X.LocalEquations} (h : DivEq d₁ d₂) :
    d₁.picClass = d₂.picClass := by
  obtain ⟨𝒲, h₁, h₂, H⟩ := h
  rw [← d₁.picClass_restrict 𝒲 h₁, ← d₂.picClass_restrict 𝒲 h₂]
  have hres : d₁.restrict 𝒲 h₁ = (d₂.restrict 𝒲 h₂).rescale (fun x => (H x).choose) := by
    refine ext_eqn rfl (heq_of_eq (funext fun x => ?_))
    exact (H x).choose_spec
  rw [hres, picClass_rescale]

end Scheme.LocalEquations

/-! ## The finite chart adaptation -/

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k)

/-- **The `Fin`-indexed basic-open cover data** of the two pinned charts of the relative
curve (`informal/spec-dd-1.md` §1a): `m₀ + m₁` basic-open generators with partition
witnesses. The DAT-1 datum `BasicOpenCoverData` carries `Type u` index fields and hence
lives in `Type (u+1)`; this `Fin`-indexed form is the `Type u` carrier a functor value
can quotient. -/
structure FinCoverData [IsAffineHom π] : Type u where
  /-- The number of chart-0 pieces. -/
  m₀ : ℕ
  /-- The number of chart-1 pieces. -/
  m₁ : ℕ
  /-- The chart-0 basic-open generators. -/
  h₀ : Fin m₀ → Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀)
  /-- The chart-1 basic-open generators. -/
  h₁ : Fin m₁ → Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₁)
  /-- The chart-0 partition coefficients. -/
  a₀ : Fin m₀ → Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀)
  /-- The chart-1 partition coefficients. -/
  a₁ : Fin m₁ → Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₁)
  /-- The chart-0 partition witness. -/
  partition₀ : ∑ j : Fin m₀, a₀ j * h₀ j = 1
  /-- The chart-1 partition witness. -/
  partition₁ : ∑ j : Fin m₁, a₁ j * h₁ j = 1

namespace FinCoverData

variable {C R π} [IsAffineHom π] (D : FinCoverData C R π)

/-- The gluing index of the adaptation, `Fin m₀ ⊕ Fin m₁`. -/
abbrev index : Type := Fin D.m₀ ⊕ Fin D.m₁

/-- The pieces: the basic opens `D(h_j)` of the two pinned charts. -/
noncomputable def pieces : D.index → (relCurve C R).Opens :=
  Sum.elim (fun j => (relCurve C R).basicOpen (D.h₀ j))
    (fun j => (relCurve C R).basicOpen (D.h₁ j))

@[simp]
lemma pieces_inl (j : Fin D.m₀) :
    D.pieces (Sum.inl j) = (relCurve C R).basicOpen (D.h₀ j) := rfl

@[simp]
lemma pieces_inr (j : Fin D.m₁) :
    D.pieces (Sum.inr j) = (relCurve C R).basicOpen (D.h₁ j) := rfl

/-- The chart-0 pieces cover the pinned chart `V₀ᴿ`. -/
lemma cover₀ : (relCover C R (fiberTwoCover π)).V₀ ≤
    ⨆ j : Fin D.m₀, (relCurve C R).basicOpen (D.h₀ j) :=
  le_iSup_basicOpen_of_sum_eq_one D.a₀ D.h₀ D.partition₀

/-- The chart-1 pieces cover the pinned chart `V₁ᴿ`. -/
lemma cover₁ : (relCover C R (fiberTwoCover π)).V₁ ≤
    ⨆ j : Fin D.m₁, (relCurve C R).basicOpen (D.h₁ j) :=
  le_iSup_basicOpen_of_sum_eq_one D.a₁ D.h₁ D.partition₁

end FinCoverData

/-- Restriction of sections of the relative curve as an `R`-algebra homomorphism
(`Scheme.overSectionsAlgebra` structures on both sides). -/
noncomputable def relResAlgHom {W V : (relCurve C R).Opens} (h : W ≤ V) :
    Γ(relCurve C R, V) →ₐ[R] Γ(relCurve C R, W) :=
  AlgHom.mk' (CommRingCat.Hom.hom ((relCurve C R).presheaf.map (homOfLE h).op))
    (fun c x => by
      simp only [Algebra.smul_def]
      rw [map_mul]
      congr 1
      rw [Scheme.algebraMap_overSectionsAlgebra, Scheme.algebraMap_overSectionsAlgebra]
      exact (relCurve C R).overAlgebraMap_apply_res R (homOfLE h).op c)

@[simp]
lemma relResAlgHom_apply {W V : (relCurve C R).Opens} (h : W ≤ V) (s : Γ(relCurve C R, V)) :
    relResAlgHom C R h s = ((relCurve C R).presheaf.map (homOfLE h).op).hom s :=
  rfl

/-- **The finite chart adaptation of a local-equation system** (worksheet §1.1 (D1)):
basic-open cover data of the two pinned charts, equations `f_j` on the pieces, and the
pointwise refinement clause `eqn_rel` — on the overlap of each piece with any member of
`d.cover`, `f_j` agrees with `d`'s equation up to a unit. Regularity of the `f_j` is
DERIVED (`DivisorAdaptation.eqn_regular`), not stored. -/
structure DivisorAdaptation [IsAffineHom π] (d : (relCurve C R).LocalEquations) :
    Type u extends FinCoverData C R π where
  /-- The equation on the piece `D(h_j)`. -/
  eqn : ∀ j : toFinCoverData.index, Γ(relCurve C R, toFinCoverData.pieces j)
  /-- The equations refine `d` pointwise up to units: on the overlap of each piece with
  any member of `d`'s cover, `f_j` and `d`'s equation differ by a unit. Point-free (the
  `DivEq` spelling), so it pulls back along arbitrary morphisms — the resolution of the
  DD-1 pt-transport seam (`informal/spec-dd-2.md` §1a). The quantifier ranges over ALL
  `y`: the empty overlap carries the zero ring, where the clause is trivial. -/
  eqn_rel : ∀ (j : toFinCoverData.index) (y : relCurve C R),
    ∃ u : Γ(relCurve C R, toFinCoverData.pieces j ⊓ d.cover.opens y)ˣ,
      ((relCurve C R).presheaf.map (homOfLE inf_le_left).op).hom (eqn j)
        = (u : Γ(relCurve C R, toFinCoverData.pieces j ⊓ d.cover.opens y))
          * ((relCurve C R).presheaf.map (homOfLE inf_le_right).op).hom (d.eqn y)

namespace DivisorAdaptation

variable {C R π} [IsAffineHom π] {d : (relCurve C R).LocalEquations}
variable (A : DivisorAdaptation C R π d)

/-- **The compatibility constructor from anchored refinement data** (the pre-DD-2 field
layout): a base point `pt j` of `d.cover` per piece with `pieces j ≤ d.cover.opens (pt j)`
and a comparison unit `eqn j = unit j · res (d.eqn (pt j))`. The pointwise clause
`eqn_rel` is derived by rewriting `d.eqn (pt j)` into `d.eqn y` through the transition
unit `d.ratioUnit (pt j) y` on the overlap (the `DivEq.trans` calc pattern). -/
def ofAnchors (D : FinCoverData C R π)
    (eqn : ∀ j : D.index, Γ(relCurve C R, D.pieces j))
    (pt : D.index → relCurve C R)
    (piece_le : ∀ j, D.pieces j ≤ d.cover.opens (pt j))
    (unit : ∀ j, Γ(relCurve C R, D.pieces j)ˣ)
    (eqn_eq : ∀ j, eqn j = (unit j : Γ(relCurve C R, D.pieces j))
      * ((relCurve C R).presheaf.map (homOfLE (piece_le j)).op).hom (d.eqn (pt j))) :
    DivisorAdaptation C R π d where
  toFinCoverData := D
  eqn := eqn
  eqn_rel := fun j y => by
    have hWle : D.pieces j ⊓ d.cover.opens y
        ≤ d.cover.opens (pt j) ⊓ d.cover.opens y :=
      inf_le_inf (piece_le j) le_rfl
    have E1 := congrArg ((relCurve C R).presheaf.map (homOfLE
      (inf_le_left : D.pieces j ⊓ d.cover.opens y ≤ D.pieces j)).op).hom (eqn_eq j)
    rw [map_mul, Scheme.LocalEquations.res_res] at E1
    have E2 := congrArg ((relCurve C R).presheaf.map (homOfLE hWle).op).hom
      (d.eqn_restrict_eq (pt j) y)
    rw [map_mul, Scheme.LocalEquations.res_res, Scheme.LocalEquations.res_res] at E2
    refine ⟨(relCurve C R).unitsRestrict inf_le_left (unit j)
      * (relCurve C R).unitsRestrict hWle (d.ratioUnit (pt j) y), ?_⟩
    rw [Units.val_mul]
    calc ((relCurve C R).presheaf.map (homOfLE inf_le_left).op).hom (eqn j)
        = ((relCurve C R).unitsRestrict inf_le_left (unit j)).val
          * ((relCurve C R).presheaf.map (homOfLE
              ((inf_le_left : D.pieces j ⊓ d.cover.opens y ≤ D.pieces j).trans
                (piece_le j))).op).hom (d.eqn (pt j)) := by
          rw [show ((relCurve C R).unitsRestrict (inf_le_left :
              D.pieces j ⊓ d.cover.opens y ≤ D.pieces j) (unit j)).val
              = ((relCurve C R).presheaf.map (homOfLE (inf_le_left :
                  D.pieces j ⊓ d.cover.opens y ≤ D.pieces j)).op).hom (unit j).val
            from rfl]
          exact E1
      _ = ((relCurve C R).unitsRestrict inf_le_left (unit j)).val
          * (((relCurve C R).unitsRestrict hWle (d.ratioUnit (pt j) y)).val
            * ((relCurve C R).presheaf.map (homOfLE (hWle.trans
                (inf_le_right : d.cover.opens (pt j) ⊓ d.cover.opens y
                  ≤ d.cover.opens y))).op).hom (d.eqn y)) := by
          rw [show ((relCurve C R).unitsRestrict hWle (d.ratioUnit (pt j) y)).val
              = ((relCurve C R).presheaf.map
                  (homOfLE hWle).op).hom (d.ratioUnit (pt j) y).val from rfl]
          rw [E2]
      _ = ((relCurve C R).unitsRestrict inf_le_left (unit j)).val
          * ((relCurve C R).unitsRestrict hWle (d.ratioUnit (pt j) y)).val
          * ((relCurve C R).presheaf.map (homOfLE
              (inf_le_right : D.pieces j ⊓ d.cover.opens y
                ≤ d.cover.opens y)).op).hom (d.eqn y) := by
          rw [mul_assoc]

/-- The adaptation's equations are regular: at `z ∈ D(h_j)` the pointwise clause
`eqn_rel j z` presents the germ of `f_j` as a unit germ times the germ of `d`'s regular
equation at the member of `z` itself. -/
theorem eqn_regular (j : A.index) (z : relCurve C R) (hz : z ∈ A.pieces j) :
    ((relCurve C R).presheaf.germ (A.pieces j) z hz).hom (A.eqn j)
      ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk z) := by
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
  rw [hgerm]
  exact mul_mem
    ((u.isUnit.map ((relCurve C R).presheaf.germ
      (A.pieces j ⊓ d.cover.opens z) z hzW).hom).mem_nonZeroDivisors)
    (d.regular z z (d.cover.mem_opens z))

/-! ### The colength modules and the glued equalizer -/

/-- The chart-local colength module `Γ(D(h_j)) ⧸ (f_j)`, an `R`-algebra through
`Scheme.overSectionsAlgebra`. -/
noncomputable abbrev colength (j : A.index) : Type u :=
  Γ(relCurve C R, A.pieces j) ⧸ Ideal.span {A.eqn j}

/-- The symmetric overlap ideal: both equations restricted to the piece overlap. The
two restrictions generate the same ideal (the equations differ by units on overlaps
through the refinement witness), but the symmetric span needs no transport in the
DEFINITION. -/
noncomputable abbrev ovlIdeal (i j : A.index) :
    Ideal Γ(relCurve C R, A.pieces i ⊓ A.pieces j) :=
  Ideal.span
    {relResAlgHom C R (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i) (A.eqn i),
     relResAlgHom C R (inf_le_right : A.pieces i ⊓ A.pieces j ≤ A.pieces j) (A.eqn j)}

/-- The overlap colength module `Γ(D(h_i) ⊓ D(h_j)) ⧸ (f_i, f_j)`. -/
noncomputable abbrev ovlColength (i j : A.index) : Type u :=
  Γ(relCurve C R, A.pieces i ⊓ A.pieces j) ⧸ A.ovlIdeal i j

/-- The induced `R`-algebra map `colength i → ovlColength i j` (restrict, then quotient;
the ideal of `f_i` lands in the symmetric span). -/
noncomputable def toOvlLeft (i j : A.index) : A.colength i →ₐ[R] A.ovlColength i j :=
  Ideal.Quotient.liftₐ (Ideal.span {A.eqn i})
    ((Ideal.Quotient.mkₐ R (A.ovlIdeal i j)).comp (relResAlgHom C R inf_le_left))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      simp only [AlgHom.comp_apply, map_mul]
      have hmem : relResAlgHom C R
          (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i) (A.eqn i)
          ∈ A.ovlIdeal i j :=
        Ideal.subset_span (Set.mem_insert _ _)
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_mul])

/-- The induced `R`-algebra map `colength j → ovlColength i j`. -/
noncomputable def toOvlRight (i j : A.index) : A.colength j →ₐ[R] A.ovlColength i j :=
  Ideal.Quotient.liftₐ (Ideal.span {A.eqn j})
    ((Ideal.Quotient.mkₐ R (A.ovlIdeal i j)).comp (relResAlgHom C R inf_le_right))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      simp only [AlgHom.comp_apply, map_mul]
      have hmem : relResAlgHom C R
          (inf_le_right : A.pieces i ⊓ A.pieces j ≤ A.pieces j) (A.eqn j)
          ∈ A.ovlIdeal i j :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_mul])

/-- The product of the chart-local colength modules (an `abbrev`, so the `Pi.module`
instances apply directly — probe finding, spec §1b(iii)). -/
noncomputable abbrev chartProd : Type u := ∀ j : A.index, A.colength j

/-- The product of the overlap colength modules over ordered index pairs. -/
noncomputable abbrev ovlProd : Type u := ∀ p : A.index × A.index, A.ovlColength p.1 p.2

/-- The left arrow of the equalizer: restrict the `p.1` component to each overlap. -/
noncomputable def deltaLeft : A.chartProd →ₗ[R] A.ovlProd :=
  LinearMap.pi
    (fun p : A.index × A.index => (A.toOvlLeft p.1 p.2).toLinearMap ∘ₗ LinearMap.proj p.1)

/-- The right arrow of the equalizer: restrict the `p.2` component to each overlap. -/
noncomputable def deltaRight : A.chartProd →ₗ[R] A.ovlProd :=
  LinearMap.pi
    (fun p : A.index × A.index => (A.toOvlRight p.1 p.2).toLinearMap ∘ₗ LinearMap.proj p.2)

/-- **The glued colength module `W(d)`** (worksheet §1.1 (c2)): the equalizer of the two
overlap-restriction arrows on the product of chart-local colengths, spelled as the
kernel of their difference (so the `FlatCokernel` base-change keystone applies
verbatim); the equalizer description is `mem_gluedSubmodule_iff`. -/
noncomputable def gluedSubmodule : Submodule R A.chartProd :=
  LinearMap.ker (A.deltaLeft - A.deltaRight)

/-- The equalizer description of the glued colength module: componentwise agreement of
the two overlap restrictions. -/
lemma mem_gluedSubmodule_iff (s : A.chartProd) :
    s ∈ A.gluedSubmodule ↔ ∀ p : A.index × A.index,
      A.toOvlLeft p.1 p.2 (s p.1) = A.toOvlRight p.1 p.2 (s p.2) := by
  simp only [gluedSubmodule, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    funext_iff, deltaLeft, deltaRight, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]

/-- The glued colength module, as a type. -/
noncomputable abbrev Glued : Type u := ↥A.gluedSubmodule

/-! ### The certificate -/

/-- **The colength certificate** (worksheet §1.1 (c1)/(c2) in the spec-dd-1 §1c frozen
spelling): chart-local colengths finite projective over `R` (c1); the glued module
finite projective of constant fibre rank `n` — honest finrank at every prime through
`Module.rankAtStalk` (c2); and the two flat-cokernel clauses (c3)/(c4) that make
certificates base-change along ARBITRARY test maps (trivial over a field; transported
by right-exactness; consumed by `FlatCokernel.tensorKer_bijective_of_flat_coker`). -/
structure IsCertified (n : ℕ) : Prop where
  /-- (c1) Each chart-local colength module is a finite `R`-module. -/
  finite_colength : ∀ j, Module.Finite R (A.colength j)
  /-- (c1) Each chart-local colength module is projective over `R`. -/
  projective_colength : ∀ j, Module.Projective R (A.colength j)
  /-- (c2) The glued colength module is a finite `R`-module. -/
  finite_glued : Module.Finite R A.Glued
  /-- (c2) The glued colength module is projective over `R`. -/
  projective_glued : Module.Projective R A.Glued
  /-- (c2) The glued colength module has constant fibre rank `n`. -/
  rankAtStalk_glued : ∀ p : PrimeSpectrum R, Module.rankAtStalk A.Glued p = n
  /-- (c3) The cokernel of `W(d) ↪ Π_j colength j` is flat. -/
  flat_coker_incl : Module.Flat R (A.chartProd ⧸ A.gluedSubmodule)
  /-- (c4) The cokernel of the difference arrow is flat. -/
  flat_coker_diff :
    Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))

end DivisorAdaptation

/-! ## The certified family and the divisor-functor value -/

variable (n : ℕ)

/-- **A certified divisor family of degree `n` over the test ring `R`** (the worksheet's
(D1) pair `(d, c)`): a local-equation system with a certified finite chart
adaptation. -/
structure CertifiedDivisorFamily [IsAffineHom π] : Type u where
  /-- The local-equation system on the relative curve. -/
  eqns : (relCurve C R).LocalEquations
  /-- The finite chart adaptation refining it. -/
  adaptation : DivisorAdaptation C R π eqns
  /-- The colength certificate of degree `n`. -/
  certified : adaptation.IsCertified n

/-- The divisor-equality setoid on certified families: the underlying local-equation
systems cut the same divisor (`Scheme.LocalEquations.DivEq`); the adaptation and
certificate are per-representative data and do not enter the relation. -/
def divFamSetoid [IsAffineHom π] : Setoid (CertifiedDivisorFamily C R π n) where
  r F G := Scheme.LocalEquations.DivEq F.eqns G.eqns
  iseqv :=
    ⟨fun F => Scheme.LocalEquations.divEq_refl F.eqns,
     fun h => h.symm, fun h h' => h.trans h'⟩

/-- **The divisor-functor value on the affine test `R`** (worksheet §1.1): certified
divisor families of degree `n` up to divisor equality. A `Type u` quotient — the
carrier the affine-opens-limit vehicle ranges over. -/
def DivFam [IsAffineHom π] : Type u := Quotient (divFamSetoid C R π n)

namespace DivFam

variable {C R π n} [IsAffineHom π]

/-- The class of a certified family. -/
def mk (F : CertifiedDivisorFamily C R π n) : DivFam C R π n :=
  Quotient.mk (divFamSetoid C R π n) F

lemma mk_eq_mk_iff {F G : CertifiedDivisorFamily C R π n} :
    mk F = mk G ↔ Scheme.LocalEquations.DivEq F.eqns G.eqns :=
  Quotient.eq (r := divFamSetoid C R π n)

/-- **The Picard class of a divisor family** `𝒪(D)`: well defined on the quotient by
the class laws (`picClass_eq_of_divEq`). This is the Abel hook DAT-C consumes. -/
noncomputable def picClass (F : DivFam C R π n) : (relCurve C R).CechPic :=
  Quotient.lift (fun F : CertifiedDivisorFamily C R π n => F.eqns.picClass)
    (fun _ _ h => Scheme.LocalEquations.picClass_eq_of_divEq h) F

@[simp]
lemma picClass_mk (F : CertifiedDivisorFamily C R π n) :
    picClass (mk F) = F.eqns.picClass :=
  rfl

end DivFam

end AlgebraicGeometry
