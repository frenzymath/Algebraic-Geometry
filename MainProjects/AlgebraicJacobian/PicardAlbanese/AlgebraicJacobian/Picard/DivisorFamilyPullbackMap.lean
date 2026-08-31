/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyPullbackGlued
import AlgebraicJacobian.Picard.SectionsToDivisors

/-!
# The pulled local-equation system: regularity of the pulled equations (DD-1a)

The `hreg` discharge for `LocalEquations.pullback` along the relative-curve comparison
`relCurveMap C R R'` (`informal/spec-dd-1.md` §3 stage (c), the DD-1a row): for a
certified divisor adaptation, the pulled equations have nonzerodivisor germs at every
point, so the pulled system `d' = d.pullback (relCurveMap C R R')` exists — with **no
flatness hypothesis on `R'`**: the regularity comes from the certificate's colength
projectivity through `FlatCokernel`'s
`Algebra.TensorProduct.includeRight_mem_nonZeroDivisors_of_flat_coker` and the affine
germ seam `IsAffineOpen.germ_mem_nonZeroDivisors`.

* `FinCoverData.pieceTermBaseChange` — the indexed piece-level term identification
  `R' ⊗[R] Γ(D(h_j)) ≃ₐ[R'] Γ(D(h'_j))`, with `1 ⊗ s ↦ piecesMap s`.
* `FinCoverData.exists_mem_pieces`, `FinCoverData.isAffineOpen_pieces` — every point
  lies in an (affine) piece.
* `DivisorAdaptation.eqn_mem_nonZeroDivisors`/`pulledEqn_mem_nonZeroDivisors` — the
  adaptation's equations are section-level regular, and stay so after any base change.
* `DivisorAdaptation.germ_pullbackEqn_mem_nonZeroDivisors` — **the `hreg` discharge**:
  germs of the pulled equations of `d` are nonzerodivisors at every point (each point
  lies in a piece; there the pulled equation differs from the pulled piece equation by
  a stalk unit, through the pointwise clause `eqn_rel` of the adaptation).
* `DivisorAdaptation.pulledEquations` — the pulled local-equation system on
  `relCurve C R'`.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-- A ring isomorphism carries nonzerodivisors to nonzerodivisors. -/
private lemma map_mem_nonZeroDivisors {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {a : A} (ha : a ∈ nonZeroDivisors A) : e a ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff] at ha ⊢
  obtain ⟨hl, hr⟩ := ha
  constructor
  · intro b hb
    have h := congrArg e.symm hb
    rw [map_mul, map_zero, e.symm_apply_apply] at h
    have hb0 : e.symm b = 0 := hl _ h
    calc b = e (e.symm b) := (e.apply_symm_apply b).symm
      _ = 0 := by rw [hb0, map_zero]
  · intro b hb
    have h := congrArg e.symm hb
    rw [map_mul, map_zero, e.symm_apply_apply] at h
    have hb0 : e.symm b = 0 := hr _ h
    calc b = e (e.symm b) := (e.apply_symm_apply b).symm
      _ = 0 := by rw [hb0, map_zero]

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

namespace FinCoverData

variable (D : FinCoverData C R π)

/-- Every point of the relative curve lies in a piece: the pieces partition the two
pinned charts, which cover the curve. -/
lemma exists_mem_pieces (z : relCurve C R) : ∃ j : D.index, z ∈ D.pieces j := by
  have hz : z ∈ (relCover C R (fiberTwoCover π)).V₀ ⊔ (relCover C R (fiberTwoCover π)).V₁ := by
    rw [relCover_sup]
    trivial
  rcases Opens.mem_sup.mp hz with h | h
  · have hcov := D.cover₀ h
    rw [Opens.mem_iSup] at hcov
    obtain ⟨j, hj⟩ := hcov
    exact ⟨Sum.inl j, hj⟩
  · have hcov := D.cover₁ h
    rw [Opens.mem_iSup] at hcov
    obtain ⟨j, hj⟩ := hcov
    exact ⟨Sum.inr j, hj⟩

/-- The pieces are affine opens (basic opens of the affine pinned charts). -/
lemma isAffineOpen_pieces (j : D.index) : IsAffineOpen (D.pieces j) := by
  cases j
  · exact (relCover_isAffineOpen₀ C R (fiberTwoCover π)).basicOpen _
  · exact (relCover_isAffineOpen₁ C R (fiberTwoCover π)).basicOpen _

/-- The indexed piece-level term identification
`R' ⊗[R] Γ(D(h_j)) ≃ₐ[R'] Γ(D(h'_j))` (casewise the generic
`pieceTermBaseChangeAlg` at the pinned charts). -/
noncomputable def pieceTermBaseChange :
    ∀ j : D.index, R' ⊗[R] Γ(relCurve C R, D.pieces j) ≃ₐ[R']
      Γ(relCurve C R', (D.baseChange R').pieces j)
  | .inl j =>
      pieceTermBaseChangeAlg R' (fiberChart₀ π)
        (fiberTwoCover π).isAffineOpen₀.isCompact
        (fiberTwoCover π).isAffineOpen₀.isQuasiSeparated
        (relCover_isAffineOpen₀ C R (fiberTwoCover π))
        (relCover_isAffineOpen₀ C R' (fiberTwoCover π)) (D.h₀ j)
  | .inr j =>
      pieceTermBaseChangeAlg R' (fiberChart₁ π)
        (fiberTwoCover π).isAffineOpen₁.isCompact
        (fiberTwoCover π).isAffineOpen₁.isQuasiSeparated
        (relCover_isAffineOpen₁ C R (fiberTwoCover π))
        (relCover_isAffineOpen₁ C R' (fiberTwoCover π)) (D.h₁ j)

/-- The indexed term identification on `1 ⊗ s`: the piece comparison. -/
lemma pieceTermBaseChange_one_tmul (j : D.index) (s : Γ(relCurve C R, D.pieces j)) :
    D.pieceTermBaseChange R' j ((1 : R') ⊗ₜ[R] s) = D.piecesMap R' j s := by
  cases j with
  | inl j =>
      exact pieceTermBaseChangeAlg_one_tmul R' (fiberChart₀ π)
        (fiberTwoCover π).isAffineOpen₀.isCompact
        (fiberTwoCover π).isAffineOpen₀.isQuasiSeparated
        (relCover_isAffineOpen₀ C R (fiberTwoCover π))
        (relCover_isAffineOpen₀ C R' (fiberTwoCover π)) (D.h₀ j) s
  | inr j =>
      exact pieceTermBaseChangeAlg_one_tmul R' (fiberChart₁ π)
        (fiberTwoCover π).isAffineOpen₁.isCompact
        (fiberTwoCover π).isAffineOpen₁.isQuasiSeparated
        (relCover_isAffineOpen₁ C R (fiberTwoCover π))
        (relCover_isAffineOpen₁ C R' (fiberTwoCover π)) (D.h₁ j) s

end FinCoverData

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d)

/-- The adaptation's equations are section-level regular: their germs are
nonzerodivisors at every point (`DivisorAdaptation.eqn_regular`), and sections of a
sheaf inject into the product of their germs. -/
theorem eqn_mem_nonZeroDivisors (j : A.index) :
    A.eqn j ∈ nonZeroDivisors Γ(relCurve C R, A.pieces j) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro t ht
  apply TopCat.Presheaf.section_ext (relCurve C R).sheaf (A.pieces j) t 0
  intro z hz
  rw [map_zero]
  have key : ((relCurve C R).presheaf.germ (A.pieces j) z hz).hom t
      * ((relCurve C R).presheaf.germ (A.pieces j) z hz).hom (A.eqn j) = 0 := by
    rw [← map_mul, ht, map_zero]
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff (A.eqn_regular j z hz)).mp
    (by rw [mul_comm] at key; exact key)

/-- **The pulled equations are section-level regular** (Kleiman `lm:ctn` (i)⟹(iii) made
cheap; no hypothesis on `R'`): the colength `Γ(D(h_j))⧸(f_j)` is projective hence flat
over `R`, so `f_j` stays regular in `R' ⊗[R] Γ(D(h_j)) ≅ Γ(D(h'_j))`
(`includeRight_mem_nonZeroDivisors_of_flat_coker` through the piece-level term
identification). -/
theorem pulledEqn_mem_nonZeroDivisors
    (hproj : ∀ j, Module.Projective R (A.colength j)) (j : A.index) :
    A.pulledEqn R' j ∈
      nonZeroDivisors Γ(relCurve C R', (A.toFinCoverData.baseChange R').pieces j) := by
  haveI := hproj j
  have hreg := Algebra.TensorProduct.includeRight_mem_nonZeroDivisors_of_flat_coker
    (R := R) R' (A.eqn j) (A.eqn_mem_nonZeroDivisors j)
  have h2 := map_mem_nonZeroDivisors
    (A.toFinCoverData.pieceTermBaseChange R' j).toRingEquiv hreg
  have h1 : (A.toFinCoverData.pieceTermBaseChange R' j).toRingEquiv
      (Algebra.TensorProduct.includeRight (A.eqn j)) = A.pulledEqn R' j := by
    rw [Algebra.TensorProduct.includeRight_apply]
    exact A.toFinCoverData.pieceTermBaseChange_one_tmul R' j (A.eqn j)
  rwa [h1] at h2

/-- **The `hreg` discharge** (DD-1a): germs of the pulled equations of `d` are
nonzerodivisors at every point of the pulled cover members. Each point lies in a piece;
there the pulled equation differs from the pulled piece equation — regular by
`pulledEqn_mem_nonZeroDivisors` + the affine germ seam — by a stalk unit assembled from
the adaptation unit and the transition unit of `d`. -/
theorem germ_pullbackEqn_mem_nonZeroDivisors
    (hproj : ∀ j, Module.Projective R (A.colength j))
    (y z : relCurve C R')
    (hz : z ∈ (d.cover.pullback (relCurveMap C R R')).opens y) :
    ((relCurve C R').presheaf.germ
        ((d.cover.pullback (relCurveMap C R R')).opens y) z hz).hom
        (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d y)
      ∈ nonZeroDivisors ((relCurve C R').presheaf.stalk z) := by
  obtain ⟨j, hzj⟩ := (A.toFinCoverData.baseChange R').exists_mem_pieces z
  -- the point below `z` and its memberships
  have hzj' : z ∈ relCurveMap C R R' ⁻¹ᵁ A.pieces j := by
    rw [← A.toFinCoverData.pieces_baseChange R' j]
    exact hzj
  have hfzj : (relCurveMap C R R').base z ∈ A.pieces j := hzj'
  have hfzy : (relCurveMap C R R').base z ∈ d.cover.opens ((relCurveMap C R R').base y) :=
    hz
  have hfzW : (relCurveMap C R R').base z ∈
      A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y) :=
    ⟨hfzj, hfzy⟩
  -- the regular germ of the pulled piece equation
  have hF : ((relCurve C R').presheaf.germ
      ((A.toFinCoverData.baseChange R').pieces j) z hzj).hom (A.pulledEqn R' j) ∈
      nonZeroDivisors ((relCurve C R').presheaf.stalk z) :=
    IsAffineOpen.germ_mem_nonZeroDivisors
      ((A.toFinCoverData.baseChange R').isAffineOpen_pieces j)
      (A.pulledEqn_mem_nonZeroDivisors R' hproj j) z hzj
  -- germ of the pulled piece equation = stalk image of the germ of the piece equation
  have hgermF : ((relCurve C R').presheaf.germ
      ((A.toFinCoverData.baseChange R').pieces j) z hzj).hom (A.pulledEqn R' j) =
      ((relCurveMap C R R').stalkMap z).hom
        (((relCurve C R).presheaf.germ (A.pieces j)
          ((relCurveMap C R R').base z) hfzj).hom (A.eqn j)) := by
    have happ := (relCurveMap C R R').germ_stalkMap_apply (A.pieces j) z hfzj (A.eqn j)
    -- `pulledEqn = res (app (eqn))`, so its germ over the piece is the germ of
    -- `app (eqn)` over the preimage
    have hres : ((relCurve C R').presheaf.germ
        ((A.toFinCoverData.baseChange R').pieces j) z hzj).hom (A.pulledEqn R' j) =
        ((relCurve C R').presheaf.germ
          (relCurveMap C R R' ⁻¹ᵁ A.pieces j) z hzj').hom
          (((relCurveMap C R R').app (A.pieces j)).hom (A.eqn j)) := by
      have hle : (A.toFinCoverData.baseChange R').pieces j ≤
          relCurveMap C R R' ⁻¹ᵁ A.pieces j :=
        A.toFinCoverData.baseChange_pieces_le_preimage R' j
      have := TopCat.Presheaf.germ_res_apply (relCurve C R').presheaf
        (homOfLE hle) z hzj (((relCurveMap C R R').app (A.pieces j)).hom (A.eqn j))
      rw [← this]
      rfl
    rw [hres, happ]
  -- decompose the germ of the piece equation through the pointwise unit clause of the
  -- adaptation at the base point of `y`
  obtain ⟨u, hu⟩ := A.eqn_rel j ((relCurveMap C R R').base y)
  have hdecomp : ((relCurve C R).presheaf.germ (A.pieces j)
      ((relCurveMap C R R').base z) hfzj).hom (A.eqn j) =
      ((relCurve C R).presheaf.germ
          (A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y))
          ((relCurveMap C R R').base z) hfzW).hom
        (u : Γ(relCurve C R,
          A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y))) *
        ((relCurve C R).presheaf.germ
          (d.cover.opens ((relCurveMap C R R').base y))
          ((relCurveMap C R R').base z) hfzy).hom
          (d.eqn ((relCurveMap C R R').base y)) := by
    have hkey := congrArg ((relCurve C R).presheaf.germ
        (A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y))
        ((relCurveMap C R R').base z) hfzW).hom hu
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hkey
    exact hkey
  -- the goal germ is the stalk image of the germ of `d.eqn (f.base y)`
  have hgermG : ((relCurve C R').presheaf.germ
      ((d.cover.pullback (relCurveMap C R R')).opens y) z hz).hom
      (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d y) =
      ((relCurveMap C R R').stalkMap z).hom
        (((relCurve C R).presheaf.germ
          (d.cover.opens ((relCurveMap C R R').base y))
          ((relCurveMap C R R').base z) hfzy).hom
          (d.eqn ((relCurveMap C R R').base y))) := by
    rw [Scheme.LocalEquations.pullbackEqn]
    have happLE : ((relCurveMap C R R').appLE
        (d.cover.opens ((relCurveMap C R R').base y))
        ((d.cover.pullback (relCurveMap C R R')).opens y) le_rfl).hom
        (d.eqn ((relCurveMap C R R').base y)) =
        ((relCurve C R').presheaf.map (homOfLE (le_refl
          ((d.cover.pullback (relCurveMap C R R')).opens y))).op).hom
          (((relCurveMap C R R').app
            (d.cover.opens ((relCurveMap C R R').base y))).hom
            (d.eqn ((relCurveMap C R R').base y))) := rfl
    rw [happLE, TopCat.Presheaf.germ_res_apply]
    exact ((relCurveMap C R R').germ_stalkMap_apply
      (d.cover.opens ((relCurveMap C R R').base y)) z hfzy
      (d.eqn ((relCurveMap C R R').base y))).symm
  -- assemble: the pulled piece equation's germ is a unit multiple of the goal germ
  have hunit : IsUnit (((relCurveMap C R R').stalkMap z).hom
      (((relCurve C R).presheaf.germ
        (A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y))
        ((relCurveMap C R R').base z) hfzW).hom
        (u : Γ(relCurve C R,
          A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y))))) :=
    (u.isUnit.map ((relCurve C R).presheaf.germ
      (A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y))
      ((relCurveMap C R R').base z) hfzW).hom).map
      ((relCurveMap C R R').stalkMap z).hom
  have hkey : ((relCurve C R').presheaf.germ
      ((A.toFinCoverData.baseChange R').pieces j) z hzj).hom (A.pulledEqn R' j) =
      (hunit.unit : ((relCurve C R').presheaf.stalk z)ˣ) *
        (((relCurveMap C R R').stalkMap z).hom
          (((relCurve C R).presheaf.germ
            (d.cover.opens ((relCurveMap C R R').base y))
            ((relCurveMap C R R').base z) hfzy).hom
            (d.eqn ((relCurveMap C R R').base y)))) := by
    rw [hgermF, hdecomp, map_mul, IsUnit.unit_spec]
  rw [hgermG]
  have hSM : ((relCurveMap C R R').stalkMap z).hom
      (((relCurve C R).presheaf.germ
        (d.cover.opens ((relCurveMap C R R').base y))
        ((relCurveMap C R R').base z) hfzy).hom
        (d.eqn ((relCurveMap C R R').base y))) =
      ↑hunit.unit⁻¹ *
        ((relCurve C R').presheaf.germ
          ((A.toFinCoverData.baseChange R').pieces j) z hzj).hom (A.pulledEqn R' j) := by
    rw [hkey, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hSM]
  exact mul_mem hunit.unit⁻¹.isUnit.mem_nonZeroDivisors hF

/-- **The pulled local-equation system** on the relative curve over `R'`: `d` pulls back
along the relative-curve comparison, with regularity discharged by the certificate's
colength projectivity. -/
noncomputable def pulledEquations (hproj : ∀ j, Module.Projective R (A.colength j)) :
    (relCurve C R').LocalEquations :=
  d.pullback (relCurveMap C R R') (A.germ_pullbackEqn_mem_nonZeroDivisors R' hproj)

@[simp]
lemma pulledEquations_cover (hproj : ∀ j, Module.Projective R (A.colength j)) :
    (A.pulledEquations R' hproj).cover = d.cover.pullback (relCurveMap C R R') :=
  rfl

/-- The Picard class of the pulled system is the pullback of the class of `d`. -/
lemma picClass_pulledEquations (hproj : ∀ j, Module.Projective R (A.colength j)) :
    (A.pulledEquations R' hproj).picClass =
      Scheme.CechPic.map (relCurveMap C R R') d.picClass :=
  Scheme.LocalEquations.picClass_pullback (relCurveMap C R R') d _

end DivisorAdaptation

end AlgebraicGeometry
