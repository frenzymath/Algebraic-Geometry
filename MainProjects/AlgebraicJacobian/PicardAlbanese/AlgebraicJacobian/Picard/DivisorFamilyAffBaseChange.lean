/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffSections
import AlgebraicJacobian.Picard.DivisorFamilyAffAdaptation
import AlgebraicJacobian.Picard.DivisorFamilyMapAlg

/-!
# Base change of the widened cover and adaptation (R2, human decision I-0492)

`DivFamZarAff` (`DivisorFamilyAffZar.lean`) is a *type*, and until this file it was a type
with no functoriality: nothing base-changed a widened certified family along `R → R'`.  The
chart-typed value owns that layer (`DivisorFamilyMapAlg.lean`,
`DivisorFamilyZarMapAlg.lean`); this file and its successors give the widened one the same.

## What the widening makes CHEAPER, not harder

The base-changed cover is defined by **preimage**: `pieces j := relCurveMap ⁻¹ᵁ pieces j`.
Three consequences, each replacing a chart-typed detour:

* `pieces_baseChange` is `rfl` (chart-side: `relSectionsMap_basicOpen`);
* the overlap identity is `Scheme.Hom.preimage_inf`, so the base-changed overlap IS the
  preimage of the overlap — the entire `ovlGen`/`basicOpen_ovlGen`/`isAffineOpen_chart_inf`
  apparatus, which existed only to re-present a piece overlap as a basic open of a chart
  overlap, has no analogue here;
* affineness of the base-changed pieces is `isAffineOpen_relCurveMap_preimage`, and the
  covering property is the preimage of a joint cover.  `FinCoverData.baseChange` had two
  partition-of-unity obligations to discharge; `AffCoverData.baseChange` has none, because the
  partitions are what R2 deleted.

## Main declarations

* `AlgebraicGeometry.AffCoverData.baseChange` — the base-changed widened cover, with
  `pieces_baseChange` (`rfl`) and `inf_baseChange`.
* `AffAdaptation.pulledEqn`, `AffAdaptation.pullback` — the base-changed adaptation; `eqn_rel`
  transports through `Scheme.Hom.unitsAppLE` exactly as `DivisorAdaptation.pullback` does.
* `AffAdaptation.eqn_mem_nonZeroDivisors`, `pulledEqn_mem_nonZeroDivisors` — section-level
  regularity of the equations, before and after base change.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-- A ring isomorphism carries nonzerodivisors to nonzerodivisors (the `private` helper of
`Picard/DivisorFamilyPullbackMap.lean`, restated here because that one is file-private —
and public here, because the widened layer needs it in more than one file). -/
lemma map_mem_nonZeroDivisors' {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {a : A} (ha : a ∈ nonZeroDivisors A) : e a ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff] at ha ⊢
  obtain ⟨hl, hr⟩ := ha
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have h := congrArg e.symm hb
    rw [map_mul, map_zero, e.symm_apply_apply] at h
    calc b = e (e.symm b) := (e.apply_symm_apply b).symm
      _ = 0 := by rw [hl _ h, map_zero]
  · have h := congrArg e.symm hb
    rw [map_mul, map_zero, e.symm_apply_apply] at h
    calc b = e (e.symm b) := (e.apply_symm_apply b).symm
      _ = 0 := by rw [hr _ h, map_zero]

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']

/-! ## The widened cover base change -/

namespace AffCoverData

variable (D : AffCoverData C R)

/-- **Base change of the widened cover datum** along `R → R'`: take preimages.  Affineness is
`isAffineOpen_relCurveMap_preimage` (preimage of an affine open along the affine `relCurveMap`)
and the covering property is the preimage of the joint cover.  There is nothing else to
discharge — no generators, no partitions. -/
noncomputable def baseChange : AffCoverData C R' where
  m := D.m
  pieces j := relCurveMap C R R' ⁻¹ᵁ D.pieces j
  isAffineOpen j := isAffineOpen_relCurveMap_preimage C R' (D.isAffineOpen j)
  cover := by
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨j, hj⟩ := D.exists_mem_pieces ((relCurveMap C R R').base z)
    exact Opens.mem_iSup.mpr ⟨j, hj⟩

@[simp]
lemma baseChange_m : (D.baseChange R').m = D.m := rfl

/-- **The pieces of the base-changed cover are the preimages of the pieces** — by definition,
so `rfl`.  Chart-side this needed `relSectionsMap_basicOpen`. -/
@[simp]
lemma pieces_baseChange (j : D.index) :
    (D.baseChange R').pieces j = relCurveMap C R R' ⁻¹ᵁ D.pieces j := rfl

/-- The overlap of two base-changed pieces IS the preimage of the overlap.  This is the
identity that makes the chart-typed overlap apparatus unnecessary. -/
lemma inf_baseChange (i j : D.index) :
    (D.baseChange R').pieces i ⊓ (D.baseChange R').pieces j
      = relCurveMap C R R' ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) :=
  (Scheme.Hom.preimage_inf _).symm

/-- The indexed piece comparison: `relAffSectionsMap` at the piece `j`.  Because the
base-changed piece IS the preimage, no `le` witness bookkeeping is needed. -/
noncomputable def piecesMap (j : D.index) :
    Γ(relCurve C R, D.pieces j) →+* Γ(relCurve C R', (D.baseChange R').pieces j) :=
  relAffSectionsMap C R' (D.pieces j)

/-- **The indexed piece-quotient transport**: `relQuotBaseChangeAff` at the piece `j`.  A
single declaration serves both the (c1) colength transport (`E` a singleton) and the overlap
transport (`E` a pair at the open `pieces i ⊓ pieces j`). -/
noncomputable def pieceQuotBaseChange (j : D.index) (E : Set Γ(relCurve C R, D.pieces j)) :
    R' ⊗[R] (Γ(relCurve C R, D.pieces j) ⧸ Ideal.span E) ≃ₐ[R']
      Γ(relCurve C R', (D.baseChange R').pieces j) ⧸ Ideal.span (D.piecesMap R' j '' E) :=
  relQuotBaseChangeAff C R' (D.isAffineOpen j) E

lemma pieceQuotBaseChange_one_tmul_mk (j : D.index)
    (E : Set Γ(relCurve C R, D.pieces j)) (s : Γ(relCurve C R, D.pieces j)) :
    D.pieceQuotBaseChange R' j E ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span E) s) =
      Ideal.Quotient.mk (Ideal.span (D.piecesMap R' j '' E)) (D.piecesMap R' j s) :=
  relQuotBaseChangeAff_one_tmul_mk C R' (D.isAffineOpen j) E s

end AffCoverData

/-! ## Section-level regularity of the widened equations -/

namespace AffAdaptation

variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d)

/-- **The equations are section-level regular**: their germs are nonzerodivisors
(`AffAdaptation.eqn_regular`) and sections of a sheaf inject into the product of their germs.
Verbatim the chart-typed `DivisorAdaptation.eqn_mem_nonZeroDivisors`; nothing about the piece
is used but that it is an open. -/
theorem eqn_mem_nonZeroDivisors (j : D.index) :
    A.eqn j ∈ nonZeroDivisors Γ(relCurve C R, D.pieces j) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro t ht
  apply TopCat.Presheaf.section_ext (relCurve C R).sheaf (D.pieces j) t 0
  intro z hz
  rw [map_zero]
  have key : ((relCurve C R).presheaf.germ (D.pieces j) z hz).hom t
      * ((relCurve C R).presheaf.germ (D.pieces j) z hz).hom (A.eqn j) = 0 := by
    rw [← map_mul, ht, map_zero]
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff (A.eqn_regular j z hz)).mp
    (by rw [mul_comm] at key; exact key)

/-- The pulled equation on the base-changed piece. -/
noncomputable def pulledEqn (j : D.index) :
    Γ(relCurve C R', (D.baseChange R').pieces j) :=
  D.piecesMap R' j (A.eqn j)

/-- **The pulled equations are section-level regular** (Kleiman `lm:ctn` (i)⟹(iii), made
cheap, with no hypothesis on `R'`): the colength is projective hence flat over `R`, so the
equation stays regular in `R' ⊗[R] Γ(pieces j) ≅ Γ(pieces' j)`.  The transport is now the
widened `relSectionsBaseChangeAff` rather than the chart-typed term identification; the
flatness input `includeRight_mem_nonZeroDivisors_of_flat_coker` is unchanged, being a statement
about a bare commutative `R`-algebra. -/
theorem pulledEqn_mem_nonZeroDivisors
    (hproj : ∀ j, Module.Projective R (A.colength j)) (j : D.index) :
    A.pulledEqn R' j ∈ nonZeroDivisors Γ(relCurve C R', (D.baseChange R').pieces j) := by
  haveI := hproj j
  have hreg := Algebra.TensorProduct.includeRight_mem_nonZeroDivisors_of_flat_coker
    (R := R) R' (A.eqn j) (A.eqn_mem_nonZeroDivisors j)
  have h2 := map_mem_nonZeroDivisors'
    (relSectionsBaseChangeAff C R' (D.isAffineOpen j)).toRingEquiv hreg
  have h1 : (relSectionsBaseChangeAff C R' (D.isAffineOpen j)).toRingEquiv
      (Algebra.TensorProduct.includeRight (A.eqn j)) = A.pulledEqn R' j := by
    rw [Algebra.TensorProduct.includeRight_apply]
    exact relSectionsBaseChangeAff_one_tmul C R' (D.isAffineOpen j) (A.eqn j)
  rwa [h1] at h2

/-- **The `hreg` discharge, widened**: germs of the pulled equations of `d` are
nonzerodivisors at every point of the pulled cover members.  Every point lies in a
base-changed piece (`AffCoverData.exists_mem_pieces`, one line from the joint-cover field
where the chart version needed `relCover_sup` plus two partitions); there the pulled equation
differs from the pulled piece equation, regular by `pulledEqn_mem_nonZeroDivisors` and the
affine germ seam, by a stalk unit assembled from the adaptation unit `eqn_rel`. -/
theorem germ_pullbackEqn_mem_nonZeroDivisors
    (hproj : ∀ j, Module.Projective R (A.colength j))
    (y z : relCurve C R')
    (hz : z ∈ (d.cover.pullback (relCurveMap C R R')).opens y) :
    ((relCurve C R').presheaf.germ
        ((d.cover.pullback (relCurveMap C R R')).opens y) z hz).hom
        (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d y)
      ∈ nonZeroDivisors ((relCurve C R').presheaf.stalk z) := by
  obtain ⟨j, hzj⟩ := (D.baseChange R').exists_mem_pieces z
  have hzj' : z ∈ relCurveMap C R R' ⁻¹ᵁ D.pieces j := hzj
  have hfzj : (relCurveMap C R R').base z ∈ D.pieces j := hzj'
  have hfzy : (relCurveMap C R R').base z ∈ d.cover.opens ((relCurveMap C R R').base y) := hz
  have hfzW : (relCurveMap C R R').base z ∈
      D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y) :=
    ⟨hfzj, hfzy⟩
  -- the regular germ of the pulled piece equation
  have hF : ((relCurve C R').presheaf.germ ((D.baseChange R').pieces j) z hzj).hom
      (A.pulledEqn R' j) ∈ nonZeroDivisors ((relCurve C R').presheaf.stalk z) :=
    IsAffineOpen.germ_mem_nonZeroDivisors ((D.baseChange R').isAffineOpen_pieces j)
      (A.pulledEqn_mem_nonZeroDivisors R' hproj j) z hzj
  -- germ of the pulled piece equation = stalk image of the germ of the piece equation
  have hgermF : ((relCurve C R').presheaf.germ ((D.baseChange R').pieces j) z hzj).hom
      (A.pulledEqn R' j) =
      ((relCurveMap C R R').stalkMap z).hom
        (((relCurve C R).presheaf.germ (D.pieces j)
          ((relCurveMap C R R').base z) hfzj).hom (A.eqn j)) := by
    have happ := (relCurveMap C R R').germ_stalkMap_apply (D.pieces j) z hfzj (A.eqn j)
    have hres : ((relCurve C R').presheaf.germ ((D.baseChange R').pieces j) z hzj).hom
        (A.pulledEqn R' j) =
        ((relCurve C R').presheaf.germ (relCurveMap C R R' ⁻¹ᵁ D.pieces j) z hzj').hom
          (((relCurveMap C R R').app (D.pieces j)).hom (A.eqn j)) := by
      have hstep := TopCat.Presheaf.germ_res_apply (relCurve C R').presheaf
        (homOfLE (le_refl (relCurveMap C R R' ⁻¹ᵁ D.pieces j))) z hzj
        (((relCurveMap C R R').app (D.pieces j)).hom (A.eqn j))
      rw [← hstep]
      rfl
    rw [hres, happ]
  -- decompose through the pointwise unit clause at the base point of `y`
  obtain ⟨u, hu⟩ := A.eqn_rel j ((relCurveMap C R R').base y)
  have hdecomp : ((relCurve C R).presheaf.germ (D.pieces j)
      ((relCurveMap C R R').base z) hfzj).hom (A.eqn j) =
      ((relCurve C R).presheaf.germ
          (D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y))
          ((relCurveMap C R R').base z) hfzW).hom
        (u : Γ(relCurve C R,
          D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y))) *
        ((relCurve C R).presheaf.germ (d.cover.opens ((relCurveMap C R R').base y))
          ((relCurveMap C R R').base z) hfzy).hom
          (d.eqn ((relCurveMap C R R').base y)) := by
    have hkey := congrArg ((relCurve C R).presheaf.germ
        (D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y))
        ((relCurveMap C R R').base z) hfzW).hom hu
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hkey
    exact hkey
  -- the goal germ is the stalk image of the germ of `d.eqn (f.base y)`
  have hgermG : ((relCurve C R').presheaf.germ
      ((d.cover.pullback (relCurveMap C R R')).opens y) z hz).hom
      (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d y) =
      ((relCurveMap C R R').stalkMap z).hom
        (((relCurve C R).presheaf.germ (d.cover.opens ((relCurveMap C R R').base y))
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
  -- assemble
  have hunit : IsUnit (((relCurveMap C R R').stalkMap z).hom
      (((relCurve C R).presheaf.germ
        (D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y))
        ((relCurveMap C R R').base z) hfzW).hom
        (u : Γ(relCurve C R,
          D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y))))) :=
    (u.isUnit.map ((relCurve C R).presheaf.germ
      (D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y))
      ((relCurveMap C R R').base z) hfzW).hom).map
      ((relCurveMap C R R').stalkMap z).hom
  have hkey : ((relCurve C R').presheaf.germ ((D.baseChange R').pieces j) z hzj).hom
      (A.pulledEqn R' j) =
      (hunit.unit : ((relCurve C R').presheaf.stalk z)ˣ) *
        (((relCurveMap C R R').stalkMap z).hom
          (((relCurve C R).presheaf.germ (d.cover.opens ((relCurveMap C R R').base y))
            ((relCurveMap C R R').base z) hfzy).hom
            (d.eqn ((relCurveMap C R R').base y)))) := by
    rw [hgermF, hdecomp, map_mul, IsUnit.unit_spec]
  rw [hgermG]
  have hSM : ((relCurveMap C R R').stalkMap z).hom
      (((relCurve C R).presheaf.germ (d.cover.opens ((relCurveMap C R R').base y))
        ((relCurveMap C R R').base z) hfzy).hom
        (d.eqn ((relCurveMap C R R').base y))) =
      ↑hunit.unit⁻¹ *
        ((relCurve C R').presheaf.germ ((D.baseChange R').pieces j) z hzj).hom
          (A.pulledEqn R' j) := by
    rw [hkey, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hSM]
  exact mul_mem hunit.unit⁻¹.isUnit.mem_nonZeroDivisors hF

/-- **The pulled local-equation system from an explicit regularity witness**: this is the
bare `Scheme.LocalEquations.pullback` construction along the relative-curve comparison.

Unlike `pulledEquations` below, this definition does not ask for projective colengths: callers
that already know the pulled equations are regular can supply exactly the `hreg` hypothesis
accepted by `Scheme.LocalEquations.pullback`. -/
noncomputable def pulledEquationsOfHreg
    (hreg : ∀ (y z : relCurve C R')
      (hz : z ∈ (d.cover.pullback (relCurveMap C R R')).opens y),
      ((relCurve C R').presheaf.germ
        ((d.cover.pullback (relCurveMap C R R')).opens y) z hz).hom
          (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d y)
        ∈ nonZeroDivisors ((relCurve C R').presheaf.stalk z)) :
    (relCurve C R').LocalEquations :=
  d.pullback (relCurveMap C R R') hreg

@[simp]
lemma pulledEquationsOfHreg_cover
    (hreg : ∀ (y z : relCurve C R')
      (hz : z ∈ (d.cover.pullback (relCurveMap C R R')).opens y),
      ((relCurve C R').presheaf.germ
        ((d.cover.pullback (relCurveMap C R R')).opens y) z hz).hom
          (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d y)
        ∈ nonZeroDivisors ((relCurve C R').presheaf.stalk z)) :
    (pulledEquationsOfHreg (C := C) R' hreg).cover =
      d.cover.pullback (relCurveMap C R R') :=
  rfl

/-- **The pulled local-equation system**, widened: the explicit-regularity construction above,
with regularity discharged by the certificate's colength projectivity. -/
noncomputable def pulledEquations (hproj : ∀ j, Module.Projective R (A.colength j)) :
    (relCurve C R').LocalEquations :=
  pulledEquationsOfHreg (C := C) R'
    (A.germ_pullbackEqn_mem_nonZeroDivisors R' hproj)

@[simp]
lemma pulledEquations_cover (hproj : ∀ j, Module.Projective R (A.colength j)) :
    (A.pulledEquations R' hproj).cover = d.cover.pullback (relCurveMap C R R') :=
  rfl

/-- The Picard class of the pulled system is the pullback of the class of `d`. -/
lemma picClass_pulledEquations (hproj : ∀ j, Module.Projective R (A.colength j)) :
    (A.pulledEquations R' hproj).picClass =
      Scheme.CechPic.map (relCurveMap C R R') d.picClass :=
  Scheme.LocalEquations.picClass_pullback (relCurveMap C R R') d _

/-! ## The base-changed adaptation -/

/-- **The base-changed widened adaptation from an explicit regularity witness**: the
base-changed cover carries `d.pullback (relCurveMap C R R') hreg`.

The pointwise refinement clause `eqn_rel` transports clause for clause exactly as in
`DivisorAdaptation.pullback`: the target overlap is the `relCurveMap`-preimage of the source
overlap and the source clause pulls through `Scheme.Hom.unitsAppLE`.  The proof uses only the
supplied regularity witness through the resulting pulled local-equation system; it does not
use projectivity or any other colength property. -/
noncomputable def pullbackOfHreg
    (hreg : ∀ (y z : relCurve C R')
      (hz : z ∈ (d.cover.pullback (relCurveMap C R R')).opens y),
      ((relCurve C R').presheaf.germ
        ((d.cover.pullback (relCurveMap C R R')).opens y) z hz).hom
          (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d y)
        ∈ nonZeroDivisors ((relCurve C R').presheaf.stalk z)) :
    AffAdaptation (D.baseChange R') (d.pullback (relCurveMap C R R') hreg) where
  eqn := A.pulledEqn R'
  eqn_rel := fun j y' => by
    obtain ⟨u, hu⟩ := A.eqn_rel j ((relCurveMap C R R').base y')
    have hle₁ : (D.baseChange R').pieces j ⊓
        (d.pullback (relCurveMap C R R') hreg).cover.opens y' ≤
        relCurveMap C R R' ⁻¹ᵁ D.pieces j :=
      inf_le_left
    have hle₂ : (D.baseChange R').pieces j ⊓
        (d.pullback (relCurveMap C R R') hreg).cover.opens y' ≤
        relCurveMap C R R' ⁻¹ᵁ d.cover.opens ((relCurveMap C R R').base y') :=
      inf_le_right
    have hle : (D.baseChange R').pieces j ⊓
        (d.pullback (relCurveMap C R R') hreg).cover.opens y' ≤
        relCurveMap C R R' ⁻¹ᵁ
          (D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y')) :=
      (relCurveMap C R R').le_preimage_inf hle₁ hle₂
    refine ⟨(relCurveMap C R R').unitsAppLE
      (D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y'))
      ((D.baseChange R').pieces j ⊓
        (d.pullback (relCurveMap C R R') hreg).cover.opens y') hle u, ?_⟩
    -- LHS: the restricted pulled equation collapses to `appLE` of the piece equation
    have hres₁ : ((relCurve C R').presheaf.map (homOfLE (inf_le_left :
        (D.baseChange R').pieces j ⊓
            (d.pullback (relCurveMap C R R') hreg).cover.opens y' ≤
          (D.baseChange R').pieces j)).op).hom (A.pulledEqn R' j) =
        ((relCurveMap C R R').appLE (D.pieces j)
          ((D.baseChange R').pieces j ⊓
            (d.pullback (relCurveMap C R R') hreg).cover.opens y')
          hle₁).hom (A.eqn j) := by
      rw [show A.pulledEqn R' j = ((relCurveMap C R R').appLE (D.pieces j)
          ((D.baseChange R').pieces j) le_rfl).hom (A.eqn j) from rfl,
        ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    -- RHS: the restricted pulled system equation collapses to `appLE` of `d`'s equation
    have hres₂ : ((relCurve C R').presheaf.map (homOfLE (inf_le_right :
        (D.baseChange R').pieces j ⊓
            (d.pullback (relCurveMap C R R') hreg).cover.opens y' ≤
          (d.pullback (relCurveMap C R R') hreg).cover.opens y')).op).hom
        ((d.pullback (relCurveMap C R R') hreg).eqn y') =
        ((relCurveMap C R R').appLE (d.cover.opens ((relCurveMap C R R').base y'))
          ((D.baseChange R').pieces j ⊓
            (d.pullback (relCurveMap C R R') hreg).cover.opens y')
          hle₂).hom (d.eqn ((relCurveMap C R R').base y')) :=
      Scheme.LocalEquations.pullbackEqn_res (relCurveMap C R R') d y' _
    -- the pre-restriction collapse on both sides
    have e₁ := congr(($(Scheme.Hom.map_appLE (relCurveMap C R R') hle
      (homOfLE (inf_le_left : D.pieces j ⊓
        d.cover.opens ((relCurveMap C R R').base y') ≤ D.pieces j)).op)).hom (A.eqn j))
    have e₂ := congr(($(Scheme.Hom.map_appLE (relCurveMap C R R') hle
      (homOfLE (inf_le_right : D.pieces j ⊓
        d.cover.opens ((relCurveMap C R R').base y') ≤
        d.cover.opens ((relCurveMap C R R').base y'))).op)).hom
      (d.eqn ((relCurveMap C R R').base y')))
    -- transport the unit relation through `appLE`
    have key := congrArg ((relCurveMap C R R').appLE
      (D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base y'))
      ((D.baseChange R').pieces j ⊓
        (d.pullback (relCurveMap C R R') hreg).cover.opens y')
      hle).hom hu
    rw [map_mul] at key
    exact hres₁.trans (e₁.symm.trans (key.trans (congrArg₂ (· * ·) rfl
      (e₂.trans hres₂.symm))))

@[simp]
lemma pullbackOfHreg_eqn
    (hreg : ∀ (y z : relCurve C R')
      (hz : z ∈ (d.cover.pullback (relCurveMap C R R')).opens y),
      ((relCurve C R').presheaf.germ
        ((d.cover.pullback (relCurveMap C R R')).opens y) z hz).hom
          (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d y)
        ∈ nonZeroDivisors ((relCurve C R').presheaf.stalk z))
    (j : D.index) :
    (A.pullbackOfHreg R' hreg).eqn j = A.pulledEqn R' j :=
  rfl

/-- **The projective-colength specialization of `pullbackOfHreg`**.  This retains the
original public base-change API while making its only use of projectivity explicit: it
produces the regularity witness for the generic adaptation pullback. -/
noncomputable def pullback (hproj : ∀ j, Module.Projective R (A.colength j)) :
    AffAdaptation (D.baseChange R') (A.pulledEquations R' hproj) :=
  A.pullbackOfHreg R' (A.germ_pullbackEqn_mem_nonZeroDivisors R' hproj)

@[simp]
lemma pullback_eqn (hproj : ∀ j, Module.Projective R (A.colength j)) (j : D.index) :
    (A.pullback R' hproj).eqn j = A.pulledEqn R' j := rfl

end AffAdaptation

end AlgebraicGeometry
