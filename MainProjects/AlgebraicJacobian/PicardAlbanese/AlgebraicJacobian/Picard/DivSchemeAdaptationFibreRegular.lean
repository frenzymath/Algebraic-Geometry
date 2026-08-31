/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeed
import AlgebraicJacobian.Picard.DivisorFamilyPullbackMap

/-!
# Fibre regularity for an adaptation extracted from a theta-generator seed

The certificate assembler requires each adaptation equation to remain regular on every
residue-field fibre.  This file transports the corresponding `ThetaGeneratorSeed`
property through the extracted local-equation system and the adaptation's pointwise
`eqn_rel` units, without assuming any colength certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-- A ring equivalence carries nonzerodivisors to nonzerodivisors. -/
private lemma map_mem_nonZeroDivisors {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {x : A} (hx : x ∈ nonZeroDivisors A) :
    e x ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff] at hx ⊢
  obtain ⟨hl, hr⟩ := hx
  constructor
  · intro y hy
    have h := congrArg e.symm hy
    rw [map_mul, map_zero, e.symm_apply_apply] at h
    have hy0 : e.symm y = 0 := hl _ h
    calc y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = 0 := by rw [hy0, map_zero]
  · intro y hy
    have h := congrArg e.symm hy
    rw [map_mul, map_zero, e.symm_apply_apply] at h
    have hy0 : e.symm y = 0 := hr _ h
    calc y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = 0 := by rw [hy0, map_zero]

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : Nat}
variable {K : Submodule R (relThetaSections C R pi a)}

/-- The side-uniform piece-sections base-change equivalence on a pinned chart. -/
noncomputable def relPinnedPieceBaseChange
    (L : Type u) [CommRing L] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
    (b : Bool) (g : Γ(relCurve C R, relPinnedChart C R pi b)) :
    L ⊗[R] Γ(relCurve C R, (relCurve C R).basicOpen g) ≃ₐ[L]
      Γ(relCurve C L,
        (relCurve C L).basicOpen (relPinnedSectionsMap C R L pi b g)) :=
  match b with
  | false =>
      pieceTermBaseChangeAlg L (fiberChart₀ pi)
        (fiberTwoCover pi).isAffineOpen₀.isCompact
        (fiberTwoCover pi).isAffineOpen₀.isQuasiSeparated
        (relCover_isAffineOpen₀ C R (fiberTwoCover pi))
        (relCover_isAffineOpen₀ C L (fiberTwoCover pi)) g
  | true =>
      pieceTermBaseChangeAlg L (fiberChart₁ pi)
        (fiberTwoCover pi).isAffineOpen₁.isCompact
        (fiberTwoCover pi).isAffineOpen₁.isQuasiSeparated
        (relCover_isAffineOpen₁ C R (fiberTwoCover pi))
        (relCover_isAffineOpen₁ C L (fiberTwoCover pi)) g

/-- The side-uniform scheme-level comparison on a pinned basic open. -/
noncomputable def relPinnedPieceSectionsMap
    (L : Type u) [CommRing L] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
    (b : Bool) (g : Γ(relCurve C R, relPinnedChart C R pi b)) :
    Γ(relCurve C R, (relCurve C R).basicOpen g) →+*
      Γ(relCurve C L,
        (relCurve C L).basicOpen (relPinnedSectionsMap C R L pi b g)) :=
  match b with
  | false => pieceSectionsMap L (fiberChart₀ pi) g
  | true => pieceSectionsMap L (fiberChart₁ pi) g

lemma relPinnedPieceBaseChange_one_tmul
    (L : Type u) [CommRing L] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
    (b : Bool) (g : Γ(relCurve C R, relPinnedChart C R pi b))
    (s : Γ(relCurve C R, (relCurve C R).basicOpen g)) :
    relPinnedPieceBaseChange (C := C) (R := R) (pi := pi) L b g
        ((1 : L) ⊗ₜ[R] s) =
      relPinnedPieceSectionsMap (C := C) (R := R) (pi := pi) L b g s := by
  cases b with
  | false =>
      exact pieceTermBaseChangeAlg_one_tmul L (fiberChart₀ pi)
        (fiberTwoCover pi).isAffineOpen₀.isCompact
        (fiberTwoCover pi).isAffineOpen₀.isQuasiSeparated
        (relCover_isAffineOpen₀ C R (fiberTwoCover pi))
        (relCover_isAffineOpen₀ C L (fiberTwoCover pi)) g s
  | true =>
      exact pieceTermBaseChangeAlg_one_tmul L (fiberChart₁ pi)
        (fiberTwoCover pi).isAffineOpen₁.isCompact
        (fiberTwoCover pi).isAffineOpen₁.isQuasiSeparated
        (relCover_isAffineOpen₁ C R (fiberTwoCover pi))
        (relCover_isAffineOpen₁ C L (fiberTwoCover pi)) g s

/-- Basic opens of pinned-chart sections commute with relative base change, uniformly
in the chosen side. -/
lemma relPinnedSectionsMap_basicOpen
    (L : Type u) [CommRing L] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
    (b : Bool) (g : Γ(relCurve C R, relPinnedChart C R pi b)) :
    (relCurve C L).basicOpen (relPinnedSectionsMap C R L pi b g) =
      relCurveMap C R L ⁻¹ᵁ (relCurve C R).basicOpen g := by
  cases b with
  | false => exact relSectionsMap_basicOpen C R L (fiberChart₀ pi) g
  | true => exact relSectionsMap_basicOpen C R L (fiberChart₁ pi) g

lemma relPinnedPieceSectionsMap_eq_appLE
    (L : Type u) [CommRing L] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
    (b : Bool) (g : Γ(relCurve C R, relPinnedChart C R pi b))
    (s : Γ(relCurve C R, (relCurve C R).basicOpen g)) :
    relPinnedPieceSectionsMap (C := C) (R := R) (pi := pi) L b g s =
      ((relCurveMap C R L).appLE
        ((relCurve C R).basicOpen g)
        ((relCurve C L).basicOpen (relPinnedSectionsMap C R L pi b g))
        (relPinnedSectionsMap_basicOpen (C := C) (R := R) (pi := pi) L b g).le).hom s := by
  cases b <;> rfl

/-- The side-uniform piece comparison carries the restriction of a pinned-chart section
to the restriction of its transported section. -/
lemma relPinnedPieceSectionsMap_algebraMap
    (L : Type u) [CommRing L] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
    (b : Bool) (g s : Γ(relCurve C R, relPinnedChart C R pi b)) :
    relPinnedPieceSectionsMap (C := C) (R := R) (pi := pi) L b g
        (algebraMap Γ(relCurve C R, relPinnedChart C R pi b)
          Γ(relCurve C R, (relCurve C R).basicOpen g) s) =
      algebraMap Γ(relCurve C L, relPinnedChart C L pi b)
        Γ(relCurve C L,
          (relCurve C L).basicOpen (relPinnedSectionsMap C R L pi b g))
        (relPinnedSectionsMap C R L pi b s) := by
  cases b with
  | false => exact pieceSectionsMap_algebraMap L (fiberChart₀ pi) g s
  | true => exact pieceSectionsMap_algebraMap L (fiberChart₁ pi) g s

namespace ThetaGeneratorSeed

variable {D : ThetaGeneratorSeed C R pi a K}

/-- The seed's fibre-regularity clause on all basic subopens includes the whole piece. -/
theorem eqn_tmul_one_mem_nonZeroDivisors (hD : D.IsGenerator)
    (z : relCurve C R) (p : PrimeSpectrum R) :
    (D.eqn z ⊗ₜ[R] (1 : p.asIdeal.ResidueField)) ∈
      nonZeroDivisors
        (Γ(relCurve C R, D.piece z) ⊗[R] p.asIdeal.ResidueField) := by
  exact tmul_one_mem_nonZeroDivisors_of_eq p.asIdeal.ResidueField
    (Scheme.basicOpen_one (X := relCurve C R) (U := D.piece z)).symm (D.eqn z)
    (hD.fibre_regular z p (1 : Γ(relCurve C R, D.piece z)))

variable [IsNoetherianRing R]

/-- Restricting the pulled seed equation to the base-changed seed piece is exactly the
side-uniform base change of the original seed equation.  This is the section-level bridge
from the pulled presentation divisor to the residue-fibre reading of the pointwise seed. -/
theorem pullbackEqn_res_self_eq_relPinnedPieceSectionsMap (hD : D.IsGenerator)
    (p : PrimeSpectrum R) (z : relCurve C p.asIdeal.ResidueField) :
    (relCurve C p.asIdeal.ResidueField).resHom
        (relPinnedSectionsMap_basicOpen (C := C) (R := R) (pi := pi)
          p.asIdeal.ResidueField
          (D.side ((relCurveMap C R p.asIdeal.ResidueField).base z))
          (D.h ((relCurveMap C R p.asIdeal.ResidueField).base z))).le
        (Scheme.LocalEquations.pullbackEqn
          (relCurveMap C R p.asIdeal.ResidueField) (D.localEquations hD) z) =
      relPinnedPieceSectionsMap (C := C) (R := R) (pi := pi)
        p.asIdeal.ResidueField
        (D.side ((relCurveMap C R p.asIdeal.ResidueField).base z))
        (D.h ((relCurveMap C R p.asIdeal.ResidueField).base z))
        (D.eqn ((relCurveMap C R p.asIdeal.ResidueField).base z)) := by
  let y : relCurve C R := (relCurveMap C R p.asIdeal.ResidueField).base z
  let hopen := relPinnedSectionsMap_basicOpen (C := C) (R := R) (pi := pi)
    p.asIdeal.ResidueField (D.side y) (D.h y)
  calc
    _ = ((relCurveMap C R p.asIdeal.ResidueField).appLE
          ((relCurve C R).basicOpen (D.h y))
          ((relCurve C p.asIdeal.ResidueField).basicOpen
            (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y) (D.h y)))
          hopen.le).hom (D.eqn y) :=
      Scheme.LocalEquations.pullbackEqn_res
        (relCurveMap C R p.asIdeal.ResidueField) (D.localEquations hD) z hopen.le
    _ = _ := (relPinnedPieceSectionsMap_eq_appLE
      (C := C) (R := R) (pi := pi) p.asIdeal.ResidueField
      (D.side y) (D.h y) (D.eqn y)).symm

/-- At a residue-fibre point, the germ of the pulled local equation is the germ of the
transported pinned-chart reading of the seed section indexed by the image point. -/
theorem germ_self_pullbackEqn_eq_germ_relPinnedSectionsMap (hD : D.IsGenerator)
    (p : PrimeSpectrum R) (z : relCurve C p.asIdeal.ResidueField)
    (hzPiece : z ∈ (relCurve C p.asIdeal.ResidueField).basicOpen
      (relPinnedSectionsMap C R p.asIdeal.ResidueField pi
        (D.side ((relCurveMap C R p.asIdeal.ResidueField).base z))
        (D.h ((relCurveMap C R p.asIdeal.ResidueField).base z))))
    (hzSide : z ∈ relPinnedChart C p.asIdeal.ResidueField pi
      (D.side ((relCurveMap C R p.asIdeal.ResidueField).base z))) :
    ((relCurve C p.asIdeal.ResidueField).presheaf.germ
        (((D.localEquations hD).cover.pullback
          (relCurveMap C R p.asIdeal.ResidueField)).opens z) z
        (((D.localEquations hD).cover.pullback
          (relCurveMap C R p.asIdeal.ResidueField)).mem_opens z)).hom
        (Scheme.LocalEquations.pullbackEqn
          (relCurveMap C R p.asIdeal.ResidueField) (D.localEquations hD) z) =
      ((relCurve C p.asIdeal.ResidueField).presheaf.germ
        (relPinnedChart C p.asIdeal.ResidueField pi
          (D.side ((relCurveMap C R p.asIdeal.ResidueField).base z))) z hzSide).hom
        (relPinnedSectionsMap C R p.asIdeal.ResidueField pi
          (D.side ((relCurveMap C R p.asIdeal.ResidueField).base z))
          (relThetaResSide a
            (D.side ((relCurveMap C R p.asIdeal.ResidueField).base z)) le_rfl
            (D.sec ((relCurveMap C R p.asIdeal.ResidueField).base z)))) := by
  let y : relCurve C R := (relCurveMap C R p.asIdeal.ResidueField).base z
  let hopen := relPinnedSectionsMap_basicOpen (C := C) (R := R) (pi := pi)
    p.asIdeal.ResidueField (D.side y) (D.h y)
  have hres := D.pullbackEqn_res_self_eq_relPinnedPieceSectionsMap hD p z
  have hgerm := congrArg
    (((relCurve C p.asIdeal.ResidueField).presheaf.germ
      ((relCurve C p.asIdeal.ResidueField).basicOpen
        (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y) (D.h y)))
      z hzPiece).hom) hres
  have heqn : D.eqn y =
      algebraMap Γ(relCurve C R, relPinnedChart C R pi (D.side y))
        Γ(relCurve C R, (relCurve C R).basicOpen (D.h y))
        (relThetaResSide a (D.side y) le_rfl (D.sec y)) := by
    change relThetaResSide a (D.side y) (D.piece_le y) (D.sec y) =
      (relCurve C R).resHom (D.piece_le y)
        (relThetaResSide a (D.side y) le_rfl (D.sec y))
    exact (resHom_relThetaResSide a (D.side y) le_rfl (D.piece_le y) (D.sec y)).symm
  have hpiece : relPinnedPieceSectionsMap (C := C) (R := R) (pi := pi)
      p.asIdeal.ResidueField (D.side y) (D.h y) (D.eqn y) =
      algebraMap
        Γ(relCurve C p.asIdeal.ResidueField,
          relPinnedChart C p.asIdeal.ResidueField pi (D.side y))
        Γ(relCurve C p.asIdeal.ResidueField,
          (relCurve C p.asIdeal.ResidueField).basicOpen
            (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y) (D.h y)))
        (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y)
          (relThetaResSide a (D.side y) le_rfl (D.sec y))) := by
    rw [heqn]
    exact relPinnedPieceSectionsMap_algebraMap
      (C := C) (R := R) (pi := pi) p.asIdeal.ResidueField
      (D.side y) (D.h y) (relThetaResSide a (D.side y) le_rfl (D.sec y))
  rw [hpiece] at hgerm
  have hleft := TopCat.Presheaf.germ_res_apply
    (relCurve C p.asIdeal.ResidueField).presheaf (homOfLE hopen.le) z hzPiece
    (Scheme.LocalEquations.pullbackEqn
      (relCurveMap C R p.asIdeal.ResidueField) (D.localEquations hD) z)
  have hright := TopCat.Presheaf.germ_res_apply
    (relCurve C p.asIdeal.ResidueField).presheaf
    (homOfLE ((relCurve C p.asIdeal.ResidueField).basicOpen_le
      (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y) (D.h y))))
    z hzPiece
    (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y)
      (relThetaResSide a (D.side y) le_rfl (D.sec y)))
  change
    ((relCurve C p.asIdeal.ResidueField).presheaf.germ
        ((relCurve C p.asIdeal.ResidueField).basicOpen
          (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y) (D.h y)))
        z hzPiece).hom
        (((relCurve C p.asIdeal.ResidueField).presheaf.map
          (homOfLE hopen.le).op).hom
          (Scheme.LocalEquations.pullbackEqn
            (relCurveMap C R p.asIdeal.ResidueField) (D.localEquations hD) z)) =
      ((relCurve C p.asIdeal.ResidueField).presheaf.germ
        ((relCurve C p.asIdeal.ResidueField).basicOpen
          (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y) (D.h y)))
        z hzPiece).hom
        (((relCurve C p.asIdeal.ResidueField).presheaf.map
          (homOfLE ((relCurve C p.asIdeal.ResidueField).basicOpen_le
            (relPinnedSectionsMap C R p.asIdeal.ResidueField pi
              (D.side y) (D.h y)))).op).hom
          (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y)
            (relThetaResSide a (D.side y) le_rfl (D.sec y)))) at hgerm
  rw [hleft, hright] at hgerm
  simpa only [y, Scheme.PointedCover.pullback_opens,
    ThetaGeneratorSeed.localEquations_cover_opens, ThetaGeneratorSeed.piece] using hgerm

/-- Version of `germ_self_pullbackEqn_eq_germ_relPinnedSectionsMap` indexed by an
explicit total-space point equal to the image of the residue-fibre point. -/
theorem germ_self_pullbackEqn_eq_germ_relPinnedSectionsMap_of_map_eq
    (hD : D.IsGenerator) (p : PrimeSpectrum R)
    (z : relCurve C p.asIdeal.ResidueField) (y : relCurve C R)
    (hy : (relCurveMap C R p.asIdeal.ResidueField).base z = y)
    (hzPiece : z ∈ (relCurve C p.asIdeal.ResidueField).basicOpen
      (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y) (D.h y)))
    (hzSide : z ∈ relPinnedChart C p.asIdeal.ResidueField pi (D.side y)) :
    ((relCurve C p.asIdeal.ResidueField).presheaf.germ
        (((D.localEquations hD).cover.pullback
          (relCurveMap C R p.asIdeal.ResidueField)).opens z) z
        (((D.localEquations hD).cover.pullback
          (relCurveMap C R p.asIdeal.ResidueField)).mem_opens z)).hom
        (Scheme.LocalEquations.pullbackEqn
          (relCurveMap C R p.asIdeal.ResidueField) (D.localEquations hD) z) =
      ((relCurve C p.asIdeal.ResidueField).presheaf.germ
        (relPinnedChart C p.asIdeal.ResidueField pi (D.side y)) z hzSide).hom
        (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y)
          (relThetaResSide a (D.side y) le_rfl (D.sec y))) := by
  subst y
  exact D.germ_self_pullbackEqn_eq_germ_relPinnedSectionsMap hD p z hzPiece hzSide

/-- The pullback of the seed local equation to a residue-field fibre is regular at its
own indexed point.  The whole-piece tensor regularity is carried through the affine
basic-open base-change equivalence, then compared with `pullbackEqn` by restriction
naturality. -/
theorem germ_self_pullbackEqn_mem_nonZeroDivisors (hD : D.IsGenerator)
    (p : PrimeSpectrum R) (z : relCurve C p.asIdeal.ResidueField) :
    ((relCurve C p.asIdeal.ResidueField).presheaf.germ
      (((D.localEquations hD).cover.pullback
        (relCurveMap C R p.asIdeal.ResidueField)).opens z) z
      (((D.localEquations hD).cover.pullback
        (relCurveMap C R p.asIdeal.ResidueField)).mem_opens z)).hom
      (Scheme.LocalEquations.pullbackEqn
        (relCurveMap C R p.asIdeal.ResidueField) (D.localEquations hD) z) ∈
      nonZeroDivisors ((relCurve C p.asIdeal.ResidueField).presheaf.stalk z) := by
  let y : relCurve C R := (relCurveMap C R p.asIdeal.ResidueField).base z
  have hseed := D.eqn_tmul_one_mem_nonZeroDivisors hD y p
  have hcomm := map_mem_nonZeroDivisors
    (Algebra.TensorProduct.comm R
      Γ(relCurve C R, D.piece y) p.asIdeal.ResidueField).toRingEquiv hseed
  change (Algebra.TensorProduct.comm R
      Γ(relCurve C R, D.piece y) p.asIdeal.ResidueField)
      (D.eqn y ⊗ₜ[R] (1 : p.asIdeal.ResidueField)) ∈
        nonZeroDivisors
          (p.asIdeal.ResidueField ⊗[R] Γ(relCurve C R, D.piece y)) at hcomm
  rw [Algebra.TensorProduct.comm_tmul] at hcomm
  have hpulled := map_mem_nonZeroDivisors
    (relPinnedPieceBaseChange (C := C) (R := R) (pi := pi)
      p.asIdeal.ResidueField (D.side y) (D.h y)).toRingEquiv hcomm
  change relPinnedPieceBaseChange (C := C) (R := R) (pi := pi)
      p.asIdeal.ResidueField (D.side y) (D.h y)
      ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] D.eqn y) ∈
        nonZeroDivisors
          Γ(relCurve C p.asIdeal.ResidueField,
            (relCurve C p.asIdeal.ResidueField).basicOpen
              (relPinnedSectionsMap C R p.asIdeal.ResidueField pi
                (D.side y) (D.h y))) at hpulled
  rw [relPinnedPieceBaseChange_one_tmul] at hpulled
  have hopen := relPinnedSectionsMap_basicOpen (C := C) (R := R) (pi := pi)
    p.asIdeal.ResidueField (D.side y) (D.h y)
  have hzW : z ∈ (relCurve C p.asIdeal.ResidueField).basicOpen
      (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y) (D.h y)) := by
    rw [hopen]
    exact (D.localEquations hD).cover.mem_opens y
  have hgerm := IsAffineOpen.germ_mem_nonZeroDivisors
    ((isAffineOpen_relPinnedChart C p.asIdeal.ResidueField pi (D.side y)).basicOpen
      (relPinnedSectionsMap C R p.asIdeal.ResidueField pi (D.side y) (D.h y)))
    hpulled z hzW
  have hres : (relCurve C p.asIdeal.ResidueField).resHom hopen.le
      (Scheme.LocalEquations.pullbackEqn
        (relCurveMap C R p.asIdeal.ResidueField) (D.localEquations hD) z) =
      relPinnedPieceSectionsMap (C := C) (R := R) (pi := pi)
        p.asIdeal.ResidueField (D.side y) (D.h y) (D.eqn y) := by
    simpa only [y, hopen] using
      D.pullbackEqn_res_self_eq_relPinnedPieceSectionsMap hD p z
  rw [← hres] at hgerm
  have hgres := TopCat.Presheaf.germ_res_apply
    (relCurve C p.asIdeal.ResidueField).presheaf (homOfLE hopen.le) z hzW
    (Scheme.LocalEquations.pullbackEqn
      (relCurveMap C R p.asIdeal.ResidueField) (D.localEquations hD) z)
  change ((relCurve C p.asIdeal.ResidueField).presheaf.germ
      ((relCurve C p.asIdeal.ResidueField).basicOpen
        (relPinnedSectionsMap C R p.asIdeal.ResidueField pi
          (D.side y) (D.h y))) z hzW).hom
      (((relCurve C p.asIdeal.ResidueField).presheaf.map
        (homOfLE hopen.le).op).hom
        (Scheme.LocalEquations.pullbackEqn
          (relCurveMap C R p.asIdeal.ResidueField) (D.localEquations hD) z)) ∈
      nonZeroDivisors ((relCurve C p.asIdeal.ResidueField).presheaf.stalk z) at hgerm
  rw [hgres] at hgerm
  exact hgerm

end ThetaGeneratorSeed

namespace DivisorAdaptation

variable {R' : Type u} [CommRing R'] [Algebra k R'] [Algebra R R']
  [IsScalarTower k R R']
variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R pi d)

/-- At a point of a pulled adaptation piece, the pulled piece equation is a unit
multiple of the pulled local equation indexed by that point.  This is the reverse
orientation of the comparison used by
`DivisorAdaptation.germ_pullbackEqn_mem_nonZeroDivisors`. -/
theorem exists_germ_pulledEqn_eq_unit_mul_pullbackEqn
    (j : A.index) (z : relCurve C R')
    (hzj : z ∈ (A.toFinCoverData.baseChange R').pieces j) :
    ∃ v : ((relCurve C R').presheaf.stalk z)ˣ,
      ((relCurve C R').presheaf.germ
          ((A.toFinCoverData.baseChange R').pieces j) z hzj).hom
          (A.pulledEqn R' j) =
        (v : (relCurve C R').presheaf.stalk z) *
          ((relCurve C R').presheaf.germ
            ((d.cover.pullback (relCurveMap C R R')).opens z) z
            ((d.cover.pullback (relCurveMap C R R')).mem_opens z)).hom
            (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d z) := by
  have hzj' : z ∈ relCurveMap C R R' ⁻¹ᵁ A.pieces j := by
    rw [← A.toFinCoverData.pieces_baseChange R' j]
    exact hzj
  have hfzj : (relCurveMap C R R').base z ∈ A.pieces j := hzj'
  have hfzz : (relCurveMap C R R').base z ∈
      d.cover.opens ((relCurveMap C R R').base z) :=
    d.cover.mem_opens _
  have hfzW : (relCurveMap C R R').base z ∈
      A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z) :=
    ⟨hfzj, hfzz⟩
  have hgermF : ((relCurve C R').presheaf.germ
      ((A.toFinCoverData.baseChange R').pieces j) z hzj).hom (A.pulledEqn R' j) =
      ((relCurveMap C R R').stalkMap z).hom
        (((relCurve C R).presheaf.germ (A.pieces j)
          ((relCurveMap C R R').base z) hfzj).hom (A.eqn j)) := by
    have happ := (relCurveMap C R R').germ_stalkMap_apply
      (A.pieces j) z hfzj (A.eqn j)
    have hres : ((relCurve C R').presheaf.germ
        ((A.toFinCoverData.baseChange R').pieces j) z hzj).hom (A.pulledEqn R' j) =
        ((relCurve C R').presheaf.germ
          (relCurveMap C R R' ⁻¹ᵁ A.pieces j) z hzj').hom
          (((relCurveMap C R R').app (A.pieces j)).hom (A.eqn j)) := by
      have hle : (A.toFinCoverData.baseChange R').pieces j ≤
          relCurveMap C R R' ⁻¹ᵁ A.pieces j :=
        A.toFinCoverData.baseChange_pieces_le_preimage R' j
      have h := TopCat.Presheaf.germ_res_apply (relCurve C R').presheaf
        (homOfLE hle) z hzj (((relCurveMap C R R').app (A.pieces j)).hom (A.eqn j))
      rw [← h]
      rfl
    rw [hres, happ]
  obtain ⟨u, hu⟩ := A.eqn_rel j ((relCurveMap C R R').base z)
  have hdecomp : ((relCurve C R).presheaf.germ (A.pieces j)
      ((relCurveMap C R R').base z) hfzj).hom (A.eqn j) =
      ((relCurve C R).presheaf.germ
          (A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z))
          ((relCurveMap C R R').base z) hfzW).hom
        (u : Γ(relCurve C R,
          A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z))) *
        ((relCurve C R).presheaf.germ
          (d.cover.opens ((relCurveMap C R R').base z))
          ((relCurveMap C R R').base z) hfzz).hom
          (d.eqn ((relCurveMap C R R').base z)) := by
    have hkey := congrArg ((relCurve C R).presheaf.germ
        (A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z))
        ((relCurveMap C R R').base z) hfzW).hom hu
    rw [map_mul, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply] at hkey
    exact hkey
  have hgermG : ((relCurve C R').presheaf.germ
      ((d.cover.pullback (relCurveMap C R R')).opens z) z
      ((d.cover.pullback (relCurveMap C R R')).mem_opens z)).hom
      (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d z) =
      ((relCurveMap C R R').stalkMap z).hom
        (((relCurve C R).presheaf.germ
          (d.cover.opens ((relCurveMap C R R').base z))
          ((relCurveMap C R R').base z) hfzz).hom
          (d.eqn ((relCurveMap C R R').base z))) := by
    rw [Scheme.LocalEquations.pullbackEqn]
    have happLE : ((relCurveMap C R R').appLE
        (d.cover.opens ((relCurveMap C R R').base z))
        ((d.cover.pullback (relCurveMap C R R')).opens z) le_rfl).hom
        (d.eqn ((relCurveMap C R R').base z)) =
        ((relCurve C R').presheaf.map (homOfLE (le_refl
          ((d.cover.pullback (relCurveMap C R R')).opens z))).op).hom
          (((relCurveMap C R R').app
            (d.cover.opens ((relCurveMap C R R').base z))).hom
            (d.eqn ((relCurveMap C R R').base z))) := rfl
    rw [happLE, TopCat.Presheaf.germ_res_apply]
    exact ((relCurveMap C R R').germ_stalkMap_apply
      (d.cover.opens ((relCurveMap C R R').base z)) z hfzz
      (d.eqn ((relCurveMap C R R').base z))).symm
  have hunit : IsUnit (((relCurveMap C R R').stalkMap z).hom
      (((relCurve C R).presheaf.germ
        (A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z))
        ((relCurveMap C R R').base z) hfzW).hom
        (u : Γ(relCurve C R,
          A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z))))) :=
    (u.isUnit.map ((relCurve C R).presheaf.germ
      (A.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z))
      ((relCurveMap C R R').base z) hfzW).hom).map
      ((relCurveMap C R R').stalkMap z).hom
  refine ⟨hunit.unit, ?_⟩
  rw [hgermF, hdecomp, map_mul, IsUnit.unit_spec, hgermG]

/-- If every pulled local equation is regular at its own point, then every pulled
adaptation equation is regular on its whole affine piece.  No colength finiteness,
flatness, or certificate is assumed. -/
theorem pulledEqn_mem_nonZeroDivisors_of_self_pullbackEqn
    (hreg : ∀ z : relCurve C R',
      ((relCurve C R').presheaf.germ
        ((d.cover.pullback (relCurveMap C R R')).opens z) z
        ((d.cover.pullback (relCurveMap C R R')).mem_opens z)).hom
        (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d z) ∈
          nonZeroDivisors ((relCurve C R').presheaf.stalk z))
    (j : A.index) :
    A.pulledEqn R' j ∈
      nonZeroDivisors
        Γ(relCurve C R', (A.toFinCoverData.baseChange R').pieces j) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro t ht
  apply TopCat.Presheaf.section_ext (relCurve C R').sheaf
    ((A.toFinCoverData.baseChange R').pieces j) t 0
  intro z hzj
  rw [map_zero]
  have heqn : ((relCurve C R').presheaf.germ
      ((A.toFinCoverData.baseChange R').pieces j) z hzj).hom (A.pulledEqn R' j) ∈
      nonZeroDivisors ((relCurve C R').presheaf.stalk z) := by
    obtain ⟨v, hv⟩ := A.exists_germ_pulledEqn_eq_unit_mul_pullbackEqn
      (R' := R') j z hzj
    rw [hv]
    exact mul_mem v.isUnit.mem_nonZeroDivisors (hreg z)
  have hzero : ((relCurve C R').presheaf.germ
      ((A.toFinCoverData.baseChange R').pieces j) z hzj).hom t *
      ((relCurve C R').presheaf.germ
        ((A.toFinCoverData.baseChange R').pieces j) z hzj).hom (A.pulledEqn R' j) = 0 := by
    rw [← map_mul, ht, map_zero]
  exact (mul_right_mem_nonZeroDivisors_eq_zero_iff heqn).mp hzero

section Seed

variable [IsNoetherianRing R]
variable {D : ThetaGeneratorSeed C R pi a K} (hD : D.IsGenerator)
variable (A : DivisorAdaptation C R pi (D.localEquations hD))

/-- Every equation of an adaptation of the seed's local-equation system is regular on
the corresponding residue-field piece. -/
theorem pulledEqn_mem_nonZeroDivisors_of_seed
    (p : PrimeSpectrum R) (j : A.index) :
    A.pulledEqn p.asIdeal.ResidueField j ∈
      nonZeroDivisors
        Γ(relCurve C p.asIdeal.ResidueField,
          (A.toFinCoverData.baseChange p.asIdeal.ResidueField).pieces j) :=
  A.pulledEqn_mem_nonZeroDivisors_of_self_pullbackEqn
    (R' := p.asIdeal.ResidueField)
    (fun z => D.germ_self_pullbackEqn_mem_nonZeroDivisors hD p z) j

/-- **The noncircular adaptation fibre-regularity bridge**: the equation on every
adaptation piece remains a nonzerodivisor after tensoring with every residue field.
It uses only the seed's `fibre_regular` clause and the adaptation's `eqn_rel`; no
colength finiteness, flatness, projectivity, or certificate is assumed. -/
theorem eqn_tmul_one_mem_nonZeroDivisors_of_seed
    (j : A.index) (p : PrimeSpectrum R) :
    (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
        Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
      nonZeroDivisors
        (Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField) := by
  have hpulled := A.pulledEqn_mem_nonZeroDivisors_of_seed hD p j
  let e := A.toFinCoverData.pieceTermBaseChange p.asIdeal.ResidueField j
  have hback := map_mem_nonZeroDivisors e.symm.toRingEquiv hpulled
  have hinv : e.symm (A.pulledEqn p.asIdeal.ResidueField j) =
      ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] A.eqn j) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (A.toFinCoverData.pieceTermBaseChange_one_tmul
      p.asIdeal.ResidueField j (A.eqn j)).symm
  change e.symm (A.pulledEqn p.asIdeal.ResidueField j) ∈
    nonZeroDivisors
      (p.asIdeal.ResidueField ⊗[R] Γ(relCurve C R, A.pieces j)) at hback
  rw [hinv] at hback
  have hflip := map_mem_nonZeroDivisors
    (Algebra.TensorProduct.comm R p.asIdeal.ResidueField
      Γ(relCurve C R, A.pieces j)).toRingEquiv hback
  change (Algebra.TensorProduct.comm R p.asIdeal.ResidueField
      Γ(relCurve C R, A.pieces j))
      ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] A.eqn j) ∈
        nonZeroDivisors
          (Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField) at hflip
  rwa [Algebra.TensorProduct.comm_tmul] at hflip

end Seed

end DivisorAdaptation

namespace ThetaGeneratorSeed

variable [IsNoetherianRing R]
variable {D : ThetaGeneratorSeed C R pi a K}

/-- The exact `hregular` input of the universal certificate assembler for the finite
adaptation extracted from a theta-generator seed. -/
theorem divisorAdaptation_fibre_regular (hD : D.IsGenerator) :
    ∀ (j : (D.divisorAdaptation hD).index) (p : PrimeSpectrum R),
      ((D.divisorAdaptation hD).eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, (D.divisorAdaptation hD).pieces j) ⊗[R]
            p.asIdeal.ResidueField) ∈
        nonZeroDivisors
          (Γ(relCurve C R, (D.divisorAdaptation hD).pieces j) ⊗[R]
            p.asIdeal.ResidueField) :=
  fun j p => (D.divisorAdaptation hD).eqn_tmul_one_mem_nonZeroDivisors_of_seed hD j p

end ThetaGeneratorSeed

end AlgebraicGeometry
