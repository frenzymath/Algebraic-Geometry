/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFibre
import AlgebraicJacobian.Picard.DivisorFamilyAffSwallow
import AlgebraicJacobian.Picard.DivisorFamilyZarGlueKit

/-!
# Fibre regularity after an away localization

The regularity clause of a theta-generator seed survives an arbitrary coefficient-ring
base change.  Applying this to the composite from the original base to a residue field of
an away localization, and then using the two-stage pullback comparison, supplies the
fibrewise regularity needed to certify an adaptation of the pulled seed equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : Nat}
variable {K : Submodule R (relThetaSections C R pi a)}

local instance instIsOpenImmersionRelCurveMapAway (r : R) :
    IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
  isOpenImmersion_relCurveMap_away C R (Localization.Away r) r

namespace ThetaGeneratorSeed

variable [IsNoetherianRing R] {D : ThetaGeneratorSeed C R pi a K}

/-- Restriction of the pulled seed equation to its transported pinned basic open,
for an arbitrary coefficient-ring extension. -/
theorem pullbackEqn_res_self_eq_relPinnedPieceSectionsMap_algebra
    (hD : D.IsGenerator) (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R']
    [IsScalarTower k R R'] (z : relCurve C R') :
    (relCurve C R').resHom
        (relPinnedSectionsMap_basicOpen (C := C) (R := R) (pi := pi) R'
          (D.side ((relCurveMap C R R').base z))
          (D.h ((relCurveMap C R R').base z))).le
        (Scheme.LocalEquations.pullbackEqn
          (relCurveMap C R R') (D.localEquations hD) z) =
      relPinnedPieceSectionsMap (C := C) (R := R) (pi := pi) R'
        (D.side ((relCurveMap C R R').base z))
        (D.h ((relCurveMap C R R').base z))
        (D.eqn ((relCurveMap C R R').base z)) := by
  let y : relCurve C R := (relCurveMap C R R').base z
  let hopen := relPinnedSectionsMap_basicOpen (C := C) (R := R) (pi := pi) R'
    (D.side y) (D.h y)
  calc
    _ = ((relCurveMap C R R').appLE
          ((relCurve C R).basicOpen (D.h y))
          ((relCurve C R').basicOpen
            (relPinnedSectionsMap C R R' pi (D.side y) (D.h y)))
          hopen.le).hom (D.eqn y) :=
      Scheme.LocalEquations.pullbackEqn_res
        (relCurveMap C R R') (D.localEquations hD) z hopen.le
    _ = _ := (relPinnedPieceSectionsMap_eq_appLE
      (C := C) (R := R) (pi := pi) R' (D.side y) (D.h y) (D.eqn y)).symm

/-- The pulled seed equation is germ-regular after every coefficient-ring base change.

The seed supplies residue-fibre regularity over the Noetherian ring `R`.  Flatness of
the pinned basic-open sections upgrades it to regularity after arbitrary base change;
the pinned-piece section equivalence then reads the result on the new relative curve. -/
theorem germ_self_pullbackEqn_mem_nonZeroDivisors_algebra
    (hD : D.IsGenerator) (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R']
    [IsScalarTower k R R'] (z : relCurve C R') :
    ((relCurve C R').presheaf.germ
      (((D.localEquations hD).cover.pullback (relCurveMap C R R')).opens z) z
      (((D.localEquations hD).cover.pullback
        (relCurveMap C R R')).mem_opens z)).hom
      (Scheme.LocalEquations.pullbackEqn
        (relCurveMap C R R') (D.localEquations hD) z) ∈
      nonZeroDivisors ((relCurve C R').presheaf.stalk z) := by
  let y : relCurve C R := (relCurveMap C R R').base z
  letI : Module.Flat R Γ(relCurve C R, D.piece y) := D.flat_sections_piece y
  have hseed :=
    Algebra.TensorProduct.includeRight_mem_nonZeroDivisors_of_forall_tmul_residueField
      (fun p => D.eqn_tmul_one_mem_nonZeroDivisors hD y p) R'
  change ((1 : R') ⊗ₜ[R] D.eqn y) ∈
      nonZeroDivisors (R' ⊗[R] Γ(relCurve C R, D.piece y)) at hseed
  have hpulled := map_mem_nonZeroDivisors'
    (relPinnedPieceBaseChange (C := C) (R := R) (pi := pi)
      R' (D.side y) (D.h y)).toRingEquiv hseed
  change relPinnedPieceBaseChange (C := C) (R := R) (pi := pi)
      R' (D.side y) (D.h y) ((1 : R') ⊗ₜ[R] D.eqn y) ∈
        nonZeroDivisors
          Γ(relCurve C R', (relCurve C R').basicOpen
            (relPinnedSectionsMap C R R' pi (D.side y) (D.h y))) at hpulled
  rw [relPinnedPieceBaseChange_one_tmul] at hpulled
  have hopen := relPinnedSectionsMap_basicOpen (C := C) (R := R) (pi := pi)
    R' (D.side y) (D.h y)
  have hzW : z ∈ (relCurve C R').basicOpen
      (relPinnedSectionsMap C R R' pi (D.side y) (D.h y)) := by
    rw [hopen]
    exact (D.localEquations hD).cover.mem_opens y
  have hgerm := IsAffineOpen.germ_mem_nonZeroDivisors
    ((isAffineOpen_relPinnedChart C R' pi (D.side y)).basicOpen
      (relPinnedSectionsMap C R R' pi (D.side y) (D.h y)))
    hpulled z hzW
  have hres : (relCurve C R').resHom hopen.le
      (Scheme.LocalEquations.pullbackEqn
        (relCurveMap C R R') (D.localEquations hD) z) =
      relPinnedPieceSectionsMap (C := C) (R := R) (pi := pi)
        R' (D.side y) (D.h y) (D.eqn y) := by
    simpa only [y, hopen] using
      D.pullbackEqn_res_self_eq_relPinnedPieceSectionsMap_algebra hD R' z
  rw [← hres] at hgerm
  have hgres := TopCat.Presheaf.germ_res_apply
    (relCurve C R').presheaf (homOfLE hopen.le) z hzW
    (Scheme.LocalEquations.pullbackEqn
      (relCurveMap C R R') (D.localEquations hD) z)
  change ((relCurve C R').presheaf.germ
      ((relCurve C R').basicOpen
        (relPinnedSectionsMap C R R' pi (D.side y) (D.h y))) z hzW).hom
      (((relCurve C R').presheaf.map (homOfLE hopen.le).op).hom
        (Scheme.LocalEquations.pullbackEqn
          (relCurveMap C R R') (D.localEquations hD) z)) ∈
      nonZeroDivisors ((relCurve C R').presheaf.stalk z) at hgerm
  rw [hgres] at hgerm
  exact hgerm

/-- Full member-normalized regularity of the seed equations after arbitrary base change. -/
theorem germ_pullbackEqn_mem_nonZeroDivisors_algebra
    (hD : D.IsGenerator) (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R']
    [IsScalarTower k R R'] :
    ∀ (y z : relCurve C R')
      (hz : z ∈ ((D.localEquations hD).cover.pullback
        (relCurveMap C R R')).opens y),
      ((relCurve C R').presheaf.germ
        (((D.localEquations hD).cover.pullback
          (relCurveMap C R R')).opens y) z hz).hom
        (Scheme.LocalEquations.pullbackEqn
          (relCurveMap C R R') (D.localEquations hD) y) ∈
        nonZeroDivisors ((relCurve C R').presheaf.stalk z) :=
  Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_forall_self
    (relCurveMap C R R') (D.localEquations hD)
      (fun z => D.germ_self_pullbackEqn_mem_nonZeroDivisors_algebra hD R' z)

end ThetaGeneratorSeed

namespace AffAdaptation

variable [IsNoetherianRing R]
variable {D : ThetaGeneratorSeed C R pi a K}

/-- Fibrewise regularity for an adaptation of the seed equations after an away
localization.  No condition on the prime of the localization is needed. -/
theorem eqn_tmul_one_mem_nonZeroDivisors_seed_pullback_away
    (hD : D.IsGenerator) (r : R)
    (Dc : AffCoverData C (Localization.Away r))
    (A : AffAdaptation Dc
      ((D.localEquations hD).pullback
        (relCurveMap C R (Localization.Away r))
        (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
          (relCurveMap C R (Localization.Away r)) (D.localEquations hD))))
    (j : Dc.index) (q : PrimeSpectrum (Localization.Away r)) :
    (A.eqn j ⊗ₜ[Localization.Away r] (1 : q.asIdeal.ResidueField) :
        Γ(relCurve C (Localization.Away r), Dc.pieces j) ⊗[Localization.Away r]
          q.asIdeal.ResidueField) ∈
      nonZeroDivisors
        (Γ(relCurve C (Localization.Away r), Dc.pieces j) ⊗[Localization.Away r]
          q.asIdeal.ResidueField) := by
  let f : relCurve C (Localization.Away r) ⟶ relCurve C R :=
    relCurveMap C R (Localization.Away r)
  let g : relCurve C q.asIdeal.ResidueField ⟶ relCurve C (Localization.Away r) :=
    relCurveMap C (Localization.Away r) q.asIdeal.ResidueField
  let h : relCurve C q.asIdeal.ResidueField ⟶ relCurve C R :=
    relCurveMap C R q.asIdeal.ResidueField
  have hgf : g ≫ f = h :=
    relCurveMap_comp (R' := Localization.Away r) (R'' := q.asIdeal.ResidueField)
  refine A.eqn_tmul_one_mem_nonZeroDivisors_of_self_pullbackEqn j q (fun z => ?_)
  have htwo := Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_pullback
    hgf (D.localEquations hD)
      (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
        f (D.localEquations hD))
      (D.germ_pullbackEqn_mem_nonZeroDivisors_algebra hD q.asIdeal.ResidueField)
  exact htwo z z
    ((((D.localEquations hD).pullback f
      (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
        f (D.localEquations hD))).cover.pullback g).mem_opens z)

variable [IsProper C.hom]

/-- On a swallowed away-local adaptation, the seed regularity supplies projectivity of
every piece colength; finiteness is the already-proved swallowed-cover consequence. -/
theorem forall_projective_colength_seed_pullback_away
    (hD : D.IsGenerator) (r : R)
    (Dc : AffCoverData C (Localization.Away r))
    (A : AffAdaptation Dc
      ((D.localEquations hD).pullback
        (relCurveMap C R (Localization.Away r))
        (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
          (relCurveMap C R (Localization.Away r)) (D.localEquations hD))))
    (hsw : Dc.SwallowedBy
      ((D.localEquations hD).pullback
        (relCurveMap C R (Localization.Away r))
        (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
          (relCurveMap C R (Localization.Away r)) (D.localEquations hD)))) :
    ∀ j, Module.Projective (Localization.Away r) (A.colength j) := by
  have hfin := A.forall_finite_colength_of_swallowedBy hsw
  intro j
  letI : Module.Finite (Localization.Away r) (A.colength j) := hfin j
  exact A.projective_colength_of_forall_tmul_residueField j
    (fun q => eqn_tmul_one_mem_nonZeroDivisors_seed_pullback_away hD r Dc A j q)

end AffAdaptation

end AlgebraicGeometry
