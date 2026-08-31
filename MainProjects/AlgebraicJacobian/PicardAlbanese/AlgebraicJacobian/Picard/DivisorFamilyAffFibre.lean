/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffMapAlg

/-!
# Obligation I-0492 4(i) DISCHARGED from the seed, at an arbitrary widened cover

Protection I-0492 clause 4(i) relocates — rather than removes — the *fibrewise-finite support*
obligation, and requires it to come from the seed's own degree data rather than hide inside a
`LocalEquations`.  `DivisorFamilyAffMapAlg.lean` restated it on the fibre curve
(`AffAdaptation.eqn_tmul_one_mem_nonZeroDivisors_iff`) but explicitly left it an obligation.
This file discharges it.

## Why this is possible at all, and it is a statement about the *shape* of the seed input

The chart-typed lane discharges its own `hfib` through
`DivisorAdaptation.eqn_tmul_one_mem_nonZeroDivisors_of_seed`, and the temptation is to read that
as chart-typed machinery.  It is not.  Trace its input: it consumes
`ThetaGeneratorSeed.germ_self_pullbackEqn_mem_nonZeroDivisors`, whose statement mentions

* the local-equation system `d = D.localEquations hD`,
* the fibre curve over `κ(p)`,
* and NOTHING ELSE — no cover, no pieces, no chart, no partition of unity.

It says: *the pulled system equation is regular at its own point on every residue-field fibre*.
That is a property of the seed and the fibre, so it is available verbatim to a widened cover.
What the chart-typed layer adds on top of it is only the comparison "the pulled PIECE equation
is a unit multiple of the pulled SYSTEM equation", and `eqn_rel` — a field of `AffAdaptation`
too — is the whole content of that comparison.

So obligation 4(i) is not a chart-typed accident: it transports, and it transports at an
ARBITRARY affine open, because the piece enters only through `eqn_rel` and the affine germ seam.

## Main declarations

* `AlgebraicGeometry.AffAdaptation.exists_germ_pulledEqn_eq_unit_mul_pullbackEqn` — the reverse
  orientation of the comparison in `germ_pullbackEqn_mem_nonZeroDivisors`, at the point itself
  and with **no projectivity hypothesis** (that hypothesis is what the forward direction needs
  and this one does not).
* `AlgebraicGeometry.AffAdaptation.pulledEqn_mem_nonZeroDivisors_of_self_pullbackEqn` — from
  self-regularity of the pulled system, section-level regularity of every pulled piece equation.
* `AlgebraicGeometry.AffAdaptation.eqn_tmul_one_mem_nonZeroDivisors_of_self_pullbackEqn` — the
  same read in the tensor shape the certificate assembler asks for.
* `AlgebraicGeometry.ThetaGeneratorSeed.affAdaptation_fibre_regular` — **obligation 4(i),
  discharged**: for a theta-generator seed, EVERY widened adaptation over EVERY widened cover
  satisfies the assembler's `hfib`, uniformly in the cover, the piece and the prime.
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

namespace AffAdaptation

variable {R' : Type u} [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d)

/-- **The comparison, in the orientation that needs no projectivity.**  At a point `z` of a
base-changed piece, the pulled piece equation is a UNIT multiple of the pulled system equation
indexed by `z` itself.

`germ_pullbackEqn_mem_nonZeroDivisors` (`DivisorFamilyAffBaseChange.lean`) runs the same
decomposition in the other direction and therefore needs the pulled piece equation to be
regular, which costs `Module.Projective R (A.colength j)`.  Here the piece equation is the
CONCLUSION's subject rather than its input, so nothing about the colength is assumed — which is
what makes this usable to *produce* the fibrewise datum instead of consuming it. -/
theorem exists_germ_pulledEqn_eq_unit_mul_pullbackEqn (j : D.index) (z : relCurve C R')
    (hzj : z ∈ (D.baseChange R').pieces j) :
    ∃ v : ((relCurve C R').presheaf.stalk z)ˣ,
      ((relCurve C R').presheaf.germ ((D.baseChange R').pieces j) z hzj).hom
          (A.pulledEqn R' j) =
        (v : (relCurve C R').presheaf.stalk z) *
          ((relCurve C R').presheaf.germ
            ((d.cover.pullback (relCurveMap C R R')).opens z) z
            ((d.cover.pullback (relCurveMap C R R')).mem_opens z)).hom
            (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d z) := by
  have hzj' : z ∈ relCurveMap C R R' ⁻¹ᵁ D.pieces j := hzj
  have hfzj : (relCurveMap C R R').base z ∈ D.pieces j := hzj'
  have hfzz : (relCurveMap C R R').base z ∈
      d.cover.opens ((relCurveMap C R R').base z) :=
    d.cover.mem_opens _
  have hfzW : (relCurveMap C R R').base z ∈
      D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z) :=
    ⟨hfzj, hfzz⟩
  -- the pulled piece equation's germ is the stalk image of the piece equation's germ
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
  -- decompose the piece equation at the point itself through `eqn_rel`
  obtain ⟨u, hu⟩ := A.eqn_rel j ((relCurveMap C R R').base z)
  have hdecomp : ((relCurve C R).presheaf.germ (D.pieces j)
      ((relCurveMap C R R').base z) hfzj).hom (A.eqn j) =
      ((relCurve C R).presheaf.germ
          (D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z))
          ((relCurveMap C R R').base z) hfzW).hom
        (u : Γ(relCurve C R,
          D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z))) *
        ((relCurve C R).presheaf.germ
          (d.cover.opens ((relCurveMap C R R').base z))
          ((relCurveMap C R R').base z) hfzz).hom
          (d.eqn ((relCurveMap C R R').base z)) := by
    have hkey := congrArg ((relCurve C R).presheaf.germ
        (D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z))
        ((relCurveMap C R R').base z) hfzW).hom hu
    rw [map_mul, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply] at hkey
    exact hkey
  -- the pulled system equation's germ is the stalk image of the system equation's germ
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
        (D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z))
        ((relCurveMap C R R').base z) hfzW).hom
        (u : Γ(relCurve C R,
          D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z))))) :=
    (u.isUnit.map ((relCurve C R).presheaf.germ
      (D.pieces j ⊓ d.cover.opens ((relCurveMap C R R').base z))
      ((relCurveMap C R R').base z) hfzW).hom).map
      ((relCurveMap C R R').stalkMap z).hom
  refine ⟨hunit.unit, ?_⟩
  rw [hgermF, hdecomp, map_mul, IsUnit.unit_spec, hgermG]

/-- **Section-level regularity of the pulled piece equations from self-regularity of the pulled
system.**  Sections of a sheaf inject into the product of their germs, and at each germ the
pulled piece equation is a unit multiple of the pulled system equation at that very point.

The chart-typed twin is `DivisorAdaptation.pulledEqn_mem_nonZeroDivisors_of_self_pullbackEqn`;
this one assumes nothing about the piece beyond its being an open of the relative curve. -/
theorem pulledEqn_mem_nonZeroDivisors_of_self_pullbackEqn
    (hreg : ∀ z : relCurve C R',
      ((relCurve C R').presheaf.germ
        ((d.cover.pullback (relCurveMap C R R')).opens z) z
        ((d.cover.pullback (relCurveMap C R R')).mem_opens z)).hom
        (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d z) ∈
          nonZeroDivisors ((relCurve C R').presheaf.stalk z))
    (j : D.index) :
    A.pulledEqn R' j ∈ nonZeroDivisors Γ(relCurve C R', (D.baseChange R').pieces j) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro t ht
  apply TopCat.Presheaf.section_ext (relCurve C R').sheaf
    ((D.baseChange R').pieces j) t 0
  intro z hzj
  rw [map_zero]
  have heqn : ((relCurve C R').presheaf.germ
      ((D.baseChange R').pieces j) z hzj).hom (A.pulledEqn R' j) ∈
      nonZeroDivisors ((relCurve C R').presheaf.stalk z) := by
    obtain ⟨v, hv⟩ := A.exists_germ_pulledEqn_eq_unit_mul_pullbackEqn (R' := R') j z hzj
    rw [hv]
    exact mul_mem v.isUnit.mem_nonZeroDivisors (hreg z)
  have hzero : ((relCurve C R').presheaf.germ
      ((D.baseChange R').pieces j) z hzj).hom t *
      ((relCurve C R').presheaf.germ
        ((D.baseChange R').pieces j) z hzj).hom (A.pulledEqn R' j) = 0 := by
    rw [← map_mul, ht, map_zero]
  exact (mul_right_mem_nonZeroDivisors_eq_zero_iff heqn).mp hzero

end AffAdaptation

/-! ## The tensor shape the assembler consumes

`AffAdaptation.eqn_tmul_one_mem_nonZeroDivisors_iff` identifies the assembler's tensor
hypothesis with regularity of `relAffSectionsMap … (A.eqn j)` on the fibre curve.  That section
IS `A.pulledEqn κ(p) j` — by definition, since `pulledEqn` is `piecesMap` is `relAffSectionsMap`
— so the previous section closes the tensor form with no further transport. -/

namespace AffAdaptation

variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d)

/-- The pulled piece equation IS the section the fibre-curve reading of `hfib` speaks about.
Definitional, recorded because it is the seam between the two files. -/
lemma pulledEqn_eq_relAffSectionsMap {R' : Type u} [CommRing R'] [Algebra k R']
    [Algebra R R'] [IsScalarTower k R R'] (j : D.index) :
    A.pulledEqn R' j = relAffSectionsMap C R' (D.pieces j) (A.eqn j) := rfl

/-- **Obligation 4(i) in the assembler's own shape, from self-regularity on the fibre.**  The
tensor condition `eqn j ⊗ 1 ∈ nonZeroDivisors (Γ(pieces j) ⊗[R] κ(p))` holds as soon as the
pulled SYSTEM equation is regular at its own point on the fibre curve over `κ(p)`. -/
theorem eqn_tmul_one_mem_nonZeroDivisors_of_self_pullbackEqn (j : D.index)
    (p : PrimeSpectrum R)
    (hreg : ∀ z : relCurve C p.asIdeal.ResidueField,
      ((relCurve C p.asIdeal.ResidueField).presheaf.germ
        ((d.cover.pullback (relCurveMap C R p.asIdeal.ResidueField)).opens z) z
        ((d.cover.pullback
          (relCurveMap C R p.asIdeal.ResidueField)).mem_opens z)).hom
        (Scheme.LocalEquations.pullbackEqn
          (relCurveMap C R p.asIdeal.ResidueField) d z) ∈
          nonZeroDivisors
            ((relCurve C p.asIdeal.ResidueField).presheaf.stalk z)) :
    (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
        Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
      nonZeroDivisors (Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField) := by
  refine (A.eqn_tmul_one_mem_nonZeroDivisors_iff j p).mpr ?_
  have h := A.pulledEqn_mem_nonZeroDivisors_of_self_pullbackEqn
    (R' := p.asIdeal.ResidueField) hreg j
  rwa [A.pulledEqn_eq_relAffSectionsMap (R' := p.asIdeal.ResidueField) j] at h

end AffAdaptation

/-! ## Obligation 4(i), discharged for a theta-generator seed

This is the point of the file, and the statement is deliberately quantified over the cover and
the adaptation: the assembler's `hfib` in `exists_isCertified_of_swallowing_affineOpen` is a
`∀ D A j p`, so it is exactly what a producer must supply. -/

namespace ThetaGeneratorSeed

variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : Nat}
variable {K : Submodule R (relThetaSections C R pi a)}
variable [IsNoetherianRing R] {D : ThetaGeneratorSeed C R pi a K}

/-- **Obligation I-0492 4(i), DISCHARGED at arbitrary affine-open pieces.**  For a
theta-generator seed, every widened adaptation over every widened cover satisfies the
fibrewise-regularity hypothesis of the widened assembler — uniformly in the cover `Dc`, the
piece `j` and the prime `p`.

Nothing about the cover is used but that its pieces are affine opens (a field of
`AffCoverData`), and nothing about the adaptation but `eqn_rel` (a field of `AffAdaptation`).
The mathematical input is the seed's own clause, through
`ThetaGeneratorSeed.germ_self_pullbackEqn_mem_nonZeroDivisors`, whose statement mentions no
cover at all — which is why widening the pieces costs nothing here.

Compare `ThetaGeneratorSeed.divisorAdaptation_fibre_regular`, the chart-typed twin: that one is
stated for the ONE extracted adaptation `D.divisorAdaptation hD`, because chart-typed pieces
come from the extraction.  This one holds for every widened adaptation there is. -/
theorem affAdaptation_fibre_regular (hD : D.IsGenerator) (Dc : AffCoverData C R)
    (A : AffAdaptation Dc (D.localEquations hD)) (j : Dc.index) (p : PrimeSpectrum R) :
    (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
        Γ(relCurve C R, Dc.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
      nonZeroDivisors (Γ(relCurve C R, Dc.pieces j) ⊗[R] p.asIdeal.ResidueField) :=
  A.eqn_tmul_one_mem_nonZeroDivisors_of_self_pullbackEqn j p
    (fun z => D.germ_self_pullbackEqn_mem_nonZeroDivisors hD p z)

end ThetaGeneratorSeed

end AlgebraicGeometry
