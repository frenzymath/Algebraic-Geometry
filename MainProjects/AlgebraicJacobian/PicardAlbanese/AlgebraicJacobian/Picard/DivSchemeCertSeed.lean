/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertUniv
import AlgebraicJacobian.Picard.DivSchemeCertFibreRank

/-!
# Certificate assembly for an extracted theta-generator adaptation

This file specializes the generic universal-family certificate assembler to the
adaptation extracted from a theta-generator seed.  No-leak supplies finite chart and
overlap colengths, seed regularity supplies their projectivity and overlap flatness,
and the degree of the pulled divisor computes the remaining fibre rank.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {a : Nat} {K : Submodule R (relThetaSections C R pi a)}
variable {D : ThetaGeneratorSeed C R pi a K} (hD : D.IsGenerator)

noncomputable local instance instIsIntegralRelCurveCertSeed
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveCertSeed
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveCertSeed
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

local notation "A" => D.divisorAdaptation hD

/-- Assemble the certificate of an extracted theta-generator adaptation from no-leak,
relative kernel spanning, and the degree of every pulled divisor.  In particular,
overlap finiteness, overlap flatness, chart projectivity, and fibre kernel dimension
are consequences rather than separate inputs. -/
theorem divisorAdaptation_isCertified_of_noLeak_kernel_spanning_degree {n : Nat}
    (hnoLeak : forall (j : (A).index) (s : Spec (.of R)),
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s}
          ∩ closure
            ((D.localEquations hD).supportLocus ∩
              ((A).pieces j : Set (relCurve C R))) ⊆
        ((A).pieces j : Set (relCurve C R)))
    (L : Submodule R (A).chartProd)
    (hle : L ≤ LinearMap.ker ((A).deltaLeft - (A).deltaRight))
    (hspan : forall p : PrimeSpectrum R,
      LinearMap.ker
          (((A).deltaLeft - (A).deltaRight).rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range (L.subtype.rTensor p.asIdeal.ResidueField))
    (hdeg : forall (p : PrimeSpectrum R)
      (hproj : forall j : (A).index, Module.Projective R ((A).colength j)),
      Scheme.CurveDivisor.deg p.asIdeal.ResidueField
          (Scheme.presentationDivisor p.asIdeal.ResidueField
            (((A).pulledEquations p.asIdeal.ResidueField hproj).presentation)) =
        (n : Int)) :
    (A).IsCertified n := by
  have hfin : forall j : (A).index, Module.Finite R ((A).colength j) :=
    fun j => (A).finite_colength_of_forall_fibre_closure_subset j (hnoLeak j)
  have hproj : forall j : (A).index, Module.Projective R ((A).colength j) := by
    intro j
    letI : Module.Finite R ((A).colength j) := hfin j
    exact (A).projective_colength_of_forall_tmul_residueField j
      (D.divisorAdaptation_fibre_regular hD j)
  have hdim : forall p : PrimeSpectrum R,
      Module.finrank p.asIdeal.ResidueField
          (LinearMap.ker
            (((A).deltaLeft - (A).deltaRight).baseChange p.asIdeal.ResidueField)) = n := by
    intro p
    exact (A).finrank_ker_delta_baseChange_eq_of_pulled_degree
      (K := p.asIdeal.ResidueField) hproj (hdeg p hproj)
  exact D.divisorAdaptation_isCertified_of_noLeak_kernel_spanning
    hD hnoLeak L hle hspan hdim

end ThetaGeneratorSeed

end AlgebraicGeometry
