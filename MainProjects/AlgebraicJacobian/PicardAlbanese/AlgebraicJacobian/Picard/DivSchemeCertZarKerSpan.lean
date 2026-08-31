/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertZarTube
import AlgebraicJacobian.Picard.DivSchemeHighWindowSyzygy

/-!
# The certificate's kernel-spanning input, with the submodule eliminated

The certificate assemblers take a submodule `L ≤ ker (δ_left − δ_right)` together with the
fibrewise-spanning law `hspan`.  Choosing `L` is not where the difficulty lies: the
canonical choice `L = ker (δ_left − δ_right)` always satisfies `hle` by `le_rfl`, and for
that choice `hspan` is *equivalent* to residue-fibre injectivity of the injectivized map
(`ker_rTensor_le_range_subtype_iff_liftQ_rTensor_injective`).

This file records the resulting assembler interfaces, which mention no submodule at all.
It is a packaging step, not a weakening: the remaining content is the fibre injectivity,
which the syzygy file already shows is equivalent to the flat-cokernel clause and so
genuinely needs relative geometry (it is not evadable by a cleverer choice of `L`).

Combined with `DivSchemeCertZarTube.lean`, the certificate obligation over an `Away` chart
is now exactly two fibrewise facts: support containment in a piece, and injectivity of the
injectivized Čech difference on each residue fibre.

## Main declarations

* `AlgebraicGeometry.DivisorAdaptation.isCertified_of_noLeak_of_forall_liftQ_injective` —
  the assembler with `L` eliminated.
* `AlgebraicGeometry.ThetaGeneratorSeed.divisorAdaptation_isCertified_of_noLeak_liftQ_degree`
  — the seed form, with the degree input in the landed pulled-divisor spelling.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace DivisorAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {d : (relCurve C R).LocalEquations}
variable (A : DivisorAdaptation C R pi d)

/-- **The assembler with the spanning submodule eliminated.** Taking `L` to be the actual
kernel of the Čech difference makes `hle` trivial and turns `hspan` into residue-fibre
injectivity of the injectivized map — so the certificate needs no invented submodule.

The remaining hypothesis `hinj` is genuine relative content: the syzygy file proves it
equivalent to the flat-cokernel clause, hence not evadable by choosing `L` differently. -/
theorem isCertified_of_noLeak_of_forall_liftQ_injective [IsNoetherianRing R] {n : ℕ}
    (hnoLeak : ∀ (j : A.index) (s : Spec (.of R)),
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (A.pieces j : Set (relCurve C R))) ⊆
        (A.pieces j : Set (relCurve C R)))
    (hregular : ∀ (j : A.index) (p : PrimeSpectrum R),
      (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors
          (Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField))
    (hovlFinite : Module.Finite R A.ovlProd)
    (hovlFlat : Module.Flat R A.ovlProd)
    (hinj : ∀ p : PrimeSpectrum R,
      Function.Injective
        (((LinearMap.ker (A.deltaLeft - A.deltaRight)).liftQ
          (A.deltaLeft - A.deltaRight) le_rfl).rTensor p.asIdeal.ResidueField))
    (hdim : ∀ p : PrimeSpectrum R,
      Module.finrank p.asIdeal.ResidueField
          (LinearMap.ker
            ((A.deltaLeft - A.deltaRight).baseChange p.asIdeal.ResidueField)) = n) :
    A.IsCertified n :=
  A.isCertified_of_noLeak_kernel_spanning hnoLeak hregular hovlFinite hovlFlat
    (LinearMap.ker (A.deltaLeft - A.deltaRight)) le_rfl
    (fun p => (ker_rTensor_le_range_subtype_iff_liftQ_rTensor_injective
      (A.deltaLeft - A.deltaRight) p.asIdeal.ResidueField).mpr (hinj p))
    hdim

end DivisorAdaptation

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {a : ℕ} {K : Submodule R (relThetaSections C R pi a)}
variable {D : ThetaGeneratorSeed C R pi a K} (hD : D.IsGenerator)

noncomputable local instance instIsIntegralRelCurveCertKerSpan
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveCertKerSpan
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveCertKerSpan
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

local notation "A" => D.divisorAdaptation hD

/-- **The seed certificate with no invented submodule and the landed degree input.** The
three substantive inputs are now: fibrewise no-leak (produced Zariski-locally by the
support tube, `DivSchemeCertZarTube.lean`), residue-fibre injectivity of the injectivized
Čech difference, and the degree of every pulled presentation divisor (already proved for
the pointwise generator seed). -/
theorem divisorAdaptation_isCertified_of_noLeak_liftQ_degree {n : ℕ}
    (hnoLeak : ∀ (j : (A).index) (s : Spec (.of R)),
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s}
          ∩ closure
            ((D.localEquations hD).supportLocus ∩
              ((A).pieces j : Set (relCurve C R))) ⊆
        ((A).pieces j : Set (relCurve C R)))
    (hinj : ∀ p : PrimeSpectrum R,
      Function.Injective
        (((LinearMap.ker ((A).deltaLeft - (A).deltaRight)).liftQ
          ((A).deltaLeft - (A).deltaRight) le_rfl).rTensor p.asIdeal.ResidueField))
    (hdeg : ∀ (p : PrimeSpectrum R)
      (hproj : ∀ j : (A).index, Module.Projective R ((A).colength j)),
      Scheme.CurveDivisor.deg p.asIdeal.ResidueField
          (Scheme.presentationDivisor p.asIdeal.ResidueField
            (((A).pulledEquations p.asIdeal.ResidueField hproj).presentation)) =
        (n : ℤ)) :
    (A).IsCertified n :=
  D.divisorAdaptation_isCertified_of_noLeak_kernel_spanning_degree hD hnoLeak
    (LinearMap.ker ((A).deltaLeft - (A).deltaRight)) le_rfl
    (fun p => (ker_rTensor_le_range_subtype_iff_liftQ_rTensor_injective
      ((A).deltaLeft - (A).deltaRight) p.asIdeal.ResidueField).mpr (hinj p))
    hdeg

end ThetaGeneratorSeed

end AlgebraicGeometry
