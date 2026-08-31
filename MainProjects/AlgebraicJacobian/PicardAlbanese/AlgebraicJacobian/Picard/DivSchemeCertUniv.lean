/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.PiLocalization
import AlgebraicJacobian.Picard.SlicingFlatKernel
import AlgebraicJacobian.Picard.SupportTubeFinite
import AlgebraicJacobian.Picard.DivSchemeCertOverlapFinite

/-! 
# The universal-family certificate assembly

This file assembles the seven fields of `DivisorAdaptation.IsCertified` from the
geometric inputs left by the universal-seed construction:

* finite chart colengths, supplied by the no-leak theorem in `SupportTubeFinite`;
* fibrewise regular chart equations, which make those colengths projective;
* a relative submodule spanning the residue-fibre kernels of the Cech difference map;
* the fibre dimension of that kernel.

The last two inputs feed `SlicingFlatKernel`, simultaneously producing the projective
glued module, its constant rank, and both flat-cokernel clauses.  Keeping this assembly
generic isolates the remaining DD-4 geometry from the certificate bookkeeping.
-/

set_option autoImplicit false

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

omit [IsProper C.hom] in
/-- Assemble a divisor-family certificate from finite regular chart colengths and a
submodule which spans the residue-fibre kernels of the Cech difference map.

The overlap product is kept as an explicit finite-flat input: producing it from the
universal seed is part of the geometric base-change wiring, while all consequences for
the certificate are discharged here. -/
theorem isCertified_of_kernel_spanning [IsNoetherianRing R] {n : Nat}
    (hfin : forall j : A.index, Module.Finite R (A.colength j))
    (hregular : forall (j : A.index) (p : PrimeSpectrum R),
      (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors
          (Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField))
    (hovlFinite : Module.Finite R A.ovlProd)
    (hovlFlat : Module.Flat R A.ovlProd)
    (L : Submodule R A.chartProd)
    (hle : L <= LinearMap.ker (A.deltaLeft - A.deltaRight))
    (hspan : forall p : PrimeSpectrum R,
      LinearMap.ker ((A.deltaLeft - A.deltaRight).rTensor p.asIdeal.ResidueField) <=
        LinearMap.range (L.subtype.rTensor p.asIdeal.ResidueField))
    (hdim : forall p : PrimeSpectrum R,
      Module.finrank p.asIdeal.ResidueField
          (LinearMap.ker
            ((A.deltaLeft - A.deltaRight).baseChange p.asIdeal.ResidueField)) = n) :
    A.IsCertified n := by
  letI hfiniteColength : forall j : A.index, Module.Finite R (A.colength j) := hfin
  letI hprojectiveColength : forall j : A.index, Module.Projective R (A.colength j) :=
    fun j => A.projective_colength_of_forall_tmul_residueField j (hregular j)
  letI hflatColength : forall j : A.index, Module.Flat R (A.colength j) :=
    fun j => A.flat_colength_of_forall_tmul_residueField j (hregular j)
  letI hfiniteChart : Module.Finite R A.chartProd := Module.Finite.pi
  letI hflatChart : Module.Flat R A.chartProd := Module.Flat.pi_of_finite
  letI hfiniteOvl : Module.Finite R A.ovlProd := hovlFinite
  letI hflatOvl : Module.Flat R A.ovlProd := hovlFlat
  have hfiniteGlued : Module.Finite R A.Glued :=
    Module.Finite.iff_fg.mpr (_root_.IsNoetherian.noetherian A.gluedSubmodule)
  have hprojectiveGlued : Module.Projective R A.Glued :=
    Module.Projective.ker_of_forall_ker_rTensor_residueField_le
      (A.deltaLeft - A.deltaRight) L hle hspan
  refine
    { finite_colength := hfin
      projective_colength := fun j => hprojectiveColength j
      finite_glued := hfiniteGlued
      projective_glued := hprojectiveGlued
      rankAtStalk_glued := fun p =>
        Module.rankAtStalk_ker_eq_of_forall_finrank_eq
          (A.deltaLeft - A.deltaRight) L hle hspan n hdim p
      flat_coker_incl :=
        Module.Flat.quotient_ker_of_forall_ker_rTensor_residueField_le
          (A.deltaLeft - A.deltaRight) L hle hspan
      flat_coker_diff :=
        Module.Flat.quotient_range_of_forall_ker_rTensor_residueField_le
          (A.deltaLeft - A.deltaRight) L hle hspan }

/-- The certificate constructor in the exact SupportTube form: fibrewise no-leak of
each chart trace supplies its finite colength, after which
`isCertified_of_kernel_spanning` handles every remaining field. -/
theorem isCertified_of_noLeak_kernel_spanning [IsNoetherianRing R] {n : Nat}
    (hnoLeak : forall (j : A.index) (s : Spec (.of R)),
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (A.pieces j : Set (relCurve C R))) <=
        (A.pieces j : Set (relCurve C R)))
    (hregular : forall (j : A.index) (p : PrimeSpectrum R),
      (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors
          (Γ(relCurve C R, A.pieces j) ⊗[R] p.asIdeal.ResidueField))
    (hovlFinite : Module.Finite R A.ovlProd)
    (hovlFlat : Module.Flat R A.ovlProd)
    (L : Submodule R A.chartProd)
    (hle : L <= LinearMap.ker (A.deltaLeft - A.deltaRight))
    (hspan : forall p : PrimeSpectrum R,
      LinearMap.ker ((A.deltaLeft - A.deltaRight).rTensor p.asIdeal.ResidueField) <=
        LinearMap.range (L.subtype.rTensor p.asIdeal.ResidueField))
    (hdim : forall p : PrimeSpectrum R,
      Module.finrank p.asIdeal.ResidueField
          (LinearMap.ker
            ((A.deltaLeft - A.deltaRight).baseChange p.asIdeal.ResidueField)) = n) :
    A.IsCertified n :=
  A.isCertified_of_kernel_spanning
    (fun j => A.finite_colength_of_forall_fibre_closure_subset j (hnoLeak j))
    hregular hovlFinite hovlFlat L hle hspan hdim

end DivisorAdaptation

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {a n : Nat} {K : Submodule R (relThetaSections C R pi a)}
variable {D : ThetaGeneratorSeed C R pi a K}

/-- Assemble the certificate of the adaptation extracted from a theta-generator seed.
Seed regularity supplies both chart regularity and overlap flatness, while no-leak
supplies both chart and overlap finiteness.  Thus only no-leak, relative kernel
spanning, and the fibre dimension remain as substantive inputs. -/
theorem divisorAdaptation_isCertified_of_noLeak_kernel_spanning
    (hD : D.IsGenerator)
    (hnoLeak : forall (j : (D.divisorAdaptation hD).index) (s : Spec (.of R)),
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {s}
          ∩ closure
            ((D.localEquations hD).supportLocus ∩
              ((D.divisorAdaptation hD).pieces j : Set (relCurve C R))) ⊆
        ((D.divisorAdaptation hD).pieces j : Set (relCurve C R)))
    (L : Submodule R (D.divisorAdaptation hD).chartProd)
    (hle : L ≤ LinearMap.ker
      ((D.divisorAdaptation hD).deltaLeft - (D.divisorAdaptation hD).deltaRight))
    (hspan : forall p : PrimeSpectrum R,
      LinearMap.ker
          (((D.divisorAdaptation hD).deltaLeft -
            (D.divisorAdaptation hD).deltaRight).rTensor p.asIdeal.ResidueField) ≤
        LinearMap.range (L.subtype.rTensor p.asIdeal.ResidueField))
    (hdim : forall p : PrimeSpectrum R,
      Module.finrank p.asIdeal.ResidueField
          (LinearMap.ker
            (((D.divisorAdaptation hD).deltaLeft -
              (D.divisorAdaptation hD).deltaRight).baseChange
                p.asIdeal.ResidueField)) = n) :
    (D.divisorAdaptation hD).IsCertified n :=
  (D.divisorAdaptation hD).isCertified_of_noLeak_kernel_spanning
    hnoLeak
    (D.divisorAdaptation_fibre_regular hD)
    ((D.divisorAdaptation hD).finite_ovlProd_of_noLeak hnoLeak)
    ((D.divisorAdaptation hD).flat_ovlProd_of_seed hD)
    L hle hspan hdim

end ThetaGeneratorSeed

end AlgebraicGeometry
