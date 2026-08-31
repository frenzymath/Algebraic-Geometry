/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertZarPointwise
import AlgebraicJacobian.Picard.SupportTubeFinite

/-!
# The support tube in `Away`-chart form

The pointwise certificate gate (`DivSchemeCertZarPointwise.lean`) asks, at each base prime
`p`, for an element `r ∉ p` such that the pulled system is certified over
`Localization.Away r`.  The support tube (`Scheme.LocalEquations.exists_supportTube`)
delivers piece isolation over an *abstract* Zariski neighbourhood `V` of `p`.  This file
refines that neighbourhood to a basic open — the shape `Localization.Away` needs — and
records the resulting statement.

The refinement is the standard fact that basic opens form a topological basis of
`Spec R` (`PrimeSpectrum.isBasis_basic_opens`); the content is only that the tube's
conclusion is monotone in the neighbourhood, so shrinking `V` to a basic open inside it
preserves support isolation.

## Main declarations

* `AlgebraicGeometry.Scheme.LocalEquations.exists_basicOpen_supportTube` — the tube with a
  basic-open neighbourhood: an `r ∉ p` whose basic open isolates the support inside `U`.
* `AlgebraicGeometry.exists_notMem_supportLocus_subset_of_fibre` — the same for the
  relative curve over a test ring, with the properness licence supplied.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace Scheme.LocalEquations

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (d : X.LocalEquations)

/-- **The support tube with a basic-open neighbourhood.** If the support fibre over a base
prime `p` lies inside an open `U`, then some `r ∉ p` has its whole basic-open preimage's
support inside `U`.

The tube produces an abstract neighbourhood; basic opens are a basis of `Spec R`
(`PrimeSpectrum.isBasis_basic_opens`), so shrinking to a basic open inside it keeps the
conclusion by monotonicity of the preimage. This is the form the `Localization.Away`
charts of `IsLocallyCertified` consume. -/
theorem exists_basicOpen_supportTube (f : X ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed f] {U : Set X} (hU : IsOpen U) {p : PrimeSpectrum R}
    (hfib : f.base ⁻¹' {(p : Spec (CommRingCat.of R))} ∩ d.supportLocus ⊆ U) :
    ∃ r : R, r ∉ p.asIdeal ∧
      f.base ⁻¹' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))
        ∩ d.supportLocus ⊆ U := by
  obtain ⟨V, hpV, hV⟩ := d.exists_supportTube f hU hfib
  -- refine `V` to a basic open around `p`
  obtain ⟨W, hWmem, hpW, hWV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) hpV V.isOpen
  obtain ⟨r, rfl⟩ := hWmem
  exact ⟨r, (PrimeSpectrum.mem_basicOpen r p).mp hpW,
    fun x hx => hV ⟨hWV hx.1, hx.2⟩⟩

end Scheme.LocalEquations

/-! ## The relative-curve form -/

section RelCurve

variable {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
variable (R : Type u) [CommRing R] [Algebra k R]

/-- **The relative-curve support tube, basic-open form.** For a local-equation system on
the relative curve over a test ring, fibrewise containment of the support in an open `U`
at a prime `p` gives an `r ∉ p` isolating the support over the basic open of `r`.

The properness licence is `instIsProperRelCurveHom`; `UniversallyClosed` fires by
resolution. -/
theorem exists_notMem_supportLocus_subset_of_fibre
    (d : (relCurve C R).LocalEquations) {U : Set (relCurve C R)} (hU : IsOpen U)
    {p : PrimeSpectrum R}
    (hfib : ((relCurve C R) ↘ Spec (CommRingCat.of R)).base ⁻¹'
        {(p : Spec (CommRingCat.of R))} ∩ d.supportLocus ⊆ U) :
    ∃ r : R, r ∉ p.asIdeal ∧
      ((relCurve C R) ↘ Spec (CommRingCat.of R)).base ⁻¹'
          (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))
        ∩ d.supportLocus ⊆ U :=
  d.exists_basicOpen_supportTube _ hU hfib

end RelCurve

/-! ## No-leak over a shrunken base, from one fibre

The point of the tube in the certificate lane: the no-leak hypothesis that is false
globally becomes *true over the tube*, because the support over the tube is already inside
the piece — so its closure is too, and the fibre clause holds for every base point of the
tube rather than only the one it was checked at. -/

section NoLeakOverTube

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]
variable {d : (relCurve C R).LocalEquations}

namespace DivisorAdaptation

variable (A : DivisorAdaptation C R pi d)

omit [IsProper C.hom]

/-- **Support containment upgrades to the fibrewise no-leak clause.** If the whole family
support lies in the piece `j`, then over every base point the fibre of the *closure* of the
piece trace stays in the piece: the trace is then all of the support, which is closed.

This is the bridge between what the tube delivers (support containment over a shrunken
base) and what the certificate assembler consumes (the fibrewise clause of
`finite_colength_of_forall_fibre_closure_subset`). -/
theorem forall_fibre_closure_subset_of_supportLocus_subset (j : A.index)
    (hsub : d.supportLocus ⊆ (A.pieces j : Set (relCurve C R))) :
    ∀ s : Spec (CommRingCat.of R),
      ((relCurve C R) ↘ Spec (CommRingCat.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (A.pieces j : Set (relCurve C R)))
        ⊆ (A.pieces j : Set (relCurve C R)) := by
  intro s x hx
  have htrace : d.supportLocus ∩ (A.pieces j : Set (relCurve C R)) = d.supportLocus :=
    Set.inter_eq_left.mpr hsub
  rw [htrace, d.isClosed_supportLocus.closure_eq] at hx
  exact hsub hx.2

/-- The no-leak clause for **every** piece, from containment of the support in each: the
exact `hnoLeak` input of the certificate assemblers
(`DivisorAdaptation.isCertified_of_noLeak_kernel_spanning`,
`ThetaGeneratorSeed.divisorAdaptation_isCertified_of_noLeak_kernel_spanning`). -/
theorem forall_noLeak_of_forall_supportLocus_subset
    (hsub : ∀ j : A.index, d.supportLocus ⊆ (A.pieces j : Set (relCurve C R))) :
    ∀ (j : A.index) (s : Spec (CommRingCat.of R)),
      ((relCurve C R) ↘ Spec (CommRingCat.of R)).base ⁻¹' {s}
          ∩ closure (d.supportLocus ∩ (A.pieces j : Set (relCurve C R)))
        ⊆ (A.pieces j : Set (relCurve C R)) :=
  fun j => A.forall_fibre_closure_subset_of_supportLocus_subset j (hsub j)

end DivisorAdaptation

end NoLeakOverTube

/-! ## The tube-fibre reduction

Combining the two halves: to obtain the certificate assembler's `hnoLeak` input over an
`Away` chart, it is enough to check at ONE base prime that the support fibre lies in an
open — the tube spreads it to a basic-open neighbourhood, and containment there upgrades to
the fibrewise clause. This is the precise statement the remaining geometric work has to
feed, and it mentions only a single fibre. -/

section TubeFibre

variable {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
variable (R : Type u) [CommRing R] [Algebra k R]

/-- **The tube-fibre reduction.** If at a base prime `p` the support fibre of the system
lies inside an open `U`, then some `r ∉ p` has the entire support over `D(r)` inside `U`.

Stated so that the remaining certificate obligation is *purely fibrewise*: check one fibre,
get a Zariski chart.  The consumer chain is
`exists_notMem_supportLocus_subset_of_fibre` → the pulled system's support over `D(r)` →
`DivisorAdaptation.forall_noLeak_of_forall_supportLocus_subset` → the assembler's
`hnoLeak`, and then `isLocallyCertified_of_forall_prime_exists_certified_adaptation`
consumes the resulting away-certificate. -/
theorem exists_away_supportLocus_subset_of_fibre_subset
    (d : (relCurve C R).LocalEquations) (U : (relCurve C R).Opens) {p : PrimeSpectrum R}
    (hfib : ((relCurve C R) ↘ Spec (CommRingCat.of R)).base ⁻¹'
        {(p : Spec (CommRingCat.of R))} ∩ d.supportLocus ⊆ (U : Set (relCurve C R))) :
    ∃ r : R, r ∉ p.asIdeal ∧
      ((relCurve C R) ↘ Spec (CommRingCat.of R)).base ⁻¹'
          (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ∩ d.supportLocus
        ⊆ (U : Set (relCurve C R)) :=
  exists_notMem_supportLocus_subset_of_fibre C R d U.isOpen hfib

end TubeFibre

end AlgebraicGeometry
