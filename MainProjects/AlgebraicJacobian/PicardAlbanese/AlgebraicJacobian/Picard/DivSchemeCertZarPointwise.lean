/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertZarSeed

/-!
# From pointwise away-certificates to a span-`⊤` family

`DivSchemeCertZarSeed.lean` reduced the DD-R certificate gate to *away-local* certificates
over a span-`⊤` family.  The geometry that produces such certificates, however, is
pointwise on the base: the support tube (`Scheme.LocalEquations.exists_supportTube`)
isolates the pieces over a Zariski neighbourhood **of one base point at a time**, and the
fibre analyses all read at a single `p : PrimeSpectrum R`.

This file closes that gap with the quasi-compactness step.  If for every prime `p` there
is some `r ∉ p` over whose away localization the system is certified, then the good
elements span the unit ideal (their basic opens cover `Spec R`), so finitely many of them
already do — and `isLocallyCertified_of_forall_exists_away` applies.

The result is that the certificate gate for the DD-R endgame is now genuinely *pointwise*:
one base point at a time, exactly the shape the landed fibre machinery delivers.

## Main declarations

* `AlgebraicGeometry.isLocallyCertified_of_forall_prime_exists_away` — the pointwise gate
  for a bare local-equation system.
* `AlgebraicGeometry.ThetaGeneratorSeed.isLocallyCertified_of_forall_prime_away_certified`
  — the seed form.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## The quasi-compactness step -/

section SpanTop

variable {R : Type u} [CommRing R]

/-- **Pointwise good elements span the unit ideal, finitely.** If a predicate `P` on `R`
holds at some element outside each prime, then finitely many elements satisfying `P` span
`⊤`.  This is quasi-compactness of `Spec R` in the elementary form the certificate gate
needs: the basic opens of the good elements cover the spectrum, hence the good set spans
the unit ideal, hence `1` is a finite combination of good elements. -/
theorem exists_fin_span_eq_top_of_forall_prime (P : R → Prop)
    (h : ∀ p : PrimeSpectrum R, ∃ r, r ∉ p.asIdeal ∧ P r) :
    ∃ (m : ℕ) (g : Fin m → R), Ideal.span (Set.range g) = ⊤ ∧ ∀ i, P (g i) := by
  classical
  -- the good elements span the unit ideal, because their basic opens cover `Spec R`
  have hspan : Ideal.span {r : R | P r} = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    refine top_le_iff.mp fun p _ => ?_
    obtain ⟨r, hrp, hrP⟩ := h p
    exact Opens.mem_iSup.mpr ⟨r, by
      simpa only [Opens.mem_iSup, PrimeSpectrum.mem_basicOpen] using ⟨hrP, hrp⟩⟩
  -- `1` is then a finite combination of good elements
  have hone : (1 : R) ∈ Submodule.span R {r : R | P r} := by
    show (1 : R) ∈ Ideal.span {r : R | P r}
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨T, hTsub, hT⟩ := Submodule.mem_span_finite_of_mem_span hone
  refine ⟨T.card, fun i => (T.equivFin.symm i : R), ?_, fun i => hTsub (T.equivFin.symm i).2⟩
  have hrange : Set.range (fun i : Fin T.card => ((T.equivFin.symm i : R))) = (T : Set R) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (T.equivFin.symm i).2
    · intro hx
      exact ⟨T.equivFin ⟨x, hx⟩, by simp⟩
  rw [hrange]
  exact Ideal.eq_top_of_isUnit_mem _ hT isUnit_one

end SpanTop

/-! ## The pointwise certificate gate -/

section Pointwise

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]

/-- **The pointwise certificate gate.** If over every prime of the base there is an away
localization carrying a certified family divisor-equal to the pulled system, the system is
locally certified.  Combines the quasi-compactness step with the span-`⊤` production rule
`isLocallyCertified_of_forall_exists_away`. -/
theorem isLocallyCertified_of_forall_prime_exists_away {n : ℕ}
    {d : (relCurve C R).LocalEquations}
    (h : ∀ p : PrimeSpectrum R, ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ G : CertifiedDivisorFamily C (Localization.Away r) pi n,
        Scheme.LocalEquations.DivEq G.eqns
          (d.pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) d))) :
    IsLocallyCertified C R pi n d := by
  obtain ⟨m, g, hg, hgood⟩ := exists_fin_span_eq_top_of_forall_prime
    (fun r =>
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ G : CertifiedDivisorFamily C (Localization.Away r) pi n,
        Scheme.LocalEquations.DivEq G.eqns
          (d.pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) d))) h
  exact isLocallyCertified_of_forall_exists_away g hg hgood

end Pointwise

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {a n : ℕ} {K : Submodule R (relThetaSections C R pi a)}
variable {D : ThetaGeneratorSeed C R pi a K}

omit [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom]

/-- **The pointwise certificate gate for a seed.** One base point at a time: an away
localization at each prime carrying a certified family divisor-equal to the pulled seed
system makes the seed's system locally certified, hence a `DivFamZar` class.

This is the shape the landed geometry actually produces — the support tube isolates pieces
over a neighbourhood of one base point, and every fibre analysis reads at a single prime —
so no globally valid no-leak hypothesis (false in general, I-0209) is required anywhere. -/
theorem isLocallyCertified_of_forall_prime_away_certified (hD : D.IsGenerator)
    (h : ∀ p : PrimeSpectrum R, ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ G : CertifiedDivisorFamily C (Localization.Away r) pi n,
        Scheme.LocalEquations.DivEq G.eqns
          ((D.localEquations hD).pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) (D.localEquations hD)))) :
    IsLocallyCertified C R pi n (D.localEquations hD) :=
  isLocallyCertified_of_forall_prime_exists_away h

/-- **The gate in its most consumable form: certify the pulled system after shrinking.**
At every prime it suffices to produce an `r ∉ p` and a certificate for *some* adaptation
of the pulled seed system over `Localization.Away r`.  The adaptation itself is free
(`exists_divisorAdaptation`), so the only genuine obligation is the certificate over the
shrunken base — where the support tube makes per-piece isolation available.

Contrast with the old gate `divisorAdaptation_isCertified_of_noLeak_kernel_spanning`,
which demanded a certificate for the *canonically extracted* adaptation over the whole
chart ring; that shape forces a globally valid no-leak hypothesis, which is false. -/
theorem isLocallyCertified_of_forall_prime_exists_certified_adaptation
    (hD : D.IsGenerator)
    (h : ∀ p : PrimeSpectrum R, ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ A : DivisorAdaptation C (Localization.Away r) pi
          ((D.localEquations hD).pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) (D.localEquations hD))),
        A.IsCertified n) :
    IsLocallyCertified C R pi n (D.localEquations hD) := by
  refine isLocallyCertified_of_forall_prime_away_certified hD fun p => ?_
  obtain ⟨r, hrp, A, hA⟩ := h p
  haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
    isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
  -- bundle the supplied adaptation and its certificate; the divisor equality is `rfl`
  exact ⟨r, hrp, ⟨_, A, hA⟩, Scheme.LocalEquations.divEq_refl _⟩

/-- The `DivFamZar` class of a seed certified pointwise on the base. -/
noncomputable def divFamZar_of_forall_prime_away_certified (hD : D.IsGenerator)
    (h : ∀ p : PrimeSpectrum R, ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ G : CertifiedDivisorFamily C (Localization.Away r) pi n,
        Scheme.LocalEquations.DivEq G.eqns
          ((D.localEquations hD).pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) (D.localEquations hD)))) :
    DivFamZar C R pi n :=
  DivFamZar.mk (D.localEquations hD)
    (isLocallyCertified_of_forall_prime_away_certified hD h)

end ThetaGeneratorSeed

end AlgebraicGeometry
