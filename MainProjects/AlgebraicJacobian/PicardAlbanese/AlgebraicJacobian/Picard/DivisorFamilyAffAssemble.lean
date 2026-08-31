/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffSwallow
import AlgebraicJacobian.Picard.DivisorFamilyAffZar

/-!
# cert-assemble on the widened cover: from a straddling piece to `DivFamZarAff`

Roadmap leaf `AJCR.w4-rep.datum.dat-d.ddr.certificate.cert-assemble`, over the widened
predicate.  This composes the lane into one statement: **pointwise on the base, a straddling
affine piece plus the (c1)/(c2) inputs give a widened locally-certified system**, hence a
`DivFamZarAff` class.

## What each hypothesis is, and why it is where it is

The assembler takes, at each prime `p` of the base, an away localization `r ∉ p` over which:

* the pulled system has an adaptation whose cover has a **straddling piece**
  (`SwallowedBy`) — the Stacks `0B8B` geometric input, explicit per I-0492 clause 2;
* the **glued clauses** (c2)/(c3)/(c4) hold.  These are not free **in general**:
  `cert-collapse` showed the diagonal of the difference arrow vanishes identically, so (c4)
  always forces flatness of the diagonal overlap colengths (I-0340).  That refutation stands
  and is about an ARBITRARY adaptation.  **But under `SwallowedBy` — which this assembler
  already assumes — they are derivable rather than assumed**: `ovlColengthDiagEquiv`
  (`…AffGlue.lean`) identifies `ovlColength i i` with `colength i`, so the flatness (c4)
  forces *is* (c1)-flatness, and `AffAdaptation.isCertified_of_swallowedBy_of_c1` delivers all
  seven clauses from (c1) plus the rank datum with these five hypotheses gone.  This
  five-hypothesis form is kept because it survives for covers that are **not** swallowed;
  a caller on a straddling cover should prefer the derived form (I-0668);
* the **fibrewise-regularity** input for (c1)-projectivity, which is I-0492 clause 4(i) in
  its per-piece form.  It is a hypothesis, not carrier data.

The clauses (c1) themselves are *produced*, not assumed: `finite_colength` from the
straddling piece via the support-trace engine, `projective_colength` from the fibrewise
input via the widened flatness route.  That is the whole value the lane adds — clause (c1),
the one the fixed-pair design could not supply for a straddling divisor, now comes for free
from an affine-open cover.

## Main declarations

* `AffAdaptation.isCertified_of_swallowedBy` — the certificate from a straddling piece plus
  the glued clauses and the fibrewise input.
* `AlgebraicGeometry.isLocallyCertifiedAff_of_forall_prime_swallowed` — the pointwise
  assembler.
* `AlgebraicGeometry.divFamZarAff_of_forall_prime_swallowed` — the resulting class, the
  object every DD-R consumer wants.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace AffAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d)

/-- **The certificate from a straddling piece.**  Clauses (c1) are PRODUCED: finiteness from
the straddling piece through the support-trace engine, projectivity from the fibrewise
regularity input through the widened flatness route (`AffCoverData.flat_sections_pieces`).
Clauses (c2)/(c3)/(c4) are hypotheses **here**, and the reason is narrower than it may look:
by `cert-collapse`/I-0340 the vanishing diagonal of the difference arrow makes (c4) imply
flatness of the diagonal overlap colengths for every adaptation whatsoever, so they are not
free in general.  Under the `hswallow` hypothesis this theorem already carries, however, they
ARE derivable — `AffAdaptation.isCertified_of_swallowedBy_of_c1` (`…AffGlue.lean`) gets all
seven clauses from (c1) plus the rank datum, because `ovlColengthDiagEquiv` makes the flatness
(c4) demands coincide with (c1)-flatness.  Prefer that form on a straddling cover; this one is
kept for covers that are not swallowed (I-0668). -/
theorem isCertified_of_swallowedBy [IsProper C.hom] [IsNoetherianRing R] {n : ℕ}
    (hswallow : D.SwallowedBy d)
    (hfib : ∀ (j : D.index) (p : PrimeSpectrum R),
      (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors
          (Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField))
    (hfinite_glued : Module.Finite R A.Glued)
    (hproj_glued : Module.Projective R A.Glued)
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk A.Glued p = n)
    (hflat_incl : Module.Flat R (A.chartProd ⧸ A.gluedSubmodule))
    (hflat_diff :
      Module.Flat R (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight))) :
    A.IsCertified n := by
  haveI hfin : ∀ j, Module.Finite R (A.colength j) :=
    A.forall_finite_colength_of_swallowedBy hswallow
  exact
    { finite_colength := hfin
      projective_colength := fun j => by
        haveI := hfin j
        exact A.projective_colength_of_forall_tmul_residueField j (hfib j)
      finite_glued := hfinite_glued
      projective_glued := hproj_glued
      rankAtStalk_glued := hrank
      flat_coker_incl := hflat_incl
      flat_coker_diff := hflat_diff }

end AffAdaptation

/-! ## The pointwise assembler -/

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {n : ℕ}

/-- **The pointwise assembler over the widened predicate.**  At every prime of the base it
suffices to produce an away localization carrying a widened certified family divisor-equal to
the pulled system; quasi-compactness of `Spec R` does the rest
(`isLocallyCertifiedAff_of_forall_prime_exists_away`).

This is the widened counterpart of
`isLocallyCertified_of_forall_prime_exists_certified_adaptation`
(`DivSchemeCertZarPointwise.lean:162`): same base-side shape, but the certificate on the
curve side is now carried by an arbitrary affine-open cover, so a divisor straddling both
pinned vertical fibres is no longer excluded. -/
theorem isLocallyCertifiedAff_of_forall_prime_certified_adaptation
    {d : (relCurve C R).LocalEquations}
    (h : ∀ p : PrimeSpectrum R, ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ (Dr : AffCoverData C (Localization.Away r))
        (A : AffAdaptation Dr
          (d.pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) d))),
        A.IsCertified n) :
    IsLocallyCertifiedAff n d := by
  refine isLocallyCertifiedAff_of_forall_prime_exists_away fun p => ?_
  obtain ⟨r, hrp, Dr, A, hA⟩ := h p
  haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
    isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
  -- bundle the supplied cover, adaptation and certificate; the divisor equality is `rfl`
  exact ⟨r, hrp, ⟨_, Dr, A, hA⟩, Scheme.LocalEquations.divEq_refl _⟩

/-- **The `DivFamZarAff` class of a system certified pointwise on the base.**  The endpoint
of the widened certificate lane: this is what a DD-R consumer receives, and no hypothesis on
`|P¹(k)|` appears anywhere in its production. -/
noncomputable def divFamZarAff_of_forall_prime_certified_adaptation
    {d : (relCurve C R).LocalEquations}
    (h : ∀ p : PrimeSpectrum R, ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ (Dr : AffCoverData C (Localization.Away r))
        (A : AffAdaptation Dr
          (d.pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) d))),
        A.IsCertified n) :
    DivFamZarAff C R n :=
  DivFamZarAff.mk d (isLocallyCertifiedAff_of_forall_prime_certified_adaptation h)

end AlgebraicGeometry
