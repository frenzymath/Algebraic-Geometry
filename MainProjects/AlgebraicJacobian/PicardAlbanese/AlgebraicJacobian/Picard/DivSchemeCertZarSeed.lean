/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertSeed
import AlgebraicJacobian.Picard.DivisorFamilyZarMapAlg

/-!
# Zariski-local certification of a seed system: relaxing the global certificate gate

The DD-R endgame consumes divisor families through `DivFamZar` (`DivisorFamilyZar.lean`),
whose membership predicate is `IsLocallyCertified`: some span-`⊤` family `g : Fin m → R`
carries certified families over the localizations `Localization.Away (g i)` which are
divisor-equal to the pulled system.  **Nothing downstream of `DivFamZar` asks for a
certificate over `R` itself.**

The certificate-assembly lane has nevertheless been attacking the *global* clause
`(D.divisorAdaptation hD).IsCertified g` over the chart ring `R_Z`, whose no-leak input
is exactly the hypothesis that is FALSE for arbitrary extracted pieces (I-0209: a piece
whose support trace leaks has a non-finite colength, and the localization repair breaks
finiteness over `R`).  The lane has been paying for a strictly stronger statement than
its consumer needs.

This file lands the relaxation.  `isLocallyCertified_of_forall_exists_away` says: to
certify a system *Zariski-locally* it suffices to produce, for each member of some
span-`⊤` family, a certified family over that localization which is divisor-equal to the
pulled system.  Then `ThetaGeneratorSeed.isLocallyCertified_of_forall_away_isCertified`
specializes it to a seed: if the seed's adaptation acquires a certificate **after
localizing at each member of a span-`⊤` family** — which is precisely what the support
tube produces (`Scheme.LocalEquations.exists_supportTube`: piece isolation is available
Zariski-locally on the base, never globally) — then the seed's own system is locally
certified, and hence has a `DivFamZar` class.

The mathematical content is the observation that `IsLocallyCertified` is designed to be
produced from local data and that the seed's pulled system over an away localization is
`DivEq` to the pulled adaptation's system on the nose; the localization step that makes
no-leak true is licensed here rather than being an unrecoverable obstruction.

## Main declarations

* `AlgebraicGeometry.isLocallyCertified_of_forall_exists_away` — the span-`⊤` production
  rule for `IsLocallyCertified`, stated with `Localization.Away` charts.
* `AlgebraicGeometry.ThetaGeneratorSeed.isLocallyCertified_of_forall_away_certified` —
  the seed form: away-local certificates give a locally certified seed system.
* `AlgebraicGeometry.ThetaGeneratorSeed.divFamZar_of_forall_away_certified` — the
  resulting `DivFamZar` class, the object every DD-R consumer actually wants.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); pin in-file. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

section Zariski

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]

/-- **The span-`⊤` production rule for local certification.** A local-equation system on
the relative curve is locally certified in degree `n` as soon as, over each member of
some span-`⊤` family of the base, a certified family is divisor-equal to the pulled
system.  This is definitionally `IsLocallyCertified`, exposed as a constructor so that
consumers never unfold the pin — and so that the *localization* step (the only place
where per-piece support isolation is available, `exists_supportTube`) is a licensed
input rather than an obstruction. -/
theorem isLocallyCertified_of_forall_exists_away {n m : ℕ} (g : Fin m → R)
    (hg : Ideal.span (Set.range g) = ⊤)
    {d : (relCurve C R).LocalEquations}
    (hcert : ∀ i : Fin m,
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (g i))) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away (g i)) (g i)
      ∃ G : CertifiedDivisorFamily C (Localization.Away (g i)) pi n,
        Scheme.LocalEquations.DivEq G.eqns
          (d.pullback (relCurveMap C R (Localization.Away (g i)))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away (g i))) d))) :
    IsLocallyCertified C R pi n d :=
  ⟨m, g, hg, hcert⟩

end Zariski

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {a n : ℕ} {K : Submodule R (relThetaSections C R pi a)}
variable {D : ThetaGeneratorSeed C R pi a K}

/- The curve instances are carried by the seed's own data; none of the declarations
below re-derives geometry from them. -/
omit [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom]

/-- **Away-local certificates give a locally certified seed system.** If over each member
of a span-`⊤` family the seed's pulled system is divisor-equal to a certified family, the
seed's own local-equation system is locally certified in degree `n`.

This is the honest replacement for the global certificate gate: the seed's no-leak input
is false for arbitrary extracted pieces (I-0209), but becomes available after shrinking
the base, and `DivFamZar` — the actual DD-R consumer — only ever needs the shrunken
data. -/
theorem isLocallyCertified_of_forall_away_certified (hD : D.IsGenerator)
    {m : ℕ} (g : Fin m → R) (hg : Ideal.span (Set.range g) = ⊤)
    (hcert : ∀ i : Fin m,
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (g i))) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away (g i)) (g i)
      ∃ G : CertifiedDivisorFamily C (Localization.Away (g i)) pi n,
        Scheme.LocalEquations.DivEq G.eqns
          ((D.localEquations hD).pullback
            (relCurveMap C R (Localization.Away (g i)))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away (g i))) (D.localEquations hD)))) :
    IsLocallyCertified C R pi n (D.localEquations hD) :=
  isLocallyCertified_of_forall_exists_away g hg hcert

/-- **The `DivFamZar` class of a Zariski-locally certified seed** — the object every DD-R
consumer (`divRepPullAt`, `DivRepAffinePullback.pull`, `divRepClassifyZar`) actually
takes as input.  No global `IsCertified` over `R` is required. -/
noncomputable def divFamZar_of_forall_away_certified (hD : D.IsGenerator)
    {m : ℕ} (g : Fin m → R) (hg : Ideal.span (Set.range g) = ⊤)
    (hcert : ∀ i : Fin m,
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (g i))) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away (g i)) (g i)
      ∃ G : CertifiedDivisorFamily C (Localization.Away (g i)) pi n,
        Scheme.LocalEquations.DivEq G.eqns
          ((D.localEquations hD).pullback
            (relCurveMap C R (Localization.Away (g i)))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away (g i))) (D.localEquations hD)))) :
    DivFamZar C R pi n :=
  DivFamZar.mk (D.localEquations hD)
    (isLocallyCertified_of_forall_away_certified hD g hg hcert)

/-- The global certificate still suffices, through the trivial one-member family: a
globally certified seed is locally certified.  Recorded so that the relaxation is a
genuine weakening of the old gate rather than a parallel track. -/
theorem isLocallyCertified_of_isCertified (hD : D.IsGenerator)
    (hc : (D.divisorAdaptation hD).IsCertified n) :
    IsLocallyCertified C R pi n (D.localEquations hD) := by
  have h := (D.certifiedFamily n hD hc).isLocallyCertified
  rwa [D.certifiedFamily_eqns hD hc] at h

end ThetaGeneratorSeed

end AlgebraicGeometry
