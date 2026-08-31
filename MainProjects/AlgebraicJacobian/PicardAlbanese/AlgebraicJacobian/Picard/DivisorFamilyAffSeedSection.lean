/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffSeedGate
import AlgebraicJacobian.Picard.DivisorFamilyAffMap

/-!
# THE SEED REACHES THE WIDENED FUNCTOR: a section of `divFunctorAff` from geometry

Roadmap leaf `AJCR.w4-rep.datum.dat-d.ddr.certificate.cert-assemble`, last link.

`…AffSeedGate.lean` produced a widened **class** `DivFamZarAff C R n` from a theta-generator
seed.  A DD-R consumer does not hold a class: it holds a section of the functor
`divFunctorAff` (`…AffMap.lean`) over a test object, because that is what
`DivRepGlobalData.pull` and `pull_comp` are about.  The step between those two is
`divFamZarAffAffineEquiv` (`…AffVehicle.lean`), and nothing had taken it.

## Why this was owed, and why it is cheap now

`informal/spec-dd-r.md` ADDENDUM 8 §8.7 records that a fresh-context reviewer *elaborated* the
composition `divFamZarAff_of_forall_prime_certified_adaptation` through
`(divFamZarAffAffineEquiv …).symm` and confirmed it typechecks — but nobody landed it, so at
`a41644c36` the widened lane still had no declaration whose **conclusion** is a functor value
built from geometry.  A composition that has been elaborated in a review and never named is
exactly the shape a sorry census reports as complete.

The caveat in `divFamZarAffAffineEquiv`'s own docstring — "getting from there to a general test
is `divFamZarAff.map`, which does **not** exist yet" — is **stale**: `divFamZarAff.map`,
`map_id`, `map_comp` and `divFunctorAff` landed in ADDENDUM 9.  So the affine section really is
a section of the functor now, and this file says so as a theorem rather than as prose.

## What this does and does not claim

It claims: geometry (a seed, the subordinate Stacks `0B8B` input, a degree datum) produces a
section of `divFunctorAff` over the affine test `overSpec k R`, and its class under the affine
collapse is the seed's own.

It does **not** claim the widened functor is representable, nor that a section over a
**general** test comes from a seed.  A general test is covered by affine opens and the widened
value on it is the glued limit; producing one from geometry means producing compatible seeds on
a cover, which is the `divRep` lane's business, not this file's.  The one landed route from a
chart-typed general-test section is `divFunctorToAff` (`…AffFunctorCompare.lean`), and it goes
old → new only, by ADDENDUM 3 §2 / ADDENDUM 4 §4.3.

## Main declarations

* `AlgebraicGeometry.ThetaGeneratorSeed.divFunctorAffSection` — the section of `divFunctorAff`
  over `overSpec k R` produced by a seed.
* `AlgebraicGeometry.ThetaGeneratorSeed.divFamZarAffAffineEquiv_divFunctorAffSection` — its
  class under the affine collapse is `divFamZarAff_of_swallowing_affineOpen`, i.e. the
  composition really is the gate's output and not some other value.
* `AlgebraicGeometry.ThetaGeneratorSeed.divFunctorAffSection_val` — its value at an affine open,
  spelled without the equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : ℕ}
variable {K : Submodule R (relThetaSections C R pi a)}

namespace ThetaGeneratorSeed

variable {D : ThetaGeneratorSeed C R pi a K}

/-- **A seed produces a section of the WIDENED FUNCTOR** over the affine test `overSpec k R`.

This is the composition ADDENDUM 8 §8.7 records as elaborated-in-review and never landed: the
gate's class carried through `(divFamZarAffAffineEquiv …).symm`.  Its conclusion is a value of
`divFunctorAff C n` at `op (overSpec k R)`, which is what a DD-R consumer restated on the
widened functor (`DivRepGlobalAffLift.lean`) actually manipulates.

The hypotheses are the gate's, unchanged and all visible: the subordinate Stacks `0B8B` input
(`hW`/`hsub`/`hWle`, assumed per I-0492 clause 2) and the degree datum `hrank` at the swallowing
piece.  Obligation 4(i) is absent because it is discharged from the seed. -/
noncomputable def divFunctorAffSection {n : ℕ} (hD : D.IsGenerator)
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (hsub : (D.localEquations hD).supportLocus ⊆ (W : Set (relCurve C R)))
    (z₀ : relCurve C R) (hWle : W ≤ (D.localEquations hD).cover.opens z₀)
    (hrank : ∀ (Dc : AffCoverData C R) (A : AffAdaptation Dc (D.localEquations hD))
      (j₀ : Dc.index),
      (D.localEquations hD).supportLocus ⊆ (Dc.pieces j₀ : Set (relCurve C R)) →
      (∀ j : Dc.index, j ≠ j₀ →
        Disjoint (D.localEquations hD).supportLocus (Dc.pieces j : Set (relCurve C R))) →
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (A.colength j₀) p = n) :
    (divFunctorAff C n).obj (op (overSpec k R)) :=
  (divFamZarAffAffineEquiv C n R).symm
    (divFamZarAff_of_swallowing_affineOpen hD hW hsub z₀ hWle hrank)

/-- **The section's class is the gate's class.**  Stated because it is the only thing that makes
the previous definition a *composition* rather than a fresh object: the affine collapse of the
produced section returns the widened class the certificate lane built, by
`Equiv.apply_symm_apply`.

Without this a consumer could not conclude anything about the section from the certificate. -/
@[simp]
theorem divFamZarAffAffineEquiv_divFunctorAffSection {n : ℕ} (hD : D.IsGenerator)
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (hsub : (D.localEquations hD).supportLocus ⊆ (W : Set (relCurve C R)))
    (z₀ : relCurve C R) (hWle : W ≤ (D.localEquations hD).cover.opens z₀)
    (hrank : ∀ (Dc : AffCoverData C R) (A : AffAdaptation Dc (D.localEquations hD))
      (j₀ : Dc.index),
      (D.localEquations hD).supportLocus ⊆ (Dc.pieces j₀ : Set (relCurve C R)) →
      (∀ j : Dc.index, j ≠ j₀ →
        Disjoint (D.localEquations hD).supportLocus (Dc.pieces j : Set (relCurve C R))) →
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (A.colength j₀) p = n) :
    divFamZarAffAffineEquiv C n R (divFunctorAffSection hD hW hsub z₀ hWle hrank)
      = divFamZarAff_of_swallowing_affineOpen hD hW hsub z₀ hWle hrank :=
  (divFamZarAffAffineEquiv C n R).apply_symm_apply _

/-- The section's value at an affine open of the test, spelled without the equivalence: the
gate's class restricted from the top affine open. -/
@[simp]
theorem divFunctorAffSection_val {n : ℕ} (hD : D.IsGenerator)
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (hsub : (D.localEquations hD).supportLocus ⊆ (W : Set (relCurve C R)))
    (z₀ : relCurve C R) (hWle : W ≤ (D.localEquations hD).cover.opens z₀)
    (hrank : ∀ (Dc : AffCoverData C R) (A : AffAdaptation Dc (D.localEquations hD))
      (j₀ : Dc.index),
      (D.localEquations hD).supportLocus ⊆ (Dc.pieces j₀ : Set (relCurve C R)) →
      (∀ j : Dc.index, j ≠ j₀ →
        Disjoint (D.localEquations hD).supportLocus (Dc.pieces j : Set (relCurve C R))) →
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (A.colength j₀) p = n)
    (U : (overSpec k R).left.affineOpens) :
    (divFunctorAffSection hD hW hsub z₀ hWle hrank).1 U
      = DivFamZarAff.mapAlgHom
          ((Over.resAlgHom (overSpec k R) le_top).comp
            (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom)
          (divFamZarAff_of_swallowing_affineOpen hD hW hsub z₀ hWle hrank) :=
  rfl

end ThetaGeneratorSeed

end AlgebraicGeometry
