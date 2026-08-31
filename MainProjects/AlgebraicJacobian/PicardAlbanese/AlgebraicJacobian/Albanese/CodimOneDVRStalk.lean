/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Albanese.CodimOneStalkRegularity
import AlgebraicJacobian.Albanese.CodimOneSmoothReduced
import AlgebraicJacobian.Algebra.SmoothPrimeRegularity
import AlgebraicJacobian.Algebra.CoheightBridge

/-!
# Regular stalks of a smooth variety; DVR at codimension-one points

Ported from the DVR-stalk layer of `Albanese/CodimOneExtension.lean` of the
previous Algebraic-Jacobian tree (identical toolchain and mathlib pin),
re-kernel-verified here. Fourth file of the codim-one extension layer.

* `isRegularLocalRing_stalk_of_smooth` — **Stacks `00TT`**: for a smooth
  integral variety `X` over `k̄`, the stalk at **every** point (closed or
  not) is a regular local ring. Chart-level standard smoothness
  (`exists_isStandardSmooth_at_of_smooth`) + the base identification
  (`gammaSpecField_ringEquiv`) + the Serre-free arbitrary-prime theorem
  `isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField`
  (`Algebra/SmoothPrimeRegularity.lean`). Public (rather than the source's
  `private`) because the Milne-3.3 lane needs it on the self-product
  `X ×_{k̄} X` to feed the pole-purity engine (`Albanese/PolePurity.lean`).
* `localRing_dvr_of_codim_one` — **smooth + codim-1 ⟹ DVR** (Hartshorne
  II.6 p. 130; Stacks `00PD`): at a point of coheight `1` the stalk is a
  discrete valuation ring. The Krull-dimension-1 input is the coheight
  bridge `Scheme.ringKrullDim_stalk_eq_coheight`
  (`Algebra/CoheightBridge.lean`).

Blueprint pin: `lem:smooth_codim_one_dvr`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

namespace Scheme

/-- **Stacks `00TT`, Jacobian-criterion direction (regularity conclusion).**
For a smooth integral variety `X` over an algebraically closed field `k̄`, the
stalk of `X` at **every** point (closed or not) is a regular local ring.

Proof: Stage 2 (`exists_isStandardSmooth_at_of_smooth`) produces an affine
chart `V ∋ z` whose section ring `Γ(X, V)` is standard-smooth over
`Γ(Spec k̄, U) ≃ k̄` (base identification `gammaSpecField_ringEquiv`,
transported by `RingHom.isStandardSmooth_respectsIso`); the stalk is the
localisation of `Γ(X, V)` at the prime of `z` (`IsAffineOpen.isLocalization_stalk`),
and the Serre-free Stacks-00TT theorem at arbitrary primes
`isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField`
(`Albanese/SmoothPrimeRegularity.lean`; conormal identity + Kähler-trdeg
identification + the polynomial-ring trdeg–height inequality) applies since
`k̄` is perfect.

**History.** This statement was the Stage-6 keystone gap of the codim-1
extension pipeline: the closed-point case was closed in `StandardSmoothDimension.lean`
(iter-199/ii.B) via `isRegularLocalRing_localizationAtPrime_of_isStandardSmooth_of_isAlgClosed`
(§3.B above), while the non-closed-point case was long believed to require
Stacks `00OF` (localisation of regular local rings, Serre's homological
characterisation — still absent from Mathlib v4.31). The
`SmoothPrimeRegularity.lean` route avoids `00OF` entirely; the previous
6-stage in-body scaffolding (flat stalks, Kähler freeness/rank at the stalk,
cotangent computation at rational points) survives as §3.A/§3.B helpers used
by the closed-point corollaries and `isReduced_of_smooth_of_isAlgClosed`.

Blueprint reference: `\cref{lem:smooth_to_regular_local_ring}` in
`blueprint/src/chapters/Albanese_CodimOneExtension.tex` (also Stacks
\href{https://stacks.math.columbia.edu/tag/00TT}{tag 00TT}). -/
theorem isRegularLocalRing_stalk_of_smooth
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    (z : X.left) :
    IsRegularLocalRing (X.left.presheaf.stalk z) := by
  -- Stage 2 chart: a standard-smooth section ring on an affine chart `V ∋ z`.
  obtain ⟨U, hU, V, hV, hzV, e, hSS⟩ := exists_isStandardSmooth_at_of_smooth X z
  -- Base identification `Γ(Spec k̄, U) ≃+* k̄` (U is nonempty: it contains the
  -- image of z).
  let ε : kbar ≃+* Γ(Spec (.of kbar), U) :=
    (gammaSpecField_ringEquiv kbar U ⟨⟨_, e hzV⟩⟩).symm
  have hSS' : ((X.hom.appLE U V e).hom.comp ε.toRingHom).IsStandardSmooth :=
    RingHom.isStandardSmooth_respectsIso.2 _ ε hSS
  letI : Algebra kbar Γ(X.left, V) :=
    ((X.hom.appLE U V e).hom.comp ε.toRingHom).toAlgebra
  haveI : Algebra.IsStandardSmooth kbar Γ(X.left, V) := hSS'.toAlgebra
  -- The stalk as the localisation of the chart ring at the prime of `z`.
  letI : Algebra Γ(X.left, V) (X.left.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨z, hzV⟩
  haveI hLoc : IsLocalization.AtPrime (X.left.presheaf.stalk z)
      (hV.primeIdealOf ⟨z, hzV⟩).asIdeal :=
    isLocalization_atPrime_stalk_of_affineOpen hV z hzV
  letI : Algebra kbar (X.left.presheaf.stalk z) :=
    ((algebraMap Γ(X.left, V) (X.left.presheaf.stalk z)).comp
      (algebraMap kbar Γ(X.left, V))).toAlgebra
  haveI : IsScalarTower kbar Γ(X.left, V) (X.left.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Nonempty V := ⟨⟨z, hzV⟩⟩
  haveI : Nontrivial Γ(X.left, V) :=
    AlgebraicGeometry.Scheme.component_nontrivial X.left V
  -- Conclude by the Serre-free Stacks-00TT theorem at arbitrary primes.
  exact isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField
    (k := kbar) (hV.primeIdealOf ⟨z, hzV⟩).asIdeal
    (hV.primeIdealOf ⟨z, hzV⟩).isPrime (X.left.presheaf.stalk z)

/-- **Helper for `localRing_dvr_of_codim_one`.** On a smooth integral variety
over an algebraically closed field, the stalk at a codimension-`1` point has a
*principal nonzero* maximal ideal. Encodes the substantive geometric content
of "regular in codimension one": smoothness ⟹ `IsRegularLocalRing` at the
stalk (Stacks `00PD`/`00TT`), and a Noetherian regular local ring with
`ringKrullDim = 1` has principal nonzero maximal ideal (Stacks `02IZ`),
via the cotangent-space `finrank = 1` characterisation.

**Iter-187 Lane M↓ refactor.** The previous body bundled both Mathlib gaps —
smooth ⟹ regular (Stacks 00TT) and codim-1 ⟹ Krull-dim-1 — into an inline
`hreg_dim` conjunction whose first conjunct was a bare `sorry`. The Krull-dim
half has been closed axiom-clean since iter-184 via
`Scheme.ringKrullDim_stalk_eq_coheight` (the iter-183 `CoheightBridge.lean`
bridge); the iter-187 refactor isolated the then-open Stacks-00TT gap as the
named helper `isRegularLocalRing_stalk_of_smooth` above, which is now fully
proved (via `Albanese/SmoothPrimeRegularity.lean`). The whole chain is
therefore **axiom-clean** — no residual gap. -/
private theorem smooth_codim_one_maximalIdeal_isPrincipal_and_ne_bot
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (X : Over (Spec (.of kbar)))
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    (z : X.left) (_hz : Order.coheight z = 1) :
    Submodule.IsPrincipal (IsLocalRing.maximalIdeal (X.left.presheaf.stalk z)) ∧
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk z) ≠ ⊥ := by
  -- Set up Noetherian structure on the stalk (needed for the cotangent-space API):
  -- `LocallyOfFiniteType X.hom` lifts the automatic `IsLocallyNoetherian (Spec k̄)`
  -- through to `IsLocallyNoetherian X.left`, from which the stalk picks up
  -- `IsNoetherianRing` (Mathlib instance).
  haveI : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  -- Regularity half: the named helper above (`isRegularLocalRing_stalk_of_smooth`,
  -- Stacks 00TT at every point — sorry-free via SmoothPrimeRegularity.lean).
  have hreg : IsRegularLocalRing (X.left.presheaf.stalk z) :=
    isRegularLocalRing_stalk_of_smooth X z
  -- Krull-dim half: closes via the iter-183 axiom-clean CoheightBridge
  -- equality + the codim-1 witness `_hz`.
  have hdim : ringKrullDim (X.left.presheaf.stalk z) = 1 := by
    rw [Scheme.ringKrullDim_stalk_eq_coheight]
    exact_mod_cast _hz
  -- From regularity + dim = 1, the cotangent space has `finrank = 1`
  -- (Mathlib `IsRegularLocalRing.iff_finrank_cotangentSpace`).
  have hfin :
      Module.finrank
        (IsLocalRing.ResidueField (X.left.presheaf.stalk z))
        (IsLocalRing.CotangentSpace (X.left.presheaf.stalk z)) = 1 := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hreg
    rw [hdim] at h
    exact_mod_cast h
  -- Principal maximal ideal: `finrank ≤ 1 ↔ IsPrincipal maximalIdeal`
  -- (Mathlib `IsLocalRing.finrank_cotangentSpace_le_one_iff`).
  have hprin : Submodule.IsPrincipal
      (IsLocalRing.maximalIdeal (X.left.presheaf.stalk z)) :=
    IsLocalRing.finrank_cotangentSpace_le_one_iff.mp hfin.le
  -- `maximalIdeal ≠ ⊥`: equivalent to "not a field" by Mathlib
  -- `IsLocalRing.isField_iff_maximalIdeal_eq`, and a field has Krull dim 0,
  -- contradicting `hdim : ringKrullDim = 1` via `ringKrullDim_eq_zero_of_isField`.
  have hne : IsLocalRing.maximalIdeal (X.left.presheaf.stalk z) ≠ ⊥ := by
    intro hbot
    have hF : IsField (X.left.presheaf.stalk z) :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot
    have h0 : ringKrullDim (X.left.presheaf.stalk z) = 0 :=
      ringKrullDim_eq_zero_of_isField hF
    -- Contradiction: `1 = 0` in `WithBot ℕ∞`.
    rw [hdim] at h0
    exact_mod_cast h0
  exact ⟨hprin, hne⟩

/-- **Smooth + codim-1 ⇒ DVR.** For a nonsingular integral variety `X` over
an algebraically closed field `k̄` and a point `η : X.left` with
`Order.coheight η = 1`, the stalk `X.left.presheaf.stalk η` is a discrete
valuation ring (with fraction field the function field `K(X)`).

The proof reduces to "regular local ring of Krull dimension `1` is a DVR"
(Mathlib `IsDiscreteValuationRing.isDiscreteValuationRing_iff` or analogous)
plus the smooth-variety fact that every local ring at a codim-1 point is
regular of dimension `1`. The geometric step is packaged in the private helper
`smooth_codim_one_maximalIdeal_isPrincipal_and_ne_bot`; the rest assembles the
DVR instance via `IsDiscreteValuationRing.TFAE`.

Blueprint reference: `lem:smooth_codim_one_dvr` (Hartshorne II.6 p. 130;
Stacks `00PD` for the regular-of-dim-1 ⇔ DVR equivalence). -/
theorem localRing_dvr_of_codim_one
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    (z : X.left) (_hz : Order.coheight z = 1) :
    IsDiscreteValuationRing (X.left.presheaf.stalk z) := by
  -- Set up Noetherian structure on the stalk:
  -- `LocallyOfFiniteType X.hom` lifts the (automatic) `IsLocallyNoetherian (Spec k̄)`
  -- to `IsLocallyNoetherian X.left`, from which the stalk inherits
  -- `IsNoetherianRing` (Mathlib instance). The stalk of an integral scheme is
  -- a domain (Mathlib instance), and stalks of schemes are always local (Mathlib
  -- instance); these are picked up automatically by typeclass search.
  haveI : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  -- Extract the principal+nonzero-maximal-ideal helper (the Mathlib-gap content).
  obtain ⟨hprin, hne⟩ :=
    smooth_codim_one_maximalIdeal_isPrincipal_and_ne_bot X z _hz
  -- The stalk is a local Noetherian domain with principal maximal ideal:
  -- promote `IsPrincipal (maximalIdeal)` to a `IsPrincipalIdealRing` instance
  -- and conclude DVR via `IsDiscreteValuationRing.mk`.
  -- The TFAE entry "principal maximal ideal ⇔ DVR" handles the conversion
  -- once we know `¬ IsField` (which follows from `maximalIdeal ≠ ⊥`).
  have hfield : ¬ IsField (X.left.presheaf.stalk z) := by
    intro hF
    exact hne ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF)
  have tfae := IsDiscreteValuationRing.TFAE (X.left.presheaf.stalk z) hfield
  -- TFAE entry index 4 is `Submodule.IsPrincipal (IsLocalRing.maximalIdeal R)`.
  exact ((tfae.out 0 4).mpr hprin)

end Scheme

end AlgebraicGeometry
