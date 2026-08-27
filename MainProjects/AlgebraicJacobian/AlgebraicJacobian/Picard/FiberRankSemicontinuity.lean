/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EntryIdealStratum

/-!
# Ring-level upper semicontinuity of the fibre rank

**Campaign milestone B5, algebraic core.**  For a finitely presented module
`M` over a commutative ring `R`, the sublevel locus of the fibre dimension

```
{p : PrimeSpectrum R | p.asIdeal.fiberRank M ≤ e}
```

is **open**, with no flatness, noetherian or finiteness hypothesis on `R`.

## Why this file exists beside `PointRankSemicontinuity.lean`

`Picard/PointRankSemicontinuity.lean` proves the *geometric* statement
`Scheme.Modules.isOpen_pointRank_le` — openness of `{s : S | pointRank S F s ≤ e}`
for a quasi-coherent `F` on a locally noetherian scheme `S`.  That is the same
mathematics one level up, and it is *not* the statement below: `pointRank`
is defined through a `choose`n affine chart and its `fiberRank` is taken at a
prime of `Γ(S, V)` for that chart, whereas this file's `fiberRank` is taken at a
prime of `R` itself with the `R`-module structure.  Measured in the earlier
round: the two are not the same term and `rfl` between them fails
(recorded as obligation (c) at `Picard/FiberH0Comparison.lean`:66-82).

Working at the ring level has three concrete consequences:

* **`IsLocallyNoetherian` disappears.**  The geometric proof runs through
  `Scheme.Modules.chartLocus`, whose construction needs the noetherian
  hypothesis; the affine argument below needs only `Module.FinitePresentation`.
* **No quasi-coherence side condition**, since there is no sheaf.
* It is the form the **two-term complex** consumers want: the fibres of a
  Čech complex's terms are modules over the base ring, not sheaves on it.

## The proof

The Nakayama prolongation `Module.FinitePresentation.exists_matrixPresentation_of_isLocalizedModule`
(`Picard/EntryIdeal.lean`, Nitsure §4) gives, for each prime `p`, an element
`g ∉ p` such that `M` localized away from `g` admits a matrix presentation with
exactly `p.fiberRank M` generators.  On the basic open `D(g)`:

* every prime `q ∈ D(g)` lifts to a prime `Q` of `R[1/g]`
  (`PrimeSpectrum.localization_away_comap_range`);
* `Ideal.fiberRank_of_isLocalizedModule` identifies `M`'s fibre rank at `q`
  with the localized module's fibre rank at `Q`;
* `Module.MatrixPresentation.fiberRank_le` bounds the latter by the generator
  count `p.fiberRank M ≤ e`.

So `D(g)` is an open neighbourhood of `p` inside the sublevel locus.  Every
ingredient was already in the tree; what was missing is that the prolongation's
generator count *is* the bound the sublevel set asks for.

## References

Nitsure, *Construction of Hilbert and Quot schemes*, §4 (the local
`e`-generator presentation).  Hartshorne III 12.8; Mumford, *Abelian
Varieties*, II §5.  Stacks 00NX.
-/

set_option autoImplicit false

universe u

open Module

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

namespace Ideal

/-- **Upper semicontinuity of the fibre rank, ring level.**

For `M` finitely presented over `R`, the set of primes at which the fibre
`κ(p) ⊗_R M` has dimension at most `e` is open in `Spec R`.  No flatness, and
no noetherian hypothesis on `R`.

Contrast `Module.isLocallyConstant_rankAtStalk`, which needs `M` *flat* and
concludes the strictly stronger local constancy; without flatness the rank
genuinely jumps and only this sublevel direction survives. -/
theorem isOpen_fiberRank_le [Module.FinitePresentation R M] (e : ℕ) :
    IsOpen {p : PrimeSpectrum R | p.asIdeal.fiberRank M ≤ e} := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  -- Nakayama prolongation at `p`: a `p.fiberRank M`-generator presentation
  -- survives on a basic open `D(g)` around `p`.
  obtain ⟨g, hg, hpres⟩ :=
    Module.FinitePresentation.exists_matrixPresentation_of_isLocalizedModule.{u, u, u, u}
      (R := R) (M := M) p.asIdeal
  obtain ⟨mm, ⟨P⟩⟩ := hpres (Localization.Away g)
    (LocalizedModule (Submonoid.powers g) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
  refine ⟨(PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)), ?_,
    (PrimeSpectrum.basicOpen g).isOpen, hg⟩
  intro q hq
  -- `q` avoids `g`, hence lifts to a prime `Q` of `R[1/g]`.
  have hrange : q ∈ Set.range (PrimeSpectrum.comap
      (algebraMap R (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact hq
  obtain ⟨Q, hQ⟩ := hrange
  have hloc := Ideal.fiberRank_of_isLocalizedModule (R := R) (M := M)
    (Submonoid.powers g) (LocalizedModule.mkLinearMap (Submonoid.powers g) M) Q.asIdeal
  have hcomap : Q.asIdeal.comap (algebraMap R (Localization.Away g)) = q.asIdeal := by
    rw [← hQ]; rfl
  change q.asIdeal.fiberRank M ≤ e
  calc q.asIdeal.fiberRank M
      = (Q.asIdeal.comap (algebraMap R (Localization.Away g))).fiberRank M :=
        Ideal.fiberRank_congr_ideal hcomap.symm
    _ = Q.asIdeal.fiberRank (LocalizedModule (Submonoid.powers g) M) := hloc.symm
    _ ≤ p.asIdeal.fiberRank M := Module.MatrixPresentation.fiberRank_le P Q.asIdeal
    _ ≤ e := hp

/-- **Ring level, closed form**: the superlevel locus of the fibre rank is
closed.  The set-theoretic complement of `isOpen_fiberRank_le`; the `ℕ`-valued
rank makes `e + 1 ≤ r` and `¬ (r ≤ e)` the same condition. -/
theorem isClosed_le_fiberRank [Module.FinitePresentation R M] (e : ℕ) :
    IsClosed {p : PrimeSpectrum R | e + 1 ≤ p.asIdeal.fiberRank M} := by
  have hcompl : {p : PrimeSpectrum R | e + 1 ≤ p.asIdeal.fiberRank M}
      = {p : PrimeSpectrum R | p.asIdeal.fiberRank M ≤ e}ᶜ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    omega
  rw [hcompl]
  exact (isOpen_fiberRank_le e).isClosed_compl

end Ideal
