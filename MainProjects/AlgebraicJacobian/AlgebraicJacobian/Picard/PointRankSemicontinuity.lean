/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FlatteningStratificationUniversal

/-!
# Upper semicontinuity of the point rank, without flatness

**Campaign milestone B5, base-side half.**  For a finitely presented
quasi-coherent module `F` on a locally noetherian scheme `S`, the sublevel
locus of the fibre dimension

```
{s : S | pointRank S F s ≤ e}
```

is **open**, with no flatness hypothesis anywhere.

## Why this is not the existing statement

`Picard/FlatteningStratificationUniversal.lean` already carries
`Scheme.Modules.isOpen_pointRank_pullback_eq`, and the two must not be
conflated:

* that theorem needs `Scheme.CoherentSheafFlat (𝟙 T)` on the pullback and
  concludes that the locus where the rank *equals* `e` is open — it is local
  constancy of the rank of a *flat* finitely presented module, geometrized;
* this one has **no flatness hypothesis** and concludes openness of the
  `≤ e` sublevel set.  Without flatness the rank genuinely jumps, so the
  equality loci are *not* open and only the sublevel direction survives.
  That is exactly the semicontinuity B5 asks for.

Neither implies the other: drop flatness from the first and it is false;
strengthen `≤ e` to `= e` here and it is false.

## The proof, and what it consumes

The locus is exactly the union `⋃ i ≤ e, chartLocus F i`, and
`Scheme.Modules.chartLocus` is by construction an `S.Opens` (a supremum of
affine opens), so openness is structural rather than earned:

* `⊆` is the **Nakayama prolongation**
  `Scheme.Modules.exists_presentationChart_mem`, packaged as
  `Scheme.Modules.mem_chartLocus_of_pointRank_eq`: a point of fibre dimension
  `i` has an affine neighbourhood carrying an `i`-generator matrix
  presentation.  Applied at `i := pointRank S F s`, which is `≤ e` by
  hypothesis;
* `⊇` is `Scheme.Modules.pointRank_le_of_mem_chartLocus` (an `i`-generator
  presentation bounds every fibre dimension in its chart by `i`), composed
  with `i ≤ e`.

So the mathematical content was already in the tree; what was missing was the
observation that the *union over `i ≤ e`* is the sublevel set.  No
monotonicity of `IsPresentationChart` in the generator count is needed — a
point contributes at its own rank, not at `e`.

## Scope, stated exactly

This is the **base-side** half of B5.  It is a statement about a module on
`S` and its fibre dimensions, and it is unconditional in the sense that
matters: no flatness, no `h¹`-vanishing, no properness.

It is **not** by itself `Scheme.HasH0Semicontinuity`
(`Picard/SemicontinuityH0.lean`), whose `h⁰` is the dimension of the global
sections of `L` on the scheme-theoretic *fibre curve* `C_t`, not the fibre
dimension of a module on the base.  Bridging the two needs the pushforward
`q_* L` to be finitely presented on the base and its fibre dimension to agree
with `q.fiberH0 L t` — and the landed bridge for that agreement,
`AlgebraicGeometry.rank_pushforward_eq_fiberH0`
(`Picard/RigidPushforwardRank.lean`), carries a `Module.Projective`
hypothesis which is *load-bearing* (a counterexample is recorded at
`Picard/RigidPushforwardP1Sheaf.lean`:567-576) and which forces `h⁰` to be
locally *constant*.  So that bridge cannot serve semicontinuity; see the
inbox issue filed by `ajc-p4` for the measurement.

## References

Nitsure, *Construction of Hilbert and Quot schemes*, §4 (the local
`e`-generator presentation and its chart).  Hartshorne III 12.8; Mumford,
*Abelian Varieties*, II §5.
-/

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

/-- **B5, base-side: the point-rank sublevel locus is open**, with no
flatness hypothesis.

For a finitely presented quasi-coherent `F` on a locally noetherian `S`, the
set of points whose fibre dimension is at most `e` is open.  Contrast
`isOpen_pointRank_pullback_eq`, which assumes flatness and gets openness of
the *equality* locus; without flatness only this sublevel direction is true.

The locus is `⋃ i ≤ e, chartLocus F i`: a point of rank `i ≤ e` lies in
`chartLocus F i` by the Nakayama prolongation, and every point of
`chartLocus F i` has rank `≤ i ≤ e`. -/
theorem isOpen_pointRank_le {S : Scheme.{u}} [IsLocallyNoetherian S] (F : S.Modules)
    [F.IsFinitePresentation] [F.IsQuasicoherent] (e : ℕ) :
    IsOpen {s : S | pointRank S F s ≤ e} := by
  have hset : {s : S | pointRank S F s ≤ e}
      = ⋃ i ∈ Finset.range (e + 1), ((chartLocus F i : S.Opens) : Set S) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · intro hs
      exact ⟨pointRank S F s, by omega, mem_chartLocus_of_pointRank_eq F _ rfl⟩
    · rintro ⟨i, hie, hmem⟩
      exact le_trans (pointRank_le_of_mem_chartLocus F i hmem) (by omega)
  rw [hset]
  exact isOpen_biUnion fun i _ => (chartLocus F i).isOpen

/-- **B5, base-side, closed form**: the superlevel locus of the point rank is
closed.  This is the direction milestone B6 consumes (closedness of a
triviality locus), obtained as the set-theoretic complement — the `ℕ`-valued
rank makes `e + 1 ≤ r` and `¬ (r ≤ e)` the same condition. -/
theorem isClosed_le_pointRank {S : Scheme.{u}} [IsLocallyNoetherian S] (F : S.Modules)
    [F.IsFinitePresentation] [F.IsQuasicoherent] (e : ℕ) :
    IsClosed {s : S | e + 1 ≤ pointRank S F s} := by
  have hcompl : {s : S | e + 1 ≤ pointRank S F s}
      = {s : S | pointRank S F s ≤ e}ᶜ := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    omega
  rw [hcompl]
  exact (isOpen_pointRank_le F e).isClosed_compl

end Modules

end Scheme

end AlgebraicGeometry
