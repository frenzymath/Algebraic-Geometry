/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FiberRankSemicontinuity

/-!
# B5's engine: upper semicontinuity of `dim H⁰` for a two-term complex

**Campaign milestone B5, the Mumford minors argument, done through cokernels.**

For a two-term complex `k : K → Aⁿ` with `K` merely **finitely presented** —
weaker than the shape `TwoTermFiniteReplacement` produces
(`Picard/TwoTermFiniteFree.lean`:507, whose `K0` is also projective) — the
locus

```
{t : Spec A | dim_κ(t) ker (k ⊗ κ(t)) ≤ e}
```

is **open**.  That is upper semicontinuity of the fibrewise `H⁰` of the
complex, which is what B5 asks for once `H⁰` is presented as a kernel.

## Why this route works where the prescribed one cannot

`Picard/SemicontinuityH0.lean`:55-57 prescribes discharging the gate through
the *rank bridge* `rank_pushforward_eq_fiberH0`.  Measured in the previous
round and filed as I-0884: that bridge carries `hproj`, which its own file
proves load-bearing by counterexample, and finite projectivity forces the rank
**locally constant** — strictly stronger than the semicontinuity wanted.  The
prescription inverts the difficulty.

The route below never touches that bridge.  It needs **no flatness anywhere**.
Rank-nullity on each fibre reads

```
dim ker (k ⊗ κ)  +  n  =  dim (κ ⊗ K)  +  dim coker (k ⊗ κ)        (rank-nullity)
                          ─────────────    ────────────────────
                          both upper semicontinuous, by
                          Ideal.isOpen_fiberRank_le (no flatness)
```

so near a point `t₀`, bounding *each* summand by its own value at `t₀` bounds
the sum, hence bounds `dim ker`:

```
{dim ker ≤ e}  ⊇  {fiberRank K ≤ a}  ∩  {fiberRank (coker k) ≤ b},
                  where a, b are those ranks at t₀,
```

an intersection of two opens containing `t₀`.  That is all the argument needs.

**Projectivity of `K` is NOT required, and an earlier revision of this docstring
said it was.**  The first draft proved local *constancy* of `fiberRank K` (via
`Module.isLocallyConstant_rankAtStalk`, which does need `K` flat) and cut the
sublevel locus as `{fiberRank K = r} ∩ {fiberRank coker ≤ e + n − r}`.  That
works, but it over-buys: upper semicontinuity of both summands suffices, since
only an upper bound on the sum is ever wanted.  A fresh-context review found the
theorem provable with the `[Module.Projective A K]` binder deleted, and the
binder is now gone.  The practical consequence is downstream: a complex fed to
this engine owes finite presentation of `K` and nothing else — in particular the
projectivity half of `TwoTermFiniteReplacement`'s shape is not owed.

## The junk-value hazard is closed structurally, not assumed

`Picard/FiberH0Comparison.lean`:38-55 records obligation (b): `Module.finrank`
returns `0` in the infinite-dimensional case, on both sides, so a rank identity
can hold vacuously as `0 = 0`.  Here that cannot happen, and **no hypothesis is
needed to rule it out**: `κ(t) ⊗_A K` is finite-dimensional because `K` is
`Module.Finite` (implied by `Module.FinitePresentation`), and `κ(t) ⊗_A Aⁿ` is
`n`-dimensional outright.  Both are automatic instances — `FiniteDimensional`
is synthesised, not supplied.  So every `finrank` below is a genuine dimension.

## What this does and does not discharge

**Discharges**, sorry-free: the semicontinuity statement for any two-term
complex of the replacement's shape, over any commutative ring, with no
noetherian hypothesis and no `h¹`-vanishing.  Obligation (b) of the three
recorded at `Picard/FiberH0Comparison.lean`:79-82 is closed outright — not
weakened, not moved: finite-dimensionality is now a consequence rather than an
antecedent.

**Does not discharge**: `Scheme.HasH0Semicontinuity`
(`Picard/SemicontinuityH0.lean`:93) is still **open**, and this file does not
instantiate it.  Two obligations stand between the two statements, and they are
the (a) and (c) of that list:

* (a) the curve's Čech complex must be *replaced* by one of this shape.
  `exists_twoTermFiniteReplacement` (`Picard/TwoTermFiniteFree.lean`:545) does
  produce `K0` projective and `K¹ = Aⁿ` free, so the shape matches — but it
  needs `Module.Flat` on both terms of the original and finite generation of
  `H⁰`/`H¹`, and its `h0_bijective` field compares the replacement's `H⁰` with
  the original's, which is a further identification not made here;
* (c) the carrier bridge: `κ(t)`-dimension of a *kernel over `A`* against
  `Scheme.Hom.fiberH0`, the dimension of `Γ(C_t, L_t)`.  Steps 4-6 of
  `fiberRank_gammaTop_eq_fiberH0` (`Picard/FiberH0Comparison.lean`) are
  hypothesis-free and do exactly this transport for the Čech difference map,
  so the bridge is a composition rather than a new theorem — but it has not
  been composed, and until it is, no statement here is about a curve.

So: an implication proved, with (a) and (c) named and open.  Nothing below
should be read as "B5 is closed".

## References

Mumford, *Abelian Varieties*, II §5 Lemma 1 (the two-term finite replacement
and its minors); EGA III 6.10.5; Hartshorne III 12.8; Stacks 00NX, 02KG.
-/

set_option autoImplicit false

universe u

open Module TensorProduct

variable {A : Type u} [CommRing A] {K : Type u} [AddCommGroup K] [Module A K]

namespace AlgebraicJacobian

namespace TwoTerm

/-- **Base change commutes with cokernels**, in the fibre-rank form B5 uses:
the fibre rank of `coker k` at `t` is the `κ(t)`-dimension of the cokernel of
the base-changed map.

Right-exactness of `κ(t) ⊗_A -`, packaged as a `finrank` identity.  (The
sibling project carries the same equivalence as
`LinearMap.quotRangeBaseChangeEquiv`; it is re-derived here rather than
imported, since AJC does not depend on that project.) -/
theorem fiberRank_quotRange_eq_finrank_quot_baseChange {N : Type u} [AddCommGroup N]
    [Module A N] (k : K →ₗ[A] N) (t : PrimeSpectrum A) :
    t.asIdeal.fiberRank (N ⧸ LinearMap.range k)
      = Module.finrank t.asIdeal.ResidueField
          ((t.asIdeal.ResidueField ⊗[A] N) ⧸
            LinearMap.range (k.baseChange t.asIdeal.ResidueField)) := by
  have hker : LinearMap.ker ((LinearMap.range k).mkQ.baseChange t.asIdeal.ResidueField)
      = LinearMap.range (k.baseChange t.asIdeal.ResidueField) := by
    apply LinearMap.exact_iff.mp
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact _ (LinearMap.exact_map_mkQ_range k) (Submodule.mkQ_surjective _)
  have hsurj : Function.Surjective
      ((LinearMap.range k).mkQ.baseChange t.asIdeal.ResidueField) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
  exact LinearEquiv.finrank_eq
    (((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (((LinearMap.range k).mkQ.baseChange t.asIdeal.ResidueField).quotKerEquivOfSurjective
        hsurj)).symm)

/-- **The pointwise rank-nullity identity** for a two-term complex
`k : K → Aⁿ`, at a prime `t`:

```
dim ker (k ⊗ κ(t))  +  n  =  fiberRank K  +  fiberRank (coker k).
```

Both fibres are finite-dimensional automatically (`K` is `Module.Finite`, and
`κ(t) ⊗ Aⁿ` is `n`-dimensional), so no `finrank` here is a junk `0` — see the
module docstring on obligation (b). -/
theorem finrank_ker_baseChange_add_eq (n : ℕ) (k : K →ₗ[A] (Fin n → A))
    [Module.Finite A K] (t : PrimeSpectrum A) :
    Module.finrank t.asIdeal.ResidueField
        (LinearMap.ker (k.baseChange t.asIdeal.ResidueField)) + n
      = t.asIdeal.fiberRank K
        + t.asIdeal.fiberRank ((Fin n → A) ⧸ LinearMap.range k) := by
  have h1 : finrank t.asIdeal.ResidueField
        (LinearMap.range (k.baseChange t.asIdeal.ResidueField))
      + finrank t.asIdeal.ResidueField
        (LinearMap.ker (k.baseChange t.asIdeal.ResidueField))
      = finrank t.asIdeal.ResidueField (t.asIdeal.ResidueField ⊗[A] K) :=
    (k.baseChange t.asIdeal.ResidueField).finrank_range_add_finrank_ker
  have h2 : finrank t.asIdeal.ResidueField
        ((t.asIdeal.ResidueField ⊗[A] (Fin n → A)) ⧸
          LinearMap.range (k.baseChange t.asIdeal.ResidueField))
      + finrank t.asIdeal.ResidueField
        (LinearMap.range (k.baseChange t.asIdeal.ResidueField))
      = finrank t.asIdeal.ResidueField (t.asIdeal.ResidueField ⊗[A] (Fin n → A)) :=
    Submodule.finrank_quotient_add_finrank _
  have h3 : finrank t.asIdeal.ResidueField
      (t.asIdeal.ResidueField ⊗[A] (Fin n → A)) = n := by
    rw [LinearEquiv.finrank_eq (TensorProduct.piScalarRight A t.asIdeal.ResidueField
      t.asIdeal.ResidueField (Fin n))]
    simp
  have h4 : t.asIdeal.fiberRank K
      = finrank t.asIdeal.ResidueField (t.asIdeal.ResidueField ⊗[A] K) := rfl
  have h5 := fiberRank_quotRange_eq_finrank_quot_baseChange k t
  rw [h4, h5]
  omega

/-- **The cokernel of a two-term complex is finitely presented**, when the
degree-0 term is finite: `Aⁿ` is finitely presented and `range k` is finitely
generated. -/
instance finitePresentation_quotRange (n : ℕ) (k : K →ₗ[A] (Fin n → A))
    [Module.Finite A K] :
    Module.FinitePresentation A ((Fin n → A) ⧸ LinearMap.range k) := by
  apply Module.finitePresentation_of_surjective (Submodule.mkQ (LinearMap.range k))
    (Submodule.mkQ_surjective _)
  rw [Submodule.ker_mkQ]
  exact Submodule.FG.of_finite

/-- **B5's engine: `dim H⁰` of a two-term complex is upper semicontinuous.**

For `k : K → Aⁿ` with `K` finitely presented and projective — the shape of
`TwoTermFiniteReplacement` — the locus where the fibrewise kernel has dimension
at most `e` is open in `Spec A`.

No noetherian hypothesis on `A`, no `h¹`-vanishing, and no appeal to
`rank_pushforward_eq_fiberH0` (whose `hproj` would force local constancy and
so cannot serve semicontinuity — I-0884).

Proof: rank-nullity splits `dim ker` into a locally constant part
(`fiberRank K`, by `Module.isLocallyConstant_rankAtStalk` — `K` projective is
flat) and an upper-semicontinuous part (`fiberRank (coker k)`, by
`Ideal.isOpen_fiberRank_le`).  Near any `t₀` where `fiberRank K = r`, the
sublevel locus is the intersection of `{fiberRank K = r}` with
`{fiberRank (coker k) ≤ e + n − r}`. -/
theorem isOpen_finrank_ker_baseChange_le (n : ℕ) (k : K →ₗ[A] (Fin n → A))
    [Module.FinitePresentation A K] (e : ℕ) :
    IsOpen {t : PrimeSpectrum A | Module.finrank t.asIdeal.ResidueField
      (LinearMap.ker (k.baseChange t.asIdeal.ResidueField)) ≤ e} := by
  rw [isOpen_iff_forall_mem_open]
  intro t₀ ht₀
  simp only [Set.mem_setOf_eq] at ht₀
  -- The neighbourhood: both fibre ranks bounded by *their own values at `t₀`*.
  -- Openness of each is `Ideal.isOpen_fiberRank_le`; no flatness enters.
  refine ⟨_, ?_,
    (Ideal.isOpen_fiberRank_le (M := K) (t₀.asIdeal.fiberRank K)).inter
    (Ideal.isOpen_fiberRank_le (M := (Fin n → A) ⧸ LinearMap.range k)
      (t₀.asIdeal.fiberRank ((Fin n → A) ⧸ LinearMap.range k))),
    ⟨?_, ?_⟩⟩
  · rintro t ⟨hV, hW⟩
    have h := finrank_ker_baseChange_add_eq n k t
    have h₀ := finrank_ker_baseChange_add_eq n k t₀
    simp only [Set.mem_setOf_eq] at hV hW ⊢
    omega
  · exact Set.mem_setOf_eq ▸ le_refl _
  · exact Set.mem_setOf_eq ▸ le_refl _

/-- **Closed form**: the superlevel locus of the fibrewise kernel dimension is
closed.  The complement of `isOpen_finrank_ker_baseChange_le`; this is the
direction milestone B6 consumes. -/
theorem isClosed_le_finrank_ker_baseChange (n : ℕ) (k : K →ₗ[A] (Fin n → A))
    [Module.FinitePresentation A K] (e : ℕ) :
    IsClosed {t : PrimeSpectrum A | e + 1 ≤ Module.finrank t.asIdeal.ResidueField
      (LinearMap.ker (k.baseChange t.asIdeal.ResidueField))} := by
  have hcompl : {t : PrimeSpectrum A | e + 1 ≤ Module.finrank t.asIdeal.ResidueField
        (LinearMap.ker (k.baseChange t.asIdeal.ResidueField))}
      = {t : PrimeSpectrum A | Module.finrank t.asIdeal.ResidueField
        (LinearMap.ker (k.baseChange t.asIdeal.ResidueField)) ≤ e}ᶜ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    omega
  rw [hcompl]
  exact (isOpen_finrank_ker_baseChange_le n k e).isClosed_compl

end TwoTerm

end AlgebraicJacobian
