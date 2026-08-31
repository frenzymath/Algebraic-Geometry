/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.SectionDrop

/-!
# From the order-cone to a degree threshold: single-field bounded vanishing

`Ledger/SectionDrop.lean` proved that `H¹` vanishing is upward closed **in the divisor order**
(`subsingleton_hModule_one_of_le`) and reduced degree-threshold vanishing to a named
hypothesis `exists_bound_of_cofinal_vanishing`: *every divisor of large degree dominates some
divisor at which `H¹` vanishes*.  Its docstring called that cofinality statement open, and
recorded that "nothing in AJC or AJCR currently produces it".

**That was wrong, and this file discharges it.**  The missing move is not a new cofinality
input: it is that the peel may be applied to a *linearly equivalent translate* of the base
divisor.  `Ledger/MulEquiv.lean` already supplies the translation
(`mulEquivDivisorSheaf : 𝒪(A) ≅ 𝒪(A − div g)`) and `Ledger/ChiLedger.lean` already supplies
the Riemann inequality that manufactures the translating function.  Both were in the tree
before this file; what was missing was to put them together.

## PROVENANCE, AND IT IS NOT "NEW": THIS IS AJCR'S ARGUMENT

Read this before describing anything below as novel.  The sibling project
`Algebraic-Jacobian-Challenge-Rebuild` **already runs exactly this argument**, in
`RiemannRoch/UniformVanishing.lean:71`
(`exists_bound_subsingleton_hModule_one_of_isFinite_toP1`), whose conclusion is literally the
shape of `exists_bound_subsingleton_hModule_one` below and whose bound
`n₁·deg F + 1 − χ(𝒪_Y)` has the same `+ 1 − χ` form as ours.  Its three steps are ours:

1. class invariance of `H¹` vanishing — AJCR's `RiemannRoch/ClassCohomology.lean:111`
   `subsingleton_hModule_one_of_picClass_eq`, proved by exactly the transport
   `(Sheaf.HModule.mapEquiv … 1).toEquiv` that `subsingleton_hModule_one_sub_divOf` uses here;
2. an effective witness in the class from a degree bound (`exists_effective_of_picClass`), which
   is our `exists_unit_nonneg_of_h0_pos` composed with the Riemann inequality;
3. peel the effective part (`peel_effective`), which is `SectionDrop`'s
   `subsingleton_hModule_one_add_effective`.

So what is genuinely this file's own is **not the mathematics**.  It is (a) that the argument
runs on AJC's Ledger carrier with **no Picard vocabulary at all** — AJCR routes every step
through `picClass`, `classDeg` and `CechPic`, which AJC's Ledger tree does not have and whose
import would drag in eleven `Picard/` presentation modules; (b) that it is stated from an
*arbitrary* base vanishing rather than specialised to the fibre tower of a finite map to `ℙ¹`,
so it does not require `π` at all; and (c) the global-generation half (item 3 below), which
AJCR does not derive from this bound.

**Claim (c) machine-checked, since (a) and (b) are the kind of claim this lane has now got
wrong three times.**  AJCR *has* the slice lemma `RiemannRoch/ChiSlice.exact_map_g_delta`, but
its only two uses in that project are inside `ChiSlice.lean` itself, for χ-additivity; and the
only `Function.Surjective (Sheaf.HModule.map …)` anywhere in AJCR is
`SectionBound.lean:74`, which is the **peel** `map … .f 1`, not the evaluation `map … .g 0`.
So neither project derived generation from the slice before this file.  Grep, not inference —
and it is a *negative* claim about a name, so it is measured across the whole sibling project,
per the cone-scoping rule that caught this lane twice (`I-0622`, `I-0642`).

An earlier version of this docstring, and the commit message that landed it, presented the
insight as new to the workspace and said the ingredients had merely never been "put together".
That was the *third* time this lane misjudged availability by searching too narrowly — here the
whole assembled theorem existed next door, and a predecessor session had even read
`UniformVanishing.lean` and reported it as "single-field bounded vanishing AJC already owns",
without noticing that the argument inside it was the very step this lane went on to publish as
open.  Treat the value of this file as a *port with a carrier change*, not a discovery.

## The argument, in one paragraph

Fix any `D₀` with `H¹(𝒪(D₀)) = 0`.  Let `D` be a divisor with
`deg D ≥ deg D₀ + 1 − χ(𝒪_X)`.  Then `deg (D − D₀) + χ(𝒪_X) ≥ 1`, so the Riemann inequality
`riemann_inequality` gives `h⁰(𝒪(D − D₀)) ≥ 1`: there is a **nonzero global section** of
`𝒪(D − D₀)`, i.e. a `g ∈ K(X)ˣ` with `D − D₀ + div g ≥ 0`.  Set `D₀' := D₀ − div g`.  Then
`D₀' ≤ D` by construction, and `H¹(𝒪(D₀')) = 0` because `𝒪(D₀) ≅ 𝒪(D₀ − div g)`.  Apply the
order-cone peel to `D₀' ≤ D`.  Done — and note this is *exactly* the cofinality statement
`exists_bound_of_cofinal_vanishing` asks for, now proved rather than assumed.

## What is proved

* `exists_unit_nonneg_of_h0_pos` — the section-to-effective bridge on AJC's carrier: a
  nonzero global section of `𝒪(A)` is a `g ∈ K(X)ˣ` with `0 ≤ A + div g`.  (AJCR has this as
  `RiemannRoch/SectionBound.exists_effective_of_h0_pos`, stated through its `picClass`
  machinery, which AJC's Ledger tree does not have; this is the same three-step proof stated
  with no Picard vocabulary at all — see the provenance note there.)
* `exists_le_subsingleton_of_deg_ge` (★) — **the cofinality theorem**, i.e. the hypothesis of
  `exists_bound_of_cofinal_vanishing` discharged: from one base vanishing, every `D` of degree
  `≥ deg D₀ + 1 − χ(𝒪_X)` dominates a vanishing divisor.
* `subsingleton_hModule_one_of_deg_ge` (★★) — **single-field bounded vanishing**:
  `H¹(𝒪(D)) = 0` for every `D` with `deg D ≥ deg D₀ + 1 − χ(𝒪_X)`.  This is cluster-P item 1,
  and it is a *degree* half-space, not an order-cone.
* `exists_bound_subsingleton_hModule_one` — the `∃ b, ∀ D, b ≤ deg D → …` shape, which is the
  form downstream consumers ask for.
* `subsingleton_hModule_one_sub_divOf` — the invariance step on its own: `H¹` vanishing
  transports along `𝒪(A) ≅ 𝒪(A − div g)`.  This is the lemma that makes the whole file work and
  it needs no finiteness, being a transport of a `Subsingleton` along an isomorphism.
* `h1_eq_zero_of_deg_ge`, `deg_lt_of_not_subsingleton` — the `h¹`-spelling of the headline, and
  its contrapositive: a *non*-vanishing `H¹` forces `deg D < deg D₀ + 1 − χ(𝒪_X)`, so
  non-vanishing is a bounded-degree phenomenon.
* `subsingleton_of_h1_eq_zero`, `subsingleton_hModule_one_of_deg_ge_of_h1_eq_zero` — the entry
  point for a caller holding the base vanishing in the *numeric* `h¹ = 0` spelling plus
  finiteness of that `H¹`.  The `Subsingleton` form stays primitive throughout, because `h¹ = 0`
  alone is vacuous on an infinite-dimensional `H¹`; these only convert where finiteness is in
  hand, which is where a genus computation puts it.
* `h0_eq_of_deg_ge`, `exists_bound_h0_eq` (★★) — **exact Riemann–Roch above a degree bound**:
  `h⁰(𝒪(D)) = χ(𝒪_X) + deg D`, in explicit-bound and existential forms.  The curve spelling
  `h⁰(𝒪(D)) = 1 − genus + deg D` is not declared here; it is `χ(𝒪_C) = 1 − ledgerGenus C`
  (`Ledger/ChiCurve.chi_moduleKSheaf`) substituted into the above, and the substituted form is
  exercised by `probe_rr_deg_ge_curve` in `scripts/ajcrr-degreevanishing-axioms.lean`.
* `h0_eq_h0_sub_point_add_residueDeg_of_deg_ge` — the section drop becomes **exact** above the
  bound: every further point contributes its full residue degree.
* `surjective_hModule_zero_devissageπ`, `surjective_eval_of_deg_ge`, `generated_of_deg_ge`
  (★★) — **global generation**, cluster-P item 3: evaluation `H⁰(𝒪(D)) → H⁰(sky_x J) ≅ κ(x)` is
  surjective at every closed point above the bound.  Off the six-term slice, with no finiteness.
* `subsingleton_of_deg_ge_of_zero`, `subsingleton_of_deg_ge_of_moduleKSheaf` — the specialisation
  to `D₀ = 0`, whose base vanishing is `H¹(𝒪_X) = 0`, and which therefore fires exactly on the
  curves of genus zero.  Recorded to make the *shape* of the input honest.

## THE THREE CLUSTER-P ITEMS, KEPT APART

This file closes exactly one of the three, and it is worth being blunt about which.

1. **Single-field bounded vanishing — CLOSED HERE, conditionally on one base vanishing.**
   `subsingleton_hModule_one_of_deg_ge` is it.  The residual input is *one* divisor `D₀` with
   `H¹(𝒪(D₀)) = 0`; note it is a *single* hypothesis at a *single* divisor, not a family, and
   the bound is then explicit: `deg D₀ + 1 − χ(𝒪_X)`.

   **THE ANTECEDENT IS NOW WITNESSED — the paragraphs that follow are HISTORY, kept because the
   distinction they draw is still the right one to draw.**  `Ledger/FiberVanishing.lean` (the
   AJCR port named in the third paragraph below) landed, and `Ledger/FiberBound.lean` composes it
   with the χ-ledger, so at a smooth proper geometrically irreducible curve the conclusions of
   this file hold **with no vanishing hypothesis at all**: see
   `exists_bound_subsingleton_hModule_one_curve` and `exists_bound_h0_eq_genus_curve`, which carry
   the three curve binders only.  Consume those when you want an unconditional statement; consume
   the theorems in *this* file when you have a base vanishing from somewhere else, or want the
   explicit bound in terms of your own `D₀`.  What has NOT changed is item 2 below:
   extension-uniformity remains untouched.

   What follows is the state as measured before that port, and it records the failure mode worth
   remembering — a file can be sorry-free and axiom-clean while every theorem in it rests on an
   antecedent the project cannot produce.  At that time: **AJC proved that antecedent at no proper
   curve at all.**  The only producer of
   `Subsingleton (Sheaf.HModule (X.moduleKSheaf k) 1)` in the project is
   `Ledger/AffineVanishing.Scheme.subsingleton_moduleKSheaf_hModule_one` (:329), and it carries
   `[IsAffine X]` — which a proper curve never satisfies.  No `genus … = 0` or
   `ledgerGenus … = 0` is proved anywhere either, so the genus-zero route below is a *shape*, not
   an instance: it says what to feed the theorems, not that AJC can feed them.

   So the honest reading of everything in this file is **conditional, with an antecedent that is
   currently unwitnessed in this project**.  The theorems are not vacuous — the hypothesis is
   satisfiable, and AJCR discharges its analogue (see the provenance section) — but nobody should
   read "the residue is one base vanishing" as "AJC is one lemma from unconditional bounded
   vanishing at a curve".  The residue was the AJCR port named below — which has since landed, so
   every ★ and ★★ here now has an unconditional counterpart in `Ledger/FiberBound.lean`.
   - Over a curve of genus `0` (equivalently `h¹(𝒪_X) = 0` with the `Subsingleton` spelling),
     `D₀ = 0` works and the whole thing is unconditional — `subsingleton_of_deg_ge_of_zero`.
     Recorded as the cheapest *shape* of the input, not as an available instance: per the
     paragraph above, AJC does not prove `H¹(𝒪_C) = 0` for any proper `C`.
   - In general it is a port: AJCR's `RiemannRoch/FLVVanishing.lean:302`
     (`subsingleton_hModule_divisorSheaf_one_of_isFinite_toP1`) produces, for a finite dominant
     `π : Y ⟶ ℙ¹`, an `n₀` with `H¹(𝒪(D + n·F)) = 0` for `n ≥ n₀`.  Any one member of that
     tower is a `D₀`.  **The port cost recorded here was an overestimate, and the correction is
     the reusable lesson.**  This paragraph used to price the port at 59 closure modules with an
     unavoidable Picard-presentation dependency, "~2.5k lines and a Picard dependency".  That
     counted IMPORT LINES.  Counted instead by DECLARATION REFERENCE, the vanishing chain uses
     `picClass`, `CechPic`, `divisorClass` and `classDeg` exactly zero times: the fourteen
     `Picard/` modules enter only through AJCR `FiberTwist.lean`'s class-side material
     (`fiberDivisor`/`fiberTwist`/`classDeg_fiberTwist`), which the argument never mentions, and
     `AlgebraicJacobian.Challenge` arrives the same way through `ChiCurve ← Degree ← classDeg`.
     Dropping the class half and keeping the cover half, the port is
     `FiberChart` / `FiberDivisor` / `FiberLattice` / `DivisorSheafQcoh` / `FiberVanishing` plus
     the two `Qcoh` files — no Picard module, and the only thing that edge was carrying was the
     `coeffAt` calculus, now in `Ledger/FiberDivisor.lean`.  An import closure is an upper bound
     and can overstate tenfold when a file bundles a construction with its class-side theory.

     Note that AJCR has *already assembled* those two halves into the unconditional bound, in
     `RiemannRoch/UniformVanishing.lean:71` — it specialises the base to the fibre tower `n₁·F`
     of a finite dominant `π : Y ⟶ ℙ¹` and gets `∃ b, ∀ D, b ≤ deg D → H¹(𝒪(D)) = 0` outright.
     So the statement was never novel anywhere; it was the AJCR port above.  What *this* file
     contributes is the half that does **not** need `π` — everything from an arbitrary base
     vanishing onwards — and that is exactly the half `Ledger/FiberBound.lean` now feeds the
     ported `π`-side into.
2. **Extension-uniformity — UNTOUCHED, and nothing here bears on it.** Every statement in
   this file is over the one field `K`; `CurveDivisor.deg K` and `residueDeg K` are pinned to
   it.  A bound uniform over finite extensions `K'/K` would need the bound
   `deg D₀ + 1 − χ(𝒪_X)` to be controlled *along base change*, and `χ` is exactly what base
   change is not known to preserve here.  Do not read `exists_bound_subsingleton_hModule_one`
   as uniform: its `b` depends on `X`, `K` and `D₀`.
3. **Global generation — ALSO CLOSED HERE, on the same one base vanishing.**  An earlier
   version of this docstring said generation was untouched "because no evaluation map appears
   in this file".  That was a claim about the *file*, not about the *carrier*, and it was the
   same mistake as item 1's: the carrier does supply an evaluation map, namely the dévissage
   quotient `𝒪(D) ↠ sky_x J`.  Its `H⁰` is `H⁰(𝒪(D)) → H⁰(sky_x J) ≅ J ≅ κ(x)` — evaluation at
   `x` up to the identification — and the six-term slice makes its surjectivity follow from
   `H¹(𝒪(D − x)) = 0`, which above the degree bound is a theorem.  See
   `surjective_eval_of_deg_ge` and `generated_of_deg_ge`.

   Two things worth keeping straight.  First, this is generation *at a closed point*, and
   `generated_of_deg_ge` is the same statement quantified over points — that is what "generated
   by global sections" means here; no coherent-sheaf generation vocabulary is introduced.
   Second, it is **not** the dimension count: `h0_eq_h0_sub_point_add_residueDeg_of_deg_ge` is
   the numerical shadow of generation and is proved separately, and neither implies the other
   without the exactness input.  Note also that the slice route needs **no finiteness at all**,
   whereas `Adelic/GlobalGeneration.evalMap_surjective` needs two `Module.Finite` binders and
   two ledger hypotheses, because it proves surjectivity by comparing dimensions.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

section DegreeVanishing

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-! ## The section-to-effective bridge

A nonzero global section of `𝒪(A)` is a rational function whose poles are bounded by `A`
everywhere; as a unit of `K(X)` its principal divisor therefore satisfies `A + div g ≥ 0`.
This is the only place in the file where a section is unpacked. -/

/-- **A nonzero global section is an effectivity certificate** (the bridge): if `𝒪(A)` has a
nonzero global section then there is `g ∈ K(X)ˣ` with `0 ≤ A + div g`.

**Provenance: this proof is AJCR's, line for line.**  It is
`RiemannRoch/SectionBound.exists_effective_of_h0_pos`, whose body performs the same four steps
(nontriviality from `finrank_pos`, extract a nonzero element of `H⁰` through `linearEquiv₀`,
read it as a nonzero rational function via `divisorVal`, turn the pole bound into
`0 ≤ A + div g` pointwise through `ord_val_eq`).  The **only** change is the conclusion: AJCR
says "the class of `A` is realised by an effective divisor" using `CurveDivisor.picClass`, and
this states the underlying unit-and-inequality fact directly, so that it lands one import above
`DivisorSheaf`/`MulEquiv` and needs no Picard layer.  Do not read the restatement as new
mathematics; it is a carrier change. -/
theorem exists_unit_nonneg_of_h0_pos (A : X.CurveDivisor)
    (hA : 0 < Sheaf.h0 (X.divisorSheaf K A)) :
    ∃ g : X.functionFieldˣ,
      0 ≤ A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g := by
  haveI : Nontrivial (Sheaf.HModule (X.divisorSheaf K A) 0) :=
    Module.nontrivial_of_finrank_pos hA
  obtain ⟨t, ht⟩ := exists_ne (0 : Sheaf.HModule (X.divisorSheaf K A) 0)
  set s := (Sheaf.HModule.linearEquiv₀ (Opens.grothendieckTopology (X : TopCat))
    (isTerminalTop : IsTerminal (⊤ : X.Opens)) (X.divisorSheaf K A)) t with hs
  have hsne : s ≠ 0 := by
    rw [hs]; exact (LinearEquiv.map_ne_zero_iff _).mpr ht
  set g : X.functionField := divisorVal K s with hg
  have hgmem : g ∈ divisorSections K A ⊤ := divisorVal_mem K s
  have hgne : g ≠ 0 := by
    intro h
    exact hsne (divisorSection_ext K
      (show divisorVal K s = divisorVal K (0 : _) from by rw [← hg, h]; rfl))
  set u : X.functionFieldˣ := Units.mk0 g hgne with hu
  refine ⟨u, ?_⟩
  refine Finsupp.le_def.mpr (fun p => ?_)
  have htop : ((⊤ : X.Opens) : Set X).Nonempty := ⟨genericPoint X, trivial⟩
  have hb := (mem_divisorSections_of_nonempty K htop).mp hgmem p.1 p.2 trivial
  -- `ord_val_eq` reads the valuation of the unit `u` as the bound of `-div u`; the two sides
  -- of `hb` are then `ofAdd` of integer coefficients.
  have hval : Scheme.ord (X ↘ Spec (CommRingCat.of K)) p.2 g
      = divisorBound (- Scheme.divOf (X ↘ Spec (CommRingCat.of K)) u) p.2 := by
    have h := Scheme.ord_val_eq K u p.2
    rwa [show ((u : X.functionFieldˣ) : X.functionField) = g from rfl] at h
  rw [hval] at hb
  simp only [divisorBound, WithZero.coe_le_coe, Multiplicative.ofAdd_le] at hb
  change (0 : ℤ) ≤ (toFinsupp
    (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) u)) p
  have hadd : (toFinsupp
      (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) u)) p
      = (toFinsupp A) p
        + (toFinsupp (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) u)) p :=
    rfl
  -- `simp` has already stripped the `toFinsupp` wrapper off `hb`, leaving a raw application
  -- of the `CurveDivisor`s; restate it on the `Finsupp` side by `change` rather than `rw`.
  have hb' : - (toFinsupp (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) u)) p
      ≤ (toFinsupp A) p := hb
  rw [hadd]
  omega

/-! ## Translating the base vanishing along a linear equivalence

The peel needs a vanishing divisor **below** `D`.  A given `D₀` need not be below `D`, but its
linear-equivalence class is spread over the whole divisor group, and `H¹` is a class invariant
(`mulEquivDivisorSheaf` plus `Sheaf.h1_congr` / the `Subsingleton` transport).  The Riemann
inequality then supplies the translating function. -/

variable [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

omit [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **`H¹` vanishing is a linear-equivalence invariant**: `H¹(𝒪(A)) = 0` iff
`H¹(𝒪(A − div g)) = 0`, transported along `mulEquivDivisorSheaf`.  No finiteness: this is a
transport of a `Subsingleton` along an isomorphism, not a dimension count. -/
theorem subsingleton_hModule_one_sub_divOf (g : X.functionFieldˣ) (A : X.CurveDivisor)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K A) 1)) :
    Subsingleton (Sheaf.HModule
      (X.divisorSheaf K (A - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g)) 1) :=
  (Sheaf.HModule.mapEquiv (Scheme.mulEquivDivisorSheaf K g A) 1).toEquiv.symm.subsingleton

/-- **The cofinality theorem** (★): the hypothesis that `SectionDrop`'s
`exists_bound_of_cofinal_vanishing` takes as given, here **proved**.  From a single base
vanishing at `D₀`, every divisor `D` with `deg D ≥ deg D₀ + 1 − χ(𝒪_X)` dominates a divisor at
which `H¹` vanishes — namely the translate `D₀ − div g` for a `g` manufactured by the Riemann
inequality on `D − D₀`.

The bound is explicit and its shape is the content: one needs `deg (D − D₀) + χ(𝒪_X) ≥ 1` to
force a nonzero section of `𝒪(D − D₀)`, and that is exactly `deg D ≥ deg D₀ + 1 − χ(𝒪_X)`. -/
theorem exists_le_subsingleton_of_deg_ge {D₀ : X.CurveDivisor}
    (h₀ : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1))
    (D : X.CurveDivisor)
    (hD : CurveDivisor.deg K D₀ + 1 - Sheaf.chi (X.moduleKSheaf K)
      ≤ CurveDivisor.deg K D) :
    ∃ D₁ : X.CurveDivisor, D₁ ≤ D ∧
      Subsingleton (Sheaf.HModule (X.divisorSheaf K D₁) 1) := by
  -- `deg (D − D₀) + χ ≥ 1`, so the Riemann inequality gives a nonzero section of `𝒪(D − D₀)`.
  have hdegsub : CurveDivisor.deg K (D - D₀)
      = CurveDivisor.deg K D - CurveDivisor.deg K D₀ := by
    have h := CurveDivisor.deg_add K (D - D₀) D₀
    rw [sub_add_cancel] at h
    omega
  have hri := riemann_inequality K (D - D₀)
  have hpos : 0 < Sheaf.h0 (X.divisorSheaf K (D - D₀)) := by
    have : (1 : ℤ) ≤ (Sheaf.h0 (X.divisorSheaf K (D - D₀)) : ℤ) := by omega
    exact_mod_cast this
  obtain ⟨g, hg⟩ := exists_unit_nonneg_of_h0_pos K (D - D₀) hpos
  refine ⟨D₀ - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g, ?_,
    subsingleton_hModule_one_sub_divOf K g D₀ h₀⟩
  -- `0 ≤ (D − D₀) + div g` is literally `D₀ − div g ≤ D`, coefficientwise.
  refine Finsupp.le_def.mpr (fun p => ?_)
  have hgp : (0 : ℤ) ≤ (toFinsupp ((D - D₀)
      + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g)) p := Finsupp.le_def.mp hg p
  have h1 : (toFinsupp ((D - D₀)
      + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g)) p
      = ((toFinsupp D) p - (toFinsupp D₀) p)
        + (toFinsupp (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g)) p := rfl
  have h2 : (toFinsupp (D₀ - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g)) p
      = (toFinsupp D₀) p
        - (toFinsupp (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g)) p := rfl
  change (toFinsupp (D₀ - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g)) p
    ≤ (toFinsupp D) p
  rw [h1] at hgp
  rw [h2]
  omega

/-! ## Single-field bounded vanishing -/

/-- **Single-field bounded vanishing** (★★, cluster-P item 1): from one base vanishing at
`D₀`, `H¹(𝒪(D))` vanishes for **every** divisor of degree at least
`deg D₀ + 1 − χ(𝒪_X)`.

This is a **degree half-space**, not the order-cone of `SectionDrop`: no relation between `D`
and `D₀` in the divisor order is assumed, and none holds in general.  The bridge is that the
class of `D₀` has a representative below `D` once `D` has enough degree
(`exists_le_subsingleton_of_deg_ge`), and `H¹` vanishing is a class invariant
(`subsingleton_hModule_one_sub_divOf`).

It says nothing about uniformity over field extensions: `b`, `deg` and `χ` are all over the
single field `K`.  See item 2 of the module docstring. -/
theorem subsingleton_hModule_one_of_deg_ge {D₀ : X.CurveDivisor}
    (h₀ : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1))
    (D : X.CurveDivisor)
    (hD : CurveDivisor.deg K D₀ + 1 - Sheaf.chi (X.moduleKSheaf K)
      ≤ CurveDivisor.deg K D) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1) := by
  obtain ⟨D₁, hle, hvan⟩ := exists_le_subsingleton_of_deg_ge K h₀ D hD
  exact subsingleton_hModule_one_of_le K hle hvan

/-- The `h¹`-spelling of bounded vanishing.  Weaker than the `Subsingleton` form above
(`Module.finrank` reads `0` on an infinite-dimensional space), kept because downstream
numeric statements are phrased with `h¹`. -/
theorem h1_eq_zero_of_deg_ge {D₀ : X.CurveDivisor}
    (h₀ : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1))
    (D : X.CurveDivisor)
    (hD : CurveDivisor.deg K D₀ + 1 - Sheaf.chi (X.moduleKSheaf K)
      ≤ CurveDivisor.deg K D) :
    Sheaf.h1 (X.divisorSheaf K D) = 0 :=
  Sheaf.h1_eq_zero (subsingleton_hModule_one_of_deg_ge K h₀ D hD)

/-- **The existential form** that downstream consumers ask for: *there is* a degree bound past
which `H¹` vanishes identically.  Equivalent to
`subsingleton_hModule_one_of_deg_ge` with the explicit bound hidden; the explicit form is the
one to use when the constant matters. -/
theorem exists_bound_subsingleton_hModule_one {D₀ : X.CurveDivisor}
    (h₀ : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1)) :
    ∃ b : ℤ, ∀ D : X.CurveDivisor, b ≤ CurveDivisor.deg K D →
      Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1) :=
  ⟨CurveDivisor.deg K D₀ + 1 - Sheaf.chi (X.moduleKSheaf K),
    fun D hD => subsingleton_hModule_one_of_deg_ge K h₀ D hD⟩

/-! ## Exact Riemann–Roch above a degree bound -/

/-- **Exact Riemann–Roch on a degree half-space** (★★): `h⁰(𝒪(D)) = χ(𝒪_X) + deg D` for every
`D` of degree at least `deg D₀ + 1 − χ(𝒪_X)`.

Contrast `SectionDrop.h0_divisorSheaf_of_subsingleton_of_le`, whose hypothesis is `D₀ ≤ D` in
the divisor **order**.  That restriction is what this file removes: the conclusion now holds on
a half-space of the degree homomorphism, which is what "Riemann–Roch for large degree" means. -/
theorem h0_eq_of_deg_ge {D₀ : X.CurveDivisor}
    (h₀ : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1))
    (D : X.CurveDivisor)
    (hD : CurveDivisor.deg K D₀ + 1 - Sheaf.chi (X.moduleKSheaf K)
      ≤ CurveDivisor.deg K D) :
    (Sheaf.h0 (X.divisorSheaf K D) : ℤ) =
      Sheaf.chi (X.moduleKSheaf K) + CurveDivisor.deg K D := by
  have hvan := subsingleton_hModule_one_of_deg_ge K h₀ D hD
  have hchi := chi_divisorSheaf K D
  rw [Sheaf.chi_eq_h0 hvan] at hchi
  exact hchi

/-- **Riemann–Roch above a bound, existential form**: there is a degree bound past which
`h⁰(𝒪(D)) = χ(𝒪_X) + deg D` exactly. -/
theorem exists_bound_h0_eq {D₀ : X.CurveDivisor}
    (h₀ : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1)) :
    ∃ b : ℤ, ∀ D : X.CurveDivisor, b ≤ CurveDivisor.deg K D →
      (Sheaf.h0 (X.divisorSheaf K D) : ℤ) =
        Sheaf.chi (X.moduleKSheaf K) + CurveDivisor.deg K D :=
  ⟨CurveDivisor.deg K D₀ + 1 - Sheaf.chi (X.moduleKSheaf K),
    fun D hD => h0_eq_of_deg_ge K h₀ D hD⟩

/-- **The section drop is exact above the degree bound**: past the bound every closed point
contributes its full residue degree, `h⁰(𝒪(D)) = h⁰(𝒪(D − x)) + [κ(x) : K]`.  The hypothesis is
on `deg (D − x)`, so that the peel applies at both ends. -/
theorem h0_eq_h0_sub_point_add_residueDeg_of_deg_ge {D₀ : X.CurveDivisor}
    (h₀ : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1))
    {x : X} (hx : x ≠ genericPoint X) (D : X.CurveDivisor)
    (hD : CurveDivisor.deg K D₀ + 1 - Sheaf.chi (X.moduleKSheaf K)
      ≤ CurveDivisor.deg K (D - CurveDivisor.single hx 1)) :
    (Sheaf.h0 (X.divisorSheaf K D) : ℤ) =
      Sheaf.h0 (X.divisorSheaf K (D - CurveDivisor.single hx 1)) + X.residueDeg K x :=
  h0_eq_h0_sub_point_add_residueDeg_of_subsingleton K hx D
    (subsingleton_hModule_one_of_deg_ge K h₀ _ hD)

/-! ## The unconditional specialisation, and the honest shape of the residual input

Taking `D₀ = 0` makes the base vanishing `H¹(𝒪(0)) = 0`, i.e. `H¹(𝒪_X) = 0` up to the
identification `divisorSheafZeroIso`.  That holds exactly on the curves of genus zero, so the
specialisation below is *not* a general theorem — it is recorded to show precisely how small
the residual input is: **one** vanishing at **one** divisor. -/

/-- **The `D₀ = 0` specialisation**: if `H¹(𝒪_X) = 0` then `H¹(𝒪(D)) = 0` for every `D` of
degree at least `1 − χ(𝒪_X)`, with no other input.  On a genus-zero curve `χ(𝒪_X) = 1` and the
bound is `deg D ≥ 0`, the classical statement.

Note what this does and does not say: it is unconditional *given* `H¹(𝒪_X) = 0`, which is a
genus-zero hypothesis, not a fact about every curve.  For the general case use
`Ledger/FiberBound.exists_bound_subsingleton_hModule_one_curve`, which needs no vanishing
hypothesis at any genus. -/
theorem subsingleton_of_deg_ge_of_zero
    (h₀ : Subsingleton (Sheaf.HModule (X.divisorSheaf K (0 : X.CurveDivisor)) 1))
    (D : X.CurveDivisor)
    (hD : 1 - Sheaf.chi (X.moduleKSheaf K) ≤ CurveDivisor.deg K D) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1) := by
  refine subsingleton_hModule_one_of_deg_ge K h₀ D ?_
  rwa [CurveDivisor.deg_zero, zero_add]

/-- The same, from a vanishing stated on the **structure sheaf** rather than on `𝒪(0)`: the two
are identified by `divisorSheafZeroIso`, so this is the spelling a caller with
`Subsingleton (H¹(𝒪_X))` in hand can use directly. -/
theorem subsingleton_of_deg_ge_of_moduleKSheaf
    (h₀ : Subsingleton (Sheaf.HModule (X.moduleKSheaf K) 1))
    (D : X.CurveDivisor)
    (hD : 1 - Sheaf.chi (X.moduleKSheaf K) ≤ CurveDivisor.deg K D) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1) := by
  -- `divisorSheafZeroIso : 𝒪(0) ≅ 𝒪_X`, so the transport of the vanishing runs backwards
  -- along the induced equivalence on `H¹`.
  have hzero : Subsingleton (Sheaf.HModule (X.divisorSheaf K (0 : X.CurveDivisor)) 1) :=
    haveI := h₀
    (Sheaf.HModule.mapEquiv (Scheme.divisorSheafZeroIso K (X := X)) 1).toEquiv.subsingleton
  exact subsingleton_of_deg_ge_of_zero K hzero D hD

/-! ## Global generation: evaluation is surjective above the bound

Cluster-P item 3.  Read the module docstring's item 3 first, then this: the *original* version
of this file claimed generation was untouched here, on the ground that "no evaluation map
appears".  That was a statement about the file, not about the carrier, and the carrier does
supply one — the dévissage quotient map.

`H⁰(𝒪(D)) → H⁰(sky_x J)` is the third slot of the six-term slice, and `H⁰(sky_x J) ≅ J ≅ κ(x)`
by `skyModuleGammaEquiv` and `jumpEquivResidueField`.  So that map **is** evaluation at `x`, up
to the identification, and `ChiSlice.exact_map_g_delta` makes its surjectivity equivalent to the
vanishing of the connecting map into `H¹(𝒪(D − x))`.  One sufficient condition is therefore
`H¹(𝒪(D − x)) = 0` — which above the degree bound is a theorem, not a hypothesis.

This is genuinely *generation at a point*, and it is weaker than "𝒪(D) is generated by global
sections" only in that the latter is the statement for all `x` at once, which is the same
theorem quantified (`generated_of_deg_ge` below). -/

section GlobalGeneration

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **Evaluation at a closed point is surjective when `H¹` vanishes below**: the dévissage
quotient map `H⁰(𝒪(D)) → H⁰(sky_x J)` is onto as soon as `H¹(𝒪(D − x)) = 0`.

The proof is the slice, not a computation: exactness at `H⁰(X₃)` says the image of this map is
the kernel of the connecting `δ : H⁰(X₃) → H¹(X₁)`, and `X₁ = 𝒪(D − x)` has no `H¹`, so that
kernel is everything.  No finiteness is used — surjectivity is not a dimension count, which is
why this carries no `Module.Finite` binder (contrast `Adelic/GlobalGeneration.evalMap_surjective`,
which goes through equal finite dimensions and so needs two, plus two ledger hypotheses).  The
linter confirms it: three ambient binders are unused here and are omitted, `LocallyOfFiniteType`
among them. -/
theorem surjective_hModule_zero_devissageπ {x : X} (hx : x ≠ genericPoint X)
    (D : X.CurveDivisor)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K (D - CurveDivisor.single hx 1)) 1)) :
    Function.Surjective
      (Sheaf.HModule.map (devissageSES K hx D).g 0) := by
  intro y
  haveI hsub : Subsingleton (Sheaf.HModule (devissageSES K hx D).X₁ 1) := h
  refine (Sheaf.HModule.exact_map_g_delta (devissageSES_shortExact K hx D) rfl y).mp ?_
  exact Subsingleton.elim _ 0

/-- **Generation at a point above the degree bound** (★★, cluster-P item 3): past
`deg D₀ + 1 − χ(𝒪_X)` — with a degree of room for the point being peeled — evaluation
`H⁰(𝒪(D)) → H⁰(sky_x J) ≅ κ(x)` is surjective at **every** closed point `x`.

The hypothesis is stated on `deg (D − x)` rather than `deg D` because it is the vanishing at
`D − x`, not at `D`, that the slice consumes; the difference is exactly one residue degree. -/
theorem surjective_eval_of_deg_ge {D₀ : X.CurveDivisor}
    (h₀ : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1))
    {x : X} (hx : x ≠ genericPoint X) (D : X.CurveDivisor)
    (hD : CurveDivisor.deg K D₀ + 1 - Sheaf.chi (X.moduleKSheaf K)
      ≤ CurveDivisor.deg K (D - CurveDivisor.single hx 1)) :
    Function.Surjective (Sheaf.HModule.map (devissageSES K hx D).g 0) :=
  surjective_hModule_zero_devissageπ K hx D
    (subsingleton_hModule_one_of_deg_ge K h₀ _ hD)

/-- **Global generation above the bound, all points at once** (★★): there is a degree bound
past which `𝒪(D)` is generated at every closed point.  The bound absorbs the one residue
degree of slack by requiring it of `D − x` uniformly, which is what the explicit hypothesis
below spells out.

This is the honest form of "𝒪(D) is generated by its global sections for `deg D` large": a
statement about surjectivity of evaluation at each point, quantified over points — *not* the
dimension count `h⁰(𝒪(D)) = h⁰(𝒪(D − x)) + [κ(x) : K]`, which is its numerical shadow and which
`h0_eq_h0_sub_point_add_residueDeg_of_deg_ge` proves separately. -/
theorem generated_of_deg_ge {D₀ : X.CurveDivisor}
    (h₀ : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1))
    (D : X.CurveDivisor)
    (hD : ∀ {x : X} (hx : x ≠ genericPoint X),
      CurveDivisor.deg K D₀ + 1 - Sheaf.chi (X.moduleKSheaf K)
        ≤ CurveDivisor.deg K (D - CurveDivisor.single hx 1)) :
    ∀ {x : X} (hx : x ≠ genericPoint X),
      Function.Surjective (Sheaf.HModule.map (devissageSES K hx D).g 0) :=
  fun {_} hx => surjective_eval_of_deg_ge K h₀ hx D (hD hx)

end GlobalGeneration

/-! ### The `h¹ = 0` entry point

Every theorem above takes its base vanishing in the `Subsingleton` spelling, which is the
strong one: `Module.finrank` reads `0` on an infinite-dimensional space, so `h¹ = 0` alone is
strictly weaker and would make the hypotheses cheap for the wrong reason.  A caller holding
`h¹ = 0` *together with* finiteness of `H¹` can nevertheless enter, since over a field the two
spellings agree on finite-dimensional spaces.  This matters in practice because the numeric
form is what the genus computations produce (`ledgerGenus C = 0`), and finiteness of `H¹` is
exactly what `ChiCurve`/`Finiteness` discharge at a curve. -/

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)] in
/-- **`h¹ = 0` upgrades to the `Subsingleton` vanishing when `H¹` is finite.** The bridge from
the numeric spelling (what a genus computation gives) to the strong spelling (what the peel
consumes).  The `Module.Finite` hypothesis on `H¹(𝒪(D₀))` is not removable: without it
`h¹ = 0` is vacuous.

Note how little this needs — the linter found it, not me: **no** curve geometry at all beyond
what names `divisorSheaf`.  It is the general fact that over a field `finrank = 0` and
`Subsingleton` agree on a finite module, so the four omitted binders (properness,
quasi-compactness, and both structure-sheaf finiteness instances) play no part. -/
theorem subsingleton_of_h1_eq_zero {D₀ : X.CurveDivisor}
    [Module.Finite K (Sheaf.HModule (X.divisorSheaf K D₀) 1)]
    (h : Sheaf.h1 (X.divisorSheaf K D₀) = 0) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1) := by
  haveI : FiniteDimensional K (Sheaf.HModule (X.divisorSheaf K D₀) 1) := inferInstance
  exact subsingleton_iff_forall_eq 0 |>.mpr (finrank_zero_iff_forall_zero.mp h)

/-- **Bounded vanishing from the numeric base**: the headline with its base vanishing supplied
in the `h¹ = 0` spelling plus finiteness of `H¹(𝒪(D₀))`.  Convenience form of
`subsingleton_hModule_one_of_deg_ge`; the `Subsingleton` version remains the primitive. -/
theorem subsingleton_hModule_one_of_deg_ge_of_h1_eq_zero {D₀ : X.CurveDivisor}
    [Module.Finite K (Sheaf.HModule (X.divisorSheaf K D₀) 1)]
    (h₀ : Sheaf.h1 (X.divisorSheaf K D₀) = 0) (D : X.CurveDivisor)
    (hD : CurveDivisor.deg K D₀ + 1 - Sheaf.chi (X.moduleKSheaf K)
      ≤ CurveDivisor.deg K D) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1) :=
  subsingleton_hModule_one_of_deg_ge K (subsingleton_of_h1_eq_zero K h₀) D hD

/-- **Contrapositive, as a degree obstruction**: if `H¹(𝒪(D))` does *not* vanish while
`H¹(𝒪(D₀))` does, then `deg D < deg D₀ + 1 − χ(𝒪_X)`.  A non-vanishing `H¹` is therefore a
*bounded-degree* phenomenon — the numerical content of "vanishing is generic". -/
theorem deg_lt_of_not_subsingleton {D₀ : X.CurveDivisor}
    (h₀ : Subsingleton (Sheaf.HModule (X.divisorSheaf K D₀) 1))
    (D : X.CurveDivisor)
    (hD : ¬ Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1)) :
    CurveDivisor.deg K D < CurveDivisor.deg K D₀ + 1 - Sheaf.chi (X.moduleKSheaf K) := by
  by_contra hcon
  exact hD (subsingleton_hModule_one_of_deg_ge K h₀ D (by omega))

end DegreeVanishing

end AlgebraicGeometry
