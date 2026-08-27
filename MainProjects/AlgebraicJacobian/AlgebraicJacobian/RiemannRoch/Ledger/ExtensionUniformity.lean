/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.FiberBound
import AlgebraicJacobian.RiemannRoch.CurveBaseChange

/-!
# Extension-uniformity: the free half WITNESSED, and the open half reduced to one scalar

`Ledger/FiberBound.lean` closes cluster-P items 1 and 3 over a *single* field `k`, and its
closing section says extension-uniformity splits into a free half and an open half.  That
section states the free half as a property of three **morphism classes**
(`baseChange_binders_stable`: `IsProper`, `SmoothOfRelativeDimension 1` and
`GeometricallyIrreducible` are each stable under base change).  That is true, and it is not
the same statement as "the vanishing theorem re-fires at the base-changed curve": a class
being stable under base change says nothing until some object is exhibited carrying the
base-changed instances, in the spelling the consuming theorem actually elaborates against.

This file supplies the object.  `Scheme.baseChangeField C κ` (`RiemannRoch/CurveBaseChange.lean`)
is AJC's named base-changed curve `C_κ = C ×_{Spec k} Spec κ`, and it already carries
`IsProper`, `SmoothOfRelativeDimension 1` and `GeometricallyIntegral` as **named instances**.
One instance was missing from that stack — `GeometricallyIrreducible`, which is what the
`Ledger` curve statements bind — and `geometricallyIrreducible_hom_baseChangeField` below adds
it.  With it, every curve-level statement of `FiberBound` applies to `C_κ` **by instance
synthesis alone**, at base field `κ`, with no new mathematics and no hypothesis on `κ/k`: not
finiteness, not separability, not perfectness.

## What is proved here, and what is deliberately not

* `vanishing_baseChangeField` / `riemannRoch_baseChangeField` — the **free half, witnessed**:
  a threshold `b(κ)` exists at `C_κ` for every `κ`, and exact Riemann–Roch holds above it with
  the base-changed genus `genus C_κ`.  This is the honest content of "the theorem re-fires per
  field", now stated at an object rather than about a class.
* `UniformVanishing` — the **open half, named as a definition** so that consumers can quantify
  over it and so that its exact quantifier order is inspectable: `∃ b, ∀ κ, ∀ D on C_κ, …`.
  The `b` is chosen **before** `κ`.  This is *not* proved here and this file does not claim it.
* `uniformVanishing_of_uniform_base_of_genus_invariant` — the **reduction**: the open half
  follows from exactly **two** inputs, a uniform degree bound on a vanishing base divisor and
  base-field invariance of the genus.  Neither is proved here; both are named precisely.
  **Update:** the genus input is now proved in `Ledger/GenusFieldInvariance.lean`, so prefer
  `GenusFieldInvariance.uniformVanishing_of_uniformBaseDivisor`, which needs only the first.
* `exists_deg_ge` — **non-vacuity**: degrees are unbounded above given one closed point of
  positive residue degree, so a degree half-space is never empty and `UniformVanishing` is not
  trivially satisfiable by having no instances.  Proved.

## What the constant actually decomposes into (correcting my own earlier account)

`FiberBound`'s closing docstring located the obstruction in the constant: `b(κ)` is built from
`n₀(κ)`, a `Classical.choose` on a Noetherian stabilization re-run at each base field, and
nothing relates `n₀(κ)` to `n₀(k)`.  That describes the *proof*, not the *problem*.  The
threshold produced by `DegreeVanishing.exists_bound_subsingleton_hModule_one` is

`b = deg D₀ + 1 − χ(𝒪)`,

and that existential is **monotone in `b`** (a `D` of degree `≥ b'` has degree `≥ b` whenever
`b ≤ b'`).  So `n₀` itself never has to transport: it suffices to bound `b(κ)` above by
something independent of `κ`.  Since `χ(𝒪_{C_κ}) = 1 − genus C_κ` (`ChiCurve.chi_moduleKSheaf`
composed with `GenusBridge.ledgerGenus_eq_genus`, both at `C_κ` — this is checked, not assumed),

`b(κ) = deg_κ D₀(κ) + genus C_κ`,

which exposes **two** `κ`-dependencies, not one:

1. `genus C_κ` — a scalar, addressed by base-field invariance of the genus;
2. `deg_κ D₀(κ)` — the degree of the base divisor, where `D₀(κ) = n₀(κ) • F_κ`.  This is where
   the `Classical.choose` survives, and bounding it is *not* a corollary of (1).

**A retraction.**  An earlier version of this docstring said the threshold "can be taken to be
`2g − 1`", which would have collapsed (2) into (1) and made the genus identity the whole
residue.  That is standard curve theory but it is **not available here**: `deg D ≥ 2g − 1 ⟹
H¹ = 0` goes through Serre duality, and there is **no Serre duality, canonical divisor or
dualizing sheaf anywhere in this workspace** — searched across AJC, AJCR and mathlib, which
has no Serre duality for curves at all.  So the reduction below carries both hypotheses.  I
had published the one-input version on the team thread before checking it; this is the
corrected form.

## Where the two inputs stand (provenance, honestly)

**INPUT (1) IS NOW A THEOREM OF AJC — everything in the rest of this section is history.**
`Ledger/GenusFieldInvariance.genus_baseChangeField` proves `genus C_κ = genus C` for every field
extension `κ/k`, sorry-free and axiom-clean, so the reduction below can be called with only its
*first* antecedent: use `GenusFieldInvariance.uniformVanishing_of_uniformBaseDivisor`, which
carries `UniformBaseDivisor C d` and nothing else.

Read the paragraphs below as the record of what the cost estimate *was*, because one of them was
wrong in a way worth keeping visible: the carrier note called the AJC/AJCR object-level `rfl` the
live boundary.  It was not the obstacle.  What actually had to be built was (a) the cover-level
assembly — AJCR states its version over `AffineTwoCover`, which does not exist in AJC — and (b)
the right-exactness brick `quotRangeBaseChangeEquiv`, also absent here and rederived from
`lTensor_exact`.  The object `rfl` was true, and irrelevant.

**Input (1), genus invariance: proved sorry-free next door, on a different carrier.**
`AlgebraicJacobian/Cohomology/H1BaseFieldInvariance.lean` in
Algebraic-Jacobian-Challenge-Rebuild proves `finrank_h1_baseField` (the `κ`-dimension of
`H¹(C_κ, 𝒪)` equals the `k`-dimension of `H¹(C, 𝒪)`, arbitrary field extension) and deduces
`genus_baseField`.  Its engine is termwise base change of the two-term Čech complex of an
affine two-cover plus right-exactness of `⊗` — not semicontinuity, not Mumford II.5.

**The carrier question is settled, and favourably.**  AJCR states it at `baseChangeBundle C K`,
built from its own `overSpec`/`⊗` `Over`-tensor spelling, whereas AJC's `C_κ` is
`Over.mk (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k κ))))`.  Those agree by
`rfl` — **the whole bundled object, structure morphism included**, not merely the underlying
scheme.  AJCR's `⊗` is the monoidal product in `Over (Spec k)`, whose `tensorObj` *is* the
pullback and whose `snd` *is* `pullback.snd`, so the difference is notational indirection.

Verified at *this* project's spelling rather than taken on report, with a negative control: the
same `rfl` with the pullback arguments swapped fails on a type mismatch, so the check is not
proving whatever it is handed.  Two caveats survive, and neither is cosmetic:

* the verdict is defeq **at the object**.  A port that pushes it through a functor must re-run
  `rfl` there; a lane in this workspace shipped a false claim this week by carrying an
  object-level verdict across `Spec.map`.
* defeq of carriers is necessary, not sufficient.  The genus statements also bind AJCR's own
  curve-instance stack (`Curve.BaseChangeInstances`) and its two-cover `curveCover`, and whether
  *those* land on AJC's `CurveBaseChange` instances is a separate measurement, not settled here.

So the honest status of input (1) is: **reachable, cost not yet measured** — no longer "blocked on
a carrier mismatch", which is what I would have recorded had I stopped at the mismatch.  It stays
a hypothesis in the reduction below until the port is actually made, because an unmeasured port
is not an available theorem.

**The AJC-native route to input (1), measured.**  Because the carriers agree, there is a second
option besides porting AJCR's file: assemble the identity from bricks AJC already owns.  What is
present, checked at HEAD:

* a **cover on `C`**: `Adelic.LaurentChartData.pullbackSquare` (`Adelic/FinitenessP1.lean:439`)
  builds a `C.left.AffineCoverMVSquare` from the ℙ¹ chart data and any finite `π`, and
  `Ledger/MapToP1.exists_isFinite_isDominant_toP1` supplies the `π` at AJC's curve;
* a **cover on `C_κ`**: `Scheme.AffineCoverMVSquare.baseChangeField` (`CurveBaseChange.lean:340`)
  transports it, since the first projection `C_κ ⟶ C` is affine;
* the **genus read on that cover**: `AffineCoverMVSquare.h1_unit_baseChangeField_eq_genus`
  (`CohomologyKit.lean:582`) already says `h¹(𝒪_{C_κ})` on the base-changed cover *is*
  `genus C_κ`, and `h0_unit_baseChangeField_eq_one` gives `h⁰ = 1`.

So AJC has both sides of the comparison expressed on transported covers; what is **missing** is
the comparison itself — the termwise base-change equivalence `Γ(C, V) ⊗_k κ ≃ Γ(C_κ, V_κ)` on
chart sections, which is what AJCR's `relSectionsBaseChange` supplies and what makes `h¹` agree
rather than merely both being defined.  That equivalence is the actual deliverable, on either
route.  Note the shape of the two projects' cover carriers differs — AJCR uses `AffineTwoCover`,
AJC `AffineCoverMVSquare` (and `AffineTwoCover` does not occur anywhere in AJC) — so a port
crosses a second carrier boundary that the `rfl` above does *not* cover.

**Input (2), a uniform base-divisor degree bound: open for `genus C ≥ 1`; closed at genus 0, and
since `Ledger/P1Vanishing.lean` witnessed at `ℙ¹` rather than only implied.**
It asks for one `d` with a vanishing `D₀` of degree `≤ d` over *every* `κ`.  Nothing in AJC
bounds `n₀(κ)` uniformly, and `n₀` is a `Classical.choose` on Noetherian stabilization of the
fiber-lattice chain (`Ledger/FiberVanishing.lean`), re-run at each base field with no numeric
extraction — so the route "bound AJC's own `n₀` uniformly" is not available.

What *is* available, and is the genus-0 closure (producer in `Ledger/VanishingFieldDescent.lean`,
witness in `Ledger/P1Vanishing.lean` — see item 2 below on why both are needed to say "closed"):
that file bypasses `n₀` entirely.  Instead of transporting the *stabilization index*, it
transports the *vanishing statement*, using faithful flatness of `κ/k` on
`GenusFieldInvariance`'s `Ȟ¹` comparison.  The
witness divisor is then `0` at every `κ`, whose degree is `0` with no choice involved.  That
works exactly when `H¹(𝒪_C)` already vanishes, i.e. `genus C = 0`.

**The claim about AJCR that used to stand here is withdrawn** — see
`Ledger/GenusFieldInvariance.lean` §"What is NOT closed".  It said AJCR's analogue is a `Nat.find`
per field; in fact `WindowFieldTransport.deg_windowN` gives the degree over `K` as
`windowM_choice π hπ g * windowδ π` with **both factors computed at `k`**, so that constant does
move.  Whether AJCR has input (2), or material for it, is unmeasured here and must not be cited
as evidence that the input is hard.  The paragraph below is kept because it correctly describes
**AJC's own** `n₀`; its AJCR clause is the retracted part.  AJCR's `WindowFieldTransport.lean`
transports vanishing
*facts* one field at a time precisely because the constant does not move.

So `uniformVanishing_of_uniform_base_of_genus_invariant` **was** a conditional result with one
antecedent proved-elsewhere-modulo-a-carrier and one genuinely open.  It is now a conditional
result with **one** open antecedent: input (1) is discharged in
`Ledger/GenusFieldInvariance.lean`.  New consumers should call
`GenusFieldInvariance.uniformVanishing_of_uniformBaseDivisor` instead of this theorem; this one
stays because it is the honest statement of *which* two facts the implication rests on, and
because a caller who has a genus bound by some other route may still want it.

## The three cluster-P statements, kept apart (unchanged discipline)

1. **Single-field bounded vanishing** — closed at AJC's curve (`FiberBound`, three curve
   binders, nothing else).  This file changes nothing about it.
2. **Extension-uniformity** — free half now *witnessed* at `C_κ` (was: asserted of morphism
   classes); open half decomposed into a genus identity plus a uniform base-divisor degree bound.
   **The genus identity is now proved** (`Ledger/GenusFieldInvariance.lean`), so the open half is
   *exactly* the base-divisor bound — one input, not two.  Open in AJC for `genus C ≥ 1`.

   **Genus 0: the producer is in `Ledger/VanishingFieldDescent.lean` and its witness is in
   `Ledger/P1Vanishing.lean`.**  `H¹(𝒪)` vanishing is base-field invariant in *both* directions by
   faithfully flat descent of the `Ȟ¹` comparison, which produces `UniformBaseDivisor C 0` and
   hence `UniformVanishing C` whenever `H¹(𝒪_C)` vanishes.

   That producer stood for one round with **no curve satisfying its hypothesis** — a true
   implication with no instance, recorded as such in its own `§NON-VACUITY`.  Saying "genus 0 is
   closed" of that state was too strong, and it is corrected here rather than left standing: what
   was closed was the implication, not a case.  `Ledger/P1Vanishing.lean` now supplies the missing
   antecedent (`genus_p1Over_eq_zero`, from `Ȟ¹(𝒪) = 0` on the Laurent chart cover), so
   `uniformVanishing_p1Over` is extension-uniform bounded vanishing **at a curve this project
   has**, threshold `0`.

   That is the whole of what is closed: for `genus C ≥ 1` the hypothesis is false and the
   base-divisor bound is still a missing production from geometry.

   On AJCR: whether it has input (2) was measured this round and the answer is **effectively no,
   for AJC's purposes**.  `WindowFieldTransport.deg_windowN` does give a `κ`-independent degree
   (`windowM_choice π hπ g * windowδ π`, both factors at `k`) with `subsingleton_h1_windowN`
   giving the vanishing — so the *content* of a uniform base divisor exists there.  But it is
   uniform **by construction of the statement** (its `π` is bound at `P1 k`, pinning every
   constant to `k`) rather than by a theorem, it is stated on the `relCurve`/glued-datum carrier,
   and neither `UniformBaseDivisor` nor `UniformVanishing` occurs in AJCR at all.  The transport
   cost is an 88–139 file dependency cone plus two carrier boundaries with no bridge in either
   project (`AffineTwoCover`↔`AffineCoverMVSquare`, `relCurve`↔`baseChangeField`).  The earlier
   "`Nat.find` per field" claim stays withdrawn; the correct reading is that the constant does
   move and the obstacle is carriers, not mathematics.
3. **Global generation** — closed at AJC's curve by the dévissage route
   (`FiberBound.exists_bound_generated_of_isFinite_toP1`), independent of (1).  This file does
   not touch it; in particular nothing here makes generation uniform over extensions either.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))

/-! ## §1. The missing instance

`RiemannRoch/CurveBaseChange.lean` gives `C_κ` the named instances `IsProper`,
`SmoothOfRelativeDimension 1` and `GeometricallyIntegral`.  The `Ledger` curve statements bind
`GeometricallyIrreducible`, which is the *irreducibility* half of geometric integrality and is
not recovered from it by synthesis.  Mathlib has the stability instance; this names it on the
`baseChangeField` spelling, exactly as its three siblings do. -/

/-- **Geometric irreducibility is stable under the field base change.**  The instance that was
missing from the `CurveBaseChange` stack: with it, every curve-level statement of
`Ledger/FiberBound.lean` applies to `C_κ` by synthesis, with no hypothesis on `κ/k`.

Companion of `Scheme.geometricallyIntegral_hom_baseChangeField`, which is the *integral*
form; the `Ledger` layer binds the irreducible one. -/
instance Scheme.geometricallyIrreducible_hom_baseChangeField (κ : Type u) [Field κ]
    [Algebra k κ] [GeometricallyIrreducible C.hom] :
    GeometricallyIrreducible (Scheme.baseChangeField C κ).hom :=
  MorphismProperty.pullback_snd _ _ ‹GeometricallyIrreducible C.hom›

/-! ## §2. The free half, witnessed at `C_κ`

Each theorem below is the corresponding `FiberBound` curve statement applied to
`Scheme.baseChangeField C κ`.  The proofs are one term each: that is the point — nothing has to
be redone at `C_κ`, and the reason nothing has to be redone is §1, not a stability claim about
morphism classes.

The `letI`/`haveI` prologue is the standing `ChiCurve` idiom (see `FiberBound.lean` §Curve): it
makes the ambient structure morphism of `C_κ` definitionally its bundle map, so the smoothness
binder that `divisorSheaf` needs transfers by `inferInstanceAs`. -/

section FreeHalf

variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]

/-- **Bounded `H¹` vanishing at `C_κ`, for every field extension `κ/k`** (the free half of
extension-uniformity, witnessed): a degree threshold exists over `κ`.

The quantifier order is the whole content, and it is the *weak* one: `κ` comes first, then `b`.
Read `UniformVanishing` below for the strong order, which this does **not** give. -/
theorem vanishing_baseChangeField (κ : Type u) [Field κ] [Algebra k κ] :
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    ∃ b : ℤ, ∀ D : (Scheme.baseChangeField C κ).left.CurveDivisor,
      b ≤ CurveDivisor.deg κ D →
      Subsingleton (Sheaf.HModule ((Scheme.baseChangeField C κ).left.divisorSheaf κ D) 1) :=
  exists_bound_subsingleton_hModule_one_curve (Scheme.baseChangeField C κ)

/-- **Exact Riemann–Roch at `C_κ`, for every field extension `κ/k`**:
`h⁰(𝒪(D)) = 1 − genus C_κ + deg_κ D` above a threshold over `κ`.

Note the genus on the right is `genus C_κ`, taken over `κ`, **not** `genus C`.  Replacing it by
`genus C` is exactly the scalar identity §3 isolates, and it is not available here. -/
theorem riemannRoch_baseChangeField (κ : Type u) [Field κ] [Algebra k κ] :
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    ∃ b : ℤ, ∀ D : (Scheme.baseChangeField C κ).left.CurveDivisor,
      b ≤ CurveDivisor.deg κ D →
      (Sheaf.h0 ((Scheme.baseChangeField C κ).left.divisorSheaf κ D) : ℤ)
        = 1 - genus (Scheme.baseChangeField C κ) + CurveDivisor.deg κ D :=
  exists_bound_h0_eq_genus_curve (Scheme.baseChangeField C κ)

/-! ### The χ of `C_κ` is `1 − genus C_κ`

The step that makes the decomposition of `b(κ)` in the module docstring a computation rather
than an estimate.  It is `ChiCurve.chi_moduleKSheaf` at `C_κ` with the genus name corrected by
`GenusBridge.ledgerGenus_eq_genus`; both fire at `C_κ` only because of §1. -/

/-- **`χ(𝒪_{C_κ}) = 1 − genus C_κ`.**  Isolated because it is what pins the `κ`-dependence of
the vanishing threshold to the genus *and nothing else on the `χ` side*: the residual
`κ`-dependence of `b(κ)` sits entirely in `deg_κ D₀(κ)`. -/
theorem chi_moduleKSheaf_baseChangeField (κ : Type u) [Field κ] [Algebra k κ] :
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    Sheaf.chi ((Scheme.baseChangeField C κ).left.moduleKSheaf κ)
      = 1 - (genus (Scheme.baseChangeField C κ) : ℤ) := by
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  rw [chi_moduleKSheaf (Scheme.baseChangeField C κ),
    ledgerGenus_eq_genus (Scheme.baseChangeField C κ)]

end FreeHalf

/-! ## §3. The open half: named, and reduced to two explicit inputs

`UniformVanishing` states the strong quantifier order — `b` before `κ` — as a definition, so
that a consumer can hypothesise it and so that the order is inspectable rather than buried in a
docstring.  It is **not proved**.

`uniformVanishing_of_uniform_base_of_genus_invariant` reduces it to the two inputs the module
docstring names.  The reduction itself is unconditional: no vanishing hypothesis, no finiteness
supplied by the caller, and no appeal to Serre duality (which this workspace does not have). -/

section OpenHalf

variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]

/-- **Extension-uniform bounded vanishing**, the statement.  One threshold `b`, chosen before
any field, serving every finite or infinite extension `κ/k` simultaneously.

Contrast `vanishing_baseChangeField`, which is the same body with the quantifiers swapped:
there `κ` is fixed first and `b` may depend on it.  That one is a theorem; this one is open. -/
def UniformVanishing : Prop :=
  ∃ b : ℤ, ∀ (κ : Type u) [Field κ] [Algebra k κ],
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    ∀ D : (Scheme.baseChangeField C κ).left.CurveDivisor,
      b ≤ CurveDivisor.deg κ D →
      Subsingleton (Sheaf.HModule ((Scheme.baseChangeField C κ).left.divisorSheaf κ D) 1)

/-- **A uniform base-divisor datum**: one degree bound `d` such that over *every* extension
`κ/k` some divisor of degree `≤ d` already has vanishing `H¹`.

This is input (2) of the reduction, and it is the genuinely open one.  Over a single `κ`,
`FiberBound.exists_base_subsingleton_of_isFinite_toP1` supplies such a `D₀` — namely `n₀ • F` —
but with no control of `deg_κ D₀` as `κ` varies, because `n₀(κ)` is chosen by a Noetherian
stabilization re-run at each base field.

**This paragraph's diagnosis is the correct one, and it is now witnessed rather than described**
(2026-07-29, lane `ajc-p2`).
`Ledger/BaseDivisorEveryField.exists_base_subsingleton_baseChangeField`
states exactly the "over a single `κ`" half *as a theorem quantified over every* `κ`, on the three
curve binders and with no genus hypothesis — so of this definition's two clauses only the degree
inequality is open.  Worth noting because the downstream index for this gap
(`GenusFieldInvariance.lean` §Reduction) had priced it as a missing production from geometry
confined to `genus C = 0`, which is a different and stricter claim than what this docstring says;
that paragraph now carries a correction. -/
def UniformBaseDivisor (d : ℤ) : Prop :=
  ∀ (κ : Type u) [Field κ] [Algebra k κ],
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    ∃ D₀ : (Scheme.baseChangeField C κ).left.CurveDivisor,
      Subsingleton (Sheaf.HModule ((Scheme.baseChangeField C κ).left.divisorSheaf κ D₀) 1)
        ∧ CurveDivisor.deg κ D₀ ≤ d

/-- **The reduction** (★): extension-uniform vanishing follows from a uniform base-divisor
degree bound together with base-field invariance of the genus, and the uniform threshold is
then simply `d + g`.

Both hypotheses are needed and neither implies the other; see the module docstring for where
each stands.  The proof is the monotonicity observation and nothing more: the explicit bound of
`DegreeVanishing.subsingleton_hModule_one_of_deg_ge` at `C_κ` is
`deg_κ D₀ + 1 − χ(𝒪_{C_κ}) = deg_κ D₀ + genus C_κ ≤ d + g`, so a `D` of degree `≥ d + g`
clears it. -/
theorem uniformVanishing_of_uniform_base_of_genus_invariant {d : ℤ} {g : ℕ}
    (hbase : UniformBaseDivisor C d)
    (hgenus : ∀ (κ : Type u) [Field κ] [Algebra k κ],
      genus (Scheme.baseChangeField C κ) = g) :
    UniformVanishing C := by
  refine ⟨d + (g : ℤ), fun κ _ _ => ?_⟩
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
  intro D hD
  obtain ⟨D₀, hvan, hdeg⟩ := hbase κ
  have hchi : Sheaf.chi ((Scheme.baseChangeField C κ).left.moduleKSheaf κ) = 1 - (g : ℤ) := by
    rw [chi_moduleKSheaf_baseChangeField C κ, hgenus κ]
  refine subsingleton_hModule_one_of_deg_ge κ hvan D ?_
  rw [hchi]
  omega

/-! ### Non-vacuity: the degree half-space is never empty

A `∀ D, b ≤ deg D → …` statement is worth nothing if no divisor ever reaches degree `b`; it would
then be true for large `b` by having no instances, and `UniformVanishing` would be trivially
satisfiable.  This rules that out: one closed point of positive residue degree makes `deg`
unbounded above, so every degree half-space contains divisors.

The hypothesis is the honest one — `residueDeg` positivity at a single point — rather than a
claim that AJC witnesses it at the challenge curve, which is a separate question and is not
asserted here. -/

/-- **Degrees are unbounded above**, given one closed point of positive residue degree: for every
`b` there is a divisor of degree at least `b`, namely a large multiple of that point
(`deg (n • x) = n · [κ(x) : K]`).

This is what makes the bounded-vanishing statements of this file and of `DegreeVanishing`
non-vacuous rather than true-by-emptiness. -/
theorem exists_deg_ge {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] [IsIntegral X] {x : X} (hx : x ≠ genericPoint X)
    (hpos : 0 < X.residueDeg K x) (b : ℤ) :
    ∃ D : X.CurveDivisor, b ≤ CurveDivisor.deg K D := by
  refine ⟨CurveDivisor.single hx (max b 0), ?_⟩
  rw [Scheme.CurveDivisor.deg_single' K hx]
  have h1 : (1 : ℤ) ≤ (X.residueDeg K x : ℤ) := by exact_mod_cast hpos
  have h0 : (0 : ℤ) ≤ max b 0 := le_max_right _ _
  calc b ≤ max b 0 := le_max_left _ _
    _ = max b 0 * 1 := by ring
    _ ≤ max b 0 * (X.residueDeg K x : ℤ) := mul_le_mul_of_nonneg_left h1 h0

omit [IsProper C.hom] in
/-- The uniform statement is **strictly stronger** than the per-field one, in the only sense
that can be stated without proving either: it implies the per-field conclusion at every `κ`.
Recorded so that a consumer cannot mistake `vanishing_baseChangeField` for it.

The `omit [IsProper C.hom]` is informative rather than cosmetic: the implication is pure
quantifier weakening — instantiate the single `b` at each `κ` — so it needs no properness, and
the linter caught that.  It confirms the two statements differ *only* in quantifier order, with
no geometry in between. -/
theorem vanishing_baseChangeField_of_uniformVanishing (h : UniformVanishing C)
    (κ : Type u) [Field κ] [Algebra k κ] :
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    haveI : SmoothOfRelativeDimension 1
        ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
    ∃ b : ℤ, ∀ D : (Scheme.baseChangeField C κ).left.CurveDivisor,
      b ≤ CurveDivisor.deg κ D →
      Subsingleton (Sheaf.HModule ((Scheme.baseChangeField C κ).left.divisorSheaf κ D) 1) := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, hb κ⟩

end OpenHalf

end AlgebraicGeometry
