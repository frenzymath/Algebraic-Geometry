/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.GenusFieldInvariance
import AlgebraicJacobian.RiemannRoch.Ledger.GenusBridge

/-!
# `H¹(𝒪)` vanishing is a base-field-invariant property, and the first producer for
`UniformBaseDivisor`

`Ledger/GenusFieldInvariance.lean` closed **input (1)** of the extension-uniformity reduction
(the genus is base-field invariant) and left **input (2)** — `UniformBaseDivisor C d` — as the
single open antecedent.  Its closing docstring measured the *shape* of that gap with the
producer/consumer test and recorded the verdict: `UniformBaseDivisor` is a `def` with five
consumers and **no producer anywhere in AJC**.

This file supplies a producer.  It is a genuine one — `uniformBaseDivisor_zero_of_subsingleton`
below concludes `UniformBaseDivisor C 0` from a hypothesis about `C` alone, with no `κ` in it —
and it is **narrow**: its hypothesis is `Subsingleton (H¹(𝒪_C))`, which for AJC's curve is
equivalent to `genus C = 0` (`subsingleton_hModule_one_iff_genus_eq_zero`, a theorem of this file
— it was prose in an earlier version, and a review pointed out that every scope claim below rests
on it).  Read the scope section before citing it, because the distance between "a
producer exists" and "the input is discharged" is exactly where this cluster has gone wrong
before.

## The mathematical content: faithfully flat descent, in both directions

The engine is one observation the previous round did not use.  `GenusFieldInvariance`'s
comparison `h1CokₗBaseChangeField` is a `κ`-linear equivalence

`κ ⊗[k] Ȟ¹(S, 𝒪_C) ≃ₗ[κ] Ȟ¹(S_κ, 𝒪_{C_κ})`,

and a field extension `κ/k` is **faithfully flat** (`κ` is a nontrivial free `k`-module, so
mathlib's `Module.FaithfullyFlat.instOfNontrivialOfFree` applies — checked, it is not a direct
instance and needs that route).  Faithful flatness makes `κ ⊗[k] −` reflect *and* preserve
triviality (`Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right`), so the comparison
upgrades from an isomorphism of modules to an **equivalence of vanishing statements**:

`Subsingleton (H¹(𝒪_C))  ↔  Subsingleton (H¹(𝒪_{C_κ}))`.

Both directions are new here.  The previous round only ever used the comparison for its
`finrank`, which gives the genus identity but *not* the `Subsingleton` statement: `finrank`
reads `0` on an infinite-dimensional space, so a dimension equality cannot by itself decide
vanishing (this is the standing `Subsingleton`-vs-`finrank` distinction of
`Ledger/DegreeVanishing.h1_eq_zero_of_deg_ge`, and it is why the ascent below is not a
corollary of `genus_baseChangeField`).

The descent direction (`←`) is the one with no analogue anywhere in the workspace: it says a
vanishing established over *any* single extension — however large, e.g. `k̄` — descends to `k`.

## What is proved, and what it does and does not give

* `Scheme.subsingleton_h1Cokₗ_unit_baseChangeField_iff` — the equivalence above, on the Čech
  carrier.  No hypothesis on `κ/k` (not finiteness, separability, perfectness or algebraic
  closedness) and, measured rather than claimed, **no curve hypothesis at all**.
* `Scheme.subsingleton_hModule_one_moduleKSheaf_baseChangeField_iff` — the same on the
  `Sheaf.HModule` carrier that the `Ledger` divisor statements bind, across the `Ext` universe
  annotation hop of `Ledger/GenusBridge.lean`.
* `subsingleton_hModule_one_baseChangeField_iff_curve` — the same with the cover discharged, so it
  carries the three curve binders and nothing else.
* `subsingleton_hModule_one_iff_genus_eq_zero` — the scope translation, as a **theorem**:
  `Subsingleton (H¹(𝒪_C)) ↔ genus C = 0`.
* `uniformBaseDivisor_zero_of_subsingleton` — **the producer**: `UniformBaseDivisor C 0` from
  `Subsingleton (H¹(𝒪_C))`.  The witness at each `κ` is the zero divisor: `deg_κ 0 = 0 ≤ 0`, and
  its `H¹` vanishes by the ascent composed with `divisorSheafZeroIso`.
* `uniformVanishing_of_subsingleton_h1` — chaining it through
  `GenusFieldInvariance.uniformVanishing_of_uniformBaseDivisor_curve`: **`UniformVanishing C` is
  a theorem when `H¹(𝒪_C)` vanishes.**  This is the first *producer* of `UniformVanishing` in AJC
  — previously the type had none, only the reduction.  It is an **implication, not an
  unconditional instance**.  When this was written AJC exhibited no curve satisfying its
  hypothesis; `Ledger/P1Vanishing.lean` now does (`uniformVanishing_p1Over`, at `ℙ¹`).  It is
  still an implication, not an unconditional instance — the hypothesis is real and false for
  `genus C ≥ 1`.  See §NON-VACUITY.
* `uniformBaseDivisor_zero_of_genus_eq_zero`, `uniformVanishing_of_genus_eq_zero` — the same two
  with the hypothesis in the `genus C = 0` form a consumer meets.

## SCOPE: what this does NOT do, stated precisely

The three cluster-P statements stay apart, and so do the three things this file could be
mistaken for.

1. **It does not close input (2) in general.**  `UniformBaseDivisor C d` for `d` large is what a
   positive-genus curve needs, and this file produces only the `d = 0` case under a hypothesis
   equivalent to `genus C = 0` (`subsingleton_hModule_one_iff_genus_eq_zero`).  For `genus C ≥ 1`
   that hypothesis is therefore **false** — by the theorem, not by the docstring — and the
   producer says nothing.  So the gap named by the previous round is **narrowed, not closed**:
   it now has a producer with a restrictive hypothesis rather than no producer at all.
2. **It is not extension-uniformity for positive genus.**  `uniformVanishing_of_subsingleton_h1`
   is `UniformVanishing C` under a genus-0 hypothesis.  The general statement remains open, and
   its residue is still exactly `UniformBaseDivisor C d` for a `d` that the geometry has to
   produce — the "missing production from geometry" verdict is unchanged in the case that
   matters.
3. **It says nothing about global generation.**  Cluster-P item 3 is a single-field statement
   (`FiberBound.exists_bound_generated_of_isFinite_toP1`) and nothing here makes it uniform over
   extensions.  The descent equivalence is about `H¹` of `𝒪` only; it is not about `H⁰`, not
   about a general divisor sheaf, and not about generation at a point.

## NON-VACUITY IS NOT ESTABLISHED HERE, and that is a real gap, not a formality

`Ledger/NonVacuity.lean` exists because this workspace has twice shipped results whose binders
turned out to be unsatisfiable at a curve, so the question "does any object satisfy the
hypothesis?" is asked in Lean here rather than assumed.  Applying that test to §3:
`Adelic.p1Over k` satisfies the three curve binders (that *is* proved, in `NonVacuity.lean`), so
the producer's *ambient* hypotheses are inhabited.  Its *own* hypothesis is not discharged
anywhere.

**SUPERSEDED — the gap this section named is now closed by `Ledger/P1Vanishing.lean`.**  The
paragraphs below describe the state as of the round that wrote them and are kept because the
distinction they draw (a producer versus a witnessed case) is the one that mattered; the *absence*
they record is no longer the state.  `P1Vanishing.subsingleton_hModule_one_p1Over` and
`genus_p1Over_eq_zero` supply exactly the two statements said to be missing, so
`uniformVanishing_of_subsingleton_h1` below now HAS an exhibited instance
(`P1Vanishing.uniformVanishing_p1Over`).  Read on for the original scoping, not for current
status.

*As of the round that wrote this section:* **searched, and absent: AJC has no
`Subsingleton (H¹(𝒪_{ℙ¹}))` and no `genus (p1Over k) = 0`.**
Checked semantically as well as by name (workspace index and `exact?` on the goal), because this
lane has shipped absence claims that only surveyed part of the project.  So `genus C = 0` was a
hypothesis AJC could *state* at a concrete curve but not yet *verify* at one, and consequently:

* `uniformVanishing_of_subsingleton_h1` was **not known to be non-vacuous**: a true implication
  with no exhibited instance.  The honest reading of "the first `UniformVanishing` instance in
  AJC" was *the first producer of that type* — not the first curve for which extension-uniform
  vanishing is known.  **`Ledger/P1Vanishing.lean` closed this**: `uniformVanishing_p1Over` is
  the first witnessed curve, so the two readings now both hold.
* the missing brick was named as small: `h¹(𝒪_{ℙ¹}) = 0`, which on the two-chart Laurent cover is
  the statement that the Čech cokernel of `k[t] × k[t⁻¹] → k[t, t⁻¹]` vanishes.
  `Adelic.LaurentChartData` supplies the cover.  **Landed** as
  `P1Vanishing.LaurentChartData.subsingleton_h1Cok`, and it needed no new `LaurentChartData` field:
  the overlap span `I-0746` priced as a structural obstacle is derivable from the fields already
  present (`P1Vanishing.LaurentChartData.span_ladder_overlap`).

Recording this rather than leaving it implicit, because "produces `UniformBaseDivisor` from a
hypothesis" and "produces it at a curve this project has" are different claims, and a reader who
conflated them would take the genus-0 case as settled when only the implication is.

One further limit worth naming because it bounds the method rather than the statement: the
descent equivalence is proved for the **unit** module.  `h1CokₗBaseChangeField` is stated at
`SheafOfModules.unit`, so the argument does not transport a vanishing for `𝒪(D)` with `D ≠ 0`.
That is the reason the producer's `d` is `0` and not something larger: it is not that a larger
`d` was hard to reach from here, but that there is no divisor-level base-change comparison in
AJC to reach it with.  A general-module `h1CokₗBaseChangeField` is the brick that would move
this, and it does not exist in AJC (AJCR has one — `datum_subsingleton_h1_baseChange`, arbitrary
datum and arbitrary ring map — but on its glued-datum carrier, behind an 88-file cone and the
unbridged `AffineTwoCover`/`AffineCoverMVSquare` and `relCurve`/`baseChangeField` boundaries;
measured this round, not portable).

## Provenance

**Rederived in AJC's abstractions; not a port.**  The faithful-flatness step is mathlib
(`Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right` plus the `instOfNontrivialOfFree`
route to the instance), applied to AJC's own `h1CokₗBaseChangeField`.  AJCR does not contain
this statement: it has no `UniformBaseDivisor`, no `UniformVanishing`, and its vanishing
transport (`WindowFieldTransport.subsingleton_h1_windowN`) goes the *other* way — `k`-side
hypothesis to `K`-side conclusion for a specific window divisor — and never descends.  The
universe hop between the two `H¹` carriers (`Sheaf.HModule` at `u+1`, `Scheme.HModule` at `u+2`)
is `Ledger/GenusBridge`'s `Abelian.Ext.chgUnivLinearEquiv`, reused rather than redone.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct

namespace AlgebraicGeometry

namespace Scheme

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable (κ : Type u) [Field κ] [Algebra k κ]

/-! ## §1. A field extension is faithfully flat

Not an instance in mathlib on the nose: `Module.FaithfullyFlat k κ` does not synthesise from
`[Field k] [Field κ] [Algebra k κ]` (checked — it fails), because it goes through
`Module.Free k κ`, which needs the vector-space basis instance.  Named here so the two descent
lemmas below can `letI` it rather than each rediscovering the route. -/

/-- **A field extension is faithfully flat.**  `κ` is a nontrivial free `k`-module, so
`Module.FaithfullyFlat.instOfNontrivialOfFree` applies.

Stated as a `lemma` and used via `letI` rather than declared an `instance`: it is mathlib's fact
about mathlib's classes, and AJC should not be the project that globally instances it. -/
lemma faithfullyFlat_of_field_extension : Module.FaithfullyFlat k κ :=
  Module.FaithfullyFlat.instOfNontrivialOfFree k κ

/-! ## §2. Vanishing of `Ȟ¹(𝒪)` is invariant under base field extension

The upgrade of `GenusFieldInvariance.h1CokₗBaseChangeField` from an isomorphism to an
equivalence of vanishing statements.  Both directions come from the same faithful-flatness
iff, read the two ways. -/

/-- **`Ȟ¹(𝒪)` vanishes at `C_κ` iff it vanishes at `C`** (★★), on a 2-affine cover, for every
field extension `κ/k`.

The `→` direction is **descent**: a vanishing established over any single extension, however
large, descends to the base field.  The `←` direction is **ascent**.  Neither is a corollary of
the genus identity `genus C_κ = genus C`: that is an identity of `finrank`s, and `finrank` reads
`0` on an infinite-dimensional space, so it cannot decide `Subsingleton` in either direction.

No hypothesis on `κ/k` and none on `C` beyond carrying the cover — in particular no properness,
no smoothness, and no finiteness of the cohomology, since the faithful-flatness step needs none
of them. -/
theorem subsingleton_h1Cokₗ_unit_baseChangeField_iff (S : C.left.AffineCoverMVSquare) :
    Subsingleton ((S.baseChangeField κ).H1Cokₗ (baseChangeField C κ)
        (SheafOfModules.unit (baseChangeField C κ).left.ringCatSheaf)) ↔
      Subsingleton (S.H1Cokₗ C (SheafOfModules.unit C.left.ringCatSheaf)) := by
  letI : Module.FaithfullyFlat k κ := faithfullyFlat_of_field_extension κ
  rw [← (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k κ
    (N := S.H1Cokₗ C (SheafOfModules.unit C.left.ringCatSheaf)))]
  exact (Scheme.h1CokₗBaseChangeField κ S).toEquiv.subsingleton_congr.symm

/-- **`H¹(𝒪)` vanishes at `C_κ` iff it vanishes at `C`**, on the `Sheaf.HModule` carrier that
the `Ledger` divisor statements bind.

`subsingleton_h1Cokₗ_unit_baseChangeField_iff` transported across two bridges AJC already owns:
`hModuleOneEquivH1Cokₗ_unit` (gate-free, every cover, every field) and the universe annotation
hop `Abelian.Ext.chgUnivLinearEquiv` of `Ledger/GenusBridge.lean`. -/
theorem subsingleton_hModule_one_moduleKSheaf_baseChangeField_iff
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    (S : C.left.AffineCoverMVSquare) :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    letI : (baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (baseChangeField C κ).hom
    Subsingleton (Sheaf.HModule ((baseChangeField C κ).left.moduleKSheaf κ) 1) ↔
      Subsingleton (Sheaf.HModule (C.left.moduleKSheaf k) 1) := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  letI : (baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (baseChangeField C κ).hom
  calc Subsingleton (Sheaf.HModule ((baseChangeField C κ).left.moduleKSheaf κ) 1)
      ↔ Subsingleton (Scheme.HModule κ (Scheme.toModuleKSheaf (baseChangeField C κ)) 1) :=
        (Abelian.Ext.chgUnivLinearEquiv (R := κ)).toEquiv.subsingleton_congr
    _ ↔ Subsingleton ((S.baseChangeField κ).H1Cokₗ (baseChangeField C κ)
          (SheafOfModules.unit (baseChangeField C κ).left.ringCatSheaf)) :=
        ((S.baseChangeField κ).hModuleOneEquivH1Cokₗ_unit
          (baseChangeField C κ)).toEquiv.subsingleton_congr
    _ ↔ Subsingleton (S.H1Cokₗ C (SheafOfModules.unit C.left.ringCatSheaf)) :=
        subsingleton_h1Cokₗ_unit_baseChangeField_iff κ S
    _ ↔ Subsingleton (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
        ((Abelian.Ext.chgUnivLinearEquiv (R := k)).toEquiv.subsingleton_congr.trans
          (S.hModuleOneEquivH1Cokₗ_unit C).toEquiv.subsingleton_congr).symm

end Scheme

/-! ## §3. The producer for `UniformBaseDivisor`, and the first `UniformVanishing` instance

§2 with the cover discharged (`GenusFieldInvariance.nonempty_affineCoverMVSquare_of_curve`) and
composed with `divisorSheafZeroIso` to land on the carrier `UniformBaseDivisor` binds.

Read §"SCOPE" of the module docstring on what the hypothesis costs: `Subsingleton (H¹(𝒪_C))` is
equivalent to `genus C = 0` (`subsingleton_hModule_one_iff_genus_eq_zero`, below), so these are
genus-0 statements. -/

section Producer

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyIntegral C.hom]

/-- **`H¹(𝒪)` vanishing is base-field invariant, cover discharged** (★★): on the three curve
binders and nothing else, `H¹(𝒪_{C_κ})` vanishes iff `H¹(𝒪_C)` does, for every field extension.

The cover is produced rather than assumed (`nonempty_affineCoverMVSquare_of_curve`), so this is
an unqualified claim about AJC's curve rather than one about curves that happen to come with a
cover — the distinction `GenusFieldInvariance` had to make for the genus identity, made again
here for the same reason. -/
theorem subsingleton_hModule_one_baseChangeField_iff_curve (κ : Type u) [Field κ] [Algebra k κ] :
    letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
    letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
      .ofHom (Scheme.baseChangeField C κ).hom
    Subsingleton (Sheaf.HModule ((Scheme.baseChangeField C κ).left.moduleKSheaf κ) 1) ↔
      Subsingleton (Sheaf.HModule (C.left.moduleKSheaf k) 1) := by
  obtain ⟨S⟩ := nonempty_affineCoverMVSquare_of_curve C
  exact Scheme.subsingleton_hModule_one_moduleKSheaf_baseChangeField_iff κ S

set_option synthInstance.maxHeartbeats 800000 in
-- The `Module.Finite` instance for the genus carrier is found through the `Ext`/`Sheaf.HModule`
-- annotation diamond of `Ledger/GenusBridge.lean`, whose synthesis exceeds the default budget.
omit [GeometricallyIntegral C.hom] in
/-- **The hypothesis of §3 is exactly `genus C = 0`** (★): `Subsingleton (H¹(𝒪_C)) ↔ genus C = 0`.

Proved rather than asserted, because it is the sentence that makes every scope claim in this
file checkable.  An earlier version of this module stated the identification in prose at three
sites and cited `Ledger/GenusBridge.moduleFinite_genus_carrier`, which is only the finiteness
half — enough for `←`, and not a proof of either direction.  A fresh-context review flagged it;
this is the theorem.

Both directions are short and neither is free:

* `→` (the one that limits scope, and the one the prose most needed): `finrank` of a subsingleton
  is `0`, across the `Ext` universe hop of `Ledger/GenusBridge.lean`.  No finiteness needed.
* `←`: needs `moduleFinite_genus_carrier`, since `finrank = 0` forces triviality only in finite
  dimension — this is the standing `Subsingleton`-vs-`finrank` asymmetry again, here as the
  reason the two directions have different hypotheses rather than as a caveat. -/
theorem subsingleton_hModule_one_iff_genus_eq_zero :
    (letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
     Subsingleton (Sheaf.HModule (C.left.moduleKSheaf k) 1)) ↔ genus C = 0 := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
  haveI hfin : Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
    moduleFinite_genus_carrier C
  constructor
  · intro h
    have h2 : Subsingleton (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
      (Abelian.Ext.chgUnivLinearEquiv (R := k)).toEquiv.subsingleton_congr.mp h
    haveI := h2
    change Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) = 0
    exact Module.finrank_zero_of_subsingleton
  · intro h
    change Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) = 0 at h
    haveI h2 : Subsingleton (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
      Module.finrank_zero_iff.mp h
    exact (Abelian.Ext.chgUnivLinearEquiv (R := k)).toEquiv.subsingleton_congr.mpr h2

/-- **The producer** (★★): `UniformBaseDivisor C 0` from vanishing of `H¹(𝒪_C)`.

This is the first declaration in AJC whose *conclusion* is `UniformBaseDivisor`, which is the
producer/consumer test `Ledger/GenusFieldInvariance.lean` applied to record that the type had
consumers and none.  The witness at each `κ` is the **zero divisor**: `deg_κ 0 = 0 ≤ 0`, and
its `H¹` vanishes by §2's ascent composed with `divisorSheafZeroIso` at `κ`.

(The earlier record of that test said "five consumers".  Re-measured: **three** signature sites —
`ExtensionUniformity.lean:364`, `GenusFieldInvariance.lean:442` and `:461` — plus the `def`.  A
figure re-asserted across files instead of re-counted is the same failure as a prose claim carried
without checking, so it is corrected rather than repeated.)

**Its hypothesis is restrictive and that is the honest content of the result.**  For AJC's curve
`Subsingleton (H¹(𝒪_C))` is *equivalent* to `genus C = 0` — proved above as
`subsingleton_hModule_one_iff_genus_eq_zero`, not asserted here.  So this closes input (2) for
rational curves and says **nothing**
about `genus C ≥ 1`, where the input remains a missing production from geometry.  See the module
docstring §SCOPE item 1. -/
theorem uniformBaseDivisor_zero_of_subsingleton
    (h : letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
         Subsingleton (Sheaf.HModule (C.left.moduleKSheaf k) 1)) :
    UniformBaseDivisor C 0 := by
  intro κ _ _
  letI : (Scheme.baseChangeField C κ).left.Over (Spec (CommRingCat.of κ)) :=
    .ofHom (Scheme.baseChangeField C κ).hom
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.baseChangeField C κ).left ↘ Spec (CommRingCat.of κ)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Scheme.baseChangeField C κ).hom)
  refine ⟨0, ?_, by rw [Scheme.CurveDivisor.deg_zero]⟩
  have hκ : Subsingleton (Sheaf.HModule
      ((Scheme.baseChangeField C κ).left.moduleKSheaf κ) 1) :=
    (subsingleton_hModule_one_baseChangeField_iff_curve C κ).mpr h
  exact (Sheaf.HModule.mapEquiv (Scheme.divisorSheafZeroIso κ) 1).toEquiv.subsingleton_congr.mpr
    hκ

/-- **`UniformVanishing C` is a theorem when `H¹(𝒪_C)` vanishes** (★★) — the first *producer* of
extension-uniform bounded vanishing in AJC.

Before this, `UniformVanishing` had **no** producer: `Ledger/ExtensionUniformity.lean` stated it
and `Ledger/GenusFieldInvariance.lean` reduced it to `UniformBaseDivisor`, but nothing produced
either.  The uniform threshold is `0 + genus C`, which is `0` exactly when the hypothesis holds
(`subsingleton_hModule_one_iff_genus_eq_zero`).

**This is an implication, not an unconditional instance.**  An earlier version of this docstring
said "the first unconditional instance", which is false: the statement carries an explicit
hypothesis.  (When that correction was made AJC discharged the hypothesis at no curve;
`Ledger/P1Vanishing.lean` now discharges it at `ℙ¹`, which makes the statement non-vacuous but
still not unconditional — see §NON-VACUITY in the module docstring.)  The word
survived the round that added the non-vacuity caveat, which is exactly how a caveat fails —
it corrected the weaker phrase and left the stronger one standing.  Caught by a fresh-context
review.

**Genus 0, and the general case is untouched.**  Composing `uniformBaseDivisor_zero_of_subsingleton`
with `GenusFieldInvariance.uniformVanishing_of_uniformBaseDivisor_curve` inherits that theorem's
hypothesis exactly, so this is `UniformVanishing` for rational curves.  For `genus C ≥ 1` the
hypothesis is false and extension-uniformity remains open with the same residue as before. -/
theorem uniformVanishing_of_subsingleton_h1
    (h : letI : C.left.Over (Spec (CommRingCat.of k)) := .ofHom C.hom
         Subsingleton (Sheaf.HModule (C.left.moduleKSheaf k) 1)) :
    UniformVanishing C :=
  uniformVanishing_of_uniformBaseDivisor_curve C (uniformBaseDivisor_zero_of_subsingleton C h)

/-! ### The same two results with the hypothesis in genus form

`genus C = 0` is how a consumer meets this hypothesis, and having the translation as a theorem
(`subsingleton_hModule_one_iff_genus_eq_zero`) rather than a docstring sentence is what stops
this file's scope claims from resting on prose. -/

/-- **`UniformBaseDivisor C 0` for a curve of genus zero** (★★). -/
theorem uniformBaseDivisor_zero_of_genus_eq_zero (hg : genus C = 0) :
    UniformBaseDivisor C 0 :=
  uniformBaseDivisor_zero_of_subsingleton C
    ((subsingleton_hModule_one_iff_genus_eq_zero C).mpr hg)

/-- **Extension-uniform bounded vanishing for a curve of genus zero** (★★).

**Non-vacuity: settled, at `ℙ¹` only.**  When this was written AJC exhibited no curve with
`genus C = 0`, making it a true implication with no known instance.
`Ledger/P1Vanishing.genus_p1Over_eq_zero` supplies one, and
`P1Vanishing.uniformVanishing_p1Over` is this theorem applied there.  Still not a settled *case*
in general: the hypothesis is false for `genus C ≥ 1`. -/
theorem uniformVanishing_of_genus_eq_zero (hg : genus C = 0) : UniformVanishing C :=
  uniformVanishing_of_subsingleton_h1 C
    ((subsingleton_hModule_one_iff_genus_eq_zero C).mpr hg)

end Producer

end AlgebraicGeometry
