/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Challenge
import AlgebraicJacobian.Cohomology.TwoCover
import AlgebraicJacobian.Curve.P1Charts
import AlgebraicJacobian.Curve.P1Curve

/-!
# `H¹(ℙ¹, 𝒪) = 0`, hence `genus ℙ¹ = 0` — both halves were already in this project

`Curve/P1Charts.lean` bundles the two standard charts of `ℙ¹` as a `LaurentChartPair` and proves
its **Laurent span** property: every section on the overlap is a sum of a restriction from the
left chart and one from the right (`LaurentChartPair.exists_res_add_res`, from
`LaurentPolynomial.exists_toLaurent_add_aeval`).  `Cohomology/TwoCover.lean` proves the
**Mayer–Vietoris bridge**: for two affine opens covering a scheme, `H¹` of the structure sheaf is
the cokernel of the restriction-difference map (`TwoCover.h1CokEquiv`).

**Nothing connected them**, and their composite is the vanishing: Laurent span says the
difference map is surjective, so the cokernel is trivial, so `H¹` is.  This file is that
composite, plus the genus corollary.

## The two forms are INTERDERIVABLE here — an earlier version of this section said otherwise

This section used to argue that `Subsingleton` is strictly stronger than `genus = 0`, because
`finrank` reads `0` on an infinite-dimensional space, and concluded that the `Subsingleton` is
"the theorem" and the genus "its corollary, not the reverse".  **The general fact is true and it
is idle in this tree**, so the conclusion was wrong: `Cohomology/Finiteness.lean` registers
`moduleFinite_hModule_one` as a *global instance* at every curve carrying the three binders, and
under `Module.Finite` mathlib's `Module.finrank_zero_iff` is an **iff**.  Compiler-checked, at
exactly the carrier `P1.subsingleton_hModule_one` states:

```
theorem converse {k} [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] (h : genus C = 0) :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    Subsingleton (Sheaf.HModule (C.left.moduleKSheaf k) 1) := by
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  haveI := moduleFinite_hModule_one C
  rw [genus] at h; exact (Module.finrank_zero_iff (R := k)).mp h
```

So cite either form freely.  The order below is a convenience of proof, not a strength gap: the
two-cover bridge produces a `Subsingleton` directly, so that is what gets proved first.  The one
real asymmetry is mechanical: the `Module.Finite` instance is keyed on the `letI` spelling `genus`
uses, so recovering the vanishing from the genus at the `(P1 k).moduleKSheaf` spelling needs that
instance routed in by hand rather than found by search.

## Why this is a representability fact

`Albanese/Genus0Terminal.lean` isolates `genus C = 0 → pic0Subgroup C T = ⊥` as "the single
mathematical debt of S11", and `Picard/Pic0VanishingRoute.lean` produces a `JacobianData` from
testwise `pic⁰` vanishing.  Neither could be *instantiated* at any object until
`Curve/P1Curve.lean` gave the project a curve.  This file supplies the other half of the pair at
that same curve: `ℙ¹` now carries both the three curve binders and `genus = 0`.

**What is still missing — THREE inputs, not one, and an earlier version of this paragraph said
"one implication about Picard groups", which was false about the Albanese target.**  Counted at
the two different destinations, because they cost different things:

* to a **`JacobianData`** at `ℙ¹`, one input remains: `pic0Subgroup C T = ⊥` at every test `T`,
  the debt `Genus0Terminal`'s header names, proved nowhere in the tree.  It needs the relative
  statement `Pic(ℙ¹_T) ≅ Pic(T) × ℤ`; a base-field-only version does **not** discharge the
  `∀ T` binder.  Given it, `isTerminal_of_pic0Subgroup_eq_bot` and `jacobianData_of_subsingleton`
  do the rest — verified, `jacobianData_of_subsingleton (P1.asOver k) h` elaborates and
  `Surjective (P1.asOver k).hom` is `inferInstance`;
* to the challenge's **`exists_unique_ofCurve_comp`**, two *further* inputs, and
  `Genus0Terminal` only ever discharges the uniqueness half: a **`k`-rational point**
  `P : 𝟙_ ⟶ P1.asOver k`, which this project does not construct at `ℙ¹` (no `HasRationalPoint`
  producer there), and the **existence** hypothesis `hex`, which is Milne I 3.9 and which
  `Genus0Terminal.lean:160-167` states is not removable.

So this file closes the *cohomological* input and leaves those.  What it does remove is the
possibility of treating `genus = 0` as unreachable: the hypothesis is now discharged at a
concrete curve.

## Main declarations

* `AlgebraicGeometry.LaurentChartPair.exists_res_add_res_inf` — the Laurent span restated at the
  `U₀ ⊓ U₁` spelling the Mayer–Vietoris machinery consumes (the packaged form is stated at the
  pair's own `U₀₁` field).
* `AlgebraicGeometry.LaurentChartPair.diff_surjective` — **the difference map is surjective.**
  The sign is where the two statements differ: the span produces `a + b`, the difference map
  computes `a - b`, so the witness is `(a, -b)`.
* `AlgebraicGeometry.LaurentChartPair.subsingleton_h1Cok` — the Mayer–Vietoris cokernel is
  trivial.
* `AlgebraicGeometry.LaurentChartPair.subsingleton_hModule_one` — **`H¹(ℙ¹, 𝒪) = 0`**, for an
  arbitrary field and any Laurent chart pair.
* `AlgebraicGeometry.P1.subsingleton_hModule_one` — the same at the canonical pair.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

attribute [local instance] Scheme.overModule

noncomputable section

/-- `ℙ¹` as a scheme over `Spec k`, in the `Scheme.Over` form the cohomology machinery binds.
`Curve/P1.lean` provides the `Over (Spec k)` *object* `P1.asOver`; this is the same morphism as
a typeclass, which is what `Scheme.moduleKSheaf` and `TwoCover` consume. -/
instance instOverP1 (k : Type u) [Field k] : (P1 k).Over (Spec (.of k)) :=
  .ofHom (P1.structureMap k)

namespace LaurentChartPair

/-- **The Laurent span at the `⊓` spelling.**

`exists_res_add_res` is stated at the pair's own `U₀₁` field; the Mayer–Vietoris difference map is
stated at `U₀ ⊓ U₁`.  The two are equal by the pair's `inf_eq`, but not syntactically, and the
sections types depend on the open — so the transport is by destructuring the pair and `subst`ing
the field equation, which makes the two spellings literally the same open. -/
theorem exists_res_add_res_inf (D : LaurentChartPair k) (z : Γ(P1 k, D.U₀ ⊓ D.U₁)) :
    ∃ (a : Γ(P1 k, D.U₀)) (b : Γ(P1 k, D.U₁)),
      z = (P1 k).resHom inf_le_left a + (P1 k).resHom inf_le_right b := by
  obtain ⟨U₀, U₁, U₀₁, hle₀, hle₁, hinf, ha₀, ha₁, ha₀₁, hsup, G₀, G₁, G₀₁, hr₀, hr₁⟩ := D
  subst hinf
  exact LaurentChartPair.exists_res_add_res
    ⟨U₀, U₁, U₀ ⊓ U₁, hle₀, hle₁, rfl, ha₀, ha₁, ha₀₁, hsup, G₀, G₁, G₀₁, hr₀, hr₁⟩ z

/-- **The Mayer–Vietoris difference map is surjective on a Laurent chart pair.**

The one thing to notice is the sign.  The span gives `z = a|∩ + b|∩`; `TwoCover.diff` computes
`s₀|∩ - s₁|∩`.  So the preimage of `z` is `(a, -b)`, and that is the whole difference between the
two statements. -/
theorem diff_surjective (D : LaurentChartPair k) :
    Function.Surjective (TwoCover.diff k (P1 k) D.U₀ D.U₁) := by
  intro z
  obtain ⟨a, b, hab⟩ := exists_res_add_res_inf D z
  refine ⟨(a, -b), ?_⟩
  rw [TwoCover.diff_apply]
  simpa [sub_neg_eq_add] using hab.symm

/-- **The two-cover cokernel is trivial**: a quotient by a submodule that is everything. -/
theorem subsingleton_h1Cok (D : LaurentChartPair k) :
    Subsingleton (TwoCover.H1Cok k (P1 k) D.U₀ D.U₁) :=
  Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr (diff_surjective D))

/-- **`H¹(ℙ¹, 𝒪) = 0`**, for an arbitrary field `k`.

The composite of two facts this project already had and had never put together: the cokernel is
trivial by Laurent span, and `TwoCover.h1CokEquiv` identifies `H¹` with that cokernel using only
that the two charts are affine and cover — both fields of the pair.

Stated as `Subsingleton`, not as `finrank = 0`: the former is the usable direction, since
`finrank` reads `0` on an infinite-dimensional space and so the numerical statement would not
give the vanishing back. -/
theorem subsingleton_hModule_one (D : LaurentChartPair k) :
    Subsingleton (Sheaf.HModule ((P1 k).moduleKSheaf k) 1) := by
  haveI := subsingleton_h1Cok D
  exact (TwoCover.h1CokEquiv k (P1 k) D.U₀ D.U₁ D.sup_eq_top D.isAffineOpen_U₀
    D.isAffineOpen_U₁).toEquiv.subsingleton

end LaurentChartPair

namespace P1

variable (k) in
/-- **`H¹(ℙ¹_k, 𝒪) = 0`** at the canonical two-chart pair, for every field `k`. -/
theorem subsingleton_hModule_one :
    Subsingleton (Sheaf.HModule ((P1 k).moduleKSheaf k) 1) :=
  LaurentChartPair.subsingleton_hModule_one (laurentChartPair k)

set_option synthInstance.maxHeartbeats 400000 in
-- `genus` unfolds to a `letI`-supplied `Over` instance on `(asOver k).left`, and reconciling it
-- with `instOverP1` above exceeds the default instance-search budget.
/-- **`genus (ℙ¹_k) = 0`**, for every field `k` — the corollary, in the weaker numerical form.

`genus` is `Module.finrank k (Sheaf.HModule (moduleKSheaf k) 1)` and the vanishing above makes
that module a subsingleton, so the rank is `0`.  This used to say the implication runs one way
only; it does not — `Cohomology/Finiteness.lean`'s `moduleFinite_hModule_one` makes
`Module.finrank_zero_iff` an iff at every curve with the three binders, so the two forms are
interderivable (see the header for the compiler-checked converse).  Cite whichever is convenient.

The three binders `genus` requires are the ones `Curve/P1Curve.lean` supplies, so this statement
is only expressible because that file exists. -/
theorem genus_asOver_eq_zero (k : Type u) [Field k] : genus (asOver k) = 0 := by
  rw [genus]
  haveI : Subsingleton (Sheaf.HModule (Scheme.moduleKSheaf k (asOver k).left) 1) :=
    subsingleton_hModule_one k
  exact Module.finrank_zero_of_subsingleton

end P1

end

end AlgebraicGeometry
