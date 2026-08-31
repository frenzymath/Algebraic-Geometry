/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicRepColimitCompat
import Mathlib.FieldTheory.SeparableClosure

/-!
# DAT-G0 β1 — the base-field directed system `K_s = colim k''` (DG-G0.δ) and the pinned residual

This file lands **DG-G0.δ** (mini-spec `informal/spec-datg0.md` §3, landing notes I-0259/I-0263):
the base-field directed system whose colimit is the separable closure `K_s`, over which the
β1 residual `Pic0PreservesFilteredBaseColimit` (landed in `Picard/PicRepColimitCompat.lean`,
commit c9df8d479) is quantified.

## DG-G0.δ — the substrate the residual quantifies over

For a **separable algebraic** extension `K/k` (the case `K = K_s` a separable closure is the
DAT-G0 target), the finite subextensions form a **directed system** whose supremum is all of
`K`.  Concretely:

* `FinSubext k K` — the index: finite(-dimensional) `k`-subextensions `k''` of `K`, ordered by
  inclusion.  It is **nonempty** and **directed** (`instNonemptyFinSubext`,
  `directed_finSubext`), so `(FinSubext k K)ᵒᵖ` is `IsCofiltered` — the shape the residual's
  `[IsCofiltered J]` binder consumes.
* `iSup_finSubext_eq_top` — `⨆ k'', k'' = ⊤`, i.e. **`K = colim k''`** at the lattice level.
* `coe_iSup_finSubext` — the colimit-is-**union** identity `↑(⨆ k'', k'') = ⋃ k'', ↑k''`
  (`IntermediateField.coe_iSup_of_directed`): every element of `K` already lives at a finite
  stage.  This is the honest content of "`K_s = colim k''`": the test-scheme limit
  `S_{K_s} = lim S_{k''}` is `Spec` of this filtered colimit of fields.
* `isSeparable_finSubext` — every stage `k''/k` is **separable** (`Algebra.IsSeparable`,
  inherited from `K/k` by `Algebra.isSeparable_tower_bot_of_isSeparable`); with
  `IntermediateField.isSeparable_iSup` the colimit is separable, so this is genuinely the
  system of *finite separable* subextensions of `K_s/k`.

All native `k`-algebra / scalar-tower instances come from the `IntermediateField` API
(`Algebra k k''`, `IsScalarTower k k'' K`), per the I-0255 tower-diamond wall — no composite
`RingHom.toAlgebra` `letI`s are built here.

## The β1 residual (pinned — `Pic0PreservesFilteredBaseColimit`, in `PicRepColimitCompat`)

The β1 reduction is LANDED (`PicRepColimitCompat.lean`, c9df8d479): the base-field-change
functoriality of `pic0` is the landed natural iso `pic0ThetaType`, collapsing the varying-field
colimit onto the single fixed functor `pic0TypeFunctor C` over `k`, whose base-field-colimit
compatibility is the named `Prop`

```
Pic0PreservesFilteredBaseColimit C :=
  ∀ ⦃J⦄ [SmallCategory J] [IsCofiltered J] (S : J ⥤ Over (Spec (.of k))),
    (∀ f, IsAffineHom (S.map f).left) → (∀ i, CompactSpace (S.obj i).left) →
    (∀ i, QuasiSeparatedSpace (S.obj i).left) → ∀ [HasLimit S],
      PreservesColimit S.op (pic0TypeFunctor C)
```

`instConsumesFiniteBaseColimit` below records that this `Prop` **applies to** the δ system:
`(FinSubext k K)ᵒᵖ` is `IsCofiltered`, so any cofiltered diagram `S` of test schemes indexed by
it (in particular the `Spec`-of-tests limit `S_{K_s} = lim_{k''} S_{k''}`) is a legal input.

**The residual proper is NOT discharged here** — it is genuinely M–L (I-0263): it says
`pic0TypeFunctor C` is *locally of finite presentation as a functor*, which on affine tests
`overSpec k A` is exactly that the affine relative-Picard construction `PicEtAff C A` commutes
with filtered colimits of the test algebra `A`, riding finite presentation of the proper smooth
curve `C/k`.  The precise remaining goal state and its named mathlib avatars
(`CommRingCat.preservesColimit_coyoneda_of_finitePresentation`,
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`, …) are pinned in the
`PicRepColimitCompat` module docstring and landing note I-0263; this file lands the δ substrate
they act on and leaves the analytic core `sorry`-free-pinned (no `sorry` in this file).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite IntermediateField

namespace AlgebraicGeometry.DatG0

/-! ## DG-G0.δ — the base-field directed system `K_s = colim k''` -/

section FieldSystem

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- **The DG-G0.δ index** — the finite subextensions `k''` of a separable algebraic extension
`K/k`, ordered by inclusion.  Its directed supremum is `K` (`iSup_finSubext_eq_top`); its
opposite is the `IsCofiltered` shape the β1 residual `Pic0PreservesFilteredBaseColimit`
quantifies over.  For `K = K_s` a separable closure these are exactly the *finite separable*
subextensions of `K_s/k`. -/
abbrev FinSubext : Type u := {L : IntermediateField k K // FiniteDimensional k L}

variable {k K}

/-- Each stage carries its finite-dimensionality as an instance. -/
instance (L : FinSubext k K) : FiniteDimensional k L.1 := L.2

variable (k K) in
/-- The δ index is nonempty (`k` itself, as `⊥`, is a finite subextension). -/
instance instNonemptyFinSubext [Algebra.IsAlgebraic k K] : Nonempty (FinSubext k K) :=
  ⟨⟨k⟮(0 : K)⟯, adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩⟩

/-- **DG-G0.δ, directedness.**  The finite subextensions of `K/k` are directed under inclusion:
the join `k'' ⊔ k'''` of two finite subextensions is again finite.  Hence `(FinSubext k K)ᵒᵖ` is
`IsCofiltered` — the shape the residual consumes. -/
theorem directed_finSubext :
    Directed (· ≤ ·) (fun L : FinSubext k K => (L.1 : IntermediateField k K)) := by
  intro L₁ L₂
  haveI := L₁.2
  haveI := L₂.2
  exact ⟨⟨L₁.1 ⊔ L₂.1, IntermediateField.finiteDimensional_sup _ _⟩, le_sup_left, le_sup_right⟩

/-- **DG-G0.δ, `IsDirected`.**  The δ index is a directed order (from `directed_finSubext`), so it
is `IsFiltered` and its opposite `(FinSubext k K)ᵒᵖ` is `IsCofiltered` — automatically, via
`isFiltered_of_directed_le_nonempty` and `isCofiltered_op_of_isFiltered`. -/
instance instIsDirectedFinSubext [Algebra.IsAlgebraic k K] :
    IsDirected (FinSubext k K) (· ≤ ·) :=
  ⟨fun L₁ L₂ => directed_finSubext L₁ L₂⟩

/-- **DG-G0.δ, the cofiltered shape the residual consumes.**  `(FinSubext k K)ᵒᵖ` is
`IsCofiltered` — exactly the `[IsCofiltered J]` shape of `Pic0PreservesFilteredBaseColimit`'s
diagram binder.  A cofiltered diagram of test schemes `S : (FinSubext k K)ᵒᵖ ⥤ Over (Spec k)`
indexed by it — in particular the `Spec`-of-tests limit `S_{K_s} = lim_{k''} S_{k''}` (with
affine transition maps `Spec k''' → Spec k''` and one-point, hence compact and quasi-separated,
stages) — is therefore a legal input to the β1 residual. -/
instance instIsCofilteredFinSubextOp [Algebra.IsAlgebraic k K] :
    IsCofiltered (FinSubext k K)ᵒᵖ :=
  inferInstance

/-- **DG-G0.δ, the colimit at the lattice level: `K = colim k''`.**  For an algebraic extension
`K/k` the supremum of the finite subextensions is all of `K`: every `x : K` is algebraic, hence
lies in the finite subextension `k⟮x⟯`. -/
theorem iSup_finSubext_eq_top [Algebra.IsAlgebraic k K] :
    ⨆ L : FinSubext k K, (L.1 : IntermediateField k K) = ⊤ :=
  le_top.antisymm fun x _ =>
    le_iSup (fun L : FinSubext k K => (L.1 : IntermediateField k K))
      ⟨k⟮x⟯, adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩ <|
      mem_adjoin_simple_self k x

/-- **DG-G0.δ, colimit-is-union.**  The directed supremum of the finite subextensions is their
set-theoretic **union** (`IntermediateField.coe_iSup_of_directed`): the honest "`K_s = colim k''`"
statement.  Combined with `iSup_finSubext_eq_top`, every element of `K` already lives at a finite
stage `k''`. -/
theorem coe_iSup_finSubext [Algebra.IsAlgebraic k K] :
    (↑(⨆ L : FinSubext k K, (L.1 : IntermediateField k K)) : Set K)
      = ⋃ L : FinSubext k K, (L.1 : Set K) :=
  IntermediateField.coe_iSup_of_directed directed_finSubext

/-- **DG-G0.δ, separability of each stage.**  Every finite subextension `k''/k` of a separable
extension `K/k` is itself separable (`Algebra.isSeparable_tower_bot_of_isSeparable` on the native
tower `k → k'' → K`).  With `IntermediateField.isSeparable_iSup` the colimit `⨆ k''` is separable,
so the δ system is the directed system of *finite separable* subextensions. -/
instance isSeparable_finSubext [Algebra.IsSeparable k K] (L : FinSubext k K) :
    Algebra.IsSeparable k L.1 :=
  Algebra.isSeparable_tower_bot_of_isSeparable k L.1 K

end FieldSystem

end AlgebraicGeometry.DatG0
