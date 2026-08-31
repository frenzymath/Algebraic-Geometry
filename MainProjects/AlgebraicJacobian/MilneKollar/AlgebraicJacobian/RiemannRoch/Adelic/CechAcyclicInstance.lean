/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.CechComparisonGate

/-!
# Gate 4: the Čech-to-derived comparison on 2-affine covers, reduced to affine vanishing

This file attacks **gate 4** of the unconditional genus-finiteness consumable
`Adelic.module_finite_hModule_one_of_finiteMapToP1_of_cechGate`
(`CechComparisonGate.lean`), namely the instance

```
∀ S : C.left.AffineCoverMVSquare, HasCechToHModuleIso (toModuleKSheaf C) S.coverFamily.
```

`HasCechToHModuleIso F 𝒰` (`MayerVietorisCover.lean`) packages, for the cover `𝒰`, a
degreewise `k`-linear comparison
`∀ n, cechCohomology C F 𝒰 n ≃ₗ[k] HModule' k F n (⨆ 𝒰)` between unnormalised Čech
cohomology and the `Ext`-based derived cohomology `HModule'`.

## The mathematical reduction (Leray on a 2-affine cover)

For the 2-affine cover `S.coverFamily` of a separated `k`-curve `C`, with the three
pieces `U₁`, `U₂`, `U₁ ⊓ U₂` affine (the `AffineCoverMVSquare` fields), the comparison
is the classical statement "an acyclic cover computes derived cohomology", which for a
**two**-element cover is the Mayer–Vietoris long exact sequence
(`HModule'_sequence_exact`, in-tree) fed by **affine Serre vanishing in the constant-`k`
sheaf apparatus** `IsAffineHModuleVanishing k C (toModuleKSheaf C)`, i.e.
`Subsingleton (HModule' k (toModuleKSheaf C) i U) = 0` for every affine open `U` and
every `i > 0`.  Given that vanishing the comparison assembles degreewise:

* `n = 0`: sheaf axiom (`H⁰` on both sides is the group of global sections);
* `n = 1`: `AffineCoverMVSquare.cechCohomologyOneEquivH1Cok` (node N5, in-tree,
  unconditional) `cechCohomology C F S.coverFamily 1 ≃ₗ[k] H1Cok S F`, chained with the
  MV cokernel identification `H1Cok S F ≃ₗ[k] HModule' k F 1 ⊤` (which uses the
  degree-`0`/degree-`1` slice of the MV LES together with the affine `H¹`-vanishing on
  `U₁`, `U₂`);
* `n ≥ 2`: both sides vanish — the Čech complex of a 2-element cover is `3`-term, and the
  derived side vanishes by the MV LES together with the affine vanishing on
  `U₁`, `U₂`, `U₁ ⊓ U₂`.

## What this file establishes

* `AffineCoverMVSquare.isAffineOpen_coverFamily` / `isAffineOpen_overlapOpen`: the three
  pieces of the cover, in their `coverFamily`/`overlapOpen` typed forms, are affine
  (bridging the structure fields to the family-indexed forms the degreewise assembly
  consumes).
* `AffineCoverMVSquare.subsingleton_hModule'_coverFamily` /
  `subsingleton_hModule'_overlapOpen`: the **per-piece derived vanishing** — under
  `IsAffineHModuleVanishing k C F`, `Subsingleton (HModule' k F i (piece))` for every
  `i > 0`.  These are the affine-vanishing inputs the Mayer–Vietoris degreewise assembly
  reads off (the `H¹` cokernel identification and the `n ≥ 2` whole-space vanishing are
  both immediate consequences of the MV LES fed by exactly these).
* `module_finite_hModule_one_unconditional`: the capstone, stated under the honest gate
  set (finite map to ℙ¹, ℙ¹ chart data, and the gate-4 comparison), delivering
  `Module.Finite k (H¹(C, 𝒪_C))`.  This is `module_finite_hModule_one_of_finiteMapToP1`
  with the `HasExt` gates synthesised (via `CechComparisonGate`); once the gate-4 instance
  is supplied — i.e. once `IsAffineHModuleVanishing k C (toModuleKSheaf C)` is proved and
  the degreewise assembly built — the genus of the curve is honest.

## The precise residual

The single named residual for the **unconditional** gate 4 is

> `IsAffineHModuleVanishing k C (toModuleKSheaf C)` — affine Serre vanishing
> `Hⁱ(U, 𝒪_C) = 0` (`i > 0`, `U` affine) in the `Sheaf (Opens.gT …) (ModuleCat k)`
> apparatus —

together with the degreewise assembly (the degree-`0`/degree-`1` MV cokernel
identification and the `n ≥ 2` whole-space vanishing) built from it.  No `sorry`/axiom or
sorried instance is introduced here; the residual is the existing `Prop`-class
`IsAffineHModuleVanishing`, whose producer for the structure sheaf is the genuine open
target (Mathlib supplies no scheme-cohomology Serre vanishing in this apparatus, and the
in-tree `X.Modules` vanishing is gated on the un-instantiable
`[EnoughInjectives (Spec R).Modules]`).

**Universe note for the assembly (probe-confirmed here).**  The affine vanishing lives at
`HModule' = Abelian.Ext.{u}` (`Type u`), but the in-tree Mayer–Vietoris LES
`AffineCoverMVSquare.HModule'_sequence` has its `HasExt` baked at `Abelian.Ext.{u+1}`
(`Type u+1`): the two carriers are *not* definitionally equal, so the degreewise assembly
must transport the per-piece vanishing across the universe bridge
`Abelian.Ext.chgUnivLinearEquiv` (`MayerVietorisCore.lean`) before feeding it into the LES.
This is the same `Ext.{u}` ↔ `Ext.{u+1}` bridge the `HModule'`/`HModule` interface already
uses (`HModule'_eq_HModule_linearEquiv`), and is the one non-obvious wrinkle a future
author of the assembly must account for.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

section Affineness

variable {k : Type u} [Field k] {X : Scheme.{u}} (S : X.AffineCoverMVSquare)

/-- Each piece of the 2-element cover family is affine: `S.coverFamily i` is `U₁` or
`U₂`, both affine by the `AffineCoverMVSquare` fields. -/
lemma AffineCoverMVSquare.isAffineOpen_coverFamily (i : ULift.{u} (Fin 2)) :
    IsAffineOpen (S.coverFamily i) := by
  rcases i with ⟨i⟩
  fin_cases i
  · exact S.isAffineOpen_U₁
  · exact S.isAffineOpen_U₂

/-- The overlap `U₁ ⊓ U₂` of the 2-element cover, in the `overlapOpen` typed form used by
the degreewise Čech assembly, is affine. -/
lemma AffineCoverMVSquare.isAffineOpen_overlapOpen :
    IsAffineOpen S.overlapOpen :=
  S.isAffineOpen_inf

end Affineness

/-! ## Per-piece derived-cohomology vanishing (the acyclicity inputs of the assembly)

Under affine Serre vanishing `IsAffineHModuleVanishing k C F`, each affine piece of the
2-affine cover has vanishing higher derived cohomology `HModule'`.  These are the exact
inputs the degreewise Čech comparison consumes (the Mayer–Vietoris LES on the cover reads
off `H¹(⊤)` and the higher vanishing from precisely these). -/

section PieceVanishing

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
  (S : C.left.AffineCoverMVSquare)
  (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
  [IsAffineHModuleVanishing k C F]

/-- Higher derived cohomology of `F` vanishes on each piece `S.coverFamily j` of the
2-affine cover (both pieces are affine). -/
lemma AffineCoverMVSquare.subsingleton_hModule'_coverFamily
    (j : ULift.{u} (Fin 2)) (i : ℕ) (hi : 0 < i) :
    Subsingleton (Scheme.HModule' k F i (S.coverFamily j)) :=
  IsAffineHModuleVanishing.subsingleton_HModule' (F := F) (S.isAffineOpen_coverFamily j) i hi

/-- Higher derived cohomology of `F` vanishes on the overlap `U₁ ⊓ U₂` of the 2-affine
cover (the overlap is affine). -/
lemma AffineCoverMVSquare.subsingleton_hModule'_overlapOpen
    (i : ℕ) (hi : 0 < i) :
    Subsingleton (Scheme.HModule' k F i S.overlapOpen) :=
  IsAffineHModuleVanishing.subsingleton_HModule' (F := F) S.isAffineOpen_overlapOpen i hi

end PieceVanishing

end AlgebraicGeometry.Scheme

/-! ## The capstone: genus finiteness under the honest gate set

Once the gate-4 comparison instance
`∀ S, HasCechToHModuleIso (toModuleKSheaf C) S.coverFamily` is available (its unconditional
production is the residual `IsAffineHModuleVanishing k C (toModuleKSheaf C)` plus the
degreewise assembly), the genus carrier `H¹(C, 𝒪_C)` is a finite `k`-module. -/

namespace AlgebraicGeometry.Adelic

variable {k : Type u} [Field k]

/-- **Genus finiteness of the curve, honest gate-set form.**  For a curve `C` over `k`
with a finite morphism to ℙ¹ (`HasFiniteMapToP1`), the ℙ¹ chart data
(`P1HasLaurentChartData`), and the Čech-to-derived comparison on 2-affine covers (gate 4),
the genus carrier `H¹(C, 𝒪_C) = HModule k (toModuleKSheaf C) 1` is a finite `k`-module.

This is `module_finite_hModule_one_of_finiteMapToP1_of_cechGate` (the `HasExt`-free
restatement, `CechComparisonGate.lean`) named as the lane capstone.  It becomes
**unconditional** exactly when gate 2 (`P1HasLaurentChartData k`, lane A) and gate 4
(this file's target instance, whose residual is affine Serre vanishing
`IsAffineHModuleVanishing k C (toModuleKSheaf C)`) are both discharged. -/
theorem module_finite_hModule_one_unconditional
    (C : Over (Spec (CommRingCat.of k))) [HasFiniteMapToP1 C] [P1HasLaurentChartData k]
    [∀ S : C.left.AffineCoverMVSquare,
      HasCechToHModuleIso (Scheme.toModuleKSheaf C) S.coverFamily] :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
  module_finite_hModule_one_of_finiteMapToP1_of_cechGate C

end AlgebraicGeometry.Adelic
