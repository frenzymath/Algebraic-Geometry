/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.FinitenessP1

/-!
# Genus finiteness of the curve (node `N12`, the adelic lane's consumable)

This file is part of the **adelic Riemann–Roch lane**.  It composes the two halves
of the lane that are now proved:

* the **keystone** `Adelic.module_finite_hModule_one_of_finite_map`
  (`FinitenessP1.lean`, node `N11`): under the gates `HasFiniteMapToP1 C` and
  `P1HasLaurentChartData k`, *some* 2-affine cover `S` of `C` (the pullback of the
  standard ℙ¹ charts along the finite map) has finite-dimensional Čech cokernel
  `Ȟ¹ = S.H1Cok`, so any comparison `H¹(C, 𝒪_C) ≃ₗ[k] S.H1Cok` transports the
  finiteness to the genus carrier;
* the **comparison** `AffineCoverMVSquare.hModuleOneEquivH1Cok`
  (`Cokernel.lean`, nodes `N5` + `N6`): for *every* 2-affine cover `S`, under the
  Čech-to-derived gate `HasCechToHModuleIso (toModuleKSheaf C) S.coverFamily`,
  `HModule k (toModuleKSheaf C) 1 ≃ₗ[k] S.H1Cok (toModuleKSheaf C)` — the N5 half
  (`cechCohomology 1 ≃ₗ H1Cok`) is unconditional, only the N6 half is gated.

## The honest gate set

The keystone produces an *existential* cover (`D.pullbackSquare π` for a chosen
finite `π` and chart data `D`), which cannot be named in a theorem signature; the
comparison must therefore be available for **all** 2-affine covers, i.e. the honest
Čech-to-derived hypothesis is the `∀`-quantified instance gate
`[∀ S, HasCechToHModuleIso (toModuleKSheaf C) S.coverFamily]` (a `Prop`-class
hypothesis with no sorried instance, in the `HasFiniteMapToP1` gating pattern).
The full gate set of the consumable is

* `HasFiniteMapToP1 C` — node `N9`; derived in `FiniteMapToP1.lean` from the single
  strictly weaker gate `ExistsNonconstantMapToP1 C` under the ambient curve
  hypotheses;
* `P1HasLaurentChartData k` — node `N11b`, the ℙ¹ chart-ring computation
  (`P1ChartData.lean` is building towards its instance);
* `HasExt.{u}`/`HasExt.{u+1}` — the ambient `Ext`-theory instances the `HModule`
  machinery runs on;
* `∀ S, HasCechToHModuleIso (toModuleKSheaf C) S.coverFamily` — the Čech-to-derived
  comparison (Leray/Cartan) for 2-affine covers of the curve.

Under these, the genus carrier `H¹(C, 𝒪_C) = HModule k (toModuleKSheaf C) 1` is a
finite-dimensional `k`-vector space, so `genus C = finrank k H¹(C, 𝒪_C)` is an
honest natural number.
-/

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Adelic

variable {k : Type u} [Field k]

/-- **Genus finiteness of the curve (node `N12`, gated).**  For a curve `C` over `k`
with a finite morphism to ℙ¹ and the ℙ¹ chart data, and with the Čech-to-derived
comparison available on 2-affine covers, the genus carrier `H¹(C, 𝒪_C)` is a finite
`k`-module.  Composes the `N11` keystone `module_finite_hModule_one_of_finite_map`
with the `N5`+`N6` comparison `hModuleOneEquivH1Cok` of `Cokernel.lean`. -/
theorem module_finite_hModule_one_of_finiteMapToP1
    (C : Over (Spec (CommRingCat.of k))) [HasFiniteMapToP1 C] [P1HasLaurentChartData k]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    [∀ S : C.left.AffineCoverMVSquare,
      HasCechToHModuleIso (Scheme.toModuleKSheaf C) S.coverFamily] :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
  module_finite_hModule_one_of_finite_map C
    (fun S => ⟨S.hModuleOneEquivH1Cok (Scheme.toModuleKSheaf C)⟩)

end AlgebraicGeometry.Adelic
