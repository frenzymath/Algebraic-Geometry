/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.GenusFiniteness

/-!
# The last genus-finiteness gates: scoping the Čech-to-derived comparison

This file scopes the **final** gates of the adelic genus-finiteness consumable
`Adelic.module_finite_hModule_one_of_finiteMapToP1` (`GenusFiniteness.lean`, node `N12`).
That consumable is stated under four gates:

1. `HasFiniteMapToP1 C`               — node `N9`  (curve ⟶ ℙ¹, in progress elsewhere);
2. `P1HasLaurentChartData k`          — node `N11b` (ℙ¹ chart rings, `P1ChartData.lean`);
3. `HasExt.{u}` **and** `HasExt.{u+1}` for the sheaf category
   `Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)`
   — the ambient `Ext`-theory the `HModule` genus carrier runs on;
4. `∀ S : C.left.AffineCoverMVSquare,
      HasCechToHModuleIso (toModuleKSheaf C) S.coverFamily`
   — the Čech-to-derived comparison (Leray/Cartan) on 2-affine covers.

The question this file answers: **are gates 3 and 4 instantiable today?**

## Gate 3 (the `HasExt` pair): INSTANTIABLE — proved here

The genus carrier lives in the sheaf category `𝒮 := Sheaf (Opens.grothendieckTopology
C.left.toTopCat) (ModuleCat.{u} k)`, i.e. sheaves of `k`-modules for the *constant* base
field `k`.  This is the crucial point that dissolves the historical blocker: `𝒮` is a
**Grothendieck abelian category** (Mathlib `IsGrothendieckAbelian.{v} (Sheaf J A)` for a
small site `J` and Grothendieck-abelian `A = ModuleCat k`), so Mathlib supplies
`EnoughInjectives 𝒮` (`079H`) and both `HasExt.{u} 𝒮`, `HasExt.{u+1} 𝒮` (`HasExt.standard`)
**for free**.  See `hasExt_moduleKSheaf` / `hasExt_succ_moduleKSheaf` /
`enoughInjectives_moduleKSheaf` / `isGrothendieckAbelian_moduleKSheaf` below.

This is *not* the situation of the `SheafOfModules R = X.Modules` apparatus (`Ext` over the
structure sheaf `𝒪_X` as a sheaf of rings), which the historical Čech capstone
(`CechToCohomology.cech_eq_cohomology_of_basis`, `AffineSerreVanishing.affine_serre_vanishing`)
runs on: there Mathlib v4.31 provides *no* Grothendieck-abelian / enough-injectives instance
for `SheafOfModules`, so every derived-functor statement in that lane carries
`[EnoughInjectives X.Modules]` / `[HasInjectiveResolutions X.Modules]` as an un-instantiable
hypothesis.  The genus carrier deliberately uses the constant-`k` sheaf category precisely to
avoid that trap — and the trap is genuinely avoided.

Consequence (`module_finite_hModule_one_of_finiteMapToP1_of_cechGate`): gate 3 can simply be
dropped from the `N12` consumable — Mathlib synthesises it — leaving only gates 1, 2, 4.

## Gate 4 (the comparison `∀ S, HasCechToHModuleIso …`): NOT instantiable today

`HasCechToHModuleIso F 𝒰` (`MayerVietorisCover.lean`) is the `Prop`-class packaging of the
comparison data `∀ n, cechCohomology C F 𝒰 n ≃ₗ[k] HModule' k F n (⨆ 𝒰)`, i.e. "for the cover
`𝒰`, unnormalised Čech cohomology equals derived (`Ext`) cohomology in every degree".

For the 2-affine cover `S.coverFamily` this comparison is *mathematically* the Leray statement
"an affine cover is acyclic ⟹ Čech computes cohomology", which for a **two**-element cover is
exactly the Mayer–Vietoris long exact sequence (`HModule'_sequence_exact`, in-tree) together
with **affine Serre vanishing in the constant-`k` sheaf apparatus**:
`IsAffineHModuleVanishing k C (toModuleKSheaf C)`, i.e. `Subsingleton (HModule' k
(toModuleKSheaf C) i U) = 0` for every affine open `U` and every `i > 0`.  Given that vanishing,
the comparison assembles degreewise: `n = 0` (sheaf axiom), `n = 1` (`cechCohomologyOneEquivH1Cok`
= node `N5`, in-tree, plus the MV cokernel identification), `n ≥ 2` (both sides vanish).

The **precise gap** is therefore this single named input:

> **MISSING:** `IsAffineHModuleVanishing k C (toModuleKSheaf C)` — Serre vanishing
> `Hⁱ(U, 𝒪_C) = 0` (`i > 0`, `U` affine) in the `Sheaf (Opens.gT …) (ModuleCat k)` apparatus,
> **plus** the degreewise assembly of the 2-cover comparison from it.

Neither piece is a one-line consequence of an existing lemma:

* Mathlib has no scheme-cohomology Serre vanishing at all, in any apparatus.
* The in-tree Serre vanishing `AffineSerreVanishing.affine_serre_vanishing` lives in the *wrong*
  category (`X.Modules`, `Ext (jShriekOU U)`) and is itself gated on the un-instantiable
  `[EnoughInjectives (Spec R).Modules]`; bridging it to the constant-`k` apparatus would need a
  "cohomology is independent of the linear structure" comparison that is likewise absent.
* The Čech-to-derived carrier `IsAffineHModuleVanishing` is currently *produced* in-tree only
  from `HasAffineCechAcyclicCover` — which itself bundles `HasCechToHModuleIso` on the affine
  sub-covers, i.e. the very comparison we are trying to instantiate (a circular producer).

So gate 4 is a genuine multi-lemma target, **but the historical infrastructure blocker is gone**:
because `EnoughInjectives 𝒮` is now available (proved below), the honest way to close gate 4 is
to build affine Serre vanishing + the Čech comparison *directly in the constant-`k` sheaf
category* `𝒮` (where injective resolutions exist), rather than attempting to route through the
blocked `SheafOfModules` lane.  That is the recommended roadmap for the next wave.

## Deliverable of this file

* the gate-3 infrastructure, proved and named for citation
  (`isGrothendieckAbelian_moduleKSheaf`, `enoughInjectives_moduleKSheaf`,
  `hasExt_moduleKSheaf`, `hasExt_succ_moduleKSheaf`);
* the gate-3-free restatement of the `N12` consumable
  (`module_finite_hModule_one_of_finiteMapToP1_of_cechGate`): under gates 1, 2, 4 alone,
  `H¹(C, 𝒪_C)` is a finite `k`-module.  Once `P1ChartData` lands (gate 2) and the gate-4
  comparison is built, `Module.Finite k H¹(C, 𝒪_C)` — hence the honesty of `genus C` — is
  unconditional on a curve with a finite map to ℙ¹.
-/

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Adelic

variable {k : Type u} [Field k]

/-! ## Gate 3: the `Ext` infrastructure of the constant-`k` sheaf category is present -/

/-- The genus-carrier sheaf category `Sheaf (Opens.gT X) (ModuleCat k)` is **Grothendieck
abelian**: sheaves valued in the Grothendieck-abelian `ModuleCat.{u} k` on the small site of
opens of `X`.  Mathlib's `IsGrothendieckAbelian.{v} (Sheaf J A)` fires here.  This is the
structural fact that makes the derived-functor genus apparatus well-founded (contrast the
`SheafOfModules 𝒪_X` apparatus, for which Mathlib v4.31 supplies no such instance). -/
theorem isGrothendieckAbelian_moduleKSheaf (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u}
      (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)) :=
  inferInstance

/-- The genus-carrier sheaf category has **enough injectives** (Stacks `079H`, from
Grothendieck-abelianness).  This is the input the entire `Ext`/derived-functor comparison
needs, and the exact instance the `SheafOfModules 𝒪_X` lane cannot supply.  Its availability
here is what dissolves the historical Čech-capstone blocker for the *constant-`k`* apparatus. -/
theorem enoughInjectives_moduleKSheaf (X : Scheme.{u}) :
    EnoughInjectives
      (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)) :=
  inferInstance

/-- Gate 3, lower universe: `HasExt.{u}` for the genus-carrier sheaf category is synthesisable
(from `HasExt.standard`, itself from Grothendieck-abelianness). -/
theorem hasExt_moduleKSheaf (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)) :=
  inferInstance

/-- Gate 3, upper universe: `HasExt.{u+1}` for the genus-carrier sheaf category is
synthesisable (the ambient `Ext`-theory the universe-bridged `HModule` genus carrier runs on). -/
theorem hasExt_succ_moduleKSheaf (X : Scheme.{u}) :
    HasExt.{u+1} (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)) :=
  inferInstance

/-! ## Gate-3-free restatement of the genus-finiteness consumable (node `N12`)

Because both `HasExt` gates are now synthesised (gate 3 above), the `N12` consumable of
`GenusFiniteness.lean` can be restated without them: the only remaining gates are the geometric
inputs (`HasFiniteMapToP1 C`, `P1HasLaurentChartData k`) and the Čech-to-derived comparison
(gate 4).  This is the honest, tightest current form of adelic genus finiteness. -/

/-- **Genus finiteness of the curve, gate-3-free form (node `N12`).**  For a curve `C` over `k`
with a finite morphism to ℙ¹ and the ℙ¹ chart data, and with the Čech-to-derived comparison on
2-affine covers (gate 4), the genus carrier `H¹(C, 𝒪_C) = HModule k (toModuleKSheaf C) 1` is a
finite `k`-module.  Identical to `Adelic.module_finite_hModule_one_of_finiteMapToP1` but with the
two `HasExt` hypotheses dropped — Mathlib synthesises them from the Grothendieck-abelianness of
the constant-`k` sheaf category (`hasExt_moduleKSheaf`, `hasExt_succ_moduleKSheaf`).  Once gates
2 and 4 are discharged, `Module.Finite k H¹(C, 𝒪_C)` — and hence the honesty of `genus C` — is
unconditional on any curve with a finite map to ℙ¹. -/
theorem module_finite_hModule_one_of_finiteMapToP1_of_cechGate
    (C : Over (Spec (CommRingCat.of k))) [HasFiniteMapToP1 C] [P1HasLaurentChartData k]
    [∀ S : C.left.AffineCoverMVSquare,
      HasCechToHModuleIso (Scheme.toModuleKSheaf C) S.coverFamily] :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
  module_finite_hModule_one_of_finite_map C
    (fun S => ⟨S.hModuleOneEquivH1Cok (Scheme.toModuleKSheaf C)⟩)

end AlgebraicGeometry.Adelic
