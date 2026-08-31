/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.CurveCoheight

/-!
# The universe gap between the two projects' cohomology carriers is NOT an obstruction

`WeilDivisor.lean` records that the sibling project `Algebraic-Jacobian-Challenge-Rebuild`
proves the closed χ-ledger sorry-free (`RiemannRoch/ChiLedger.lean`: `chi_divisorSheaf`,
`deg_divOf`) and lists the carrier mismatches that make porting it real work.  Task `ajc-rr`
audited that port.  Two of the mismatches are now settled, and this file records the second one
in Lean rather than in prose, because it is the one that looked fatal and is not.

## The apparent obstruction

The two projects' sheaf-cohomology carriers are annotated in **different universes**:

* AJCR: `CategoryTheory.Sheaf.HModule F n := Abelian.Ext (constModuleSheaf J R) F n`, declared
  `Type u`, over a **small** site (`Cohomology/ModuleKSheaf.lean:74`).
* AJC: `Scheme.HModule k F n := Abelian.Ext ((constantSheaf J _).obj (ModuleCat.of k k)) F n`,
  declared `Type (u+1)`, over a general `[Category.{u,v} C]`
  (`Cohomology/StructureSheafModuleK/Carriers.lean:51`).

Both instantiate at the *same* site `Opens.grothendieckTopology X.toTopCat` with the *same*
coefficients `ModuleCat.{u} k`, and — inspecting the definitions — at the *same* constant sheaf.
A `Type u` and a `Type (u+1)` are not the same type, and a bare `LinearEquiv` between them is
not even statable, so the mismatch reads like a wall.

## Why it is not a wall — three facts, each machine-checked

1. **`HasExt.{u}` is synthesised at AJC's own site**, not merely assumable: see
   `Adelic/CechComparisonGate.hasExt_moduleKSheaf`.  So the *lower*-universe `Ext` exists in AJC
   already; nothing needs to be built for it.
2. **The `Type u` `Ext` typechecks in AJC at AJC's arguments.**  `extLowerUniverse` below is
   AJCR's carrier shape, written in AJC, elaborating.  So AJC's `Type (u+1)` annotation is a
   *choice* made by `Carriers.lean` (for a general site where the lower `HasExt` need not exist),
   not a constraint imposed by AJC's geometry.
3. **`finrank` is ULift-invariant** (`finrank_uLift`).  This is the fact that decides the port,
   because the χ-ledger's content is entirely *dimension* statements: `χ = h⁰ − h¹`,
   `χ(𝒪(D)) = χ(𝒪_X) + deg D`, `deg (div g) = 0`.  A universe mismatch between carriers does not
   obstruct transporting an equation between their `finrank`s.

## NON-VACUITY OF THE CHART-FINITENESS RESULT, measured at a synthesis site

`scripts/axiom-frontier.lean` §6e records trap (d): a theorem whose instance binders nothing can
instantiate for the ambient object reports clean axioms and always will.  Its own resolution note
adds the sting — instantiability is `open`-sensitive, so the check must elaborate a *consumer*
rather than read a signature.  `ChartFinitenessRefuted`'s results carry `[IsConstantField k X]`
and `[Algebra k X.functionField]`, both of whose producers are **scoped** instances in
`Adelic/GateInstances.lean`, so they are exactly the shape trap (d) catches.

Checked, and it took three attempts, which is the point:

* with an arbitrary `[Algebra k C.left.functionField]` binder supplied by hand,
  `IsConstantField k C.left` does **not** synthesise — the producer needs the *scoped*
  `functionFieldAlgebra`, not any `k`-algebra structure;
* with `open scoped AlgebraicGeometry.Scheme` but without importing `GateInstances`, `Algebra k
  C.left.functionField` itself fails;
* with `import AlgebraicJacobian.RiemannRoch.Adelic.GateInstances` **and** `open scoped
  AlgebraicGeometry.Scheme`, `not_chart_finite_of_primeDivisor k hU P` elaborates at an AJC curve
  bundle `C : Over (Spec (CommRingCat.of k))` with `[IsIntegral] [IsLocallyNoetherian]
  [IsRegularInCodimensionOne]` and nothing else — every remaining binder synthesised.

So the collapse is **not** trap (d): it fires at the object the lane actually runs on.  A consumer
must import `GateInstances` and open the scope, and a failure to do so looks exactly like
un-instantiability even though the instance exists — the fifth thing §6e says no axiom line shows.

## The audit verdict this supports

The universe gap is an **annotation artifact**, not a mathematical obstruction: it costs a
`ULift` in the statement of a comparison, and nothing in the proofs.  It is therefore *not*
among the real costs of porting AJCR's ledger.  The real costs are the ones `WeilDivisor.lean`
names — the divisor index set (now closed, `CurveCoheight.equivNonGeneric`), the residue-degree
weighting of `deg` (discharged over `k̄`), and the genuine bulk: AJC has no `divisorSheaf`, no
skyscraper, and no dévissage machinery at all, so those must be ported or rederived.

Stated as a number, from the measured cone: 22 files / 5,491 lines for AJCR's ChiLedger, of
which 7 files are outside its `RiemannRoch/`.  That is the cheap end of AJCR's 17.8k-line
`RiemannRoch/` by a factor of three (`UniformVanishing` needs 62 files / 16,750 lines;
`WindowFieldTransport` 139 / 39,929).  A multi-session port, but a port of sorry-free material
along identified comparisons — not a rederivation.

## Provenance

AJC-native; nothing is ported.  The three declarations below are AJC statements about AJC's own
carriers plus mathlib, written to make the audit's central claim checkable rather than asserted.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry
namespace Adelic

/-- **`finrank` does not see a universe lift.**  The fact that makes the two projects'
cohomology carriers comparable: their χ-invariants are `finrank`s, and `finrank` is invariant
under `ULift`, so an equation between dimensions transports across the universe gap even though
the carriers themselves cannot be identified by a `LinearEquiv`.

This is the load-bearing lemma of the portability audit; see the module docstring. -/
theorem finrank_uLift (k : Type u) (V : Type u) [Field k] [AddCommGroup V] [Module k V] :
    Module.finrank k (ULift.{v} V) = Module.finrank k V :=
  (ULift.moduleEquiv (R := k) (M := V)).finrank_eq

/-- **The sibling project's `Type u` cohomology carrier, written in AJC.**

AJCR's `Sheaf.HModule` is `Abelian.Ext (constModuleSheaf J R) F n` at `Type u` on a small site;
AJC's `Scheme.HModule` is the same `Ext` at `Type (u+1)` over a general site.  That this
definition elaborates *here*, at AJC's own site and coefficients, is the point: the lower
universe is available to AJC, so the `Type (u+1)` annotation in
`Cohomology/StructureSheafModuleK/Carriers.lean` is a choice for generality, not a constraint.

The `HasExt.{u}` binder is not an extra assumption at AJC's site — it is synthesised there
(`Adelic.hasExt_moduleKSheaf`); it appears as a binder only because this statement is made for
an arbitrary scheme without unfolding that instance. -/
noncomputable def extLowerUniverse (k : Type u) [Field k] (X : Scheme.{u})
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k))]
    (F : Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)) (n : ℕ) : Type u :=
  Abelian.Ext.{u}
    ((constantSheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)).obj
      (ModuleCat.of k k)) F n

/-- **`HasExt.{u}` really is synthesised at AJC's site**, so `extLowerUniverse` is inhabited
territory rather than a hypothetical.  Restated here (it is
`Adelic.CechComparisonGate.hasExt_moduleKSheaf`) so this module is self-contained as the audit's
evidence. -/
theorem hasExt_lower_of_scheme (k : Type u) [Field k] (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)) :=
  inferInstance

end Adelic
end AlgebraicGeometry
