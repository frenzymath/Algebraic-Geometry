/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffStrict
import AlgebraicJacobian.Picard.DivisorFamilyAffAssemble

/-!
# Clause 3 of I-0492: the widened route does not depend on the partitioned datum

Protection `I-0492` clause 3 says the chart-wise partitions of unity "have to go". The standing
measurement of that obligation (`I-0667`) is **33 textual `partition₀`/`partition₁` hits across 11
files** — a *file-level* count, and by `I-0678` (price a port by declaration reference, not by
import closure) a file-level count cannot decide the question: a module can sit in an import cone
without a single declaration of the widened route referencing it.

This module answers it at the level that matters, in two forms.

## 1. As a dependency measurement

`#eval partitionAuditReport` walks the transitive constant-dependency closure of four widened
endpoints and of two chart-typed **controls**, reporting which mention the `FinCoverData` carrier.
Measured 2026-07-29 (run 0070 s0014):

| declaration | closure | mentions `FinCoverData`? |
|---|---|---|
| `exists_affAdaptation_isCertified_of_straddling` | 4270 | **no** |
| `exists_isCertified_of_swallowing_affineOpen` | 4270 | **no** |
| `AffAdaptation.isCertified_of_swallowedBy_of_c1` | 3860 | **no** |
| `divFamZarAff_of_forall_prime_certified_adaptation` | 3024 | **no** |
| CONTROL `DivisorAdaptation.ofChartPair` | 3897 | yes — `FinCoverData`, `.mk`, `.pieces` |
| CONTROL `chartPairCoverData` | 3863 | yes — `FinCoverData`, `.mk` |

**Read the controls first.** A probe reporting "absent" on both sides measures nothing, and the
first version of this one did exactly that: it searched for the FIELD names
`partition₀`/`partition₁`/`cover₀`/`cover₁` and came back empty *including on the controls*. The
reason is worth keeping — a producer builds the structure with `FinCoverData.mk`, so the field name
never occurs in the term. **A structure field is not a constant a proof term mentions.** Probing
the carrier and its constructor makes the controls fire, and only then does a clean reading on the
widened side license a conclusion. This is trap (c) of `I-0442` in dependency form: uncalibrated
absence and real absence print identically.

## 2. As a theorem

A dependency walk is evidence about *proof terms*, which no `#print axioms` and no build checks for
you. So the content is also stated as an ordinary theorem, `isCertified_partitionFree` — see its
docstring for what is and is not being claimed.

## What this does NOT say

It does **not** say the 49-file consumer migration of `I-0667` is unnecessary. The two measurements
answer different questions: that count is about which carrier the *consumers* use, this one about
whether the widened *route* depends on the partitioned datum. Both can be true at once.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open Lean CategoryTheory

namespace AlgebraicGeometry

/-! ## The dependency measurement -/

/-- The transitive constant-dependency closure of `start`, following both a declaration's TYPE and
its `value?` (where a theorem's proof term lives).

Named `depClosure` rather than `closure`: with this project's namespaces open, `closure` collides
with the topological closure, and the collision surfaces as a baffling `TopologicalSpace Name`
instance failure rather than as an ambiguity. -/
def depClosure (env : Environment) (start : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := [start]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      let mut cs : NameSet := ci.type.getUsedConstants.foldl (·.insert ·) {}
      if let some v := ci.value? then
        cs := v.getUsedConstants.foldl (·.insert ·) cs
      for c in cs.toList do
        if !seen.contains c then stack := c :: stack
  return seen

/-- What a dependency on the partitioned datum looks like. NOT the field names — see §1 of the
module docstring for why probing those reports empty even on the controls. -/
def partitionAuditTargets : List Name :=
  [``FinCoverData, ``FinCoverData.mk, ``FinCoverData.cover₀, ``FinCoverData.cover₁,
   ``FinCoverData.pieces]

/-- The widened endpoints, which must come back clean. -/
def partitionAuditWidened : List Name :=
  [``exists_affAdaptation_isCertified_of_straddling,
   ``exists_isCertified_of_swallowing_affineOpen,
   ``AffAdaptation.isCertified_of_swallowedBy_of_c1,
   ``divFamZarAff_of_forall_prime_certified_adaptation]

/-- The chart-typed controls, which MUST show a dependency. If they do not, the audit is
uncalibrated and its clean readings mean nothing. -/
def partitionAuditControls : List Name :=
  [``DivisorAdaptation.ofChartPair, ``chartPairCoverData]

/-- One row of the audit: the closure size and which targets occur in it. -/
def partitionAuditRow (env : Environment) (label : Name) : Name × Nat × List Name :=
  let cl := depClosure env label
  (label, cl.size, partitionAuditTargets.filter cl.contains)

/-- The audit report; run it with `#eval partitionAuditReport`. Widened endpoints first, then the
controls. -/
def partitionAuditReport : CoreM (List (Name × Nat × List Name)) := do
  let env ← getEnv
  return (partitionAuditWidened ++ partitionAuditControls).map (partitionAuditRow env)

/-! ## The mathematical content -/

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R] [Algebra k R]

/-- **The widened certificate is a statement about affine opens alone.**

`AffCoverData` carries `m`, `pieces`, `isAffineOpen` and the joint `cover` — no partition of unity,
no `Sum` index, no chart typing (`DivisorFamilyAffCover.lean`). So every clause of
`AffAdaptation.IsCertified` is quantified over that data and *cannot* mention a partition: there is
none to mention.

**This theorem is proved by `id`, and that is deliberate — read it as a type-level assertion, not
as mathematical content.** Its value is that the statement elaborates: the certificate predicate
can be written down, at an arbitrary widened cover and adaptation, with no partition anywhere in
scope. What would falsify clause 3 is not a false theorem here but a *different* signature — an
`IsCertified` whose binders needed `FinCoverData` — and that is what the `#eval` audit above
measures on the actual proof terms. The two together are the honest evidence; neither alone is.

Contrast the chart-typed side, where `FinCoverData` must *derive* `cover₀`/`cover₁` from two
partitions before any clause can be stated. That derivation is what the widening deleted. -/
theorem isCertified_partitionFree {n : ℕ} {D : AffCoverData C R}
    {d : (relCurve C R).LocalEquations} (A : AffAdaptation D d) (h : A.IsCertified n) :
    A.IsCertified n :=
  h

end AlgebraicGeometry
