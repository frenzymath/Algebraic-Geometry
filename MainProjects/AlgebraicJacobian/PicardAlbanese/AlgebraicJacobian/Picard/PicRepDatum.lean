/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0SigmaSheaf

/-!
# The `k'`-level representability datum `PicRepDatum` (DAT-glue → DAT-G handoff, DG-0)

The **frozen intermediate handoff shape** of the DAT-glue node
(`informal/w4-datglue-worksheet.md` §1/§3.3/§3.4; DG-0 row of §4).  The 01JJ
`RepresentableBy` assembly is honest only at a *separably closed* base `K_s` (DAT-B
staging finding, I-0248): the raw 01JJ output is a representation of `pic0TypeFunctor` at
`K_s`, not at the challenge base `k`.  The `K_s → k'` finite-level transfer (DAT-G0, the
worksheet-first mountain owned by DAT-glue; mini-spec `informal/spec-datg0.md`) lands its
output in this structure — a representation at a **finite separable** `k'/k` — which is
exactly the interface the downstream DAT-G lane (finite Galois / Speiser descent `k' → k`)
consumes.

`PicRepDatum` is deliberately the `JacobianData` shape *minus* the quasi-compactness
certificate (re-derived at `k'` by the same image-of-`DivScheme` argument, or inherited
a posteriori by DAT-J at `k`; worksheet §3.4) and *plus* the `[Algebra k k']` datum that
records how the intermediate field sits over the challenge base.

## Binder deviation from the worksheet §3.3 skeleton (RECORDED, forced by elaboration)

The worksheet §3.3 froze `structure PicRepDatum (k' : Type u) … [Algebra k k'] …` with `k`
an *ambient* `variable {k}`.  That does not elaborate for *consumers*: unlike
`JacobianData C` (where `C : Over (Spec (.of k))` pins `k`), here the explicit data pin
only `k'` (`C' : Over (Spec (.of k'))`), and `k` occurs solely inside `[Algebra k k']`, so
`PicRepDatum k' C'` leaves `k` an undetermined metavariable (`Algebra ?m k'` typeclass
stuck).  DG-0 therefore makes **`k` explicit** — `PicRepDatum k k' C'` — the minimal change
that keeps every field, instance, and the mathematical content of the frozen shape while
making `k` recoverable.  The frozen *math* (fields `J`/`rep`/`lft`, the four curve
instances, `[Algebra k k']`) is unchanged.

## The `pic0TypeFunctor`-vs-`JacobianData.rep` defeq note (worksheet §1.1, RECORDED)

The `rep` field is typed against `(pic0TypeFunctor C').RepresentableBy J`.  Since
`pic0TypeFunctor C'` is the `noncomputable abbrev`
`(pic0Functor C' ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat`
(`Pic0SigmaSheaf.lean`), this type is **definitionally** the `rep`-field type of
`JacobianData` (`JacobianData.lean`, whose `rep` is
`((pic0Functor C ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat).RepresentableBy J`).  So
when `k' = k`, a `PicRepDatum` (with quasi-compactness re-supplied) transports into a
`JacobianData` with **no massage** — recorded machine-checked by the `example` below.
This is also why DAT-glue's raw 01JJ output `pic0RepresentableByOfCharts`
(`Pic0SigmaSheaf.lean`) is *directly* a `rep`-shaped datum: no `forget₂ ⋙ forget`
adaptation, no ε⁺-shift at assembly time (the shift lives inside DAT-C's `chartValue`).

## Main declarations

* `AlgebraicGeometry.PicRepDatum k k' C'` — the frozen `k'`-level datum: representing
  object `J`, the honest `RepresentableBy` datum `rep` (no `Nonempty`, no choice), and
  the locally-of-finite-type certificate `lft` (carried from `K_s` along DAT-G0, worksheet
  §2.3/§3.3 step 3).
* `AlgebraicGeometry.PicRepDatum.homEquiv` / `homEquiv_comp` — the universal property in
  consumer form: `(T ⟶ d.J) ≃ pic0Subgroup C' T`, natural against `pic0Map` (owns the
  `forget₂ ⋙ forget` defeq once, exactly as `JacobianData.homEquiv` does).
* `AlgebraicGeometry.PicRepDatum.uniqueUpToIso` — any two `k'`-level data have canonically
  isomorphic representing objects.

This file is **statements/struct only** (DG-0, launchable pre-`divRep`): no
`divRep`-gated producer lives here.  The producer `picRepDatumKprime` (DG-4) and its
DAT-G0 transfer (DG-3) target this frozen shape.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- **The frozen `k'`-level representability datum** (worksheet §3.3/§3.4): a
representation of the degree-zero Picard functor of the base-changed curve `C'` over a
finite separable `k'/k`, together with the construction's locally-of-finite-type
certificate.  This is the DAT-glue → DAT-G handoff shape.

Deliberately the `JacobianData` shape minus quasi-compactness (re-derived at `k'`, or
inherited a posteriori by DAT-J at `k`) and plus the `[Algebra k k']` interface datum.
Properness / universal-closedness are **not** stored — they are Wave-5's problem
(DD-Q delivers only lft + qc; worksheet §2.2 boundary).  NEVER a sorried instance,
NEVER `Nonempty` + choice: producers are plain defs.

(`k` is an explicit parameter — see the module "Binder deviation" note.) -/
structure PicRepDatum (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (C' : Over (Spec (.of k'))) [IsProper C'.hom]
    [SmoothOfRelativeDimension 1 C'.hom] [GeometricallyIrreducible C'.hom] :
    Type (u + 1) where
  /-- The representing object over `k'` (the descended Jacobian-to-be). -/
  J : Over (Spec (.of k'))
  /-- The pinned universal datum: `Hom(T, J) ≃ Pic⁰(T)`, naturally in the test `T`.
  Definitionally the `rep`-field shape of `JacobianData` (module defeq note). -/
  rep : (pic0TypeFunctor C').RepresentableBy J
  /-- The locally-of-finite-type certificate, carried from the `K_s`-level glued object
  along the DAT-G0 spread (worksheet §2.3 locality-on-source, §3.3 step 3 carry). -/
  lft : LocallyOfFiniteType J.hom

namespace PicRepDatum

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
  {C' : Over (Spec (.of k'))} [IsProper C'.hom]
  [SmoothOfRelativeDimension 1 C'.hom] [GeometricallyIrreducible C'.hom]

/-- The group-object structure canonically transported from the represented
degree-zero Picard functor.  This is construction output from `d.rep`, not an
additional field of `PicRepDatum`; activate it locally with `letI := d.grpObj`.
-/
@[implicit_reducible]
noncomputable def grpObj (d : PicRepDatum k k' C') : GrpObj d.J :=
  GrpObj.ofRepresentableBy d.J
    (pic0Functor C' ⋙ forget₂ CommGrpCat GrpCat) d.rep

/-- **The universal property, consumer form**: morphisms into `d.J` are degree-zero
étale Picard classes.  Owns the `forget₂ ⋙ forget` defeq massage once — the target is
the honest subgroup carrier `pic0Subgroup C' T` (as `pic0TypeFunctor_obj` is `rfl`). -/
def homEquiv (d : PicRepDatum k k' C') {T : Over (Spec (.of k'))} :
    (T ⟶ d.J) ≃ pic0Subgroup C' T :=
  d.rep.homEquiv

/-- Naturality of `homEquiv` against the degree-zero restriction maps `pic0Map`
(element form of the `RepresentableBy` naturality, with the functor value unfolded
through `forget₂ ⋙ forget`). -/
theorem homEquiv_comp (d : PicRepDatum k k' C') {T T' : Over (Spec (.of k'))}
    (f : T' ⟶ T) (g : T ⟶ d.J) :
    d.homEquiv (f ≫ g) = pic0Map C' f (d.homEquiv g) :=
  d.rep.homEquiv_comp f g

/-- Representing objects are unique up to isomorphism (mathlib
`Functor.RepresentableBy.uniqueUpToIso`): any two `k'`-level data for the same curve have
canonically isomorphic `J`. -/
noncomputable def uniqueUpToIso (d d' : PicRepDatum k k' C') : d.J ≅ d'.J :=
  d.rep.uniqueUpToIso d'.rep

end PicRepDatum

/-! ## The `JacobianData.rep` defeq smoke test (module note; `example`-level)

Records machine-checked that the `PicRepDatum.rep` field type is *definitionally* the
`JacobianData.rep` field type at the same curve — so the `k' = k` specialization
transports into a `JacobianData` (with quasi-compactness re-supplied) with no transport
lemma.  If a mathlib bump ever breaks this, the fix belongs HERE, not in DAT-G / DAT-J. -/
section DefeqSmokeTest

variable {k' : Type u} [Field k']
  (C' : Over (Spec (.of k'))) [IsProper C'.hom]
  [SmoothOfRelativeDimension 1 C'.hom] [GeometricallyIrreducible C'.hom]

/-- The `rep` field's functor is definitionally `JacobianData.rep`'s functor. -/
example (J : Over (Spec (.of k'))) (r : (pic0TypeFunctor C').RepresentableBy J) :
    ((pic0Functor C' ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat).RepresentableBy J :=
  r

end DefeqSmokeTest

end AlgebraicGeometry
