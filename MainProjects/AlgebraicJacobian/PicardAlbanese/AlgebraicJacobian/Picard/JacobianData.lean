/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0Functor

/-!
# The Jacobian representability datum (Wave-4 seam D1, `JacobianData`)

The pinned representability datum for the degree-zero étale-sheafified relative Picard
functor `pic0Functor C` of the challenge curve: a representing object `J`, an honest
`Functor.RepresentableBy` datum (no `Nonempty`, no choice), and the two construction
certificates (`LocallyOfFiniteType`, `QuasiCompact`).  This is the frozen Wave-4
interface shape (`informal/w4-datum-worksheet.md` §1.1, verbatim), together with the
design-§5 consumers `grpObj` / `homEquiv` / `uniqueUpToIso` — and nothing else.

## Ownership split (binding, w5-worksheet D1)

* The **producer** `jacobianData C : JacobianData C`, the quasi-compactness certificate,
  and the discharge of the frozen `Jacobian`/`instGrpObj` sorries of `Challenge.lean`
  are **DAT-J property** (the parallel Wave-4 fleet).  None of them lives here.
* This file is the **Wave-5/6/7 consumption interface**: downstream files take
  `(d : JacobianData C)` as a section variable, activate the group structure per proof
  via `letI := d.grpObj` (or `attribute [local instance] JacobianData.grpObj`), and
  phrase every statement about `d.J`.  At DAT-J discharge time the frozen gate
  instantiates them by `exact theorem_x … (jacobianData C)` — definitionally, since
  `Jacobian C := (jacobianData C).J`.
* Extensions to this file are **additive only**; the structure shape never changes.

## The `forget₂ ⋙ forget` massage

`rep` is typed against `(pic0Functor C ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat`
so that mathlib's `GrpObj.ofRepresentableBy` applies **verbatim** with
`F := pic0Functor C ⋙ forget₂ CommGrpCat GrpCat`.  The functor value at a test `T` is
*definitionally* the coerced subgroup `↥(pic0Subgroup C T)`; `homEquiv` and
`homEquiv_comp` below own this defeq once, exposing the equivalence against
`pic0Subgroup C T` and the naturality against `pic0Map` — no consumer ever meets the
`forget₂ ⋙ forget` spelling again.

## η-defeq verdict (recon §5 "lower-order unknown", RECORDED)

**POSITIVE, with one keying caveat.**  `Over.mk d.J.hom` is definitionally equal to
`d.J` (structure-eta for `Comma`/`CostructuredArrow` plus unit-like eta for the
`Discrete PUnit` right leg): the ascription
`(d.grpObj : GrpObj (Over.mk d.J.hom))` elaborates as-is, so **no transport lemma is
ever needed**.  Caveat: bare instance *search* does not unfold `Over.mk` on its own,
so a consumer of `smooth_of_grpObj` — whose group hypothesis is `[GrpObj (Over.mk f)]`
at `f := d.J.hom` — must key the instance at the `Over.mk` spelling:
`letI : GrpObj (Over.mk d.J.hom) := d.grpObj` (pure defeq, zero cost; mathlib itself
uses the same ascription idiom in `Group/Smooth.lean`).  Instances stated directly on
`G : Over (Spec (.of K))` (e.g. `IsClosedImmersion η[G].left`) fire on `d.J` with no
massage at all.  The `example`-level smoke tests at the bottom of this file are the
machine-checked record; the T-chain (tangent lane) and S2 (`Smooth` via
`smooth_of_grpObj`) may rely on this freely.

## Main declarations

* `AlgebraicGeometry.JacobianData C` — the frozen datum structure.
* `AlgebraicGeometry.JacobianData.grpObj` — the group-object structure on `d.J` via
  `GrpObj.ofRepresentableBy` (the discharge route of the frozen `instGrpObj`).
* `AlgebraicGeometry.JacobianData.homEquiv` / `homEquiv_comp` — the universal property
  in consumer form: `(T ⟶ d.J) ≃ pic0Subgroup C T`, natural against `pic0Map`.
* `AlgebraicGeometry.JacobianData.uniqueUpToIso` / `homEquiv_uniqueUpToIso_hom` — any
  two data have canonically isomorphic representing objects (Wave-7's `baseChangeIso`
  mechanism), with the intertwining property.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **The pinned representability datum** for the degree-zero étale-sheafified relative
Picard functor of the curve `C` (w4-datum-worksheet §1.1, frozen).  Produced once, by
explicit construction, in Wave 4 (DAT-J: `jacobianData`); consumed as a section
variable everywhere else.  NEVER a sorried instance, NEVER `Nonempty` + choice.

The typing of `rep` is chosen so that `GrpObj.ofRepresentableBy` applies verbatim with
`F := pic0Functor C ⋙ forget₂ CommGrpCat GrpCat` (see `JacobianData.grpObj`). -/
structure JacobianData (C : Over (Spec (.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    Type (u + 1) where
  /-- The representing object (the Jacobian-to-be). -/
  J : Over (Spec (.of k))
  /-- The pinned universal datum: `Hom(T, J) ≃ Pic⁰(T)`, naturally in the test `T`. -/
  rep : ((pic0Functor C ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat).RepresentableBy J
  /-- Certificate from the construction (Kleiman 4.8(1) shape); NOT re-derived via the
  EGA limit criterion. -/
  locallyOfFiniteType : LocallyOfFiniteType J.hom
  /-- Certificate from the construction (a posteriori: `|J|` is the image of a
  quasi-compact divisor scheme under the Abel map).  Feeds `IsProper` (Wave 5) via
  `finite type = qc + lft`. -/
  quasiCompact : QuasiCompact J.hom

namespace JacobianData

variable {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- The group-object structure on the representing object, via mathlib's
`GrpObj.ofRepresentableBy` — this is the (definitional) discharge route of the frozen
`Jacobian.instGrpObj`.  Not a global instance here (the datum is a section variable);
activate per proof with `letI := d.grpObj` or
`attribute [local instance] JacobianData.grpObj`. -/
@[implicit_reducible]
noncomputable def grpObj (d : JacobianData C) : GrpObj d.J :=
  GrpObj.ofRepresentableBy d.J (pic0Functor C ⋙ forget₂ CommGrpCat GrpCat) d.rep

/-- **The universal property, consumer form**: morphisms into `d.J` are degree-zero
étale Picard classes.  This accessor owns the `forget₂ ⋙ forget` defeq massage once:
the target is the honest subgroup carrier `pic0Subgroup C T`. -/
def homEquiv (d : JacobianData C) {T : Over (Spec (.of k))} :
    (T ⟶ d.J) ≃ pic0Subgroup C T :=
  d.rep.homEquiv

/-- Naturality of `homEquiv` against the degree-zero restriction maps `pic0Map`
(element form of the `RepresentableBy` naturality, with the functor value unfolded
through `forget₂ ⋙ forget`). -/
theorem homEquiv_comp (d : JacobianData C) {T T' : Over (Spec (.of k))}
    (f : T' ⟶ T) (g : T ⟶ d.J) :
    d.homEquiv (f ≫ g) = pic0Map C f (d.homEquiv g) :=
  d.rep.homEquiv_comp f g

/-- Representing objects are unique up to isomorphism (mathlib
`Functor.RepresentableBy.uniqueUpToIso`): any two Jacobian data for the same curve have
canonically isomorphic `J`.  This is Wave-7's `baseChangeIso` mechanism. -/
noncomputable def uniqueUpToIso (d d' : JacobianData C) : d.J ≅ d'.J :=
  d.rep.uniqueUpToIso d'.rep

/-- The intertwining property of `uniqueUpToIso`: composing with the canonical
isomorphism commutes with the two universal properties. -/
theorem homEquiv_uniqueUpToIso_hom (d d' : JacobianData C) {T : Over (Spec (.of k))}
    (f : T ⟶ d.J) :
    d'.homEquiv (f ≫ (d.uniqueUpToIso d').hom) = d.homEquiv f := by
  have h : (d.uniqueUpToIso d').hom = d'.rep.homEquiv.symm (d.rep.homEquiv (𝟙 d.J)) := rfl
  rw [homEquiv, homEquiv, h, Functor.RepresentableBy.comp_homEquiv_symm]
  exact (d'.rep.homEquiv.apply_symm_apply _).trans (d.rep.homEquiv_eq f).symm

end JacobianData

/-! ## η-defeq smoke tests (recon §5 lower-order unknown; `example`-level, nothing
registered)

The first test records that `Over.mk d.J.hom ≡ d.J` definitionally (structure eta); the
second that instance resolution crosses it — `smooth_of_grpObj`'s hypothesis
`[GrpObj (Over.mk f)]` at `f := d.J.hom` is discharged by `letI := d.grpObj`; the third
that mathlib's `IsClosedImmersion η[d.J].left` instance fires on `d.J` as-is.  T-chain
and S2 depend on these; if a mathlib bump ever breaks them, a transport lemma must be
added HERE, not in the consumers. -/

section EtaDefeqSmokeTests

open MonObj

variable {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- Smoke test 1: `Over.mk d.J.hom` is definitionally `d.J` — the ascription
elaborates with no transport. -/
noncomputable example (d : JacobianData C) : GrpObj (Over.mk d.J.hom) := d.grpObj

/-- Smoke test 2: `smooth_of_grpObj` applies to `d.J.hom` with no transport lemma;
the group instance must be *keyed* at `Over.mk d.J.hom` (the ascribed `letI` below —
instance search does not unfold `Over.mk` on its own, but the ascription is pure
defeq). -/
example (d : JacobianData C) [GeometricallyReduced d.J.hom] : Smooth d.J.hom :=
  letI := d.locallyOfFiniteType
  letI : GrpObj (Over.mk d.J.hom) := d.grpObj
  smooth_of_grpObj d.J.hom

/-- Smoke test 3: the unit section of `d.J` is a closed immersion (mathlib's
group-scheme instance fires on `d.J` directly, with the datum's group structure in
scope). -/
example (d : JacobianData C) [GrpObj d.J] : IsClosedImmersion η[d.J].left :=
  inferInstance

end EtaDefeqSmokeTests

end AlgebraicGeometry
