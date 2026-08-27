/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.FGAPicRepresentability
import AlgebraicJacobian.Picard.IdentityComponent

/-!
# `Pic⁰_{C/k}` over an arbitrary base field

The identity component of the Picard scheme representing the **étale-sheafified**
relative Picard functor — the Jacobian candidate of the headline, available for
every smooth proper geometrically integral curve with **no hypothesis on
`C(k)`** (owner decision of 2026-07-28, protection I-0491).

## Why this file exists beside `Picard/Pic0AbelianVariety.lean`

That file develops `Pic⁰` for `Scheme.Pic0Scheme C = IdentityComponent
(PicScheme C)`, the identity component of the scheme representing the
*unsheafified* functor `picSharp C`. Since the owner decision, the sole producer
of that scheme's existence gate is the conditional
`Scheme.picSchemeOfHasRationalPoint`, so everything there is a statement about a
**pointed** curve. Its mathematics is not wasted — the tangent-space chain and
the dimension count are exactly the same arguments — but the *object* the
headline needs is the identity component of `PicSchemeEt C`.

Two of the four abelian-variety properties come for free at this level, and two
do not, which is the same split as in the `picSharp` development:

* `Pic0Et.grpObj` and `Pic0Et.geometricallyIrreducible` are **proved** here, from
  the unconditional `groupSchemeStructureEt` and
  `GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible`;
* `Pic0Et.isSeparated` is **proved**, from the unconditional separatedness of
  `PicSchemeEt` along the clopen immersion;
* `Pic0Et.smooth` and `Pic0Et.proper` are the two remaining obligations of the
  headline, and both are stated here as **assemblies** rather than as bare
  `sorry`s, following the run-0067 reduction of the `picSharp` side
  (`Picard/Pic0AbelianVariety.lean`). Their actual residues are one statement
  each:
  - `Pic0Et.geometricallyReduced` — Cartier's theorem in characteristic zero, a
    genuine statement in characteristic `p`. Everything else in smoothness is
    mathlib's `smooth_of_grpObj` plus the two inputs proved above;
  - `Pic0Et.universallyClosed` — Kleiman §5 Thm. `th:qpp&p`. The other two
    conjuncts of properness (separatedness, local finiteness) are proved.

  Both residues are **true statements**, in contrast with the deleted
  rational-point leaf, which was false.

## References

Kleiman, "The Picard scheme" (arXiv:math/0504020), §5 (`lem:agps`, `prp:pic0`,
Thm. `thm:tgtsp`). Blueprint: `def:pic_zero_subscheme`,
`thm:pic_zero_is_abelian_variety`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

/-- **`Pic⁰_{C/k}` over an arbitrary base field**: the identity component of the
scheme representing the étale-sheafified relative Picard functor.

Unconditional — no `[HasRationalPoint C]`, and no `[HasPicScheme C]`. The two
inputs `GroupScheme.IdentityComponent` requires are both available for
`PicSchemeEt C` without hypotheses on `C(k)`: the group structure
`groupSchemeStructureEt` (Yoneda transport of the étale sheaf's abelian-group
structure) and `instPicSchemeEtLocallyOfFiniteType` (Kleiman §4 `th:main`(1),
extracted from the representability package).

This is the Jacobian candidate of the headline. When `genus C = 0` it is
`Spec k`, with no separate construction: the tangent space `H¹(C, 𝒪_C)` is then
`0`-dimensional. -/
noncomputable def Pic0SchemeEt {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    Over (Spec (.of k)) :=
  GroupScheme.IdentityComponent (PicSchemeEt C)

namespace Pic0Et

/-- **`Pic⁰_{C/k}` is a group scheme** — PROVED, unconditionally.

The identity component of a `k`-group scheme locally of finite type is an open
and closed subgroup scheme (`GroupScheme.IdentityComponent.isOpenSubgroupScheme`,
Kleiman §5 Lem. `lem:agps`(3)), and its group structure is the one transported
onto `PicSchemeEt C` from the étale Picard sheaf by
`groupSchemeStructureEt`. Neither step needs a rational point.

Stated as `Nonempty` because `GrpObj` is data and the identity-component
substrate delivers the subgroup-scheme structure existentially. -/
theorem grpObj {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    Nonempty (GrpObj (Pic0SchemeEt C)) :=
  GroupScheme.IdentityComponent.isSubgroupHomomorphism (PicSchemeEt C)

/-- **`Pic⁰_{C/k}` is geometrically irreducible** — PROVED, unconditionally.

`GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible` (Kleiman §5
Lem. `lem:agps`): the identity component of a `k`-group scheme locally of finite
type is locally of finite type, quasi-compact and geometrically irreducible. Only
the third conjunct is taken here. -/
theorem geometricallyIrreducible {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    GeometricallyIrreducible (Pic0SchemeEt C).hom :=
  (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
    (PicSchemeEt C)).2.2

/-- `Pic⁰_{C/k}` is locally of finite type over `k` — PROVED, unconditionally
(first conjunct of `isFiniteTypeGeometricallyIrreducible`). -/
theorem locallyOfFiniteType {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    LocallyOfFiniteType (Pic0SchemeEt C).hom :=
  (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
    (PicSchemeEt C)).1

/-- **`Pic⁰_{C/k}` is smooth over `k`** — OPEN OBLIGATION, and a **true**
statement.

Kleiman §5: a group scheme locally of finite type over a field is smooth as soon
as it is geometrically reduced. Mathlib's `smooth_of_grpObj` takes exactly
`[LocallyOfFiniteType f]`, `[GrpObj (Over.mk f)]` and `[GeometricallyReduced f]`
over an arbitrary field, and the first two are proved above
(`locallyOfFiniteType`, `grpObj`). So the entire remaining content is
`GeometricallyReduced (Pic0SchemeEt C).hom` — Cartier's theorem in
characteristic zero, and a genuine characteristic-`p` statement otherwise. It
does not synthesize, and its only producer in the tree is
`Smooth.geometricallyReduced`, which would be circular.

This is the étale-formulation counterpart of `Scheme.Pic0.smooth`, and it is one
of the five obligations of the Jacobian headline. Following the run-0067 reduction
of the `picSharp` side (`Picard/Pic0AbelianVariety.lean`), it is stated here as an
**assembly** rather than an obligation: the translation argument is mathlib's and
the two other inputs are proved above, so the obligation proper is
`geometricallyReduced` below and nothing else. -/
theorem smooth_of_geometricallyReduced {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C]
    (h : GeometricallyReduced (Pic0SchemeEt C).hom) :
    Smooth (Pic0SchemeEt C).hom := by
  haveI : LocallyOfFiniteType (Pic0SchemeEt C).hom := locallyOfFiniteType C
  haveI := h
  letI : GrpObj (Over.mk (Pic0SchemeEt C).hom) := (grpObj C).some
  exact smooth_of_grpObj (Pic0SchemeEt C).hom

/-- **The sole remaining input to smoothness: geometric reducedness of
`Pic⁰_{C/k}`** — OPEN OBLIGATION, a **true** statement.

Cartier's theorem in characteristic zero; in characteristic `p` a genuine
statement (it is where `H²(C, 𝒪_C) = 0` enters on the `picSharp` side). It does
not synthesize, and its only producer in the tree is
`Smooth.geometricallyReduced`, which would be circular here.

This is the étale counterpart of `Scheme.Pic0.geometricallyReduced`. -/
theorem geometricallyReduced {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    GeometricallyReduced (Pic0SchemeEt C).hom :=
  sorry

/-- **`Pic⁰_{C/k}` is smooth over `k`** — assembly of
`smooth_of_geometricallyReduced` with its single open input. -/
theorem smooth {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    Smooth (Pic0SchemeEt C).hom :=
  smooth_of_geometricallyReduced C (geometricallyReduced C)

/-- **`Pic⁰_{C/k}` is proper over `k`** — OPEN OBLIGATION, and a **true**
statement.

Kleiman §5 Prp. `prp:pic0`: the identity component of the Picard scheme of a
smooth proper curve is proper (indeed projective) over the base. Quasi-compactness
of the identity component is available
(`GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible`, second
conjunct) and separatedness descends from `instPicSchemeEtIsSeparated` along the
clopen immersion; what is missing is universal closedness, which is where the
properness of `C` enters through the Abel map.

This is the étale-formulation counterpart of `Scheme.Pic0.proper`, and it is one
of the five obligations of the Jacobian headline. As with smoothness, it is stated
as an **assembly**: two of the three conjuncts of properness are proved, so the
obligation proper is `universallyClosed` below. -/
theorem isSeparated {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    IsSeparated (Pic0SchemeEt C).hom := by
  obtain ⟨⟨f, hopen, -⟩⟩ :=
    GroupScheme.IdentityComponent.isOpenSubgroupScheme (PicSchemeEt C)
  haveI := hopen
  change IsSeparated (GroupScheme.IdentityComponent (PicSchemeEt C)).hom
  rw [← Over.w f]
  infer_instance

/-- **The sole remaining input to properness: universal closedness of
`Pic⁰_{C/k}`** — OPEN OBLIGATION, a **true** statement.

Kleiman §5 Thm. `th:qpp&p`: a smooth proper curve is geometrically normal, so the
projectivity upgrade applies to its Picard scheme and the identity component is
proper. Separatedness (`isSeparated` above, from `instPicSchemeEtIsSeparated`
along the clopen immersion) and local finiteness (`locallyOfFiniteType`) are the
two conjuncts that are proved; this is the third.

This is the étale counterpart of `Scheme.Pic0.universallyClosed`. -/
theorem universallyClosed {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    UniversallyClosed (Pic0SchemeEt C).hom :=
  sorry

/-- **`Pic⁰_{C/k}` is proper over `k`** — assembly of the two proved conjuncts
with the single open one. -/
theorem proper {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    IsProper (Pic0SchemeEt C).hom := by
  haveI : IsSeparated (Pic0SchemeEt C).hom := isSeparated C
  haveI : LocallyOfFiniteType (Pic0SchemeEt C).hom := locallyOfFiniteType C
  haveI := universallyClosed C
  constructor

end Pic0Et

end Scheme

end AlgebraicGeometry
