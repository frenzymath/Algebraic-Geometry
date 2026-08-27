/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.Pic0Et
import AlgebraicJacobian.Picard.GroupSchemeSmoothAlgClosed
import AlgebraicJacobian.Curve.GeometricallyReduced

/-!
# Smoothness and properness of `Pic⁰` on the étale tower, reduced to `k̄`

The two remaining obligations of `Picard/Pic0Et.lean` —
`Scheme.Pic0Et.geometricallyReduced` (`:170`) and
`Scheme.Pic0Et.universallyClosed` (`:223`) — are among the **five** obligations
named under `picardJacobianWitness` (`Jacobian.lean`), which is the headline's
witness. This file reduces each of them to a statement about a **single scheme**,
and proves that both reductions are *equivalences* rather than weakenings.

**The five obligations are not independent, and the list reads as if they were.**
`Jacobian.lean`'s enumeration and this file's first draft both invited the reader to
count `geometricallyReduced` and `smoothOfRelativeDimension_genus_pic0Et` (obligation
4, `Jacobian.lean:454`) as two separate distances. They are not: obligation 4 implies
this file's reducedness target, since
`SmoothOfRelativeDimension.geometricallyReduced (genus C)` yields
`GeometricallyReduced (Pic0SchemeEt C).hom` directly. Measured here and independently
by the lane holding obligation 4 (inbox `I-1040`, `I-1039`). The arrow runs 4 ⟹ 2, so
nothing proved about the reducedness half is wasted — but a reader adding the two gets
a remaining distance that is too long by one.

The **properness** half below is genuinely independent of obligation 4, and
`quasiCompact` is the reason it is reachable at all on this tower.

## What is proved here, and what is not

**Proved.** Four reductions and their four converses, all sorry-free:

* `geometricallyReduced_of_isReduced_algebraicClosureBaseChange` — reducedness of
  the one scheme `Pic⁰ ×_{Spec k} Spec k̄` gives `GeometricallyReduced` of the
  structure morphism, hence (`smooth_of_isReduced_algebraicClosureBaseChange`)
  smoothness. No quantifier over field extensions.
* `isReduced_algebraicClosureBaseChange_of_geometricallyReduced` — the converse,
  so the hypothesis above is **equivalent** to the obligation, packaged as
  `geometricallyReduced_iff_isReduced_algebraicClosureBaseChange`.
* `universallyClosed_of_valuativeCriterion` / `proper_of_valuativeCriterion` — the
  valuative route to properness, whose `QuasiCompact` side condition is *free* on
  this tower (`quasiCompact` below).
* `proper_of_valuativeCriterion_existence` — the sharpest form: **every** side
  condition of mathlib's `IsProper.of_valuativeCriterion` is a theorem here
  (`quasiCompact`, `quasiSeparated`, `locallyOfFiniteType`) and so is the
  `Uniqueness` half of the criterion (`valuativeCriterion_uniqueness`, from
  separatedness). So `ValuativeCriterion.Existence` is *the entire* remaining content
  of properness on this tower — not one of several missing pieces.
* `valuativeCriterion_existence_of_specializingMap` — a purely **topological** route to
  that same residue, needing no valuation rings: universal specialization-lifting of
  the underlying map suffices.
* `universallyClosed_of_baseChange` and its converse
  `universallyClosed_iff_baseChange` — universal closedness is fpqc-local, so it
  too reduces to `k̄` losslessly.

**Not proved, and not weakened.** `IsReduced (Pic⁰ ×_k k̄)` and
`ValuativeCriterion.Existence` are **hypotheses** in every statement below. This
file does not witness either one for any curve; it shows that each obligation *is*
one single-scheme statement and nothing else. The two `sorry`s in `Pic0Et.lean`
stay exactly where they are — see "Honest accounting" below.

## Why this was worth doing: the picSharp side had it and the étale side did not

`Picard/Pic0AbelianVariety.lean` carries all four of these reductions for
`Scheme.Pic0Scheme C`, the identity component of the scheme representing the
*unsheafified* functor. Every one of them binds `[HasPicScheme C]`, a class with
**no instance** — its only producer is the conditional `picSchemeOfHasRationalPoint`,
and `hasRationalPoint_of_curve` was deleted as false (protection `I-0491`). So the
picSharp reductions, correct as they are, are statements about no curve.

The headline's object is `Scheme.Pic0SchemeEt C`. Its gate `[HasPicSchemeEt C]` is
unconditionally inhabited. Transporting the reductions therefore moves them from a
tower nothing inhabits onto the tower `picardJacobianWitness` actually uses.

**The transport is not automatic and half of it was recorded as unmeasured.** The
smoothness half was measured to transfer in a scratch file by a review pass (inbox
`I-0944`) and is landed here. The properness half was explicitly *not*:
`AJC.pic0av.structure` said "`universallyClosed_of_valuativeCriterion` is stated for
`Pic0Scheme` and its `QuasiCompact` side condition was proved there; whether it
carries to `Pic0SchemeEt` is unmeasured, so do not assume it". It does carry, and
`quasiCompact` below is why: the second conjunct of
`GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible` is available for
`PicSchemeEt C` with no hypothesis beyond the gate.

## Two measured negatives, recorded so they are not retried

* **`IsProper` does not fpqc-descend at this mathlib**, so properness must be assembled
  conjunct-by-conjunct after descending the closedness half — which is what
  `proper_of_baseChange` does. `MorphismProperty.DescendsAlong @IsProper (@Surjective ⊓
  @Flat ⊓ @QuasiCompact)` fails to synthesize at mathlib v4.31.

  Of `IsProper`'s three conjuncts, **two of the three descend and only `IsSeparated`
  does not**: `UniversallyClosed` via
  `descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact` and
  `LocallyOfFiniteType` via `Mathlib/AlgebraicGeometry/Morphisms/LocalFlatDescent.lean`,
  both instances; `DescendsAlong @IsSeparated (…)` is the one that fails. An earlier
  revision of this file said only the `UniversallyClosed` conjunct descends — measured
  and corrected (inbox `I-1065`).
* **Mathlib has no Cartier theorem.** There is no result in
  `Mathlib/AlgebraicGeometry` making a group scheme reduced in characteristic zero,
  and no `CharZero` hypothesis anywhere in `Mathlib/AlgebraicGeometry/Group/`. The
  reducedness input below is therefore genuine mathematics and not a missing
  `import`; a lane looking for a cheap discharge of it will not find one in the
  pinned mathlib.
* **There is no perfect-field shortcut, and this is the tempting wrong turn.**
  Mathlib's generic smoothness `Scheme.Hom.dense_smoothLocus_of_perfectField` takes
  `[PerfectField K] [IsReduced X]` — no algebraic closure — which suggests replacing
  the base change by reducedness of `Pic⁰` *itself* over a perfect field. Measured: it
  does not work. The translation half of the argument
  (`smooth_of_grpObj_of_isAlgClosed'`, transcribed from mathlib) additionally needs
  `pointEquivClosedPoint`, and elaborating it under `[PerfectField k]` alone fails to
  synthesize `IsAlgClosed k`. Generic smoothness is only one of the two inputs; the
  transitivity of translations on closed points is the other, and that one really does
  want an algebraically closed field. So the `k̄` base change is not a convenience of
  the statement — it is where the argument lives.

  Note the ring-level shape confirms this is the standard formulation:
  `Algebra.isGeometricallyReduced_field_iff` characterises geometric reducedness over a
  **field** as exactly `IsReduced (k̄ ⊗[k] A)`. The equivalence proved below is the
  scheme-level image of that iff, not a project-specific weakening. (Cite the `_field_iff`
  form, not `Algebra.isGeometricallyReduced_iff` — that one is the general-base statement,
  quantified over primes of `R` and their residue fields, and does not say what this
  sentence needs. An earlier revision of this file cited it; corrected per `I-1065`.)

## Honest accounting

**The hypotheses are not free — measured, and one of the four checks does not apply.**
Three of the four antecedents used below fail to synthesize on their own, so the
reductions are not vacuous: `IsReduced (Pic⁰ ×_k k̄)`, `UniversallyClosed` of the `k̄`
pullback projection, and `GeometricallyReduced (Pic0SchemeEt C).hom` each report
"failed to synthesize" at a probe site with the gate assumed. The fourth,
`ValuativeCriterion.Existence`, is **not a class** — it is a plain `Prop`-valued
definition, so no `infer_instance` test is meaningful for it and no such test is
claimed here. Its non-freeness rests on the ordinary observation that it is an
explicit hypothesis of the two theorems that use it and is discharged nowhere in this
project.

Every declaration in this file binds `[Scheme.HasPicSchemeEt C]`. That class *does*
have an unconditional instance, but that instance is
`(Scheme.fgaPicardRepresentability C).1` — a projection of the project's central
`sorry`. So the theorems here are axiom-clean **as implications** and
`sorry`-reachable **on instantiation** at any curve (the shape recorded in inbox
`I-0988`, `I-1020`). Nothing in this file closes a gate, and nothing in it should be
read as evidence that the two `Pic0Et` obligations are discharged: it converts each
into one named single-scheme antecedent, and proves the conversion loses nothing.

## References

Kleiman, "The Picard scheme" (arXiv:math/0504020), §5 (`lem:agps`, `prp:pic0`,
Thm. `th:qpp&p`); Stacks 01KF (valuative criterion), 02KS (fpqc descent of universal
closedness). Blueprint: `thm:pic_zero_is_abelian_variety`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

namespace Pic0Et

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C]

/-! ### Quasi-compactness, and why the properness route is open at all -/

/-- **`Pic⁰_{C/k}` is quasi-compact over `k`** — PROVED, unconditionally on the
étale tower.

Second conjunct of `GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible`
(Kleiman §5 Lem. `lem:agps`(3)), applied to `G = PicSchemeEt C`. The first and third
conjuncts are already taken in `Pic0Et.locallyOfFiniteType` and
`Pic0Et.geometricallyIrreducible`; this is the one that was never extracted.

It is the side condition of mathlib's valuative criterion, and the reason the
valuative route to properness is available on this tower and not merely on the
`picSharp` one. -/
theorem quasiCompact : QuasiCompact (Pic0SchemeEt C).hom :=
  (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
    (PicSchemeEt C)).2.1

/-! ### Smoothness: the `k̄` reduction, and that it is lossless -/

/-- **Geometric reducedness of `Pic⁰_{C/k}` from reducedness of the single scheme
`Pic⁰ ×_{Spec k} Spec k̄`.**

This is the étale counterpart of
`Scheme.Pic0.geometricallyReduced_of_isReduced_algebraicClosureBaseChange`, and it
discharges the *statement* of `Pic0Et.geometricallyReduced` from a hypothesis about
one scheme, with no quantifier over field extensions.

The route, and why it needs this project's own converse: mathlib's
`smooth_of_grpObj` wants the full `GeometricallyReduced` class, and
`GeometricallyReduced` has no `MorphismProperty.DescendsAlong` instance at v4.31, so
the general-to-`k̄` reduction is not available from mathlib. What *is* available is
`smooth_of_grpObj_of_isReduced_algebraicClosureBaseChange` (this project, taking
reducedness over `k̄` alone) composed with this project's
`Smooth.geometricallyReduced` — which is why the single-scheme form is legitimate
here even though it is not derivable in mathlib alone. Both of `Pic0Et`'s inputs to
that engine are unconditional (`locallyOfFiniteType`, `grpObj`). -/
theorem geometricallyReduced_of_isReduced_algebraicClosureBaseChange
    (h : IsReduced (Limits.pullback (Pic0SchemeEt C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    GeometricallyReduced (Pic0SchemeEt C).hom := by
  haveI : LocallyOfFiniteType (Pic0SchemeEt C).hom := locallyOfFiniteType C
  letI : GrpObj (Over.mk (Pic0SchemeEt C).hom) := (grpObj C).some
  haveI : Smooth (Pic0SchemeEt C).hom :=
    smooth_of_grpObj_of_isReduced_algebraicClosureBaseChange _ h
  infer_instance

/-- **Smoothness of `Pic⁰_{C/k}` from the same single-scheme hypothesis.** The
assembly `Pic0Et.smooth_of_geometricallyReduced` fed by the reduction above. -/
theorem smooth_of_isReduced_algebraicClosureBaseChange
    (h : IsReduced (Limits.pullback (Pic0SchemeEt C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    Smooth (Pic0SchemeEt C).hom :=
  smooth_of_geometricallyReduced C
    (geometricallyReduced_of_isReduced_algebraicClosureBaseChange C h)

/-- **The converse: the reduction above loses nothing.** `GeometricallyReduced` of
the structure morphism gives back reducedness of the `k̄` base change, since the base
change of a geometrically reduced morphism along any morphism is geometrically
reduced and `Spec k̄` is reduced.

Stated because a reduction that is not an equivalence has moved the obstruction
rather than isolated it. Here nothing moved. -/
theorem isReduced_algebraicClosureBaseChange_of_geometricallyReduced
    (h : GeometricallyReduced (Pic0SchemeEt C).hom) :
    IsReduced (Limits.pullback (Pic0SchemeEt C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) := by
  haveI := h
  infer_instance

/-- **The smoothness obligation of the headline is exactly one single-scheme
statement.** `Pic0Et.geometricallyReduced` holds iff `Pic⁰ ×_{Spec k} Spec k̄` is
reduced.

Neither side is proved here: this is the equivalence, and the mathematics owed is
Kleiman §5 `cor:sm` (on a curve `H²(C, 𝒪_C) = 0` makes the deformation functor of an
invertible sheaf unobstructed; characteristic-free *because* `dim C = 1`). -/
theorem geometricallyReduced_iff_isReduced_algebraicClosureBaseChange :
    GeometricallyReduced (Pic0SchemeEt C).hom ↔
      IsReduced (Limits.pullback (Pic0SchemeEt C).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
  ⟨isReduced_algebraicClosureBaseChange_of_geometricallyReduced C,
    geometricallyReduced_of_isReduced_algebraicClosureBaseChange C⟩

/-! ### Properness: the valuative route and the `k̄` route, both transferred -/

/-- **Universal closedness of `Pic⁰_{C/k}` from the valuative criterion** — the
transfer the board recorded as unmeasured.

`UniversallyClosed.of_valuativeCriterion` (Stacks 01KF) needs `[QuasiCompact]` of the
morphism, which is `quasiCompact` above, plus `ValuativeCriterion.Existence`, the
hypothesis. So universal closedness on this tower needs no quasi-projectivity
vocabulary — which matters, because mathlib v4.31 has none, and that absence is the
standing reason (`I-0074` Caveat 2) Kleiman's §5 `th:qpp&p` route cannot be
formalised as written.

Through representability a `Spec R`-point of `Pic⁰` is a relative Picard class, so
the lifting statement is the concrete assertion that an invertible sheaf on
`C ×_k Spec K` extends over the valuation ring — the classical content of properness. -/
theorem universallyClosed_of_valuativeCriterion
    (h : ValuativeCriterion.Existence (Pic0SchemeEt C).hom) :
    UniversallyClosed (Pic0SchemeEt C).hom := by
  haveI : QuasiCompact (Pic0SchemeEt C).hom := quasiCompact C
  exact UniversallyClosed.of_valuativeCriterion _ h

/-- **Properness of `Pic⁰_{C/k}` from the valuative existence criterion alone.**

Every other conjunct of `IsProper` is a theorem: `IsSeparated` is
`Pic0Et.isSeparated` (clopen immersion into the separated ambient `PicSchemeEt`),
`LocallyOfFiniteType` is `Pic0Et.locallyOfFiniteType`, and `QuasiCompact` is
`quasiCompact` above. So this is the sharpest properness reduction available on the
étale tower, and its hypothesis is the only one mathlib has vocabulary for.

Note that the *ambient* route is refuted and must not be retried: universal
closedness of `Pic_{C/k}` is false, since it would force `CompactSpace` on an
infinite disjoint union over `deg ∈ ℤ` (`Picard/AmbientPicNotProper.lean`). That does
not touch this statement — `Pic⁰` is quasi-compact, `Pic` is not, and `quasiCompact`
above is precisely the difference. -/
theorem proper_of_valuativeCriterion
    (h : ValuativeCriterion.Existence (Pic0SchemeEt C).hom) :
    IsProper (Pic0SchemeEt C).hom := by
  haveI : IsSeparated (Pic0SchemeEt C).hom := isSeparated C
  haveI : LocallyOfFiniteType (Pic0SchemeEt C).hom := locallyOfFiniteType C
  haveI := universallyClosed_of_valuativeCriterion C h
  constructor

/-- **The uniqueness half of the valuative criterion is FREE on this tower.**

`ValuativeCriterion` is `Existence ⊓ Uniqueness` (`ValuativeCriterion.eq`), and
`IsSeparated.valuativeCriterion` supplies the second factor from separatedness — which
is `Pic0Et.isSeparated`, a theorem. So the *whole* criterion reduces to `Existence`,
with no second obligation hiding in the uniqueness clause. -/
theorem valuativeCriterion_uniqueness :
    ValuativeCriterion.Uniqueness (Pic0SchemeEt C).hom := by
  haveI : IsSeparated (Pic0SchemeEt C).hom := isSeparated C
  exact IsSeparated.valuativeCriterion _

/-- **Quasi-separatedness is free too**, from separatedness. The third side condition of
mathlib's `IsProper.of_valuativeCriterion`. -/
theorem quasiSeparated : QuasiSeparated (Pic0SchemeEt C).hom := by
  haveI : IsSeparated (Pic0SchemeEt C).hom := isSeparated C
  infer_instance

/-- **The full valuative criterion from `Existence` alone.** -/
theorem valuativeCriterion_of_existence
    (h : ValuativeCriterion.Existence (Pic0SchemeEt C).hom) :
    ValuativeCriterion (Pic0SchemeEt C).hom :=
  ValuativeCriterion.iff.mpr ⟨h, valuativeCriterion_uniqueness C⟩

/-- **Properness directly from mathlib's `IsProper.of_valuativeCriterion`** — a second,
independent assembly of properness, and the sharpest statement of the properness
obligation available here.

All three side conditions mathlib asks for are theorems on this tower:
`QuasiCompact` (`quasiCompact`), `QuasiSeparated` (`quasiSeparated`) and
`LocallyOfFiniteType` (`Pic0Et.locallyOfFiniteType`); the `Uniqueness` half of the
criterion is `valuativeCriterion_uniqueness`. So `ValuativeCriterion.Existence` is
**the entire remaining content of properness** for `Pic⁰` on the étale tower — not one
of several missing pieces.

Compare `proper_of_valuativeCriterion` above, which reaches the same conclusion through
`UniversallyClosed`. Both are kept: this one shows the residue is exactly `Existence`,
that one exhibits the `UniversallyClosed` conjunct explicitly for the `k̄` route. -/
theorem proper_of_valuativeCriterion_existence
    (h : ValuativeCriterion.Existence (Pic0SchemeEt C).hom) :
    IsProper (Pic0SchemeEt C).hom := by
  haveI : QuasiCompact (Pic0SchemeEt C).hom := quasiCompact C
  haveI : QuasiSeparated (Pic0SchemeEt C).hom := quasiSeparated C
  haveI : LocallyOfFiniteType (Pic0SchemeEt C).hom := locallyOfFiniteType C
  exact IsProper.of_valuativeCriterion _ (valuativeCriterion_of_existence C h)

/-- **`UniversallyClosed` gives the valuative existence back** — so the two properness
hypotheses of this file are interderivable, and there is only ONE properness obligation
here rather than two.

`UniversallyClosed.eq_valuativeCriterion` states
`@UniversallyClosed = ValuativeCriterion.Existence ⊓ @QuasiCompact` as an equality of
morphism properties; the first projection is this lemma. Note what makes it usable at
all: the `QuasiCompact` factor is what one normally has to supply, and on this tower it
is free (`quasiCompact`).

CORRECTS AN EARLIER REVISION of this file, which said the valuative and `k̄` hypotheses
were "not interderivable by anything in this file". They are, in both directions, and the
sentence made the file's own result look weaker than it is. Found by a fresh-context
adversarial audit of the first two commits (inbox `I-1064`). -/
theorem valuativeCriterion_existence_of_universallyClosed
    (h : UniversallyClosed (Pic0SchemeEt C).hom) :
    ValuativeCriterion.Existence (Pic0SchemeEt C).hom := by
  have e : @UniversallyClosed = ValuativeCriterion.Existence ⊓ @QuasiCompact :=
    UniversallyClosed.eq_valuativeCriterion
  exact (e ▸ h).1

/-- **The properness residue is a single equivalence class.** The valuative existence
hypothesis, universal closedness over `k`, and universal closedness over `k̄` are all
equivalent on this tower.

So `Pic0Et.universallyClosed` has exactly ONE residue with three interchangeable
formulations — not three obligations, and not two independent routes as an earlier
revision of this file claimed. A lane may attack whichever form is most convenient
(valuation lifting, closedness over the algebraic closure, or the topological
`SpecializingMap` form below) with no loss. -/
theorem valuativeCriterion_existence_iff_universallyClosed :
    ValuativeCriterion.Existence (Pic0SchemeEt C).hom ↔
      UniversallyClosed (Pic0SchemeEt C).hom :=
  ⟨universallyClosed_of_valuativeCriterion C,
    valuativeCriterion_existence_of_universallyClosed C⟩

/-- **A purely topological route to the properness residue.**
`ValuativeCriterion.Existence.of_specializingMap`: universal specialization-lifting of
the underlying continuous map suffices. Recorded because it needs no valuation rings and
no invertible-sheaf extension argument — it is a statement about the topology of
`Pic⁰_{C/k}` — and is therefore a genuinely different attack on the same obligation. -/
theorem valuativeCriterion_existence_of_specializingMap
    (h : (topologically @SpecializingMap).universally (Pic0SchemeEt C).hom) :
    ValuativeCriterion.Existence (Pic0SchemeEt C).hom :=
  ValuativeCriterion.Existence.of_specializingMap _ h

/-- **Universal closedness descends from `k̄`** (Stacks 02KS, EGA IV₂ 2.6.4).

`Spec.map (algebraMap k k̄)` is surjective, flat and quasi-compact, and mathlib
packages the fpqc descent of `UniversallyClosed` along exactly that property as an
instance, so this is one application of
`MorphismProperty.of_pullback_snd_of_descendsAlong`.

This is the second, independent route to the properness obligation: either lift
valuations (`universallyClosed_of_valuativeCriterion`) or prove closedness over the
algebraic closure. -/
theorem universallyClosed_of_baseChange
    (h : UniversallyClosed (Limits.pullback.snd (Pic0SchemeEt C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    UniversallyClosed (Pic0SchemeEt C).hom :=
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

/-- **The converse: the `k̄` descent is lossless too.** `UniversallyClosed` is stable
under base change, so the reduction is an equivalence. -/
theorem universallyClosed_baseChange_of_universallyClosed
    (h : UniversallyClosed (Pic0SchemeEt C).hom) :
    UniversallyClosed (Limits.pullback.snd (Pic0SchemeEt C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) := by
  haveI := h
  infer_instance

/-- **The properness obligation of the headline is exactly universal closedness over
`k̄`.** Neither side is proved; this records that the descent isolates the obligation
rather than relocating it. -/
theorem universallyClosed_iff_baseChange :
    UniversallyClosed (Pic0SchemeEt C).hom ↔
      UniversallyClosed (Limits.pullback.snd (Pic0SchemeEt C).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
  ⟨universallyClosed_baseChange_of_universallyClosed C,
    universallyClosed_of_baseChange C⟩

/-- **Properness of `Pic⁰_{C/k}` from universal closedness over `k̄` alone.**

Assembled conjunct-by-conjunct rather than by descending `IsProper` itself, because
**`IsProper` does not fpqc-descend at mathlib v4.31**: `DescendsAlong @IsProper
(@Surjective ⊓ @Flat ⊓ @QuasiCompact)` fails to synthesize, while the same statement
for `@UniversallyClosed` is an instance. Measured, and recorded here so the shorter
proof is not attempted again. -/
theorem proper_of_baseChange
    (h : UniversallyClosed (Limits.pullback.snd (Pic0SchemeEt C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    IsProper (Pic0SchemeEt C).hom := by
  haveI : IsSeparated (Pic0SchemeEt C).hom := isSeparated C
  haveI : LocallyOfFiniteType (Pic0SchemeEt C).hom := locallyOfFiniteType C
  haveI := universallyClosed_of_baseChange C h
  constructor

/-! ### The abelian-variety package, on the tower the headline uses -/

/-- **`Pic⁰_{C/k}` is an abelian variety, from two single-scheme inputs over `k̄`.**

The étale counterpart of `Scheme.Pic0.isAbelianVariety`, which is stated under
`[HasPicScheme C]` — a class with no instance, hence about no curve. This version is
stated on `Pic0SchemeEt C`, the object `picardJacobianWitness` uses.

Two of the four conjuncts (`GeometricallyIrreducible`, `Nonempty (GrpObj …)`) are
unconditional theorems of `Pic0Et.lean`. The other two are supplied by the two
hypotheses, which are exactly the residues isolated above:

* `hred : IsReduced (Pic⁰ ×_{Spec k} Spec k̄)` — Kleiman §5 `cor:sm`;
* `huc : UniversallyClosed (Pic⁰ ×_{Spec k} Spec k̄)` — Kleiman §5 `th:qpp&p`.

Both are **hypotheses**: this is the assembly, not a discharge, and no curve is
exhibited for which either holds. -/
theorem isAbelianVariety_of_baseChange
    (hred : IsReduced (Limits.pullback (Pic0SchemeEt C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (huc : UniversallyClosed (Limits.pullback.snd (Pic0SchemeEt C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    IsProper (Pic0SchemeEt C).hom ∧ Smooth (Pic0SchemeEt C).hom ∧
      GeometricallyIrreducible (Pic0SchemeEt C).hom ∧
      Nonempty (GrpObj (Pic0SchemeEt C)) :=
  ⟨proper_of_baseChange C huc, smooth_of_isReduced_algebraicClosureBaseChange C hred,
    geometricallyIrreducible C, grpObj C⟩

/-- **The same package from the valuative form of properness.** Identical except that
closedness comes from lifting valuations rather than from `k̄`.

Strictly a corollary of `isAbelianVariety_of_baseChange`, via
`valuativeCriterion_existence_iff_universallyClosed` below: on this tower the two
properness hypotheses *are* interderivable, so this is a convenience form rather than an
independent assembly. An earlier revision of this docstring asserted the opposite; see
that theorem for the correction. -/
theorem isAbelianVariety_of_valuativeCriterion
    (hred : IsReduced (Limits.pullback (Pic0SchemeEt C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (hvc : ValuativeCriterion.Existence (Pic0SchemeEt C).hom) :
    IsProper (Pic0SchemeEt C).hom ∧ Smooth (Pic0SchemeEt C).hom ∧
      GeometricallyIrreducible (Pic0SchemeEt C).hom ∧
      Nonempty (GrpObj (Pic0SchemeEt C)) :=
  ⟨proper_of_valuativeCriterion C hvc,
    smooth_of_isReduced_algebraicClosureBaseChange C hred,
    geometricallyIrreducible C, grpObj C⟩

end Pic0Et

end Scheme

end AlgebraicGeometry
