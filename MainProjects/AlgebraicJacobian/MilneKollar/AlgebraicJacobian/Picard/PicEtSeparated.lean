/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import AlgebraicJacobian.Picard.FGAPicRepresentability
import AlgebraicJacobian.Picard.EtaleFieldCover
import AlgebraicJacobian.Picard.PicEtSubcanonical

/-!
# Field 3 of the seam's clause (1): separatedness comes from the group structure

`AJC.picrep.etale-rep.separated`.

## What this file is for

The seam `sorry` `Scheme.fgaPicardRepresentability`
(`Picard/FGAPicRepresentability.lean`) has as its clause (1) a **three-field**
existential:

```
∃ X, Nonempty ((PicScheme.picEt C).RepresentableBy X) ∧
       LocallyOfFiniteType X.hom ∧ IsSeparated X.hom
```

Every `AJC.picrep.etale-rep` row, and the seam's own four-input paragraph, price
the **first** field only (measured by `review-ajc`, `I-1286`: a grep for either
side conjunct across those rows returns zero hits). This file discharges the
**third** field outright, for an arbitrary smooth proper curve over an arbitrary
field, from nothing but a representation.

## Why it is not a descent obligation, which is the reusable part

The natural expectation is that separatedness travels across the field-extension
cover with the rest of the descent step. **It cannot**, with Mathlib `v4.31`, and
the lemma one would cite does not exist. Re-measured here independently of
`I-1286`, by `infer_instance` with the goal stated:

* `MorphismProperty.DescendsAlong @IsSeparated (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`
  — **fails** to synthesize;
* the diagonal route fails too, because
  `DescendsAlong @IsClosedImmersion (…)` is **also** absent (`IsClosedImmersion`
  is not a `HasRingHomProperty`, so `HasRingHomProperty.descendsAlong_flat` does
  not apply).

So a lane arriving at the descent step intending to carry separatedness over has
nothing to carry it with. The route here bypasses the descent step entirely:
`picEt` is `CommGrpCat`-valued (`Scheme.picEtCommGrp`), so **any** scheme
representing it is a group object over `Spec k` by Yoneda transport, and a group
scheme over a field is separated. No cover, no descent, no field extension.

Contrast field 2: `LocallyOfFiniteType` *does* descend freely, and at an
**arbitrary** field extension `k'/k` rather than only at the route's finite
separable cover — `Spec.map (algebraMap k k')` is `Surjective`, `Flat` and
`QuasiCompact` for any `k'/k` (one-point spectra, `k` a field, affine source), and
the `DescendsAlong` instance for `LocallyOfFiniteType` exists. An earlier revision
of this sentence said "for `k'/k` finite separable", matching two instance binders
on §4's theorem that its proof never consumed; both are deleted and the reason is
recorded there (`I-1356`), because finite separability is **input 1's** price and
pricing it here charges it twice. §4 carries that out
(`locallyOfFiniteType_of_baseChange`), so the contrast is compiler-checked rather
than asserted: **the two side conjuncts are free for opposite reasons**, and only
one of them is a descent argument. A costing that treats them as one item gets
one of them right for the wrong reason.

## The brick, and where it came from

"A group scheme over a field is separated" is **absent from Mathlib**: measured
both ways in one probe — `IsClosedImmersion η[G].left` synthesizes for
`[GrpObj G]` over `Spec K`, while `IsSeparated G.hom` **fails**. It is absent
from this project too (all three names below were new here). The sibling project
`Algebraic-Jacobian-Challenge-Rebuild` has it at
`AbelianVariety/GroupSeparated.lean`; §1–§2 are that argument, and they compiled
here unchanged against this file's single import.

Per `I-1287`: the ported statements were checked by elaborating them here, not by
reading the sibling's declaration headers — a `variable`-line binder is invisible
in a header. The sibling *file* is not Mathlib-only (its import chain runs through
`JacobianData`), so a header grep would misprice this as a cross-project
dependency; the two declarations used below need nothing from that chain, and the
evidence is that they elaborate here.

## What this does NOT do

It does not close the seam `sorry` and does not witness field 1 for any curve.
`k'`-side representability of `picEt` is still the campaign's undischarged
output, and §3's reduction takes it as a hypothesis. Nothing here is
`sorry`-reachable: all seven declarations report
`[propext, Classical.choice, Quot.sound]` against
`Scheme.fgaPicardRepresentability` as a control that reports `sorryAx`, per
`I-1251` — on this seam the axiom list discriminates and provability does not,
because `instHasPicSchemeEt` is unconditional.

**Non-vacuity, measured rather than asserted.** Dropping `rep` from §2 leaves
`IsSeparated X.hom` for an arbitrary `X`, and `infer_instance` **fails** — so the
representation is load-bearing, not decoration. And `LocallyOfFiniteType X.hom`
does **not** follow from `rep` (`exact?` fails), so §3 is not quietly absorbing
field 2: it is stated as a hypothesis because it is one.
-/

universe v₁ u₁ u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open CartesianMonoidalCategory MonObj

namespace CategoryTheory

/-! ## §1. The categorical half: the diagonal of a group object -/

variable {D : Type u₁} [Category.{v₁} D] [CartesianMonoidalCategory D]

/-- **The diagonal of a group object is the pullback of the unit along the
difference map** (Kleiman `lem:agps`(1), categorical half).

For a group object `G` in any cartesian monoidal category, the square with top
`Δ = lift (𝟙 G) (𝟙 G)`, left `toUnit G`, right the difference map
`fst ⋅ snd⁻¹ : G ⊗ G ⟶ G` and bottom the unit `η[G]` is a pullback. Here `⋅`/`⁻¹`
are the Hom-group operations (scoped in `CategoryTheory.MonObj`), so the
difference map is `lift (fst G G) (snd G G ≫ ι) ≫ μ` definitionally.

No geometry: the Hom-group calculus of `Mathlib/CategoryTheory/Monoidal/Cartesian`
does the work. Transcribed from the sibling project (see the module docstring). -/
theorem GrpObj.isPullback_diagonal (G : D) [GrpObj G] :
    IsPullback (toUnit G) (lift (𝟙 G) (𝟙 G)) η[G] (fst G G * (snd G G)⁻¹) where
  w := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, mul_inv_cancel, Hom.one_def]
  isLimit' := Nonempty.intro <| PullbackCone.IsLimit.mk _
    (fun s => s.snd ≫ fst G G)
    (fun s => toUnit_unique _ _)
    (fun s => by
      -- the cone condition says `(s.snd ≫ fst) ⋅ (s.snd ≫ snd)⁻¹ = 1` in the Hom-group
      have key : s.snd ≫ fst G G = s.snd ≫ snd G G := by
        have h := s.condition.symm
        rw [MonObj.comp_mul, GrpObj.comp_inv, toUnit_unique s.fst (toUnit _),
          ← Hom.one_def] at h
        exact mul_inv_eq_one.mp h
      exact CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simpa using key))
    (fun s m hm₁ hm₂ => by
      have := hm₂ =≫ fst G G
      simpa using this)

end CategoryTheory

namespace AlgebraicGeometry

/-! ## §2. Group schemes are separated -/

/-- **A group scheme whose unit section is a closed immersion is separated**
(Kleiman `lem:agps`(1)), over an arbitrary base scheme `S`.

The diagonal is the base change of `η[G].left` along the difference map — §1
pushed to schemes by `Over.forget` — and closed immersions are stable under base
change. **No finiteness hypothesis**: `LocallyOfFiniteType` is not needed, which
matters here because field 2 of the seam's clause (1) is exactly the finiteness
conjunct and this must not consume it. -/
theorem isSeparated_of_isClosedImmersion_one {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [IsClosedImmersion η[G].left] : IsSeparated G.hom := by
  constructor
  have sq := (GrpObj.isPullback_diagonal G).map (Over.forget S)
  exact MorphismProperty.of_isPullback sq ‹IsClosedImmersion η[G].left›

/-- **A group scheme over a field is separated** (Kleiman `lem:agps`(1)).

Over a field the closed-immersion hypothesis of
`isSeparated_of_isClosedImmersion_one` is Mathlib's own instance
(`AlgebraicGeometry/Group/Abelian.lean`). Absent from Mathlib as a whole,
though — measured both ways in one probe: `IsClosedImmersion η[G].left`
synthesizes here while `IsSeparated G.hom` does not, which is why this
`instance` is worth stating. -/
instance isSeparated_of_grpObj {K : Type u} [Field K] (G : Over (Spec (.of K)))
    [GrpObj G] : IsSeparated G.hom :=
  isSeparated_of_isClosedImmersion_one G

/-! ## §3. Field 3 of the seam's clause (1) -/

/-- **Any scheme representing `Pic_{(C/k)ét}` is separated over `k`** — field 3
of clause (1) of `Scheme.fgaPicardRepresentability`, discharged.

Smooth proper curve over an **arbitrary** field, no hypothesis on `C(k)`
(`I-0491`), and no hypothesis on `X` beyond carrying the representation.
`picEt` is `CommGrpCat`-valued, so `CommGrpObj.ofRepresentableBy` transports the
group structure of the étale Picard sheaf onto `X` by Yoneda, and §2 applies.

**The representation is load-bearing.** Dropping `rep` leaves `IsSeparated X.hom`
for an arbitrary `X` over `Spec k`, and `infer_instance` fails — so this is not a
statement that would have held anyway.

`[SmoothOfRelativeDimension 1 C.hom]` and `[IsProper C.hom]` are the binders of
`picEt`/`picEtCommGrp` themselves, needed to *name* the functor rather than by
the argument. `[GeometricallyIntegral C.hom]` — which the seam carries — is
**not** needed and is deliberately absent. -/
theorem isSeparated_of_representableBy_picEt {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X : Over (Spec (.of k))} (rep : (Scheme.PicScheme.picEt C).RepresentableBy X) :
    IsSeparated X.hom :=
  letI : CommGrpObj X :=
    CommGrpObj.ofRepresentableBy X (Scheme.picEtCommGrp C)
      (rep.ofIso (Scheme.picEtCommGrpForgetIso C))
  isSeparated_of_grpObj X

/-- **Clause (1) of the seam is a TWO-field obligation**: a representing scheme
that is locally of finite type suffices, and separatedness comes for free.

This is the form a lane closing the descent step should aim at. It removes an
obligation that was never on any board row, and it forecloses the dead end: do
**not** budget a separatedness-descent argument, because (module docstring) the
`DescendsAlong` instance it would cite does not exist in Mathlib `v4.31`.

**Not a discount on the seam.** The hypothesis is still the campaign's
undischarged output — a `k`-scheme representing `picEt C` — and this theorem
supplies no witness for it at any curve. What it changes is the *shape* of what
must be produced: two fields, not three. Field 2 stays a genuine obligation and
is not absorbed here: `LocallyOfFiniteType X.hom` does not follow from the
representation (`exact?` fails), which is why it is a hypothesis. At the real
cover it *does* descend freely, unlike field 3 — the two are free for opposite
reasons. -/
theorem seamClauseOne_of_representableBy_locallyOfFiniteType {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (h : ∃ X : Over (Spec (.of k)),
      Nonempty ((Scheme.PicScheme.picEt C).RepresentableBy X) ∧
        LocallyOfFiniteType X.hom) :
    ∃ X : Over (Spec (.of k)),
      Nonempty ((Scheme.PicScheme.picEt C).RepresentableBy X) ∧
        LocallyOfFiniteType X.hom ∧ IsSeparated X.hom := by
  obtain ⟨X, ⟨rep⟩, hlft⟩ := h
  exact ⟨X, ⟨rep⟩, hlft, isSeparated_of_representableBy_picEt C rep⟩

/-- **The campaign's own endpoint drops to two fields as well.**

`Scheme.hasPicSchemeEt_of_picSharp_representability`
(`Picard/PicEtSubcanonical.lean`) is the theorem that turns the Milne–Kollár
campaign's `picSharp`-shaped output into clause (1), and its hypothesis is a
*three*-field `picSharp` existential. The separatedness field is free there too,
and for the same reason: the transport
`Scheme.picSharp_representableBy_picEt_transport` does not move the representing
scheme, so the `picEt` representation lands on the **same** `X`, and §3 applies to
it.

This is the form to hand the campaign: it must deliver a `picSharp`-representing
scheme that is locally of finite type, and **nothing about separatedness**.

**Still not a discount on the seam.** The hypothesis is exactly what the campaign
has not delivered, and over an arbitrary `k` it is not merely unproved — there is
a refutation route mapped out for it
(`Scheme.PicScheme.not_exists_representing_picSharp_of_not_isIso`, conditional on
a comparison failure this project quotes rather than proves). What changes is only
how many fields the deliverable has. -/
theorem picEtClauseOne_of_picSharp_representableBy_locallyOfFiniteType
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (h : ∃ X : Over (Spec (.of k)),
      Nonempty ((Scheme.PicScheme.picSharp C).RepresentableBy X) ∧
        LocallyOfFiniteType X.hom) :
    ∃ X : Over (Spec (.of k)),
      Nonempty ((Scheme.PicScheme.picEt C).RepresentableBy X) ∧
        LocallyOfFiniteType X.hom ∧ IsSeparated X.hom := by
  obtain ⟨X, ⟨rep⟩, hlft⟩ := h
  have repEt := Scheme.picSharp_representableBy_picEt_transport C rep
  exact ⟨X, ⟨repEt⟩, hlft, isSeparated_of_representableBy_picEt C repEt⟩

/-! ## §4. Field 2, for contrast: it DOES descend, at the route's own cover -/

/-- **Field 2 descends along the field-extension cover.** If the base change of
`X` to `k'` is locally of finite type over `Spec k'`, then `X` is locally of
finite type over `Spec k`, for an **arbitrary** field extension `k'/k`.

Recorded here, beside field 3, because the *contrast* is the planning fact: field
2 is free by a **descent** argument (Mathlib has
`DescendsAlong @LocallyOfFiniteType (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`, and
`Spec.map (algebraMap k k')` satisfies all three by synthesis — surjectivity from
`Scheme.surjective_specMap_algebraMap`, the other two outright), while field 3 is
free *only* because descent is unavailable for it and the group structure
substitutes. A lane that priced the two conjuncts together would get one of them
right for the wrong reason.

**AN EARLIER REVISION CARRIED `[Algebra.IsSeparable k k']` AND `[Module.Finite k k']`
HERE AND CONSUMED NEITHER, and both are now deleted** (`I-1356`, `I-1362`;
reproduced before accepting: the body verbatim elaborates with the binders removed,
`lake env lean` `EXIT=0`, and the control still discriminates — with `h` dropped,
`LocallyOfFiniteType X.hom` by `infer_instance` **fails**). None of the three
ingredients needs them: surjectivity holds for any field extension because both
spectra are one-point, flatness because `k` is a field, quasi-compactness because
the source is affine.

That matters for a costing and not only for tidiness. Finite separability is
**input 1's** price — `Scheme.picEt_ext_of_pullback_agrees`
(`Picard/EtaleFieldCover.lean`) genuinely needs both binders, measured: deleting
them there gives `synthInstanceFailed`. Field 2 does not pay it, so a lane reading
this file as it stood budgeted separability **twice**. The seam docstring had
already corrected exactly this double-count once, at input 2; this was a second
instance of it one file over. The binders are removed rather than the sentence
requalified, because a binder no proof consumes keeps the trap for the next reader
however carefully the prose around it is written.

Nothing about `picEt` occurs: this is a statement about an arbitrary `k`-scheme,
and it is stated at that generality on purpose so that no reader takes it for a
fact about the Picard functor. -/
theorem locallyOfFiniteType_of_baseChange {k : Type u} [Field k] (k' : Type u)
    [Field k'] [Algebra k k']
    {X : Over (Spec (.of k))}
    (h : LocallyOfFiniteType
      (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k k'))) X.hom)) :
    LocallyOfFiniteType X.hom := by
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
    ⟨⟨Scheme.surjective_specMap_algebraMap k k', inferInstance⟩, inferInstance⟩
  exact MorphismProperty.of_pullback_fst_of_descendsAlong hQ h

end AlgebraicGeometry
