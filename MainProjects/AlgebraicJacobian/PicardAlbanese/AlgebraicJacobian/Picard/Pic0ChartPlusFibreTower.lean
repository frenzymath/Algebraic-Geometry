/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartPresentationConverse
import AlgebraicJacobian.Picard.DivisorFamilyMapAlg

/-!
# `hplus` from `hfib`: the tower transport CHART-U(b) was still owed

## What this file closes, and why it was not already closed

`Picard/Pic0ChartPresentationConverse.lean` reduces CHART-U(b)'s residue
`IsChartDatumPresentation` to `hfib` (`IsChartDatumPlusFibre`, the plus-class identity at each
residue field `κ(t)`) **plus** `hplus` — the same identity read at an arbitrary extension
`L/κ(t)` (`IsChartDatumPlusFibreAt`).  Its own docstring names the missing link:

> It does **not** silently assume the transport: `isChartDatumPlusFibreAt_of_isScalarTower` is
> the honest statement of when the `κ(t)`-level `hfib` gives the `L_t`-level one, and its
> hypothesis is a tower compatibility that the split witness's own instances supply.

**`isChartDatumPlusFibreAt_of_isScalarTower` does not exist.**  It is named in that paragraph and
nowhere else in the tree — a declaration advertised by a docstring and never written, the failure
mode memory `docstring-declaration-lists-unchecked` records.  The consequence was not cosmetic:
the sentence made `hplus` look like bookkeeping already discharged, while `hplus` was in fact the
*whole* of B-4's remaining content.  That reading is what this file removes, by proving the
transport rather than citing it.

## The mathematics, and why it is a transport and not a base-change theorem

`hplus` at `L` asks for

  `PicEtAff.map C L (picEtAffineEquiv C κ(t) μ_t) = PicEtAff.unit C L (relPicMk C L (D_L))`

where `D_L` is `D.cechPicClass` pulled to `L`, and `hfib` at `t` gives exactly that identity with
`L` replaced by `κ(t)`.  So apply the restriction homomorphism `PicEtAff.map C L` to `hfib t` and
identify both sides:

* **Left.** `PicEtAff.map_map` over the tower `κ(t) → L`: restricting twice is restricting once,
  so `map C L (map C κ(t) x) = map C L x`.  The `κ(t)`-level `map` in `hfib` is `map C κ(t)`
  applied to the fibre, which `map_id` collapses — this is where the two spellings meet.
* **Right.** `PicEtAff.map_unit`, the naturality of the plus unit: the image of a unit is the unit
  of the transported `relPic` class.  Then `relPicAlgMap_mk` turns `relPicMap` of a `relPicMk`
  into `relPicMk` of a `CechPic.map`, and `relCurveMap_comp` — the *composition* law of the
  relative-curve comparisons over `k → A → κ(t) → L`, already landed in `DivisorFamilyMapAlg` for
  the divisor functor laws — identifies the two-step pull `A → κ(t) → L` with the one-step pull
  `A → L` that `IsChartDatumPlusFibreAt` names.

So the transport is three functoriality laws and no geometry.  All three were in the tree; what
was missing is that nobody had put them together, because the docstring said somebody had.

## The tower hypothesis is real, and it is `IsScalarTower A κ(t) L`

The one thing the transport genuinely needs beyond instances already in scope is that the
`A`-algebra structure on `L` agrees with the composite `A → κ(t) → L`.  It is not automatic:
`IsChartDatumPlusFibreAt` takes `[Algebra A L]` as a *separate* instance from
`[Algebra κ(t) L]`, so a caller could in principle supply an unrelated one, and then the
right-hand sides genuinely differ (the `CechPic` class pulled along `A → L` is not the one
pulled along `A → κ(t) → L`).  Naming it as a hypothesis is therefore the honest statement, and
it is exactly the third component `towerOfResidueFieldExtension` already produces — so the
composite below needs nothing from the caller that the descent step did not already have.

## Main declarations

* `AlgebraicGeometry.isChartDatumPlusFibreAt_of_isScalarTower` — **the transport**, under the
  tower compatibility: `hfib` at `κ(t)` gives `hplus` at any `L`.  The declaration the converse
  file's docstring advertised.
* `AlgebraicGeometry.isChartDatumPresentation_of_plusFibre_tower` — **CHART-U(b)'s residue from
  `hfib` ALONE**, with no `hplus` side condition: the transport supplies it at every point and
  every extension, and `towerOfResidueFieldExtension` supplies the tower.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

noncomputable section

/-! ## The transport -/

variable (C π) in
/-- **THE TRANSPORT** — `hplus` at an arbitrary extension `L` from `hfib` at `κ(t)`.

This is the declaration `Pic0ChartPresentationConverse`'s header advertises by name and which did
not exist.  Under the tower compatibility `IsScalarTower A κ(t) L` — the one thing that is *not*
automatic, and the third component `towerOfResidueFieldExtension` already returns — the plus-class
identity at `κ(t)` implies the same identity at `L`.

Proof: apply `PicEtAff.map C L` to `hfib t`.  `PicEtAff.map_map` collapses the two-step
restriction on the left; `PicEtAff.map_unit` moves it through the unit on the right; and
`relCurveMap_comp` over `A → κ(t) → L` identifies the two-step pull of `D.cechPicClass` with the
one-step pull `IsChartDatumPlusFibreAt` names.  Three functoriality laws, no geometry. -/
theorem isChartDatumPlusFibreAt_of_isScalarTower {A : Type u} [CommRing A] [Algebra k A]
    (μ : picEt C (overSpec k A)) (D : BasicOpenCocycleDatum C A π)
    (t : (overSpec k A).left) (L : Type u) [Field L] [Algebra k L]
    [Algebra (Over.testPointField (T := overSpec k A) t) L]
    [IsScalarTower k (Over.testPointField (T := overSpec k A) t) L] [Algebra A L]
    [IsScalarTower k A L]
    [IsScalarTower A (Over.testPointField (T := overSpec k A) t) L]
    (hfib : IsChartDatumPlusFibre C π μ D) :
    IsChartDatumPlusFibreAt C π μ D t L := by
  have h := congrArg (PicEtAff.map C L) (hfib t)
  rw [PicEtAff.map_map, PicEtAff.map_unit, relPicAlgMap_mk] at h
  refine h.trans (congrArg (PicEtAff.unit C L) (congrArg (relPicMk C (overSpec k L)) ?_))
  -- the two-step pull `A → κ(t) → L` is the one-step pull `A → L`.  Rewriting the RHS's
  -- morphism into the composite keeps the `CechPic` type index fixed, which is what makes
  -- this a legal `rw` where rewriting the LHS is not (the two spellings `relCurve C κ(t)`
  -- and `(C ⊗ overSpec k κ(t)).left` are `rfl`-equal but block the motive).
  rw [← relCurveMap_comp (C := C) (R := A)
      (R' := Over.testPointField (T := overSpec k A) t) (R'' := L),
    Scheme.CechPic.map_comp]
  rfl

/-! ## The descent step with the tower restricted

The transport above cannot be fed to `hasWitnessH1Vanishing_of_isSplitWitness_at` as it stands,
and the reason is a genuine finding about that theorem's statement rather than a typing nuisance.
Its `hplus` binder reads

  `∀ (L) … (_ : Algebra A L) (_ : IsScalarTower k A L), IsChartDatumPlusFibreAt C π μ D t L`

— universally quantified over the `A`-algebra structure on `L`, with only the `k`-tower imposed.
That is **strictly stronger than the theorem consumes**: its proof obtains the `A`-structure from
its own `htow` argument and uses `hplus` at *that* instance only.  And the extra strength is not
harmless, because `IsChartDatumPlusFibreAt` mentions `relCurveMap C A L`, which depends on the
`A`-algebra structure: for an `Algebra A L` unrelated to the composite `A → κ(t) → L`, the
right-hand side pulls `D.cechPicClass` along a different morphism and the identity has no reason
to hold.  So the `∀`-form is not merely unprovable from `hfib` — it is the wrong statement, and
`hfib` cannot imply it.

This is the failure mode `price-the-instances-not-the-data` names, occurring inside a binder: the
hypothesis quantifies instances, and quantifying one instance too freely turns a provable
obligation into an unprovable one.  So the step is restated below with the tower compatibility
`IsScalarTower A κ(t) L` in the binder — exactly the third component
`towerOfResidueFieldExtension` already returns and which the landed step already destructures and
then discards.  The proof is the landed one; only the binder changes. -/

variable (C π) in
/-- **The descent step, with the `A`-tower in `hplus`'s binder** — otherwise
`hasWitnessH1Vanishing_of_isSplitWitness_at` verbatim.

The landed form asks for the plus-class identity at *every* `A`-algebra structure on `L`; this
asks for it only at those compatible with `A → κ(t) → L`, which is all its proof ever uses and
all that `hfib` can give (see the section note above).  With this binder the transport
`isChartDatumPlusFibreAt_of_isScalarTower` applies, and CHART-U(b)'s residue follows from `hfib`
alone. -/
theorem hasWitnessH1Vanishing_of_isSplitWitness_tower {A : Type u} [CommRing A] [Algebra k A]
    (μ : picEt C (overSpec k A)) (D : BasicOpenCocycleDatum C A π)
    (t : (overSpec k A).left)
    (hplus : ∀ (L : Type u) (_ : Field L) (_ : Algebra k L)
      (_ : Algebra (Over.testPointField (T := overSpec k A) t) L)
      (_ : IsScalarTower k (Over.testPointField (T := overSpec k A) t) L)
      (_ : Algebra A L) (_ : IsScalarTower k A L)
      (_ : IsScalarTower A (Over.testPointField (T := overSpec k A) t) L),
      IsChartDatumPlusFibreAt C π μ D t L)
    (h : IsSplitWitness C (picEtMap C (Over.testPoint t) μ)) :
    D.HasWitnessH1Vanishing (Over.testPointField (T := overSpec k A) t) := by
  obtain ⟨L, hLf, hLk, hLK, hLtow, hLfin, hLsep, M, hM, W, hW, hW1⟩ := h
  obtain ⟨hAL, hAtow, hATow⟩ := towerOfResidueFieldExtension (k := k) t L
  have hid : PicEtAff.unit C L (relPicMk C (overSpec k L) M)
      = PicEtAff.unit C L
        (relPicMk C (overSpec k L)
          (Scheme.CechPic.map (relCurveMap C A L) D.cechPicClass)) := by
    rw [← hM]
    exact hplus L hLf hLk hLK hLtow hAL hAtow hATow
  have hMcl : M = Scheme.CechPic.map (relCurveMap C A L) D.cechPicClass :=
    relPicMk_injective_of_subsingleton C (overSpec k L)
      (PicEtAff.unit_injective C L hid)
  refine (D.hasWitnessH1Vanishing_iff_of_fieldExtension
    (Over.testPointField (T := overSpec k A) t) L).mpr ⟨W, ?_, hW1⟩
  rw [hW, hMcl]

/-! ## CHART-U(b)'s residue from `hfib` alone -/

variable (C π) in
/-- **`IsChartDatumPresentation` FROM `hfib` ALONE** — no `hplus` side condition.

`isChartDatumPresentation_of_plusFibre` asks for `hfib` *and* the per-point identity at every
extension.  The transport above supplies the second from the first, and
`towerOfResidueFieldExtension` supplies the tower instance the transport needs, so the caller
owes only `hfib`.

**What this settles about the CHART-U(b) row.**  The row's state as of 2026-07-29 was "both
halves of the pointwise presentation are witness-free, and what remains is a `cechPicClass`
base-change identity at every extension of `κ(t)`, strictly more than `IsChartDatumPlusFibre`
asks".  That gap is now closed in the *cheap* direction the row did not expect: the extra
strength is not extra content, because the identity at `L` is the identity at `κ(t)` pushed
along `PicEtAff.map`.  `isChartDatumPlusFibreAt_self` measured the gap from below (at
`L := κ(t)` the two coincide by `Iff.rfl`); this measures it from above, and the two together say
the generalisation in `L` costs nothing.

So `IsChartDatumPresentation` — B-4's named residue, CHART-U(b)'s one remaining obligation, and
the thing `ChartLocusAffineLocal` reduces `haff` to — now rests on exactly one hypothesis:
`IsChartDatumPlusFibre`, a witness-free, `H¹`-free, divisor-free identity of plus classes at the
residue fields. -/
theorem isChartDatumPresentation_of_plusFibre_tower {A : Type u} [CommRing A] [Algebra k A]
    {μ : picEt C (overSpec k A)} {D : BasicOpenCocycleDatum C A π}
    (hfib : IsChartDatumPlusFibre C π μ D) :
    IsChartDatumPresentation C π μ D := by
  refine isChartDatumPresentation_of_plusFibre_of_converse C π hfib fun t hsplit => ?_
  refine hasWitnessH1Vanishing_of_isSplitWitness_tower C π μ D t
    (fun L _ _ _ _ _ _ _ => ?_) hsplit
  exact isChartDatumPlusFibreAt_of_isScalarTower C π μ D t L hfib

end

end AlgebraicGeometry
