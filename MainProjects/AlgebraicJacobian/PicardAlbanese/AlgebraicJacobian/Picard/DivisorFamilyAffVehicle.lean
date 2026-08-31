/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFace

/-!
# The widened vehicle and divisor functor: carrying a widened class to a GENERAL test

`divFamZarAff_of_forall_prime_certified_adaptation` (`…AffAssemble.lean`) is the endpoint of
the widened certificate lane, and what it returns is a class **at an affine test**
`DivFamZarAff C R n`.  Every DD-R consumer is stated against a *functor* on the whole slice
over `Spec k`, so between the lane's endpoint and its consumers sits the affine-opens limit —
the `divFamZar` vehicle of `DivisorFamilyZarVehicle.lean` — and that layer had no widened
counterpart.  This file supplies it, following the chart-typed template line for line.

## The shape, and why it is unchanged by R2

A section over a test `T` is a family of widened classes, one per affine open of `T.left`,
compatible under restriction.  R2 widened where the pieces live **on the curve**; it changed
nothing about the Zariski structure of the **base**.  So the vehicle's shape is literally the
old one with `DivFamZar` replaced by `DivFamZarAff` and `mapAlgHom` by the widened face of
`…AffFace.lean` — which is precisely why that face had to exist first.

`[IsProper C.hom]` is carried throughout: the widened base change needs it (an arbitrary affine
open's overlaps are not affine by fiat), and it is a hypothesis the DD-R lane has everywhere.

## What this file does NOT do, stated precisely

It defines the widened vehicle and proves its affine collapse.  It does **not** define the
restriction `divFamZarAff.map` along an arbitrary morphism of test objects, and therefore does
not define the widened *functor* either.  That is the remaining item of the R2 lane
(`informal/spec-dd-r.md` ADDENDUM 8 §8.3 item 2): its input is the widened form of the base-side
Zariski gluing keystone `DivFamZar.exists_glue_of_away_compat`
(`Picard/DivisorFamilyZarGlue.lean`), which should port because R2 left the base side alone —
but "should port" is a price, not a result, and nothing here assumes it.

So a consumer can today be given a widened section over an **affine** test, and the general-test
statement is still owed.  Saying which is which is the point of this paragraph: a docstring that
advertises declarations a file does not contain is its own failure mode, and this tree has
already been bitten by it once.

The comparison from the chart-typed side, `divFamZarToAffVehicle` below, does exist, and it goes
old → new only — the direction R2 asserts.  The converse is exactly what R2 says fails.

## Main declarations

* `AlgebraicGeometry.divFamZarAff` — the widened affine-opens limit at an arbitrary test.
* `divFamZarAff.eval`, `divFamZarAff.compat`, `divFamZarAff.ext` — the section API.
* `AlgebraicGeometry.divFamZarAffAffineEquiv` — on an affine test the limit collapses to
  `DivFamZarAff` of the test algebra.
* `AlgebraicGeometry.divFamZarToAffVehicle` — the comparison of vehicles, with
  `divFamZarAffAffineEquiv_toAffVehicle` for its coherence with the two affine collapses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom] {n : ℕ}

noncomputable section

/-! ## The widened affine-opens limit -/

variable (C n)

/-- **The widened locally certified divisor functor at an arbitrary test object.**  Compatible
families of *widened* locally certified divisor classes over the affine opens of `T.left`: the
value at a smaller affine open is the base change of the value at a larger one along the
section-restriction algebra map.

Identical in shape to `divFamZar` (`DivisorFamilyZarVehicle.lean`), with `DivFamZarAff` in
place of `DivFamZar` — R2 widens the curve side and leaves the base side alone.  The
compatibility is spelled with `DivFamZarAff.mapAlgHom`, which is why the explicit-map face had
to be built first: `Over.resAlgHom` carries no algebra-tower instance. -/
def divFamZarAff (T : Over (Spec (.of k))) : Type u :=
  {s : Π U : T.left.affineOpens, DivFamZarAff C Γ(T.left, U.1) n //
    ∀ (U V : T.left.affineOpens) (h : U.1 ≤ V.1),
      DivFamZarAff.mapAlgHom (Over.resAlgHom T h) (s V) = s U}

namespace divFamZarAff

variable {C n} {T : Over (Spec (.of k))}

/-- The compatibility of a section of `divFamZarAff` along an inclusion of affine opens. -/
lemma compat (s : divFamZarAff C n T) (U V : T.left.affineOpens) (h : U.1 ≤ V.1) :
    DivFamZarAff.mapAlgHom (Over.resAlgHom T h) (s.1 V) = s.1 U :=
  s.2 U V h

/-- Two sections of `divFamZarAff` agreeing at every affine open are equal. -/
@[ext]
lemma ext {s t : divFamZarAff C n T} (h : ∀ U : T.left.affineOpens, s.1 U = t.1 U) :
    s = t :=
  Subtype.ext (funext h)

variable (C n T) in
/-- Evaluation of a section of `divFamZarAff` at an affine open. -/
def eval (U : T.left.affineOpens) : divFamZarAff C n T → DivFamZarAff C Γ(T.left, U.1) n :=
  fun s => s.1 U

/-- Evaluation is projection to the component at the affine open. -/
@[simp]
lemma eval_apply (U : T.left.affineOpens) (s : divFamZarAff C n T) :
    eval C n T U s = s.1 U :=
  rfl

end divFamZarAff

/-! ## The affine comparison -/

section Affine

variable (R : Type u) [CommRing R] [Algebra k R]

/-- Evaluation at the top affine open of an affine test, composed with the `ΓSpecIso`-transport
into the test algebra: the forward direction of the widened affine comparison. -/
def divFamZarAffToAff : divFamZarAff C n (overSpec k R) → DivFamZarAff C R n :=
  fun s => DivFamZarAff.congr (Over.overSpecΓTopAlgEquiv k R) (s.1 (overSpecTopAffine R))

/-- The section of `divFamZarAff` over an affine test determined by a widened locally certified
class of the test algebra: restrict from the top affine open. -/
def divFamZarAffOfAff : DivFamZarAff C R n → divFamZarAff C n (overSpec k R) :=
  fun x =>
    ⟨fun U => DivFamZarAff.mapAlgHom
      ((Over.resAlgHom (overSpec k R) le_top).comp
        (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom) x,
      fun U V h => by rw [← DivFamZarAff.mapAlgHom_comp, ← AlgHom.comp_assoc,
        Over.resAlgHom_comp]⟩

/-- The value of `divFamZarAffOfAff` at every affine open is the restricted transported
class. -/
lemma divFamZarAffOfAff_val (x : DivFamZarAff C R n)
    (U : (overSpec k R).left.affineOpens) :
    (divFamZarAffOfAff C n R x).1 U
      = DivFamZarAff.mapAlgHom
          ((Over.resAlgHom (overSpec k R) le_top).comp
            (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom) x :=
  rfl

/-- Round trip on the vehicle side: restricting the transported top value recovers every
component, by the compatibility of the section. -/
private lemma divFamZarAffOfAff_divFamZarAffToAff (s : divFamZarAff C n (overSpec k R)) :
    divFamZarAffOfAff C n R (divFamZarAffToAff C n R s) = s := by
  refine divFamZarAff.ext fun U => ?_
  calc (divFamZarAffOfAff C n R (divFamZarAffToAff C n R s)).1 U
      = DivFamZarAff.mapAlgHom
          (((Over.resAlgHom (overSpec k R) le_top).comp
              (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom).comp
            (Over.overSpecΓTopAlgEquiv k R).toAlgHom)
          (s.1 (overSpecTopAffine R)) :=
        (DivFamZarAff.mapAlgHom_comp _ _ _).symm
    _ = DivFamZarAff.mapAlgHom (Over.resAlgHom (overSpec k R) le_top)
          (s.1 (overSpecTopAffine R)) := by
        rw [AlgHom.comp_assoc,
          show (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom.comp
              (Over.overSpecΓTopAlgEquiv k R).toAlgHom
            = AlgHom.id k Γ((overSpec k R).left, ⊤) from
            AlgHom.ext fun a => (Over.overSpecΓTopAlgEquiv k R).symm_apply_apply a,
          AlgHom.comp_id]
    _ = s.1 U := s.compat U (overSpecTopAffine R) le_top

/-- Round trip on the algebra side: the two `ΓSpecIso` transports and the trivial restriction
collapse to the identity (`DivFamZarAff.mapAlgHom_id`). -/
private lemma divFamZarAffToAff_divFamZarAffOfAff (x : DivFamZarAff C R n) :
    divFamZarAffToAff C n R (divFamZarAffOfAff C n R x) = x := by
  calc divFamZarAffToAff C n R (divFamZarAffOfAff C n R x)
      = DivFamZarAff.mapAlgHom
          ((Over.overSpecΓTopAlgEquiv k R).toAlgHom.comp
            ((Over.resAlgHom (overSpec k R) le_top).comp
              (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom)) x :=
        (DivFamZarAff.mapAlgHom_comp _ _ _).symm
    _ = DivFamZarAff.mapAlgHom (AlgHom.id k R) x := by
        rw [show Over.resAlgHom (overSpec k R) (le_top :
              (⊤ : (overSpec k R).left.Opens) ≤ (⊤ : (overSpec k R).left.Opens))
            = AlgHom.id k Γ((overSpec k R).left, ⊤) from Over.resAlgHom_rfl _ le_top,
          AlgHom.id_comp,
          show (Over.overSpecΓTopAlgEquiv k R).toAlgHom.comp
              (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom
            = AlgHom.id k R from
            AlgHom.ext fun a => (Over.overSpecΓTopAlgEquiv k R).apply_symm_apply a]
    _ = x := DivFamZarAff.mapAlgHom_id x

/-- **The widened affine comparison equivalence**: on an affine test `overSpec k R`, the
widened affine-opens limit collapses by evaluation at the terminal element `⊤` of the
affine-opens poset to the widened value `DivFamZarAff C R n` of the test algebra.

This is what makes the vehicle a genuine extension rather than a new object: the widened
certificate lane's endpoint lands in the right-hand side, so this equivalence is the step that
carries it into the vehicle.

**Exactly how far that reaches, stated so nobody over-reads it.**  It carries the endpoint into
a vehicle *section over an affine test*, and no further.  Getting from there to a general test
is `divFamZarAff.map` along an arbitrary morphism of test objects, which does **not** exist yet
(`informal/spec-dd-r.md` ADDENDUM 8 §8.3 item 2); its input is the widened form of the base-side
Zariski gluing keystone `DivFamZar.exists_glue_of_away_compat`.  So the honest reading of this
file is: the widened value now has a vehicle and collapses correctly on affine tests; the
Zariski-continuous *extension* to all tests is still owed. -/
def divFamZarAffAffineEquiv :
    divFamZarAff C n (overSpec k R) ≃ DivFamZarAff C R n where
  toFun := divFamZarAffToAff C n R
  invFun := divFamZarAffOfAff C n R
  left_inv := divFamZarAffOfAff_divFamZarAffToAff C n R
  right_inv := divFamZarAffToAff_divFamZarAffOfAff C n R

/-- The widened affine comparison evaluates at the top affine open and transports along
`Over.overSpecΓTopAlgEquiv`. -/
@[simp]
lemma divFamZarAffAffineEquiv_apply (s : divFamZarAff C n (overSpec k R)) :
    divFamZarAffAffineEquiv C n R s
      = DivFamZarAff.mapAlgHom (Over.overSpecΓTopAlgEquiv k R).toAlgHom
          (s.1 (overSpecTopAffine R)) :=
  rfl

/-- The inverse widened affine comparison restricts the transported class from the top affine
open. -/
@[simp]
lemma divFamZarAffAffineEquiv_symm_apply_val (x : DivFamZarAff C R n)
    (U : (overSpec k R).left.affineOpens) :
    ((divFamZarAffAffineEquiv C n R).symm x).1 U
      = DivFamZarAff.mapAlgHom
          ((Over.resAlgHom (overSpec k R) le_top).comp
            (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom) x :=
  rfl

end Affine

/-! ## The comparison from the chart-typed vehicle

`DivFamZar.toAff` (`…AffCompare.lean`) sends a chart-typed class to a widened one at a single
affine test, and `DivFamZar.toAff_mapAlgHom` (`…AffFace.lean`) makes that compatible with
restriction on the explicit face.  Together they lift the comparison to the *vehicles*, which is
what a consumer holding a section over a general test needs.

The direction is old → new and only old → new.  That is not a limitation of the construction: it
is the content of R2.  A widened certificate cover is an arbitrary family of affine opens, and by
`informal/spec-dd-r.md` ADDENDUM 3 §2 / ADDENDUM 4 §4.3 there is a straddling divisor at every
genus `≥ 2` that no fixed pair of `P¹` charts can confine, so no map back can exist. -/

section Compare

variable {π : C.left ⟶ P1 k} [IsAffineHom π]

variable (π) in
/-- **The comparison of vehicles**: componentwise `DivFamZar.toAff`, compatible under
restriction by `DivFamZar.toAff_mapAlgHom`.

This is the statement that makes the widened vehicle usable by a consumer that already holds a
chart-typed section: it does not have to be re-derived over the widened cover, it transports. -/
def divFamZarToAffVehicle {T : Over (Spec (.of k))} (s : divFamZar C π n T) :
    divFamZarAff C n T :=
  ⟨fun U => (s.1 U).toAff,
    fun U V h => by
      beta_reduce
      rw [← s.compat U V h, DivFamZar.toAff_mapAlgHom]⟩

/-- The value of the vehicle comparison at an affine open is the comparison of the value. -/
@[simp]
lemma divFamZarToAffVehicle_val {T : Over (Spec (.of k))} (s : divFamZar C π n T)
    (U : T.left.affineOpens) :
    (divFamZarToAffVehicle C n π s).1 U = (s.1 U).toAff :=
  rfl

/-- The comparison of vehicles is injective because it is injective on every affine-open
component. This remains only an old-to-widened statement. -/
theorem divFamZarToAffVehicle_injective {T : Over (Spec (.of k))} : Function.Injective
    (divFamZarToAffVehicle C n π (T := T)) := by
  intro s t h
  apply divFamZar.ext
  intro U
  apply DivFamZar.toAff_injective
  exact congrArg (fun x => x.1 U) h

/-- **The comparison intertwines the two affine comparisons**: on an affine test, passing to the
widened vehicle and collapsing agrees with collapsing and passing to the widened value.

Stated because it is the coherence a consumer actually uses — it says the widened vehicle's
value at an affine test is the widened value of the chart-typed one, with no ambiguity about
which of the two routes was taken. -/
lemma divFamZarAffAffineEquiv_toAffVehicle (R : Type u) [CommRing R] [Algebra k R]
    (s : divFamZar C π n (overSpec k R)) :
    divFamZarAffAffineEquiv C n R (divFamZarToAffVehicle C n π s)
      = (divFamZarAffineEquiv C π n R s).toAff := by
  rw [divFamZarAffAffineEquiv_apply, divFamZarAffineEquiv_apply,
    divFamZarToAffVehicle_val, DivFamZar.toAff_mapAlgHom]

end Compare

end

end AlgebraicGeometry
