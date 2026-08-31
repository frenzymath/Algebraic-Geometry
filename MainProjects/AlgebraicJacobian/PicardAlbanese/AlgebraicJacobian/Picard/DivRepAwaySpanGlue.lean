/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZarGlue
import AlgebraicJacobian.Picard.DivisorFamilyZarVehicle

/-!
# The away-span glue of locally certified classes at CANONICAL carriers

The S5b keystone `DivFamZar.exists_glue_of_away_compat`
(`Picard/DivisorFamilyZarGlue.lean`) glues over an away cover whose carriers `S i` and
overlap carriers `T i j` are supplied *as instance data* — eight
`Algebra`/`IsScalarTower` fields per index pair.  Every consumer that starts from a
bare spanning family `f : Fin m → S`, which is what the atlas factorization
`divScheme_exists_chartFactor` (`Picard/DivSchemeAtlasFactor.lean`) hands back, must
build that pack itself before it can glue anything.

This file builds the pack once, at the **canonical** carriers
`Localization.Away (f p)` and `Localization.Away (f p * f q)`, and restates the two
keystones so that a consumer holding only `f` and `Ideal.span (Set.range f) = ⊤` can
use them:

* `AlgebraicGeometry.DivFamZar.awayMulOfDvd` — the comparison `k`-algebra map
  `Localization.Away a →ₐ[k] Localization.Away f` attached to a factorization
  `a * b = f`, from `IsLocalization.Away.lift` at the unit
  `algebraMap S (Localization.Away f) a`; `awayMulLeft`/`awayMulRight` are its two
  instances at the overlap of a pair.
* `AlgebraicGeometry.DivFamZar.exists_glue_of_awaySpan` — **existence**: locally
  certified classes `F p` over `Localization.Away (f p)`, agreeing after base change
  along `awayMulLeft`/`awayMulRight` into each `Localization.Away (f p * f q)`, glue to
  a class over `S` restricting to every `F p`.
* `AlgebraicGeometry.DivFamZar.eq_of_awaySpan_eq` — **separation** in the same
  spelling.
* `AlgebraicGeometry.DivFamZar.existsUnique_glue_of_awaySpan` — the two combined, in
  the `∃!` form the DDR-9 forward map's choice bookkeeping consumes (`w4-ddr9`
  worksheet §3.4): it is what makes a glued value independent of every choice made in
  producing the cover.

Two design points, both deliberate.  The overlap carrier is the canonical
`Localization.Away (f p * f q)` rather than a tensor product, which is what makes the
instance pack derivable at all: it receives both away carriers by
`IsLocalization.Away.lift` against the divisibility witnesses `f p ∣ f p * f q` and
`f q ∣ f p * f q`, and the tower coherences then reduce to
`IsLocalization.Away.lift_comp` plus the landed `isScalarTower_left_of_isScalarTower`.
And the *statements* are spelled with `DivFamZar.mapAlgHom` along an explicit `AlgHom`
rather than with the instance-parameterized `DivFamZar.mapAlg`: a caller then needs no
algebra instances in scope at all, and the face-change bridge
`DivFamZar.mapAlgHom_eq_mapAlg` moves each hypothesis onto the instance face inside the
proof, where the pack is available.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {S : Type u} [CommRing S] [Algebra k S]
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}

namespace DivFamZar

/-! ## The comparison map into a canonical away localization at a multiple -/

/-- **The comparison map of a factorization**: for `a * b = f`, the canonical away
localization at `f` receives the one at `a`, because `algebraMap S (Localization.Away f) a`
is a unit (`IsLocalization.Away.isUnit_of_dvd`) so `IsLocalization.Away.lift` applies.
It is a map of `k`-algebras because both structure maps factor through `S`. -/
noncomputable def awayMulOfDvd (f a b : S) (h : a * b = f) :
    Localization.Away a →ₐ[k] Localization.Away f :=
  { IsLocalization.Away.lift a (S := Localization.Away a)
      (g := algebraMap S (Localization.Away f))
      (IsLocalization.Away.isUnit_of_dvd (x := f) ⟨b, h.symm⟩) with
    commutes' := fun x => by
      rw [IsScalarTower.algebraMap_apply k S (Localization.Away a)]
      change IsLocalization.Away.lift a _ (algebraMap S (Localization.Away a) _) = _
      rw [IsLocalization.Away.lift_eq]
      exact (IsScalarTower.algebraMap_apply k S (Localization.Away f) x).symm }

/-- **The comparison map is the localization lift**: it agrees with
`algebraMap S (Localization.Away f)` on `S`, which characterizes it. -/
@[simp]
theorem awayMulOfDvd_algebraMap (f a b : S) (h : a * b = f) (x : S) :
    awayMulOfDvd (k := k) f a b h (algebraMap S (Localization.Away a) x)
      = algebraMap S (Localization.Away f) x :=
  IsLocalization.Away.lift_eq a
    (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away f) (x := f) ⟨b, h.symm⟩) x

set_option maxHeartbeats 3200000 in
-- The composite is checked against the `IsScalarTower` structure map of the localization,
-- which unfolds the section-ring algebra tower on both sides; the defeq check is well
-- past the default budget (measured: over 800000 heartbeats).
/-- **The comparison map is a map over the base ring**: composing the structure map
`S → Localization.Away a` with the comparison into `Localization.Away f` gives the
structure map `S → Localization.Away f`.  This is the form consumed when a class pulled
back from `S` is compared across two different away localizations. -/
theorem awayMulOfDvd_toAlgHom (f a b : S) (h : a * b = f) (x : S) :
    awayMulOfDvd (k := k) f a b h (IsScalarTower.toAlgHom k S (Localization.Away a) x)
      = IsScalarTower.toAlgHom k S (Localization.Away f) x :=
  IsLocalization.Away.lift_eq a
    (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away f) (x := f) ⟨b, h.symm⟩) x

section Pack

variable {m : ℕ} (f : Fin m → S)

/-- The left comparison into the canonical overlap carrier of the pair `(p, q)`. -/
noncomputable abbrev awayMulLeft (p q : Fin m) :
    Localization.Away (f p) →ₐ[k] Localization.Away (f p * f q) :=
  awayMulOfDvd (f p * f q) (f p) (f q) rfl

/-- The right comparison into the canonical overlap carrier of the pair `(p, q)`. -/
noncomputable abbrev awayMulRight (p q : Fin m) :
    Localization.Away (f q) →ₐ[k] Localization.Away (f p * f q) :=
  awayMulOfDvd (f p * f q) (f q) (f p) (mul_comm _ _)

end Pack

/-! ## Existence -/

set_option maxHeartbeats 1600000 in
-- Eight `Algebra`/`IsScalarTower` fields are discharged in the body at the canonical
-- carriers, and each unifies the section-ring algebra towers of two away localizations
-- at once; the defeq checks exceed the default budget (as in
-- `divFamZar.exists_isGlueValue` and `DivRepClassifyZar.exists_isDivRepClassify`).
/-- **The away-span glue at canonical carriers**: locally certified divisor classes over
the canonical away localizations of a finite spanning family `f`, agreeing after base
change along the two comparison maps into each canonical overlap localization
`Localization.Away (f p * f q)`, glue to a class over `S` restricting to each of them.

This is the S5b keystone `DivFamZar.exists_glue_of_away_compat` with its instance pack
discharged at the canonical carriers: the overlap carrier receives both away carriers by
the comparison maps, the `S`-towers are `awayMulOfDvd_algebraMap`, and the `k`-towers are
the `AlgHom` commutation of the same maps.  Hypothesis and conclusion are stated on the
explicit `mapAlgHom` face and moved onto the instance face by the face-change bridge
`mapAlgHom_eq_mapAlg`, so no caller needs the pack. -/
theorem exists_glue_of_awaySpan {m : ℕ} (f : Fin m → S)
    (hspan : Ideal.span (Set.range f) = ⊤)
    (F : ∀ p : Fin m, DivFamZar C (Localization.Away (f p)) π n)
    (hcompat : ∀ p q : Fin m,
      DivFamZar.mapAlgHom (awayMulLeft (k := k) f p q) (F p)
        = DivFamZar.mapAlgHom (awayMulRight (k := k) f p q) (F q)) :
    ∃ F₀ : DivFamZar C S π n, ∀ p : Fin m,
      DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f p))) F₀ = F p := by
  classical
  -- the overlap carrier receives both away carriers, by the two comparison maps
  letI algL : ∀ p q : Fin m, Algebra (Localization.Away (f p))
      (Localization.Away (f p * f q)) := fun p q =>
    (awayMulLeft (k := k) f p q).toRingHom.toAlgebra
  letI algR : ∀ p q : Fin m, Algebra (Localization.Away (f q))
      (Localization.Away (f p * f q)) := fun p q =>
    (awayMulRight (k := k) f p q).toRingHom.toAlgebra
  -- the `S`-towers: each comparison map is the localization lift
  haveI towSL : ∀ p q : Fin m, IsScalarTower S (Localization.Away (f p))
      (Localization.Away (f p * f q)) := fun p q =>
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (awayMulOfDvd_algebraMap (k := k) (f p * f q) (f p) (f q) rfl x).symm)
  haveI towSR : ∀ p q : Fin m, IsScalarTower S (Localization.Away (f q))
      (Localization.Away (f p * f q)) := fun p q =>
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (awayMulOfDvd_algebraMap (k := k) (f p * f q) (f q) (f p)
        (mul_comm _ _) x).symm)
  -- the `k`-towers: the comparison maps are maps of `k`-algebras
  haveI towkL : ∀ p q : Fin m, IsScalarTower k (Localization.Away (f p))
      (Localization.Away (f p * f q)) := fun p q =>
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact ((awayMulLeft (k := k) f p q).commutes x).symm)
  haveI towkR : ∀ p q : Fin m, IsScalarTower k (Localization.Away (f q))
      (Localization.Away (f p * f q)) := fun p q =>
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact ((awayMulRight (k := k) f p q).commutes x).symm)
  -- the keystone, with the hypothesis transported onto the instance face.  The
  -- compatibility proof is deferred with `?_` so that the carrier families are fixed
  -- before it elaborates (otherwise `mapAlg`'s instance arguments stay metavariables).
  have hkey : ∀ l l' : ULift.{u} (Fin m),
      DivFamZar.mapAlg (C := C) (π := π)
          (Localization.Away (f l.down * f l'.down)) n (F l.down)
        = DivFamZar.mapAlg (C := C) (π := π)
          (Localization.Away (f l.down * f l'.down)) n (F l'.down) := by
    intro l l'
    rw [← DivFamZar.mapAlgHom_eq_mapAlg (awayMulLeft (k := k) f l.down l'.down)
        (fun _ => rfl),
      ← DivFamZar.mapAlgHom_eq_mapAlg (awayMulRight (k := k) f l.down l'.down)
        (fun _ => rfl)]
    exact hcompat l.down l'.down
  -- the keystone indexes over `Type u`, so the cover is reindexed by `ULift (Fin m)`
  obtain ⟨F₀, hF₀⟩ := DivFamZar.exists_glue_of_away_compat
    (fun l : ULift.{u} (Fin m) => f l.down)
    (fun l : ULift.{u} (Fin m) => Localization.Away (f l.down))
    (fun l l' : ULift.{u} (Fin m) => Localization.Away (f l.down * f l'.down))
    (by
      rw [show (Set.range fun l : ULift.{u} (Fin m) => f l.down) = Set.range f from
        ULift.down_surjective.range_comp f]
      exact hspan)
    (fun l => F l.down) hkey
  refine ⟨F₀, fun p => ?_⟩
  have hF₀p := hF₀ (ULift.up p)
  rw [DivFamZar.mapAlgHom_eq_mapAlg (IsScalarTower.toAlgHom k S (Localization.Away (f p)))
    (fun _ => rfl)]
  exact hF₀p

/-! ## Separation -/

/-- **Separation in the canonical-carrier spelling**: two locally certified classes over
`S` agreeing after base change to every `Localization.Away (f p)` of a finite spanning
family agree — `DivFamZar.eq_of_away_eq` at the canonical carriers, whose instance pack
is the ambient one, with the hypothesis read on the explicit `mapAlgHom` face. -/
theorem eq_of_awaySpan_eq {ι : Type} [Finite ι] (f : ι → S)
    (hspan : Ideal.span (Set.range f) = ⊤)
    {F G : DivFamZar C S π n}
    (h : ∀ p : ι,
      DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f p))) F
        = DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f p))) G) :
    F = G := by
  -- the keystone indexes over `Type u`, so the cover is reindexed by `ULift ι`
  refine DivFamZar.eq_of_away_eq (fun l : ULift.{u} ι => f l.down)
    (fun l : ULift.{u} ι => Localization.Away (f l.down))
    (by
      rw [show (Set.range fun l : ULift.{u} ι => f l.down) = Set.range f from
        ULift.down_surjective.range_comp f]
      exact hspan)
    (fun l => ?_)
  rw [← DivFamZar.mapAlgHom_eq_mapAlg
      (IsScalarTower.toAlgHom k S (Localization.Away (f l.down))) (fun _ => rfl) F,
    ← DivFamZar.mapAlgHom_eq_mapAlg
      (IsScalarTower.toAlgHom k S (Localization.Away (f l.down))) (fun _ => rfl) G]
  exact h l.down

/-! ## The `∃!` form -/

/-- **The away-span glue, uniquely**: the glued class of `exists_glue_of_awaySpan` is the
unique class over `S` restricting to the given family, by `eq_of_awaySpan_eq`.

**Note what this `∃!` does and does not say.**  It pins the value against *one* cover `f` and
*one* family `F`: it says the glue is determined by that data, not that it is independent of
the data.  Independence across two different covers is a genuinely separate statement — for
the DDR-9 forward map it is `divRepPullGlue_eq_of_chartFactors`
(`Picard/DivRepAffPullIndep.lean`), and it needs the overlap agreement, not just separation.
An earlier version of this docstring claimed the `∃!` made that argument unnecessary; it does
not, and a fresh-context review caught the overclaim. -/
theorem existsUnique_glue_of_awaySpan {m : ℕ} (f : Fin m → S)
    (hspan : Ideal.span (Set.range f) = ⊤)
    (F : ∀ p : Fin m, DivFamZar C (Localization.Away (f p)) π n)
    (hcompat : ∀ p q : Fin m,
      DivFamZar.mapAlgHom (awayMulLeft (k := k) f p q) (F p)
        = DivFamZar.mapAlgHom (awayMulRight (k := k) f p q) (F q)) :
    ∃! F₀ : DivFamZar C S π n, ∀ p : Fin m,
      DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k S (Localization.Away (f p))) F₀ = F p := by
  obtain ⟨F₀, hF₀⟩ := exists_glue_of_awaySpan f hspan F hcompat
  exact ⟨F₀, hF₀, fun F₁ hF₁ =>
    eq_of_awaySpan_eq f hspan (fun p => (hF₁ p).trans (hF₀ p).symm)⟩

end DivFamZar

end AlgebraicGeometry
