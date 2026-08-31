/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartLocusClass
import AlgebraicJacobian.Picard.PicEtUnit

/-!
# Field points of a general test from points of its space — CHART-U(a) input 0

`informal/w4-datc-worksheet.md` §3.3 freezes `chartLocus c λ` as a **subset of a general
test** `T`: a set of *points* `t : T.left`, at each of which one reads the fibre class of
`λ` at the residue field `κ(t)`.  `informal/w4-datb-worksheet.md` §1.6 co-signs it and
lists three missing inputs (the shifted-datum constructor, the split predicate, the
descent/étale-image transports).

**There is a fourth, prior to all three, and it is why nothing in the tree implements
`chartLocus`.**  The two vocabularies the definition has to join do not meet anywhere:

* every witness/vanishing predicate in the tree is indexed by a prime of an **affine**
  base — `q : PrimeSpectrum B`, fibre field `q.asIdeal.ResidueField`
  (`Pic0ChartLocusOpen.lean:80`, `Pic0ChartLocusClass.lean:82`,
  `DivisorFamilyH1Locus.lean:363`);
* every *class* is evaluated at a field point only through a **morphism**
  `t : overSpec k K ⟶ T` for an abstract field `K` (`degAt`, `Pic0Functor.lean:54`;
  `pic0Subgroup`, `:107`).

Nothing converts a point of `T.left` into either.  This file is that conversion, and it
is deliberately kept free of the chart layer: no `chartLocus`, no `θ`, no `Σ`, no
`divRep`.

## Main declarations

* `AlgebraicGeometry.Over.testPointField t` — the residue field `κ(t)` of a point of
  `T.left`, as a `k`-algebra (`Scheme.residueField`, with the `k`-algebra structure
  pulled back along the structure morphism).
* `AlgebraicGeometry.Over.testPoint t` — **the bridge**: the field point
  `overSpec k κ(t) ⟶ T` supported at `t`.  Built from mathlib's
  `Scheme.fromSpecResidueField`, whose triangle over `Spec k` is the `Over` datum.
* `AlgebraicGeometry.Over.testPoint_base` — it really is supported at `t`: the unique
  point of `Spec κ(t)` maps to `t`.
* `AlgebraicGeometry.Over.testPoint_comp` — **naturality**, the law every well-definedness
  argument downstream runs on: for `f : T' ⟶ T` and `t : T'.left`, the field point of `t`
  followed by `f` is the field point of `f t`, up to the residue-field extension
  `κ(f t) → κ(t)` that `f` induces.  Stated as a commuting square rather than an equality
  of morphisms out of one object, because the two sides have different sources.
* `AlgebraicGeometry.Over.testPointAffine` — the affine comparison: on `overSpec k A` the
  field point of a prime `q` is the residue-field point of `q`, so every affine-indexed
  predicate of the tree can be read through `testPoint`.

## Why the affine-chart route is *not* the definition of record

The obvious route (pick an affine open `U ∋ t`, use `q := U.2.primeIdealOf t` and
`Over.fromSpecAffine T U`, `PicEtUnit.lean:61`) needs a well-definedness lemma across the
choice of `U` before it can define anything.  Mathlib's `fromSpecResidueField` is already
canonical, so the chart-independence is *free* here and the chart comparison becomes a
lemma (`testPointField_affineOpen_iso`) instead of a side condition.  That is the whole
reason this file is short.
-/

set_option autoImplicit false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Over

variable {k : Type u} [Field k]

noncomputable section

/-! ## The residue field of a point of a test object -/

/-- **The residue field of a point of a test object**, as a `k`-algebra: the scheme
residue field `κ(t)` of `Scheme.residueField`, with the `k`-algebra structure obtained by
transporting the structure morphism `T ⟶ Spec k` through `Spec.preimage`.

This is the field at which the fibre of a class over `T` is read at `t`.  It is a bare
`Type u` field with a `k`-algebra instance, which is exactly the shape `degAt` and
`pic0Subgroup` quantify over. -/
def testPointField {T : Over (Spec (.of k))} (t : T.left) : Type u :=
  T.left.residueField t

instance instFieldTestPointField {T : Over (Spec (.of k))} (t : T.left) :
    Field (testPointField t) :=
  inferInstanceAs (Field (T.left.residueField t))

/-- The `k`-algebra structure on `κ(t)`: `Spec.preimage` of the composite
`Spec κ(t) ⟶ T.left ⟶ Spec k`. -/
instance instAlgebraTestPointField {T : Over (Spec (.of k))} (t : T.left) :
    Algebra k (testPointField t) :=
  (Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)).hom.toAlgebra

lemma algebraMap_testPointField {T : Over (Spec (.of k))} (t : T.left) :
    algebraMap k (testPointField t)
      = (Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)).hom :=
  rfl

/-! ## The affine case: the test algebra also acts

Over an affine test `overSpec k A` the residue field of a point is a `κ(t)`-algebra over `A`
as well as over `k`, and the two structures form a tower.  This is what the engine-facing
predicates of the tree require — `BasicOpenCocycleDatum.HasWitnessH1Vanishing` takes
`[Algebra B L]` and `[IsScalarTower k B L]` — so without these two instances the
`testPoint`-indexed loci and the `PrimeSpectrum`-indexed loci cannot even be compared.

Both come from the same source as the `k`-structure: `Spec.preimage` of the composite
`Spec κ(t) ⟶ Spec A`, which for an affine test is the structure morphism itself. -/

section Affine

variable {A : Type u} [CommRing A] [Algebra k A]

/-- The `A`-algebra structure on the residue field of a point of an affine test: the
`Spec.preimage` of `Spec κ(t) ⟶ Spec A`.  (Over an affine test the carrier of the test object
*is* `Spec A`, so the composite is `fromSpecResidueField` alone.) -/
instance instAlgebraTestPointFieldAffine (t : (overSpec k A).left) :
    Algebra A (testPointField (T := overSpec k A) t) :=
  (Spec.preimage ((overSpec k A).left.fromSpecResidueField t)).hom.toAlgebra

lemma algebraMap_testPointFieldAffine (t : (overSpec k A).left) :
    algebraMap A (testPointField (T := overSpec k A) t)
      = (Spec.preimage ((overSpec k A).left.fromSpecResidueField t)).hom :=
  rfl

/-- **The tower `k → A → κ(t)`** on an affine test.  `Spec` of the tower identity is the
factorisation of `Spec κ(t) ⟶ Spec k` through `Spec A`, which is the `Over` triangle of the
affine test object — the same identity `isScalarTower_fieldPointAlgebra`
(`Picard/Pic0Theta.lean:358`) proves for an abstract field point, here at the canonical
residue-field point. -/
instance instIsScalarTowerTestPointFieldAffine (t : (overSpec k A).left) :
    IsScalarTower k A (testPointField (T := overSpec k A) t) := by
  refine IsScalarTower.of_algebraMap_eq' ?_
  -- Both algebra maps are `Spec.preimage` of a morphism out of `Spec κ(t)`; `Spec.preimage`
  -- is a bijection on homs, so it suffices to compare the two morphisms, and there the
  -- identity is the `Over` triangle of the affine test object: `(overSpec k A).hom` is by
  -- definition `Spec.map (algebraMap k A)`.
  have hcomp : ((overSpec k A).left.fromSpecResidueField t ≫ (overSpec k A).hom)
      = (overSpec k A).left.fromSpecResidueField t
          ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) := rfl
  -- `Spec.preimage` is injective on the composite, and the composite identity is `hcomp`.
  have hw := congrArg (fun f => (Spec.preimage f).hom) hcomp
  have hsplit : (Spec.preimage ((overSpec k A).left.fromSpecResidueField t
        ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)))).hom
      = (algebraMap A (testPointField (T := overSpec k A) t)).comp
          (algebraMap k A) := by
    have : ((overSpec k A).left.fromSpecResidueField t
          ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)))
        = Spec.map (CommRingCat.ofHom (algebraMap k A)
            ≫ Spec.preimage ((overSpec k A).left.fromSpecResidueField t)) := by
      rw [Spec.map_comp, Spec.map_preimage]
      rfl
    rw [this, Spec.preimage_map]
    rfl
  exact hw.trans hsplit

end Affine

/-! ## The field point -/

/-- **The bridge: a point of `T.left` as a field point of `T`.**

`t : T.left` names the test object morphism `overSpec k κ(t) ⟶ T` whose carrier is
mathlib's canonical `Scheme.fromSpecResidueField` and whose triangle over `Spec k` holds
by the very definition of the `k`-algebra structure on `κ(t)`.

This is the missing input 0 of CHART-U(a): with it, `{t : T.left | P (fibre of λ at
κ(t))}` is a legal `Set T.left` for any predicate `P` on classes over a field, and that
is what `chartLocus` is. -/
def testPoint {T : Over (Spec (.of k))} (t : T.left) :
    overSpec k (testPointField t) ⟶ T :=
  Over.homMk (T.left.fromSpecResidueField t)
    (Spec.map_preimage (T.left.fromSpecResidueField t ≫ T.hom)).symm

@[simp]
lemma testPoint_left {T : Over (Spec (.of k))} (t : T.left) :
    (testPoint t).left = T.left.fromSpecResidueField t :=
  rfl

/-- **The field point is supported at the point it came from**: the unique point of
`Spec κ(t)` maps to `t`.  (`Spec` of a field has a unique point, so this pins the support
completely.) -/
@[simp]
lemma testPoint_base {T : Over (Spec (.of k))} (t : T.left)
    (s : (overSpec k (testPointField t)).left) :
    (testPoint t).left.base s = t :=
  Scheme.fromSpecResidueField_apply t s

/-! ## Naturality along a morphism of tests

The law every downstream well-definedness argument runs on.  A morphism `f : T' ⟶ T`
does not send the field point of `t` to the field point of `f t` on the nose — the two
have *different sources*, `Spec κ(t)` and `Spec κ(f t)`.  What is true, and what the
transports of `w4-datb` §1.6 use, is that the square through the induced residue-field
extension `κ(f t) → κ(t)` commutes. -/

/-- **The residue-field extension a morphism of tests induces at a point**, as a
`k`-algebra map `κ(f t) → κ(t)`.  This is `Scheme.Hom.residueFieldMap` with its
`k`-algebra structure read off; it is the extension along which every fibre-field
predicate has to be invariant for a locus over `T` to pull back to one over `T'`. -/
def testPointFieldMap {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T'.left) :
    CommRingCat.of (testPointField (T := T) (f.left.base t))
      ⟶ CommRingCat.of (testPointField (T := T') t) :=
  f.left.residueFieldMap t

/-- The residue-field extension of `testPointFieldMap`, as an algebra structure: `κ(t)` is
a `κ(f t)`-algebra.  This is the shape the fibre-field invariance lemmas of
`Pic0ChartLocusFibreField.lean` consume (`hasWitnessH1Vanishing_iff_of_fieldExtension`
takes `[Algebra L L']`). -/
@[reducible]
def testPointFieldAlgebra {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T'.left) :
    Algebra (testPointField (T := T) (f.left.base t)) (testPointField (T := T') t) :=
  (testPointFieldMap f t).hom.toAlgebra

/-- **The naturality square of the bridge**: the field point of `t : T'.left` composed
with `f` is the field point of `f t` precomposed with `Spec` of the residue-field
extension.  Both sides are morphisms `overSpec k κ(t) ⟶ T` in the slice.

This is `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField` in the over category,
and it is the only law CHART-U(b)'s transports (i)/(ii) need from this file. -/
lemma testPoint_comp_left {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T'.left) :
    (testPoint t).left ≫ f.left
      = Spec.map (testPointFieldMap f t) ≫ (testPoint (T := T) (f.left.base t)).left :=
  (f.left.SpecMap_residueFieldMap_fromSpecResidueField t).symm

end

end Over

end AlgebraicGeometry
