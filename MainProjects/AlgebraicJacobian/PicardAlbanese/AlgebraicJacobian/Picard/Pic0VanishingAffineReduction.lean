/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0VanishingRoute
import AlgebraicJacobian.Picard.PicEtUnit

/-!
# THE `∀ T` BINDER OF THE `pic⁰` VANISHING IS A STATEMENT ABOUT TEST RINGS

Two independent routes to a producer of `(pic0TypeFunctor C).RepresentableBy` meet at one
hypothesis, and that hypothesis has **no producer** anywhere in the project:

  `hvan : ∀ S : Over (Spec k), Subsingleton (pic0Subgroup C S)`

* `Pic0VanishingRoute.jacobianData_of_subsingleton` consumes it and returns a `JacobianData C`
  with no atlas, no chart certificate, no coverage and no divisor representability;
* `Pic0ChartSeamPairDecided.isLocallySurjective_abelSigmaChartZero_iff` proves the seam's
  *coverage* antecedent at parameter `0` is **equivalent** to it.

So `hvan` is not one route's private input; it is where the two routes' costs coincide.

**What this file does.** It replaces the `∀ T` quantifier — over all objects of
`Over (Spec k)`, i.e. over all `k`-schemes — by a quantifier over commutative `k`-algebras,
and it proves the replacement is an **equivalence**, not a sufficient condition.

## Why the landed reduction does not already do this

`Pic0VanishingRoute` reduces the quantifier for `picEt` (`subsingleton_picEt_of_affine`) and
proves that one is an equivalence (`subsingleton_picEtAff_of_forall`).  Its degree-zero
consequence `subsingleton_pic0_of_affine` runs **one way only**, and its own docstring says
why that is not a repair: the hypothesis is vanishing of the whole `picEt`, which is *strictly
stronger* and false at any curve carrying a class of nonzero degree — including `ℙ¹`, where
`pic⁰` does vanish.  So the landed chain cannot be applied to the hypothesis anyone needs, in
either direction.  The reduction here is for `pic0Subgroup` directly and never mentions
`picEt` vanishing.

## The mechanism, and why it needed no new mathematics

Separation, not gluing.  `Subsingleton` is an equality statement, so only the *ext* half of
the descent is used: the affine opens of `T.left` give a morphism-form open cover of `T` by
the affine-open test objects `Over.fromSpecAffine T U : overSpec k Γ(T.left, U) ⟶ T`
(`Picard/PicEtUnit.lean:60`), each an open immersion on the left because
`IsAffineOpen.fromSpec` is; and `pic0Subgroup_ext_of_cover`
(`Picard/PicEtCoverBridge.lean:342`) says two degree-zero classes agreeing on every member
agree.  Under the affine hypothesis each pair of restrictions agrees for free.

The `∃!`-gluing bridge in the same file (`pic0Subgroup_existsUnique_of_cover`) is *not* used:
producing a class from local data would need the compatibility datum, and a subsingleton
statement never has to produce anything.  That asymmetry is the whole reason this is cheap
where the corresponding representability statement is not.

## What the reduced hypothesis is, exactly

Three equivalent spellings are given, each strictly more ring-level than the last:

1. `Subsingleton (pic0Subgroup C (overSpec k A))` at every `k`-algebra `A` — the direct form;
2. the same transported through `picEtAffineEquiv` to a separation statement about **plus
   classes** `PicEtAff C A` of the test algebra, with the degree condition read through the
   comparison;
3. with the field points of `overSpec k A` themselves ring-level: every
   `t : overSpec k K ⟶ overSpec k A` **is** `Over.overSpecMap φ` for an algebra map
   `φ : A →ₐ[k] K` (`exists_algHom_eq_of_overSpec_hom`, `Spec.preimage` plus the tower
   identity).  So the surviving quantifier in (2) ranges over algebra maps into fields, and no
   scheme, open, or morphism of schemes occurs in the hypothesis at all.

## What this does NOT do

* **It does not prove the vanishing, at any curve.**  It moves the quantifier; the
  mathematical content — a computation of the degree-zero relative Picard group of the curve
  over an arbitrary test *ring* — is untouched and remains unproduced.  In particular nothing
  here discharges `hvan` at `ℙ¹`, where `Curve/P1Curve.lean` supplies the three curve binders
  and `Curve/P1H1Vanishing.lean` gives `genus (P1.asOver k) = 0`.
* **It does not make the hypothesis cheap.**  `infer_instance` fails on
  `Subsingleton (pic0Subgroup C (overSpec k A))` (measured), so the reduced form has content;
  the reduction is a change of coordinates on a real obligation, not a discount.
* **It says nothing about the atlas route's own residue.**  The coverage clause at
  parameter `n > 0` is blocked on a spreading-out (`Pic0ChartCoverageSlice.lean:221-228`),
  which is a different obligation and is not addressed here.

## Main declarations

* `AlgebraicGeometry.exists_affineOpen_test_mem` — the affine opens of a test give a
  morphism-form open cover of it by affine test objects.
* `AlgebraicGeometry.subsingleton_pic0Subgroup_of_overSpec` — **the reduction**: vanishing at
  every affine test gives vanishing at every test.
* `AlgebraicGeometry.subsingleton_pic0Subgroup_overSpec_of_forall` — **the converse**, so the
  two are the same hypothesis.
* `AlgebraicGeometry.subsingleton_pic0Subgroup_forall_iff_overSpec` — the equivalence, bundled.
* `AlgebraicGeometry.exists_algHom_eq_of_overSpec_hom` — every field point of an affine test is
  `Spec` of an algebra map, so the field-point quantifier is ring-level too.
* `AlgebraicGeometry.subsingleton_pic0Subgroup_of_picEtAff_sep` — the reduced hypothesis in
  plus-class coordinates.
* `AlgebraicGeometry.jacobianData_of_overSpec_subsingleton` — **the producer**, with the
  quantifier already reduced: a `JacobianData C` from vanishing at affine tests only.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The affine-open cover of a test object -/

/-- The affine-open test object of an affine open is an open immersion on the left, because
`IsAffineOpen.fromSpec` is.  Stated as an instance so that the cover lemmas of
`PicEtCoverBridge` apply to the family `Over.fromSpecAffine T` without a local `haveI`. -/
instance isOpenImmersion_fromSpecAffine_left (T : Over (Spec (.of k)))
    (U : T.left.affineOpens) :
    IsOpenImmersion (AlgebraicGeometry.Over.fromSpecAffine T U).left :=
  U.2.isOpenImmersion_fromSpec

/-- **The affine opens of a test object cover it, in morphism form**: every point of `T.left`
is in the range of `Over.fromSpecAffine T U` for some affine open `U`.

This is the `hcov` hypothesis of the `PicEtCoverBridge` cover lemmas, at the one cover every
test object has: the affine opens form a basis, and the range of
`Over.fromSpecAffine T U` is `U` itself (`IsAffineOpen.range_fromSpec`). -/
theorem exists_affineOpen_test_mem (T : Over (Spec (.of k))) (p : T.left) :
    ∃ U : T.left.affineOpens,
      p ∈ (AlgebraicGeometry.Over.fromSpecAffine T U).left.opensRange := by
  obtain ⟨U, hU, hmem, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.left.isBasis_affineOpens)
      (show p ∈ (⊤ : T.left.Opens) from trivial)
  refine ⟨⟨U, hU⟩, ?_⟩
  have hrange : Set.range (AlgebraicGeometry.Over.fromSpecAffine T ⟨U, hU⟩).left.base
      = ((⟨U, hU⟩ : T.left.affineOpens).1 : Set T.left) := by
    change Set.range (hU.fromSpec).base = _
    exact hU.range_fromSpec
  change p ∈ Set.range (AlgebraicGeometry.Over.fromSpecAffine T ⟨U, hU⟩).left.base
  rw [hrange]
  exact hmem

/-! ## The reduction of the `∀ T` binder -/

/-- **THE REDUCTION**: if `pic0Subgroup C (overSpec k A)` is a subsingleton at every
commutative `k`-algebra `A`, then `pic0Subgroup C T` is a subsingleton at every test object
`T` — over an arbitrary base field, with no finiteness, affineness or quasi-compactness
hypothesis on `T`.

Only the *separation* half of Zariski descent is used: two degree-zero classes agreeing on
every member of the affine-open cover agree (`pic0Subgroup_ext_of_cover`), and under the
hypothesis the restrictions to each member agree because the member's whole group is a
subsingleton.  Nothing is glued, so the compatibility datum that makes the corresponding
representability statement expensive never appears.

Contrast `subsingleton_pic0_of_affine` (`Pic0VanishingRoute.lean:283`), whose hypothesis is
vanishing of the whole `picEt` at every test algebra: that implies this one but is strictly
stronger, and is false at any curve with a class of nonzero degree. -/
theorem subsingleton_pic0Subgroup_of_overSpec
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A],
      Subsingleton (pic0Subgroup C (overSpec k A)))
    (T : Over (Spec (.of k))) : Subsingleton (pic0Subgroup C T) :=
  ⟨fun _ _ => pic0Subgroup_ext_of_cover
    (fun U : T.left.affineOpens => AlgebraicGeometry.Over.fromSpecAffine T U)
    (exists_affineOpen_test_mem T)
    fun U => @Subsingleton.elim _ (h Γ(T.left, U.1)) _ _⟩

/-- **THE CONVERSE**, so the reduction is an equivalence and not a weakening: an affine test
is a test.

Recorded because a quantifier reduction whose hypothesis is strictly stronger than its
conclusion relocates the gap instead of naming it — which is exactly the defect of the landed
`picEt`-mediated chain this file replaces. -/
theorem subsingleton_pic0Subgroup_overSpec_of_forall
    (h : ∀ T : Over (Spec (.of k)), Subsingleton (pic0Subgroup C T))
    (A : Type u) [CommRing A] [Algebra k A] :
    Subsingleton (pic0Subgroup C (overSpec k A)) :=
  h (overSpec k A)

/-- **The equivalence, bundled**: "the degree-zero relative Picard group vanishes at every
test object" and "it vanishes at every test ring" are the *same* hypothesis.

This is the form to quote when pricing either route to a `rep` producer: the `∀ T` binder that
`I-1603` calls "the whole difficulty" is not itself the difficulty — the ring-level content
is. -/
theorem subsingleton_pic0Subgroup_forall_iff_overSpec :
    (∀ T : Over (Spec (.of k)), Subsingleton (pic0Subgroup C T))
      ↔ ∀ (A : Type u) [CommRing A] [Algebra k A],
          Subsingleton (pic0Subgroup C (overSpec k A)) :=
  ⟨fun h A _ _ => subsingleton_pic0Subgroup_overSpec_of_forall C h A,
    fun h => subsingleton_pic0Subgroup_of_overSpec C h⟩

/-! ## The field-point quantifier is ring-level too -/

/-- **Every field point of an affine test is `Spec` of an algebra map.**

`pic0Subgroup` is cut out by degree vanishing at every field point `t : overSpec k K ⟶ T`
(`Pic0Functor.lean:107`), which at a general test is a morphism of schemes.  At an affine test
it is not: `Spec.preimage` inverts `Spec.map` on morphisms between affine schemes, and the
triangle over `Spec k` becomes the scalar-tower identity `algebraMap k K = φ ∘ algebraMap k A`
by `Spec.map_injective`.

Together with the reduction above, this is what makes the reduced hypothesis *entirely*
ring-level: no scheme, open, or morphism of schemes occurs in it. -/
theorem exists_algHom_eq_of_overSpec_hom (A K : Type u) [CommRing A] [Field K]
    [Algebra k A] [Algebra k K] (t : overSpec k K ⟶ overSpec k A) :
    ∃ phi : A →ₐ[k] K, t = Over.overSpecMap phi := by
  have hw : t.left ≫ (overSpec k A).hom = (overSpec k K).hom := Over.w t
  set psi : CommRingCat.of A ⟶ CommRingCat.of K := Spec.preimage t.left with hpsi
  have hmap : Spec.map psi = t.left := Spec.map_preimage t.left
  have htower : CommRingCat.ofHom (algebraMap k A) ≫ psi
      = CommRingCat.ofHom (algebraMap k K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hmap]
    exact hw
  have hcom : ∀ r : k, psi.hom (algebraMap k A r) = algebraMap k K r := fun r =>
    congrArg (fun f => f r) (congrArg CommRingCat.Hom.hom htower)
  refine ⟨{ __ := psi.hom, commutes' := hcom }, ?_⟩
  ext : 1
  exact hmap.symm

/-! ## The reduced hypothesis in plus-class coordinates -/

/-- **The reduced hypothesis transported through the affine comparison**: a *separation*
statement about the plus classes `PicEtAff C A` of the test algebra.

`picEtAffineEquiv` (`PicEt.lean:235`) is a group isomorphism `picEt C (overSpec k A) ≃*
PicEtAff C A`, so a degree-zero class of an affine test is a plus class of `A` whose
`degAt`-pullbacks vanish.  This is the spelling to attack: `PicEtAff C A` is the one-step étale
plus of the relative Picard group at a commutative ring, with no scheme-level machinery
between it and the hypothesis. -/
theorem subsingleton_pic0Subgroup_of_picEtAff_sep
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A] (q q' : PicEtAff C A),
      (∀ (K : Type u) (_ : Field K) (_ : Algebra k K) (t : overSpec k K ⟶ overSpec k A),
        degAt ((picEtAffineEquiv C A).symm q) t = 0) →
      (∀ (K : Type u) (_ : Field K) (_ : Algebra k K) (t : overSpec k K ⟶ overSpec k A),
        degAt ((picEtAffineEquiv C A).symm q') t = 0) →
      q = q')
    (A : Type u) [CommRing A] [Algebra k A] :
    Subsingleton (pic0Subgroup C (overSpec k A)) := by
  refine ⟨fun s t => Subtype.ext ?_⟩
  refine (picEtAffineEquiv C A).injective ?_
  refine h A (picEtAffineEquiv C A s.1) (picEtAffineEquiv C A t.1) ?_ ?_
  · intro K _ _ tt
    rw [MulEquiv.symm_apply_apply]
    exact s.2 K tt
  · intro K _ _ tt
    rw [MulEquiv.symm_apply_apply]
    exact t.2 K tt

/-! ## The producer, with the quantifier already reduced -/

/-- **`JacobianData C` from vanishing at affine tests only.**

The composite of the reduction with `jacobianData_of_subsingleton`
(`Pic0VanishingRoute.lean`).  Its hypothesis mentions no test object: only the degree-zero
Picard group of the curve at a commutative `k`-algebra.

This is the shape a lane computing `Pic⁰` over rings should target — and note what it does
*not* need: no atlas, no chart certificate, no coverage clause, no divisor representability,
no index finiteness, no rational point. -/
def jacobianData_of_overSpec_subsingleton
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A],
      Subsingleton (pic0Subgroup C (overSpec k A))) :
    JacobianData C :=
  jacobianData_of_subsingleton C (subsingleton_pic0Subgroup_of_overSpec C h)

end

end AlgebraicGeometry
