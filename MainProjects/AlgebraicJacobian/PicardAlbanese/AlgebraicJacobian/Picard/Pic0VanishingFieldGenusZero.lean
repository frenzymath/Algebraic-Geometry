/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.GenusZeroDegreeTrivial
import AlgebraicJacobian.Cohomology.H1BaseFieldInvariance
import AlgebraicJacobian.RiemannRoch.RelPicDegree

/-!
# THE FIELD-TEST LAYER OF THE `pic⁰` VANISHING, AT GENUS `0`

`Picard/Pic0VanishingAffineReduction.lean` reduces the `∀ T` binder of the degree-zero Picard
vanishing to an equivalent statement about test *rings*.  This file closes the **field** case
of that statement at genus `0`, for an arbitrary base field and every field extension.

The content is `RiemannRoch/GenusZeroDegreeTrivial.eq_one_of_classDeg_eq_zero_of_chi_one`
transported to the carrier `relPicDeg` actually reads: `relPic C (overSpec k L)`, the Čech
Picard group of the base-changed curve modulo classes pulled back from the base.

## Why the base change is the whole plumbing cost

`relPicDeg L` is a homomorphism out of `relPic C (overSpec k L)`, whose representatives are
Čech classes on `(C ⊗ overSpec k L).left` — the curve base-changed to `L`, *not* `C`.  So the
`χ = 1` hypothesis has to hold at the base-changed curve at **every** field extension, and
`genus C = 0` is a statement about `C` over `k`.

That transport is landed and needs no new cohomology: `finrank_h0_baseField` and
`finrank_h1_baseField_eq_genus` (`Cohomology/H1BaseFieldInvariance.lean:353,363`) compute both
Betti numbers of the base-changed curve, and `h0_moduleKSheaf` gives `h⁰ = 1` over `k`.  Then
`χ = h⁰ - h¹ = 1 - genus C = 1`.

Why *these* lemmas: they are stated at `(C ⊗ overSpec k L).left.moduleKSheaf L` under
`instOverBaseChange` (`Curve/BaseChangeInstances.lean:74`), which is the key `relPicDeg`'s
degree stack consumes, so no transport is needed.

**RETRACTED CLAIM, and it was published as a prohibition.**  An earlier version of this
paragraph said that going through `chi_moduleKSheaf` at the bundled `baseChangeBundle C L`
gives the same object under a different `Over` instance and that "the resulting `chi` terms do
not unify — measured".  **That is false.**  The bundled route closes at default heartbeats once
a `change` to the bundled spelling precedes the `simpa`; what was actually measured was one
`simpa` failing *without* that step, i.e. a fact about a tactic call, restated as a fact about
two objects.  `Curve/P1DegreeZeroTrivial.lean` (pic-g) does it the bundled way at `ℙ¹`.  Both
routes work; this one is not the only one and nothing here forecloses the other.

## What this does NOT do

* **It is not the vanishing.**  After the affine reduction the surviving obligation quantifies
  over test *rings*; a field is a ring, so this is one instance of it and not the statement.
  The general-ring case needs a fibrewise-to-global argument (cohomology and base change) that
  this tree does not have, and nothing here supplies it.
* **It says nothing at positive genus**, and it does not claim to: at `genus C > 0` the
  hypothesis `genus C = 0` simply fails, and this file exhibits no positive-genus curve.
* **It does not produce a `JacobianData`** on its own.  The producer
  `jacobianData_of_overSpec_subsingleton` wants the ring-level hypothesis; the field case does
  not discharge it.

## Main declarations

* `AlgebraicGeometry.chi_moduleKSheaf_baseChange_eq_one_of_genus_zero` — `χ(𝒪) = 1` at the
  base-changed curve, at every field extension, from `genus C = 0`.
* `AlgebraicGeometry.relPic_eq_one_of_relPicDeg_eq_zero_of_genus_zero` — **the field-test
  layer**: at genus `0`, a relative Picard class of relative degree `0` over any field
  extension is trivial.
* `AlgebraicGeometry.relPicDeg_eq_zero_iff_of_genus_zero` — the same as an iff.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
variable [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

-- The base-change instance stack of `Curve.BaseChangeInstances` is resolved twice here (both
-- Betti numbers), which exceeds the default budget; within the DAT-2/PicEtMap precedent.
omit [GeometricallyReduced C.hom] in
/-- **`χ(𝒪) = 1` at the base-changed curve**, at every field extension of the base, from
`genus C = 0`.

Both Betti numbers transport: `h⁰` by `finrank_h0_baseField` composed with `h0_moduleKSheaf`
(which is `1` on any proper geometrically integral curve), and `h¹` by
`finrank_h1_baseField_eq_genus`.  So `χ = 1 - genus C`, which the hypothesis makes `1`. -/
theorem chi_moduleKSheaf_baseChange_eq_one_of_genus_zero
    (K : Type u) [Field K] [Algebra k K] (hg : genus C = 0) :
    Sheaf.chi ((C ⊗ overSpec k K).left.moduleKSheaf K) = 1 := by
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  have hh1 : Sheaf.h1 ((C ⊗ overSpec k K).left.moduleKSheaf K) = genus C :=
    finrank_h1_baseField_eq_genus C K
  have hh0 : Sheaf.h0 ((C ⊗ overSpec k K).left.moduleKSheaf K)
      = Sheaf.h0 (C.left.moduleKSheaf k) := finrank_h0_baseField C K
  have hbase : Sheaf.h0 (C.left.moduleKSheaf k) = 1 := h0_moduleKSheaf C
  rw [Sheaf.chi, hh0, hbase, hh1, hg]
  norm_num

-- Same base-change instance stack as the χ lemma above, plus the `relPic.ind` elimination.
omit [GeometricallyReduced C.hom] in
/-- **THE FIELD-TEST LAYER**: at genus `0`, a relative Picard class of relative degree `0`
over any field extension of the base is trivial.

`relPicDeg` is defined by descending `classDeg` along `relPicMk`, and `relPicDeg_relPicMk` is
`rfl`, so on a representative the hypothesis *is* `classDeg K L = 0` and the genus-`0`
converse applies at the base-changed curve. -/
theorem relPic_eq_one_of_relPicDeg_eq_zero_of_genus_zero
    (K : Type u) [Field K] [Algebra k K] (hg : genus C = 0)
    (y : relPic C (overSpec k K)) (hy : relPicDeg (C := C) K y = 0) : y = 1 := by
  have hchi : Sheaf.chi ((C ⊗ overSpec k K).left.moduleKSheaf K) = 1 :=
    chi_moduleKSheaf_baseChange_eq_one_of_genus_zero C K hg
  induction y using relPic.ind with
  | mk L =>
    have hcl : classDeg K L = 0 := hy
    have hL1 : L = 1 := eq_one_of_classDeg_eq_zero_of_chi_one K hchi L hcl
    rw [hL1, map_one]

-- Carries the same base-change instance stack through both directions.
omit [GeometricallyReduced C.hom] in
/-- The iff form: at genus `0` the relative degree over a field extension vanishes exactly on
the trivial class.  The reverse direction is `map_one`. -/
theorem relPicDeg_eq_zero_iff_of_genus_zero
    (K : Type u) [Field K] [Algebra k K] (hg : genus C = 0)
    (y : relPic C (overSpec k K)) :
    relPicDeg (C := C) K y = 0 ↔ y = 1 :=
  ⟨relPic_eq_one_of_relPicDeg_eq_zero_of_genus_zero C K hg y, fun h => by
    subst h
    exact map_zero (relPicDeg (C := C) K)⟩

end AlgebraicGeometry
