/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.ProjectiveMorphismBasic
import AlgebraicJacobian.Picard.ProjectiveCoordinateChart
import AlgebraicJacobian.Picard.ProjectiveSpaceAffineChartIso
import AlgebraicJacobian.Picard.FiniteMapLaurentGenerators
import AlgebraicJacobian.Picard.TwistedProjectiveCoordinates
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finite-morphism embeddings

This file supplies two pieces of the standard proof that finite morphisms are
projective. Over an affine target, a finite morphism is a closed subscheme of
finite-dimensional affine space. At the other end of the compactification
argument, a proper immersion into projective space is already closed.

The remaining geometric step is to place the affine embedding in a projective
chart and globalize it over the target. These results isolate both sides of
that step without adding a projectivity hypothesis.
-/

open CategoryTheory Limits MvPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom.IsProjective

variable {X S : Scheme.{u}} {pi : X ⟶ S}

/-- A proper morphism that factors through projective space by an immersion is
projective. Properness makes the immersion closed. -/
theorem of_isProper_of_immersion (hpi : IsProper pi) {n : Type u} [Finite n]
    (i : X ⟶ ℙ(n; S)) (hi : IsImmersion i)
    (hcomp : i ≫ (ℙ(n; S) ↘ S) = pi) : pi.IsProjective := by
  letI : IsImmersion i := hi
  haveI : IsProper (i ≫ (ℙ(n; S) ↘ S)) := hcomp ▸ hpi
  haveI : IsProper i := IsProper.of_comp i (ℙ(n; S) ↘ S)
  haveI : IsClosedImmersion i :=
    (IsClosedImmersion.iff_isProper_and_mono (f := i)).mpr
      ⟨inferInstance, inferInstance⟩
  exact ⟨n, inferInstance, i, inferInstance, hcomp⟩

end Scheme.Hom.IsProjective

namespace IsFinite

/-- An algebra-generating family makes the corresponding morphism from an
affine spectrum to polynomial affine space a closed immersion. This is the
ring-level form of the chosen-generator embedding criterion. -/
theorem isClosedImmersion_SpecMap_aeval_of_adjoin_eq_top
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {n : Type u} (a : n → A)
    (hgen : Algebra.adjoin R (Set.range a) = ⊤) :
    IsClosedImmersion (Spec.map
      (CommRingCat.ofHom (MvPolynomial.aeval (R := R) a).toRingHom)) := by
  apply IsClosedImmersion.spec_of_surjective
  change Function.Surjective (MvPolynomial.aeval (R := R) a)
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
  exact hgen

/-- A specified finite module-spanning family in the affine source ring
defines a closed immersion into affine space over the base. This is the
chosen-generator form of `exists_closedImmersion_affineSpace`, used when the
generators on two base charts have already been aligned. -/
theorem isClosedImmersion_homOfVector_of_span_eq_top
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    {n : Type u} [Finite n] (a : n → Γ(X, ⊤))
    (hspan :
      letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := RingHom.toAlgebra f.appTop.hom
      Submodule.span Γ(Y, ⊤) (Set.range a) = ⊤) :
    IsClosedImmersion (AffineSpace.homOfVector f a) := by
  classical
  letI : Fintype n := Fintype.ofFinite n
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := RingHom.toAlgebra f.appTop.hom
  let i : X ⟶ 𝔸(n; Y) := AffineSpace.homOfVector f a
  have hsurj : Function.Surjective (Fintype.linearCombination Γ(Y, ⊤) a) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  apply IsClosedImmersion.of_surjective_of_isAffine
  intro x
  obtain ⟨c, rfl⟩ := hsurj x
  let p : MvPolynomial n Γ(Y, ⊤) :=
    ∑ j, C (c j) * MvPolynomial.X j
  refine ⟨(AffineSpace.isoOfIsAffine n Y).hom.appTop
    ((Scheme.ΓSpecIso (.of (MvPolynomial n Γ(Y, ⊤)))).inv p), ?_⟩
  rw [AffineSpace.isoOfIsAffine_hom_appTop]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  change (i.appTop.hom.comp
    (eval₂Hom (𝔸(n; Y) ↘ Y).appTop.hom (AffineSpace.coord Y))) p =
      Fintype.linearCombination Γ(Y, ⊤) a c
  have heval :
      i.appTop.hom.comp
        (eval₂Hom (𝔸(n; Y) ↘ Y).appTop.hom (AffineSpace.coord Y)) =
        eval₂Hom f.appTop.hom a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, eval₂Hom_C]
      have h := congrArg Scheme.Hom.appTop
        (AffineSpace.homOfVector_over f a)
      rw [Scheme.Hom.comp_appTop] at h
      exact congrArg (fun e : Γ(Y, ⊤) ⟶ Γ(X, ⊤) => e.hom r) h
    · intro j
      simp [i]
  rw [heval, Fintype.linearCombination_apply]
  simp only [p, map_sum, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X,
    Algebra.smul_def]
  change (∑ x, f.appTop.hom (c x) * a x) =
    ∑ x, f.appTop.hom (c x) * a x
  rfl

/-- A specified finite algebra-generating family in the affine source ring
defines a closed immersion into affine space over the base. Unlike the
module-spanning criterion above, this applies directly to a family combining
base-ring coordinates with module generators. -/
theorem isClosedImmersion_homOfVector_of_adjoin_eq_top
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    {n : Type u} [Finite n] (a : n → Γ(X, ⊤))
    (hgen :
      letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := RingHom.toAlgebra f.appTop.hom
      Algebra.adjoin Γ(Y, ⊤) (Set.range a) = ⊤) :
    IsClosedImmersion (AffineSpace.homOfVector f a) := by
  classical
  letI : Fintype n := Fintype.ofFinite n
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := RingHom.toAlgebra f.appTop.hom
  let i : X ⟶ 𝔸(n; Y) := AffineSpace.homOfVector f a
  have hsurj : Function.Surjective
      (MvPolynomial.aeval (R := Γ(Y, ⊤)) a) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    exact hgen
  apply IsClosedImmersion.of_surjective_of_isAffine
  intro x
  obtain ⟨p, rfl⟩ := hsurj x
  refine ⟨(AffineSpace.isoOfIsAffine n Y).hom.appTop
    ((Scheme.ΓSpecIso (.of (MvPolynomial n Γ(Y, ⊤)))).inv p), ?_⟩
  rw [AffineSpace.isoOfIsAffine_hom_appTop]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  change (i.appTop.hom.comp
    (eval₂Hom (𝔸(n; Y) ↘ Y).appTop.hom (AffineSpace.coord Y))) p =
      MvPolynomial.aeval a p
  have heval :
      i.appTop.hom.comp
        (eval₂Hom (𝔸(n; Y) ↘ Y).appTop.hom (AffineSpace.coord Y)) =
        eval₂Hom f.appTop.hom a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, eval₂Hom_C]
      have h := congrArg Scheme.Hom.appTop
        (AffineSpace.homOfVector_over f a)
      rw [Scheme.Hom.comp_appTop] at h
      exact congrArg (fun e : Γ(Y, ⊤) ⟶ Γ(X, ⊤) => e.hom r) h
    · intro j
      simp [i]
  rw [heval]
  rfl

/-- A finite morphism over an affine target is a closed subscheme of a
finite-dimensional affine space over that target. -/
theorem exists_closedImmersion_affineSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsAffine Y] :
    ∃ (n : Type u) (_ : Finite n) (i : X ⟶ 𝔸(n; Y)),
      IsClosedImmersion i ∧ i ≫ (𝔸(n; Y) ↘ Y) = f := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := RingHom.toAlgebra f.appTop.hom
  haveI : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  obtain ⟨n, hn, q, hq⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial'.mp
      (inferInstance : Algebra.FiniteType Γ(Y, ⊤) Γ(X, ⊤))
  letI : Fintype n := hn
  let i : X ⟶ 𝔸(n; Y) :=
    AffineSpace.homOfVector f fun j => q (MvPolynomial.X j)
  refine ⟨n, inferInstance, i, ?_, AffineSpace.homOfVector_over _ _⟩
  apply IsClosedImmersion.of_surjective_of_isAffine
  intro x
  obtain ⟨p, rfl⟩ := hq x
  refine ⟨(AffineSpace.isoOfIsAffine n Y).hom.appTop
    ((Scheme.ΓSpecIso (.of (MvPolynomial n Γ(Y, ⊤)))).inv p), ?_⟩
  rw [AffineSpace.isoOfIsAffine_hom_appTop]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  change (i.appTop.hom.comp
    (eval₂Hom (𝔸(n; Y) ↘ Y).appTop.hom (AffineSpace.coord Y))) p = q.toRingHom p
  apply DFunLike.congr_fun ?_ p
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, eval₂Hom_C]
    rw [show q.toRingHom (C r) = f.appTop.hom r by
      change q (C r) = f.appTop.hom r
      exact q.commutes r]
    have h := congrArg Scheme.Hom.appTop (AffineSpace.homOfVector_over f
      (fun j => q (MvPolynomial.X j)))
    rw [Scheme.Hom.comp_appTop] at h
    exact congrArg (fun e : Γ(Y, ⊤) ⟶ Γ(X, ⊤) => e.hom r) h
  · intro j
    simp [i]

/-- A finite morphism to an affine target is projective. The affine embedding
lands in the standard open chart of projective space, and properness turns the
resulting immersion into a closed immersion. -/
theorem isProjective_of_isAffine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsAffine Y] : f.IsProjective := by
  obtain ⟨n, hn, i, hi, hif⟩ := exists_closedImmersion_affineSpace f
  letI : Finite n := hn
  letI : IsClosedImmersion i := hi
  let j : X ⟶ ℙ(Option n; Y) :=
    i ≫ ProjectiveSpace.standardOpenImmersion n Y
  have hj : IsImmersion j := by
    dsimp [j]
    infer_instance
  apply Scheme.Hom.IsProjective.of_isProper_of_immersion
    (pi := f) (by infer_instance) j hj
  dsimp [j]
  rw [Category.assoc, ProjectiveSpace.standardOpenImmersion_over, hif]

end IsFinite

end AlgebraicGeometry
