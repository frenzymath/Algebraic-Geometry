/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Projective.RelativeProjectiveSpace
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Projective morphisms

This file supplies the universe-polymorphic geometric core of projectivity that
Mathlib v4.31 does not yet provide. A morphism is projective when it factors as
a closed immersion into a finite-dimensional relative projective space.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A morphism is projective if it admits a closed immersion into a
finite-dimensional relative projective space over its target. -/
def Scheme.Hom.IsProjective {X S : Scheme.{u}} (pi : X ⟶ S) : Prop :=
  ∃ (n : Type u) (_ : Finite n) (i : X ⟶ ℙ(n; S)),
    IsClosedImmersion i ∧ i ≫ (ℙ(n; S) ↘ S) = pi

namespace Scheme.Hom.IsProjective

variable {X S : Scheme.{u}} {pi : X ⟶ S}

/-- Projective morphisms are proper. -/
theorem isProper (h : pi.IsProjective) : IsProper pi := by
  obtain ⟨n, hn, i, hi, hcomp⟩ := h
  letI : Finite n := hn
  haveI := hi
  rw [← hcomp]
  infer_instance

/-- Projective morphisms are locally of finite type. -/
theorem locallyOfFiniteType (h : pi.IsProjective) : LocallyOfFiniteType pi :=
  haveI := h.isProper
  inferInstance

/-- Projective morphisms are separated. -/
theorem isSeparated (h : pi.IsProjective) : IsSeparated pi :=
  haveI := h.isProper
  inferInstance

/-- Projective morphisms are universally closed. -/
theorem universallyClosed (h : pi.IsProjective) : UniversallyClosed pi :=
  haveI := h.isProper
  inferInstance

/-- A closed immersion into a projective scheme is projective. -/
theorem comp_isClosedImmersion (h : pi.IsProjective) {Y : Scheme.{u}}
    (j : Y ⟶ X) [IsClosedImmersion j] : (j ≫ pi).IsProjective := by
  obtain ⟨n, hn, i, hi, hcomp⟩ := h
  letI : Finite n := hn
  haveI := hi
  exact ⟨n, hn, j ≫ i, inferInstance, by rw [Category.assoc, hcomp]⟩

/-- The comparison morphism from the base-changed source to the corresponding
base change of its ambient projective space. -/
private def baseChangeLift {S' : Scheme.{u}} (g : S' ⟶ S) {n : Type u}
    (i : X ⟶ ℙ(n; S)) (hcomp : i ≫ (ℙ(n; S) ↘ S) = pi) :
    pullback pi g ⟶ ℙ(n; S') :=
  (ProjectiveSpace.isPullback_map n g).lift
    (pullback.fst pi g ≫ i) (pullback.snd pi g)
    (by rw [Category.assoc, hcomp, pullback.condition])

/-- Projective morphisms are stable under arbitrary base change. -/
theorem baseChange (h : pi.IsProjective) {S' : Scheme.{u}} (g : S' ⟶ S) :
    (pullback.snd pi g).IsProjective := by
  obtain ⟨n, hn, i, hi, hcomp⟩ := h
  letI : Finite n := hn
  haveI := hi
  refine ⟨n, hn, baseChangeLift g i hcomp, ?_, ?_⟩
  · have h1 : baseChangeLift g i hcomp ≫ (ℙ(n; S') ↘ S') =
        pullback.snd pi g := IsPullback.lift_snd _ _ _ _
    have hsq : IsPullback (baseChangeLift g i hcomp) (pullback.fst pi g)
        (ProjectiveSpace.map n g) i := by
      have hbig : IsPullback
          (baseChangeLift g i hcomp ≫ (ℙ(n; S') ↘ S'))
          (pullback.fst pi g) g (i ≫ (ℙ(n; S) ↘ S)) := by
        rw [h1, hcomp]
        exact (IsPullback.of_hasPullback pi g).flip
      exact IsPullback.of_right hbig
        (IsPullback.lift_fst _ _ _ _)
        (ProjectiveSpace.isPullback_map n g).flip
    exact MorphismProperty.of_isPullback hsq.flip hi
  · exact IsPullback.lift_snd _ _ _ _

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

namespace ProjectiveSpace

/-- The structural morphism of relative projective space is projective. -/
theorem isProjective_over (n : Type u) [Finite n] (S : Scheme.{u}) :
    (ℙ(n; S) ↘ S).IsProjective :=
  ⟨n, inferInstance, 𝟙 _, inferInstance, Category.id_comp _⟩

end ProjectiveSpace

end AlgebraicGeometry
