/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.ProjectiveSpace

/-!
# Projective and H-quasi-projective morphisms

This file supplies the universe-polymorphic geometric core of projectivity that
Mathlib v4.31 does not yet provide. A morphism is projective when it factors as
a closed immersion into a finite-dimensional relative projective space.

A morphism is **H-quasi-projective** when it factors through a quasi-compact
immersion into such a projective space, following the finite-projective-space
convention of [Stacks, Tag 01VV].  The quasi-compactness is part of the
definition: without it the predicate only records an immersion/relative very
ampleness and need not imply finite type.  This predicate is not asserted to
be equivalent over arbitrary bases to every formulation using relative ample
line bundles.  Both predicates are stable under base change.

The line-bundle-carrying refinement used by the Quot construction remains in
`Picard/ProjectiveMorphism.lean`; that refinement is universe-monomorphic because
its Serre twist is built by the project-local sheaf gluing engine.
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

/-- A morphism is H-quasi-projective if it admits a quasi-compact immersion into
a finite-dimensional relative projective space over its target. -/
def Scheme.Hom.IsHQuasiProjective {X S : Scheme.{u}} (pi : X ⟶ S) : Prop :=
  ∃ (n : Type u) (_ : Finite n) (i : X ⟶ ℙ(n; S)),
    IsImmersion i ∧ QuasiCompact i ∧ i ≫ (ℙ(n; S) ↘ S) = pi

namespace Scheme.Hom.IsProjective

variable {X S : Scheme.{u}} {pi : X ⟶ S}

/-- A projective morphism is H-quasi-projective. -/
theorem isHQuasiProjective (h : pi.IsProjective) : pi.IsHQuasiProjective := by
  obtain ⟨n, hn, i, hi, hcomp⟩ := h
  letI : Finite n := hn
  haveI : IsClosedImmersion i := hi
  exact ⟨n, hn, i, inferInstance, inferInstance, hcomp⟩

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

end Scheme.Hom.IsProjective

namespace Scheme.Hom.IsHQuasiProjective

variable {X S : Scheme.{u}} {pi : X ⟶ S}

/-- H-quasi-projective morphisms are locally of finite type. -/
theorem locallyOfFiniteType (h : pi.IsHQuasiProjective) : LocallyOfFiniteType pi := by
  obtain ⟨n, hn, i, hi, _, hcomp⟩ := h
  letI : Finite n := hn
  haveI : IsImmersion i := hi
  rw [← hcomp]
  infer_instance

/-- H-quasi-projective morphisms are quasi-compact. -/
theorem quasiCompact (h : pi.IsHQuasiProjective) : QuasiCompact pi := by
  obtain ⟨n, hn, i, hi, hqc, hcomp⟩ := h
  letI : Finite n := hn
  haveI : IsImmersion i := hi
  haveI : QuasiCompact i := hqc
  rw [← hcomp]
  infer_instance

/-- H-quasi-projective morphisms are separated. -/
theorem isSeparated (h : pi.IsHQuasiProjective) : IsSeparated pi := by
  obtain ⟨n, hn, i, hi, _, hcomp⟩ := h
  letI : Finite n := hn
  haveI : IsImmersion i := hi
  rw [← hcomp]
  infer_instance

/-- A quasi-compact immersion into an H-quasi-projective scheme is
H-quasi-projective. -/
theorem comp_isImmersion (h : pi.IsHQuasiProjective) {Y : Scheme.{u}}
    (j : Y ⟶ X) [IsImmersion j] [QuasiCompact j] :
    (j ≫ pi).IsHQuasiProjective := by
  obtain ⟨n, hn, i, hi, hqc, hcomp⟩ := h
  letI : Finite n := hn
  haveI : IsImmersion i := hi
  haveI : QuasiCompact i := hqc
  exact ⟨n, hn, j ≫ i, inferInstance, inferInstance, by rw [Category.assoc, hcomp]⟩

/-- The comparison from a base-changed source to the corresponding base change
of its ambient projective space. -/
private def baseChangeLift {S' : Scheme.{u}} (g : S' ⟶ S) {n : Type u}
    (i : X ⟶ ℙ(n; S)) (hcomp : i ≫ (ℙ(n; S) ↘ S) = pi) :
    pullback pi g ⟶ ℙ(n; S') :=
  (ProjectiveSpace.isPullback_map n g).lift
    (pullback.fst pi g ≫ i) (pullback.snd pi g)
    (by rw [Category.assoc, hcomp, pullback.condition])

/-- H-quasi-projective morphisms are stable under arbitrary base change. -/
theorem baseChange (h : pi.IsHQuasiProjective) {S' : Scheme.{u}} (g : S' ⟶ S) :
    (pullback.snd pi g).IsHQuasiProjective := by
  obtain ⟨n, hn, i, hi, hqc, hcomp⟩ := h
  letI : Finite n := hn
  haveI : IsImmersion i := hi
  haveI : QuasiCompact i := hqc
  have h1 : baseChangeLift g i hcomp ≫ (ℙ(n; S') ↘ S') =
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
  exact ⟨n, hn, baseChangeLift g i hcomp,
    MorphismProperty.of_isPullback hsq.flip hi,
    MorphismProperty.of_isPullback hsq.flip hqc, h1⟩

end Scheme.Hom.IsHQuasiProjective

namespace ProjectiveSpace

/-- The structural morphism of relative projective space is projective. -/
theorem isProjective_over (n : Type u) [Finite n] (S : Scheme.{u}) :
    (ℙ(n; S) ↘ S).IsProjective :=
  ⟨n, inferInstance, 𝟙 _, inferInstance, Category.id_comp _⟩

/-- The structural morphism of relative projective space is H-quasi-projective. -/
theorem isHQuasiProjective_over (n : Type u) [Finite n] (S : Scheme.{u}) :
    (ℙ(n; S) ↘ S).IsHQuasiProjective :=
  (isProjective_over n S).isHQuasiProjective

end ProjectiveSpace

end AlgebraicGeometry
