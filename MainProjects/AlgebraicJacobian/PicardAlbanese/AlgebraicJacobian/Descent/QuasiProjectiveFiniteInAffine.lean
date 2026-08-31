/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.StableAffineCover
import AlgebraicJacobian.Picard.RelativeCurveFiniteInAffine
import AlgebraicJacobian.Projective.ProjectiveMorphism

/-!
# Finite subsets of quasi-projective schemes lie in affine opens

This module derives `Scheme.FiniteInAffine` from projectivity over an affine
base. It does not construct a quasi-projectivity witness for any Picard scheme.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- `FiniteInAffine` descends along open immersions. -/
theorem finiteInAffine_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (hY : FiniteInAffine Y) : FiniteInAffine X := by
  classical
  intro s hs
  obtain ⟨U, hU⟩ := hY (f.base '' s) (hs.image f.base)
  letI : Fintype s := hs.fintype
  obtain ⟨r, hr, hrle⟩ :=
    AlgebraicJacobian.GaloisDescent.exists_basicOpen_le_of_finite U.2
      (fun x : s => f.base x)
      (fun x => hU ⟨x, x.2, rfl⟩)
      (fun x => Scheme.Hom.mem_opensRange.mpr ⟨(x : X), rfl⟩)
  refine ⟨⟨f ⁻¹ᵁ Y.basicOpen r,
    (U.2.basicOpen r).preimage_of_isOpenImmersion f hrle⟩, ?_⟩
  intro x hx
  change f.base x ∈ Y.basicOpen r
  exact hr ⟨x, hx⟩

/-- `FiniteInAffine` descends along arbitrary immersions. -/
theorem finiteInAffine_of_isImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] (hY : FiniteInAffine Y) : FiniteInAffine X := by
  obtain ⟨Z, g₁, g₂, hg₁, hg₂, -⟩ :=
    (AlgebraicGeometry.IsImmersion.isImmersion_iff_exists (f := f)).mp
      (inferInstance : IsImmersion f)
  haveI := hg₁
  haveI := hg₂
  exact finiteInAffine_of_isAffineHom g₁
    (finiteInAffine_of_isOpenImmersion g₂ hY)

/-- Relative projective space over an affine base satisfies `FiniteInAffine`. -/
theorem finiteInAffine_projectiveSpace (n : Type u) (S : Scheme.{u}) [IsAffine S] :
    FiniteInAffine (ProjectiveSpace n S) := by
  haveI : IsAffineHom (ProjectiveSpace.toProjInt n S) := by
    rw [ProjectiveSpace.toProjInt_eq_snd]
    exact MorphismProperty.pullback_snd _ _ inferInstance
  exact finiteInAffine_of_isAffineHom (ProjectiveSpace.toProjInt n S)
    (finiteInAffine_proj (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)))

/-- A scheme projective over an affine base satisfies `FiniteInAffine`. -/
theorem finiteInAffine_of_isProjective {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S}
    (h : π.IsProjective) : FiniteInAffine X := by
  obtain ⟨n, -, i, hi, -⟩ := h
  haveI := hi
  exact finiteInAffine_of_isAffineHom i (finiteInAffine_projectiveSpace n S)

end AlgebraicGeometry.Scheme
