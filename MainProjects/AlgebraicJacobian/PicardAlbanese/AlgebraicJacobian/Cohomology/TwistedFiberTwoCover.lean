/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RigidEngine4Relative
import AlgebraicJacobian.Curve.P1Aut

/-!
# Twisting the pinned two-chart cover of a curve

The `GL₂(k)` action on `P¹_k` preserves the structure morphism and all morphism properties used by
the divisor-representability construction. Consequently a finite affine map `π : C ⟶ P¹_k` can be
replaced by `π ≫ γ_M`, and the standard two-chart construction gives the corresponding twisted
cover of `C` and of every relative curve.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The map to `P¹_k` obtained by changing homogeneous coordinates by `M`. -/
noncomputable def twistedP1Map {Y : Scheme.{u}} (π : Y ⟶ P1 k)
    (M : Matrix.GeneralLinearGroup (Fin 2) k) : Y ⟶ P1 k :=
  π ≫ P1.autOfMatrix k M

instance isAffineHom_twistedP1Map {Y : Scheme.{u}} (π : Y ⟶ P1 k)
    [IsAffineHom π] (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    IsAffineHom (twistedP1Map π M) := by
  letI : IsAffineHom (P1.autOfMatrix k M) :=
    MorphismProperty.of_isIso @IsAffineHom (P1.autOfMatrix k M)
  change IsAffineHom (π ≫ P1.autOfMatrix k M)
  exact IsAffineHom.comp_iff.mpr (by infer_instance)

instance isFinite_twistedP1Map {Y : Scheme.{u}} (π : Y ⟶ P1 k)
    [IsFinite π] (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    IsFinite (twistedP1Map π M) := by
  letI : IsFinite (P1.autOfMatrix k M) :=
    MorphismProperty.of_isIso @IsFinite (P1.autOfMatrix k M)
  change IsFinite (π ≫ P1.autOfMatrix k M)
  exact IsFinite.comp_iff.mpr (by infer_instance)

instance isDominant_twistedP1Map {Y : Scheme.{u}} (π : Y ⟶ P1 k)
    [IsDominant π] (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    IsDominant (twistedP1Map π M) := by
  letI : IsDominant (P1.autOfMatrix k M) :=
    MorphismProperty.of_isIso @IsDominant (P1.autOfMatrix k M)
  change IsDominant (π ≫ P1.autOfMatrix k M)
  exact (IsDominant.comp_iff (f := π) (g := P1.autOfMatrix k M)).mpr (by infer_instance)

/-- Changing coordinates preserves compatibility with the structure morphism to `Spec k`. -/
theorem twistedP1Map_comp_structureMap {Y : Scheme.{u}} (π : Y ⟶ P1 k)
    (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    twistedP1Map π M ≫ P1.structureMap k = π ≫ P1.structureMap k := by
  rw [twistedP1Map, Category.assoc, P1.autOfMatrix_comp_structureMap]

/-- The affine two-chart cover of `Y` associated to the coordinate-twisted map. -/
noncomputable def twistedFiberTwoCover {Y : Scheme.{u}} (π : Y ⟶ P1 k)
    [IsAffineHom π] (M : Matrix.GeneralLinearGroup (Fin 2) k) : Y.AffineTwoCover :=
  fiberTwoCover (twistedP1Map π M)

@[simp]
theorem twistedFiberTwoCover_V₀ {Y : Scheme.{u}} (π : Y ⟶ P1 k)
    [IsAffineHom π] (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    (twistedFiberTwoCover π M).V₀ = π ⁻¹ᵁ (P1.autOfMatrix k M ⁻¹ᵁ P1.chartOpen k 0) :=
  rfl

@[simp]
theorem twistedFiberTwoCover_V₁ {Y : Scheme.{u}} (π : Y ⟶ P1 k)
    [IsAffineHom π] (M : Matrix.GeneralLinearGroup (Fin 2) k) :
    (twistedFiberTwoCover π M).V₁ = π ⁻¹ᵁ (P1.autOfMatrix k M ⁻¹ᵁ P1.chartOpen k 1) :=
  rfl

/-- The base change of the coordinate-twisted two-chart cover to a relative curve. -/
noncomputable def twistedRelCover (C : Over (Spec (.of k))) (R : Type u) [CommRing R]
    [Algebra k R] (π : C.left ⟶ P1 k) [IsAffineHom π]
    (M : Matrix.GeneralLinearGroup (Fin 2) k) : (relCurve C R).AffineTwoCover :=
  relCover C R (twistedFiberTwoCover π M)

end AlgebraicGeometry
