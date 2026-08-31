/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finite type for relative tensor products

A relative tensor product of two finite-type algebras is finite type over the ground ring,
provided the displayed algebra structures form scalar towers.  The proof presents it as a
quotient of the absolute tensor product over the ground ring.
-/

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace AlgebraicJacobian

/-- If `B` and `C` are finite type over `M`, then `B ⊗[A] C` is finite type over `M`.
The `A`-algebra structures need only be compatible with the given `M`-algebra structures. -/
theorem finiteType_tensorProduct_over
    {M A B C : Type u}
    [CommRing M] [CommRing A] [CommRing B] [CommRing C]
    [Algebra M A] [Algebra A B] [Algebra A C]
    [Algebra M B] [Algebra M C]
    [IsScalarTower M A B] [IsScalarTower M A C]
    [Algebra.FiniteType M B] [Algebra.FiniteType M C] :
    Algebra.FiniteType M (B ⊗[A] C) := by
  let f : (B ⊗[M] C) →ₐ[M] (B ⊗[A] C) :=
    Algebra.TensorProduct.lift (R := M) (S := M) (A := B) (B := C)
      ((Algebra.TensorProduct.includeLeft
        (R := A) (S := A) (A := B) (B := C)).restrictScalars M)
      ((Algebra.TensorProduct.includeRight
        (R := A) (A := B) (B := C)).restrictScalars M)
      (fun _ _ => Commute.all _ _)
  have hf : Function.Surjective f := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero f⟩
    | tmul b c =>
        refine ⟨b ⊗ₜ[M] c, ?_⟩
        simp [f]
    | add x y hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add f x' y'⟩
  letI : Algebra.FiniteType B (B ⊗[M] C) := Algebra.FiniteType.baseChange B
  letI : IsScalarTower M B (B ⊗[M] C) := by infer_instance
  have hdom : Algebra.FiniteType M (B ⊗[M] C) :=
    Algebra.FiniteType.trans (R := M) (S := B)
      (inferInstance : Algebra.FiniteType M B)
      (inferInstance : Algebra.FiniteType B (B ⊗[M] C))
  exact @Algebra.FiniteType.of_surjective M (B ⊗[M] C) (B ⊗[A] C)
    _ _ _ _ _ hdom f hf

end AlgebraicJacobian
