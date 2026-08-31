import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# Trivial square-zero extensions

The algebra `R[M]` used throughout the deformation-theory blueprint is the
trivial square-zero extension of an `R`-module `M`.  This file exposes the
construction and its elementary universal properties under the Part 06
namespace.  The implementation reuses Mathlib's canonical construction while
keeping the names used by the source-facing library stable.
-/

namespace StacksPart06Lib

open scoped TensorProduct

universe u v w

section SquareZeroExtension

variable {R : Type u} {M : Type v} {N : Type w}

variable [CommRing R]
variable [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

/-- The trivial square-zero extension `R[M] = R ⊕ M`. -/
abbrev SquareZeroExtension (R : Type u) (M : Type v) := TrivSqZeroExt R M

/-- The canonical inclusion of the base ring into `R[M]`. -/
def squareZeroExtensionInclusion : R →+* SquareZeroExtension R M :=
  TrivSqZeroExt.inlHom R M

/-- The canonical projection `R[M] → R`. -/
def squareZeroExtensionProjection : SquareZeroExtension R M →ₐ[R] R :=
  TrivSqZeroExt.fstHom R R M

/-- The square-zero ideal in the trivial extension. -/
def squareZeroExtensionKernel : Ideal (SquareZeroExtension R M) :=
  RingHom.ker (squareZeroExtensionProjection (R := R) (M := M)).toRingHom

/-- The infinitesimal summand included in the square-zero extension. -/
def squareZeroExtensionInfinitesimal : M →ₗ[R] SquareZeroExtension R M :=
  TrivSqZeroExt.inrHom R M

omit [IsCentralScalar R M] in
@[simp]
theorem squareZeroExtensionInclusion_apply (r : R) :
    squareZeroExtensionInclusion (R := R) (M := M) r = TrivSqZeroExt.inl r :=
  rfl

@[simp]
theorem squareZeroExtensionProjection_apply (x : SquareZeroExtension R M) :
    squareZeroExtensionProjection (R := R) (M := M) x = x.fst :=
  rfl

@[simp]
theorem squareZeroExtension_mul (r s : R) (m n : M) :
    let x : SquareZeroExtension R M := (r, m)
    let y : SquareZeroExtension R M := (s, n)
    x * y = (r * s, r • n + s • m) := by
  dsimp
  apply TrivSqZeroExt.ext
  · exact TrivSqZeroExt.fst_mul _ _
  · rw [TrivSqZeroExt.snd_mul]
    simp

@[simp]
theorem squareZeroExtensionProjection_inclusion (r : R) :
    squareZeroExtensionProjection (R := R) (M := M)
        (squareZeroExtensionInclusion (R := R) (M := M) r) = r := by
  rfl

theorem squareZeroExtensionProjection_surjective :
    Function.Surjective (squareZeroExtensionProjection (R := R) (M := M)) := by
  intro r
  exact ⟨squareZeroExtensionInclusion (R := R) (M := M) r,
    squareZeroExtensionProjection_inclusion r⟩

omit [IsCentralScalar R M] in
theorem squareZeroExtensionInclusion_injective :
    Function.Injective (squareZeroExtensionInclusion (R := R) (M := M)) := by
  exact TrivSqZeroExt.inl_injective

@[simp]
theorem squareZeroExtensionKernel_sq :
    squareZeroExtensionKernel (R := R) (M := M) ^ 2 = ⊥ := by
  exact TrivSqZeroExt.kerIdeal_sq R M

@[simp]
theorem squareZeroExtensionKernel_mem_iff (x : SquareZeroExtension R M) :
    x ∈ squareZeroExtensionKernel (R := R) (M := M) ↔
      squareZeroExtensionProjection (R := R) (M := M) x = 0 := by
  rfl

omit [IsCentralScalar R M] in
@[simp]
theorem squareZeroExtensionInfinitesimal_mul (m n : M) :
    squareZeroExtensionInfinitesimal (R := R) (M := M) m *
        squareZeroExtensionInfinitesimal (R := R) (M := M) n = 0 := by
  exact TrivSqZeroExt.inr_mul_inr R m n

theorem squareZeroExtension_projection_zero_iff (x : SquareZeroExtension R M) :
    squareZeroExtensionProjection (R := R) (M := M) x = 0 ↔
      ∃ m, squareZeroExtensionInfinitesimal (R := R) (M := M) m = x := by
  rcases x with ⟨r, m⟩
  constructor
  · intro hr
    refine ⟨m, ?_⟩
    apply TrivSqZeroExt.ext
    · change (0 : R) = r
      exact hr.symm
    · rfl
  · rintro ⟨m', hm⟩
    rw [← hm]
    rfl

omit [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] in
theorem squareZeroExtension_inl_fst_add_inr_snd (x : SquareZeroExtension R M) :
    TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd = x := by
  exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x

variable {A : Type*} [Semiring A] [Algebra R A]

/-- Algebra maps out of `R[M]` are exactly linear maps whose image is square-zero. -/
def squareZeroExtensionAlgHomEquiv :
    { f : M →ₗ[R] A // ∀ x y, f x * f y = 0 } ≃
      (SquareZeroExtension R M →ₐ[R] A) :=
  TrivSqZeroExt.liftEquivOfComm

@[simp]
theorem squareZeroExtensionAlgHomEquiv_apply_inl
    (f : { f : M →ₗ[R] A // ∀ x y, f x * f y = 0 }) (r : R) :
    squareZeroExtensionAlgHomEquiv (R := R) (M := M) f (TrivSqZeroExt.inl r) =
      algebraMap R A r := by
  simp [squareZeroExtensionAlgHomEquiv, TrivSqZeroExt.liftEquivOfComm,
    TrivSqZeroExt.liftEquiv, TrivSqZeroExt.lift_apply_inl]

@[simp]
theorem squareZeroExtensionAlgHomEquiv_apply_inr
    (f : { f : M →ₗ[R] A // ∀ x y, f x * f y = 0 }) (m : M) :
    squareZeroExtensionAlgHomEquiv (R := R) (M := M) f (TrivSqZeroExt.inr m) = f.1 m := by
  simp [squareZeroExtensionAlgHomEquiv, TrivSqZeroExt.liftEquivOfComm,
    TrivSqZeroExt.liftEquiv, TrivSqZeroExt.lift_apply_inr]

end SquareZeroExtension

section Functoriality

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommRing R]
variable [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]

/-- A linear map induces a morphism of trivial square-zero extensions. -/
def squareZeroExtensionMap (f : M →ₗ[R] N) :
    SquareZeroExtension R M →ₐ[R] SquareZeroExtension R N :=
  TrivSqZeroExt.map f

@[simp]
theorem squareZeroExtensionMap_inclusion (f : M →ₗ[R] N) (r : R) :
    squareZeroExtensionMap f (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl r := by
  exact TrivSqZeroExt.map_inl f r

@[simp]
theorem squareZeroExtensionMap_inr (f : M →ₗ[R] N) (m : M) :
    squareZeroExtensionMap f (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (f m) := by
  exact TrivSqZeroExt.map_inr f m

@[simp]
theorem squareZeroExtensionMap_projection (f : M →ₗ[R] N)
    (x : SquareZeroExtension R M) :
    squareZeroExtensionProjection (R := R) (M := N)
        (squareZeroExtensionMap f x) =
      squareZeroExtensionProjection (R := R) (M := M) x := by
  exact TrivSqZeroExt.fst_map f x

theorem squareZeroExtensionMap_id :
    squareZeroExtensionMap (LinearMap.id : M →ₗ[R] M) = AlgHom.id R _ := by
  exact TrivSqZeroExt.map_id

variable {P : Type*}
variable [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]

theorem squareZeroExtensionMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    squareZeroExtensionMap (g ∘ₗ f) =
      (squareZeroExtensionMap g).comp (squareZeroExtensionMap f) := by
  exact TrivSqZeroExt.map_comp_map f g

end Functoriality

section DualNumbers

variable (R : Type u) [CommRing R]

/-- The dual-number algebra `R[ε]`, represented as `R[R]`. -/
abbrev DualNumbers := SquareZeroExtension R R

/-- The nilpotent ideal generated by the infinitesimal coordinate. -/
def dualNumbersKernel : Ideal (DualNumbers R) :=
  squareZeroExtensionKernel (R := R) (M := R)

@[simp]
theorem dualNumbersKernel_sq : dualNumbersKernel R ^ 2 = ⊥ := by
  exact squareZeroExtensionKernel_sq (R := R) (M := R)

@[simp]
theorem dualNumber_mul_dualNumber (x y : R) :
    (TrivSqZeroExt.inr x : DualNumbers R) * TrivSqZeroExt.inr y = 0 := by
  exact TrivSqZeroExt.inr_mul_inr R x y

end DualNumbers

end StacksPart06Lib
