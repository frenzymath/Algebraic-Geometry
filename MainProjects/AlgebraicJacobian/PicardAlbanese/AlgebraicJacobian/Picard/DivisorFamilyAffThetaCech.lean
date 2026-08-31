/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaDescent

/-!
# The intrinsic theta Cech equalizer over the widened colength algebra

The intrinsic piece and overlap quotients of `DivisorFamilyAffThetaDescent` are modules over
different local colength algebras. This file restricts all of those actions to the single
widened equalizer algebra `A_D = gluedSubalgebra A`. The two overlap restrictions then become
`A_D`-linear maps, and the intrinsic theta module is their kernel in `A_D`-modules.

The final declarations give the resulting equalizer its universal property. This is the
module-descent input needed to compare the intrinsic theta line with its piecewise base
changes and descend invertibility, without a `ChartTyping` or any additional hypothesis.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsProper C.hom]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

attribute [local instance] thetaPieceQuotientModule thetaOverlapQuotientModule

/-- Restriction of the widened equalizer algebra to one overlap colength algebra. -/
noncomputable def gluedSubalgebraOverlapMap (A : AffAdaptation D d) (i j : D.index) :
    ↥(gluedSubalgebra A) →ₐ[R] A.ovlColength i j :=
  (A.toOvlLeft i j).comp (A.gluedSubalgebraPieceMap i)

omit [IsProper C.hom] in
/-- The overlap algebra map is independent of whether it is evaluated through the left or
right piece. This is exactly the defining equalizer relation of `A_D`. -/
lemma gluedSubalgebraOverlapMap_eq_right (A : AffAdaptation D d) (i j : D.index) :
    A.gluedSubalgebraOverlapMap i j =
      (A.toOvlRight i j).comp (A.gluedSubalgebraPieceMap j) := by
  ext c
  change A.toOvlLeft i j (c.1 i) = A.toOvlRight i j (c.1 j)
  exact (A.mem_gluedSubmodule_iff (c : A.chartProd)).mp c.2 (i, j)

/-- An overlap theta quotient, restricted to an `A_D`-module through the common overlap
algebra map. -/
@[reducible]
noncomputable def thetaOverlapQuotientGluedModule (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    Module ↥(gluedSubalgebra A)
      (A.ThetaOverlapQuotient (π := π) a i j) :=
  letI : Module (A.ovlColength i j) (A.ThetaOverlapQuotient (π := π) a i j) :=
    A.thetaOverlapQuotientModule (π := π) a i j
  Module.compHom (A.ThetaOverlapQuotient (π := π) a i j)
    (A.gluedSubalgebraOverlapMap i j).toRingHom

attribute [local instance] thetaPieceQuotientGluedModule
  thetaOverlapQuotientGluedModule

/-- The intrinsic theta equalizer carries its canonical module structure over the widened
colength algebra outside this construction file as well. -/
@[reducible]
noncomputable instance intrinsicThetaGluedOverModule (A : AffAdaptation D d) (a : ℕ) :
    Module ↥(gluedSubalgebra A) (A.IntrinsicThetaGluedOver (π := π) a) :=
  letI : ∀ j, Module ↥(gluedSubalgebra A)
      (A.ThetaPieceQuotient (π := π) a j) :=
    fun j => A.thetaPieceQuotientGluedModule (π := π) a j
  Submodule.module (A.intrinsicThetaGluedOver (π := π) a)

/-- The left piece-to-overlap restriction as an `A_D`-linear map. -/
noncomputable def thetaToOverlapLeftGlued (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ThetaPieceQuotient (π := π) a i →ₗ[↥(gluedSubalgebra A)]
      A.ThetaOverlapQuotient (π := π) a i j where
  toFun := A.thetaToOverlapLeft (π := π) a i j
  map_add' := (A.thetaToOverlapLeft (π := π) a i j).map_add
  map_smul' := by
    intro c x
    change A.thetaToOverlapLeft (π := π) a i j (c.1 i • x) =
      A.gluedSubalgebraOverlapMap i j c •
        A.thetaToOverlapLeft (π := π) a i j x
    rw [A.thetaToOverlapLeft_smul]
    rfl

/-- The right piece-to-overlap restriction as an `A_D`-linear map. -/
noncomputable def thetaToOverlapRightGlued (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.ThetaPieceQuotient (π := π) a j →ₗ[↥(gluedSubalgebra A)]
      A.ThetaOverlapQuotient (π := π) a i j where
  toFun := A.thetaToOverlapRight (π := π) a i j
  map_add' := (A.thetaToOverlapRight (π := π) a i j).map_add
  map_smul' := by
    intro c x
    change A.thetaToOverlapRight (π := π) a i j (c.1 j • x) =
      A.gluedSubalgebraOverlapMap i j c •
        A.thetaToOverlapRight (π := π) a i j x
    rw [A.thetaToOverlapRight_smul]
    rw [A.gluedSubalgebraOverlapMap_eq_right i j]
    rfl

/-- The left arrow of the intrinsic theta descent fork in `A_D`-modules. -/
noncomputable def thetaIntrinsicDeltaLeftGlued (A : AffAdaptation D d) (a : ℕ) :
    A.ThetaPieceProd (π := π) a →ₗ[↥(gluedSubalgebra A)]
      A.ThetaOverlapProd (π := π) a :=
  LinearMap.pi (fun p : D.index × D.index =>
    A.thetaToOverlapLeftGlued (π := π) a p.1 p.2 ∘ₗ LinearMap.proj p.1)

/-- The right arrow of the intrinsic theta descent fork in `A_D`-modules. -/
noncomputable def thetaIntrinsicDeltaRightGlued (A : AffAdaptation D d) (a : ℕ) :
    A.ThetaPieceProd (π := π) a →ₗ[↥(gluedSubalgebra A)]
      A.ThetaOverlapProd (π := π) a :=
  LinearMap.pi (fun p : D.index × D.index =>
    A.thetaToOverlapRightGlued (π := π) a p.1 p.2 ∘ₗ LinearMap.proj p.2)

/-- The kernel of the intrinsic theta descent fork, formed in `A_D`-modules. -/
noncomputable def intrinsicThetaGluedKernelOver (A : AffAdaptation D d) (a : ℕ) :
    Submodule ↥(gluedSubalgebra A) (A.ThetaPieceProd (π := π) a) :=
  LinearMap.ker (A.thetaIntrinsicDeltaLeftGlued (π := π) a -
    A.thetaIntrinsicDeltaRightGlued (π := π) a)

/-- Membership in the `A_D`-linear kernel is pairwise equality on overlaps. -/
lemma mem_intrinsicThetaGluedKernelOver_iff (A : AffAdaptation D d) (a : ℕ)
    (s : A.ThetaPieceProd (π := π) a) :
    s ∈ A.intrinsicThetaGluedKernelOver (π := π) a ↔
      ∀ p : D.index × D.index,
        A.thetaToOverlapLeft (π := π) a p.1 p.2 (s p.1) =
          A.thetaToOverlapRight (π := π) a p.1 p.2 (s p.2) := by
  simp only [intrinsicThetaGluedKernelOver, LinearMap.mem_ker, LinearMap.sub_apply,
    sub_eq_zero, funext_iff, thetaIntrinsicDeltaLeftGlued,
    thetaIntrinsicDeltaRightGlued, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, thetaToOverlapLeftGlued,
    thetaToOverlapRightGlued]
  rfl

/-- The previously constructed intrinsic theta `A_D`-module is exactly the kernel of the
`A_D`-linear descent fork. -/
theorem intrinsicThetaGluedOver_eq_ker (A : AffAdaptation D d) (a : ℕ) :
    A.intrinsicThetaGluedOver (π := π) a =
      A.intrinsicThetaGluedKernelOver (π := π) a := by
  ext s
  change s ∈ A.intrinsicThetaGluedSubmodule (π := π) a ↔ _
  rw [A.mem_intrinsicThetaGluedSubmodule_iff,
    A.mem_intrinsicThetaGluedKernelOver_iff]

/-- Projection of the intrinsic theta equalizer to one piece quotient. -/
noncomputable def intrinsicThetaGluedToPiece (A : AffAdaptation D d) (a : ℕ)
    (j : D.index) :
    A.IntrinsicThetaGluedOver (π := π) a →ₗ[↥(gluedSubalgebra A)]
      A.ThetaPieceQuotient (π := π) a j :=
  LinearMap.proj j ∘ₗ (A.intrinsicThetaGluedOver (π := π) a).subtype

/-- The piece projections from the intrinsic theta equalizer agree on every overlap. -/
theorem intrinsicThetaGluedToPiece_overlap (A : AffAdaptation D d) (a : ℕ)
    (i j : D.index) :
    A.thetaToOverlapLeftGlued (π := π) a i j ∘ₗ
        A.intrinsicThetaGluedToPiece (π := π) a i =
      A.thetaToOverlapRightGlued (π := π) a i j ∘ₗ
        A.intrinsicThetaGluedToPiece (π := π) a j := by
  apply LinearMap.ext
  intro x
  exact (A.mem_intrinsicThetaGluedSubmodule_iff (π := π) a _).mp x.2 (i, j)

section Universal

variable (A : AffAdaptation D d)
variable {M : Type u} [AddCommGroup M]
  [Module ↥(gluedSubalgebra A) M]

set_option synthInstance.maxHeartbeats 200000 in
-- The nested dependent-product module action exceeds the default instance-search budget.
/-- A compatible family of `A_D`-linear maps to the piece theta quotients factors through
the intrinsic theta equalizer. -/
noncomputable def intrinsicThetaGluedOverLift (a : ℕ)
    (f : ∀ j : D.index, M →ₗ[↥(gluedSubalgebra A)]
      A.ThetaPieceQuotient (π := π) a j)
    (hf : ∀ i j : D.index,
      A.thetaToOverlapLeftGlued (π := π) a i j ∘ₗ f i =
        A.thetaToOverlapRightGlued (π := π) a i j ∘ₗ f j) :
    M →ₗ[↥(gluedSubalgebra A)]
      A.IntrinsicThetaGluedOver (π := π) a where
  toFun x := ⟨fun j => f j x, by
    apply (A.mem_intrinsicThetaGluedSubmodule_iff (π := π) a _).mpr
    rintro ⟨i, j⟩
    exact LinearMap.congr_fun (hf i j) x⟩
  map_add' x y := by
    apply Subtype.ext
    funext j
    exact (f j).map_add x y
  map_smul' c x := by
    apply Subtype.ext
    funext j
    exact (f j).map_smul c x

set_option synthInstance.maxHeartbeats 200000 in
-- The statement unfolds the same nested dependent-product module action as the lift.
@[simp]
lemma intrinsicThetaGluedOverLift_apply (a : ℕ)
    (f : ∀ j : D.index, M →ₗ[↥(gluedSubalgebra A)]
      A.ThetaPieceQuotient (π := π) a j)
    (hf : ∀ i j : D.index,
      A.thetaToOverlapLeftGlued (π := π) a i j ∘ₗ f i =
        A.thetaToOverlapRightGlued (π := π) a i j ∘ₗ f j)
    (x : M) (j : D.index) :
    (A.intrinsicThetaGluedOverLift (π := π) a f hf x :
      A.ThetaPieceProd (π := π) a) j = f j x := by
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Comparing the two dependent-product linear maps needs the lift's instance-search budget.
/-- The compatible-family lift is the unique `A_D`-linear map with the prescribed piece
projections. -/
theorem intrinsicThetaGluedOverLift_unique (a : ℕ)
    (f : ∀ j : D.index, M →ₗ[↥(gluedSubalgebra A)]
      A.ThetaPieceQuotient (π := π) a j)
    (hf : ∀ i j : D.index,
      A.thetaToOverlapLeftGlued (π := π) a i j ∘ₗ f i =
        A.thetaToOverlapRightGlued (π := π) a i j ∘ₗ f j)
    (g : M →ₗ[↥(gluedSubalgebra A)]
      A.IntrinsicThetaGluedOver (π := π) a)
    (hg : ∀ j : D.index,
      A.intrinsicThetaGluedToPiece (π := π) a j ∘ₗ g = f j) :
    g = A.intrinsicThetaGluedOverLift (π := π) a f hf := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext j
  exact LinearMap.congr_fun (hg j) x

end Universal

end AffAdaptation

end AlgebraicGeometry
