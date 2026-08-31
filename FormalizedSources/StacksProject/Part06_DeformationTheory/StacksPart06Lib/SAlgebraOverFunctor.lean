/-
Copyright (c) 2026 The StacksPart06Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart06Lib Contributors
-/

import StacksPart06Lib.TangentAlgebraFunctor
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Square-zero extensions over a scalar algebra

For a fixed algebra `S -> R`, the square-zero extension assignment can be
bundled in the over-category of `S`-algebras.  The construction is kept
explicit: the opposite action on a module is transported across commutativity
of `R`, and the `S`-algebra structure on `R[M]` is the composite
`S -> R -> R[M]`.

This is the categorical packaging needed before proving the finite-product
statement in the deformation-theory source.
-/

namespace StacksPart06Lib

open CategoryTheory

universe u

section

variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]

/- The opposite action is canonical for a commutative base ring. -/
@[reducible]
private def sAlgOppositeModule (M : ModuleCat.{u, u} R) :
    Module Rᵐᵒᵖ (M : Type u) :=
  Module.compHom (M : Type u)
    ((RingHom.id R).fromOpposite (by
      intro x y
      exact mul_comm x y))

@[reducible]
private def sAlgOppositeScalar (M : ModuleCat.{u, u} R) :
    SMul Rᵐᵒᵖ (M : Type u) :=
  (@Module.toDistribMulAction Rᵐᵒᵖ (M : Type u) _ _
    (sAlgOppositeModule (R := R) M)).toSMul

@[reducible]
private def sAlgCentralScalar (M : ModuleCat.{u, u} R) :
    @IsCentralScalar R (M : Type u) (inferInstance : SMul R (M : Type u))
      (sAlgOppositeScalar (R := R) M) :=
  @IsCentralScalar.mk R (M : Type u) (inferInstance : SMul R (M : Type u))
    (sAlgOppositeScalar (R := R) M) (fun r m => by
      change @SMul.smul Rᵐᵒᵖ (M : Type u) (sAlgOppositeScalar (R := R) M)
          (MulOpposite.op r) m = @SMul.smul R (M : Type u) _ r m
      rfl)

@[reducible]
private def sAlgExtensionRing (M : ModuleCat.{u, u} R) :
    CommRing (TrivSqZeroExt R (M : Type u)) :=
  @TrivSqZeroExt.commRing R (M : Type u) inferInstance inferInstance
    (inferInstance : Module R (M : Type u))
    (sAlgOppositeModule (R := R) M) (sAlgCentralScalar (R := R) M)

/- The object `R[M]` with its explicit `S`-algebra structure. -/
noncomputable def squareZeroSAlgObject (M : ModuleCat.{u, u} R) : AlgCat S := by
  letI : Module Rᵐᵒᵖ (M : Type u) := sAlgOppositeModule (R := R) M
  letI : SMul Rᵐᵒᵖ (M : Type u) := sAlgOppositeScalar (R := R) M
  letI : IsCentralScalar R (M : Type u) := sAlgCentralScalar (R := R) M
  letI : CommRing (TrivSqZeroExt R (M : Type u)) := sAlgExtensionRing (R := R) M
  let scalar : S →+* TrivSqZeroExt R (M : Type u) :=
    (TrivSqZeroExt.inlHom R (M : Type u)).comp (algebraMap S R)
  letI : Algebra S (TrivSqZeroExt R (M : Type u)) := RingHom.toAlgebra scalar
  exact AlgCat.of S (TrivSqZeroExt R (M : Type u))

/- The projection to `R` is an `S`-algebra map for this scalar structure. -/
noncomputable def squareZeroSAlgProjection (M : ModuleCat.{u, u} R) :
    squareZeroSAlgObject (S := S) (R := R) M ⟶ AlgCat.of S R := by
  letI : Module Rᵐᵒᵖ (M : Type u) := sAlgOppositeModule (R := R) M
  letI : SMul Rᵐᵒᵖ (M : Type u) := sAlgOppositeScalar (R := R) M
  letI : IsCentralScalar R (M : Type u) := sAlgCentralScalar (R := R) M
  letI : CommRing (TrivSqZeroExt R (M : Type u)) := sAlgExtensionRing (R := R) M
  let scalar : S →+* TrivSqZeroExt R (M : Type u) :=
    (TrivSqZeroExt.inlHom R (M : Type u)).comp (algebraMap S R)
  letI : Algebra S (TrivSqZeroExt R (M : Type u)) := RingHom.toAlgebra scalar
  exact AlgCat.ofHom (AlgHom.mk
    (TrivSqZeroExt.fstHom R R (M : Type u)).toRingHom
    (by
      intro s
      rfl))

/- A module map induces an `S`-algebra map between the extensions. -/
noncomputable def squareZeroSAlgMap {M N : ModuleCat.{u, u} R} (f : M ⟶ N) :
    squareZeroSAlgObject (S := S) (R := R) M ⟶
      squareZeroSAlgObject (S := S) (R := R) N := by
  letI : Module Rᵐᵒᵖ (M : Type u) := sAlgOppositeModule (R := R) M
  letI : SMul Rᵐᵒᵖ (M : Type u) := sAlgOppositeScalar (R := R) M
  letI : IsCentralScalar R (M : Type u) := sAlgCentralScalar (R := R) M
  letI : CommRing (TrivSqZeroExt R (M : Type u)) := sAlgExtensionRing (R := R) M
  let scalarM : S →+* TrivSqZeroExt R (M : Type u) :=
    (TrivSqZeroExt.inlHom R (M : Type u)).comp (algebraMap S R)
  letI : Algebra S (TrivSqZeroExt R (M : Type u)) := RingHom.toAlgebra scalarM
  letI : Module Rᵐᵒᵖ (N : Type u) := sAlgOppositeModule (R := R) N
  letI : SMul Rᵐᵒᵖ (N : Type u) := sAlgOppositeScalar (R := R) N
  letI : IsCentralScalar R (N : Type u) := sAlgCentralScalar (R := R) N
  letI : CommRing (TrivSqZeroExt R (N : Type u)) := sAlgExtensionRing (R := R) N
  let scalarN : S →+* TrivSqZeroExt R (N : Type u) :=
    (TrivSqZeroExt.inlHom R (N : Type u)).comp (algebraMap S R)
  letI : Algebra S (TrivSqZeroExt R (N : Type u)) := RingHom.toAlgebra scalarN
  exact AlgCat.ofHom (AlgHom.mk
    (squareZeroExtensionMap (R := R) f.hom).toRingHom
    (by
      intro s
      change squareZeroExtensionMap (R := R) f.hom
          (TrivSqZeroExt.inl (algebraMap S R s)) =
        TrivSqZeroExt.inl (algebraMap S R s)
      rw [squareZeroExtensionMap_inclusion]))

/- The projection makes the assignment an object of `S-Alg/R`. -/
noncomputable def squareZeroSAlgOverObj (M : ModuleCat.{u, u} R) :
    Over (AlgCat.of S R) :=
  Over.mk (squareZeroSAlgProjection (S := S) (R := R) M)

noncomputable def squareZeroSAlgOverMap {M N : ModuleCat.{u, u} R} (f : M ⟶ N) :
    squareZeroSAlgOverObj (S := S) (R := R) M ⟶
      squareZeroSAlgOverObj (S := S) (R := R) N := by
  letI : Module Rᵐᵒᵖ (M : Type u) := sAlgOppositeModule (R := R) M
  letI : SMul Rᵐᵒᵖ (M : Type u) := sAlgOppositeScalar (R := R) M
  letI : IsCentralScalar R (M : Type u) := sAlgCentralScalar (R := R) M
  letI : Module Rᵐᵒᵖ (N : Type u) := sAlgOppositeModule (R := R) N
  letI : SMul Rᵐᵒᵖ (N : Type u) := sAlgOppositeScalar (R := R) N
  letI : IsCentralScalar R (N : Type u) := sAlgCentralScalar (R := R) N
  refine Over.homMk (squareZeroSAlgMap (S := S) (R := R) f) ?_
  apply AlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change (TrivSqZeroExt.fstHom R R (N : Type u))
      (squareZeroExtensionMap (R := R) f.hom x) =
    (TrivSqZeroExt.fstHom R R (M : Type u)) x
  exact squareZeroExtensionMap_projection (R := R) f.hom x

/- The source-faithful `S-Alg/R` square-zero extension functor. -/
noncomputable def squareZeroSAlgOverFunctor :
    ModuleCat.{u, u} R ⥤ Over (AlgCat.of S R) where
  obj := squareZeroSAlgOverObj (S := S) (R := R)
  map := fun f => squareZeroSAlgOverMap (S := S) (R := R) f
  map_id := by
    intro M
    letI : Module Rᵐᵒᵖ (M : Type u) := sAlgOppositeModule (R := R) M
    letI : SMul Rᵐᵒᵖ (M : Type u) := sAlgOppositeScalar (R := R) M
    letI : IsCentralScalar R (M : Type u) := sAlgCentralScalar (R := R) M
    apply Over.OverMorphism.ext
    apply AlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change squareZeroExtensionMap (R := R)
        (LinearMap.id : (M : Type u) →ₗ[R] (M : Type u)) x = x
    rw [squareZeroExtensionMap_id]
    rfl
  map_comp := by
    intro M N P f g
    letI : Module Rᵐᵒᵖ (M : Type u) := sAlgOppositeModule (R := R) M
    letI : SMul Rᵐᵒᵖ (M : Type u) := sAlgOppositeScalar (R := R) M
    letI : IsCentralScalar R (M : Type u) := sAlgCentralScalar (R := R) M
    letI : Module Rᵐᵒᵖ (N : Type u) := sAlgOppositeModule (R := R) N
    letI : SMul Rᵐᵒᵖ (N : Type u) := sAlgOppositeScalar (R := R) N
    letI : IsCentralScalar R (N : Type u) := sAlgCentralScalar (R := R) N
    letI : Module Rᵐᵒᵖ (P : Type u) := sAlgOppositeModule (R := R) P
    letI : SMul Rᵐᵒᵖ (P : Type u) := sAlgOppositeScalar (R := R) P
    letI : IsCentralScalar R (P : Type u) := sAlgCentralScalar (R := R) P
    apply Over.OverMorphism.ext
    apply AlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change squareZeroExtensionMap (R := R) ((g.hom).comp f.hom) x =
      (squareZeroExtensionMap (R := R) g.hom)
        ((squareZeroExtensionMap (R := R) f.hom) x)
    rw [squareZeroExtensionMap_comp]
    rfl

end

end StacksPart06Lib
