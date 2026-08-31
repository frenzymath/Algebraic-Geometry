/-
Copyright (c) 2026 The StacksPart06Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart06Lib Contributors
-/

import StacksPart06Lib.TrivialSquareZero
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Under.Basic

/-!
# The square-zero extension functor

The construction `M \mapsto R[M]` from the deformation-theory blueprint is
functorial in the module.  This file packages the construction as a functor
to the category of commutative rings over `R`.  We work in one universe so
that the underlying extension can be an object of `Over (CommRingCat.of R)`.
-/

namespace StacksPart06Lib

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R]

/-- The opposite-module action needed by `TrivSqZeroExt`, obtained from
commutativity of the base ring. -/
private abbrev squareZeroOppositeModule (M : Type u) [AddCommGroup M]
    [Module R M] : Module Rᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id R).fromOpposite (by
    intro x y
    exact mul_comm x y))

/-- A module, viewed with the opposite scalar action used by the square-zero
extension API. -/
private abbrev squareZeroOppositeScalar (M : Type u) [AddCommGroup M]
    [Module R M] : SMul Rᵐᵒᵖ M :=
  (@Module.toDistribMulAction Rᵐᵒᵖ M _ _
    (squareZeroOppositeModule (R := R) M)).toSMul

/-- The left and opposite scalar actions commute on a commutative ring. -/
private abbrev squareZeroCentralScalar (M : Type u) [AddCommGroup M]
    [Module R M] :
    @IsCentralScalar R M (inferInstance : SMul R M)
      (squareZeroOppositeScalar (R := R) M) :=
  @IsCentralScalar.mk R M (inferInstance : SMul R M)
    (squareZeroOppositeScalar (R := R) M) (fun r m => by
      change @SMul.smul Rᵐᵒᵖ M (squareZeroOppositeScalar (R := R) M)
          (MulOpposite.op r) m = @SMul.smul R M _ r m
      rfl)

/-- The object `R[M] \to R` in commutative rings over `R`. -/
noncomputable def squareZeroExtensionOverObj (M : ModuleCat.{u} R) :
    Over (CommRingCat.of R) := by
  letI : Module Rᵐᵒᵖ M := squareZeroOppositeModule (R := R) M
  letI : SMul Rᵐᵒᵖ M := squareZeroOppositeScalar (R := R) M
  letI : IsCentralScalar R M := squareZeroCentralScalar (R := R) M
  exact Over.mk
    (CommRingCat.ofHom
      (squareZeroExtensionProjection (R := R) (M := M)).toRingHom)

/-- A module map induces the corresponding map of square-zero extensions over
the base ring. -/
noncomputable def squareZeroExtensionOverMap {M N : ModuleCat.{u} R}
    (f : M ⟶ N) :
    squareZeroExtensionOverObj (R := R) M ⟶
      squareZeroExtensionOverObj (R := R) N := by
  letI : Module Rᵐᵒᵖ M := squareZeroOppositeModule (R := R) M
  letI : SMul Rᵐᵒᵖ M := squareZeroOppositeScalar (R := R) M
  letI : IsCentralScalar R M := squareZeroCentralScalar (R := R) M
  letI : Module Rᵐᵒᵖ N := squareZeroOppositeModule (R := R) N
  letI : SMul Rᵐᵒᵖ N := squareZeroOppositeScalar (R := R) N
  letI : IsCentralScalar R N := squareZeroCentralScalar (R := R) N
  refine Over.homMk
    (CommRingCat.ofHom
      (squareZeroExtensionMap (R := R) f.hom).toRingHom) ?_
  change
    CommRingCat.ofHom
          (squareZeroExtensionMap (R := R) f.hom).toRingHom ≫
        (squareZeroExtensionOverObj (R := R) N).hom =
      (squareZeroExtensionOverObj (R := R) M).hom
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact squareZeroExtensionMap_projection (R := R) f.hom x

/-- The square-zero extension assignment as a functor over the base ring. -/
noncomputable def squareZeroExtensionOverFunctor :
    ModuleCat.{u} R ⥤ Over (CommRingCat.of R) where
  obj := squareZeroExtensionOverObj (R := R)
  map := fun f => squareZeroExtensionOverMap (R := R) f
  map_id := by
    intro M
    letI : Module Rᵐᵒᵖ M := squareZeroOppositeModule (R := R) M
    letI : SMul Rᵐᵒᵖ M := squareZeroOppositeScalar (R := R) M
    letI : IsCentralScalar R M := squareZeroCentralScalar (R := R) M
    apply Over.OverMorphism.ext
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change
      squareZeroExtensionMap (R := R)
          (LinearMap.id : (M : Type u) →ₗ[R] (M : Type u)) x = x
    rw [squareZeroExtensionMap_id]
    rfl
  map_comp := by
    intro M N P f g
    letI : Module Rᵐᵒᵖ M := squareZeroOppositeModule (R := R) M
    letI : SMul Rᵐᵒᵖ M := squareZeroOppositeScalar (R := R) M
    letI : IsCentralScalar R M := squareZeroCentralScalar (R := R) M
    letI : Module Rᵐᵒᵖ N := squareZeroOppositeModule (R := R) N
    letI : SMul Rᵐᵒᵖ N := squareZeroOppositeScalar (R := R) N
    letI : IsCentralScalar R N := squareZeroCentralScalar (R := R) N
    letI : Module Rᵐᵒᵖ P := squareZeroOppositeModule (R := R) P
    letI : SMul Rᵐᵒᵖ P := squareZeroOppositeScalar (R := R) P
    letI : IsCentralScalar R P := squareZeroCentralScalar (R := R) P
    apply Over.OverMorphism.ext
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change
      squareZeroExtensionMap (R := R) ((g.hom).comp f.hom) x =
        (squareZeroExtensionMap (R := R) g.hom)
          ((squareZeroExtensionMap (R := R) f.hom) x)
    rw [squareZeroExtensionMap_comp]
    rfl

end

end StacksPart06Lib
