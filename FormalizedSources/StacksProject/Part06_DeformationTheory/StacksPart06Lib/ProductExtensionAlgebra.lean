/-
Copyright (c) 2026 The StacksPart06Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart06Lib Contributors
-/

import StacksPart06Lib.ProductExtension

/-!
# The product equivalence as an algebra equivalence

The equalizer presentation of the fiber product carries a canonical `R`-algebra
structure: `r : R` acts by the pair of scalar inclusions.  This file packages
the ring equivalence from `ProductExtension` as an `AlgEquiv` over `R`.
-/

namespace StacksPart06Lib

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommRing R]
variable [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]

/-- The diagonal copy of `R` in the coordinate fiber product. -/
def squareZeroExtensionProductAlgebraMap :
    R →+* SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N) :=
  ((squareZeroExtensionInclusion (R := R) (M := M)).prod
      (squareZeroExtensionInclusion (R := R) (M := N))).codRestrict
    (SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N))
    (by
      intro r
      rw [RingHom.mem_eqLocus]
      rfl)

@[simp]
theorem squareZeroExtensionProductAlgebraMap_apply (r : R) :
    (squareZeroExtensionProductAlgebraMap (R := R) (M := M) (N := N) r :
      SquareZeroExtension R M × SquareZeroExtension R N) =
      (squareZeroExtensionInclusion (R := R) (M := M) r,
       squareZeroExtensionInclusion (R := R) (M := N) r) := by
  change ((squareZeroExtensionInclusion (R := R) (M := M) r,
    squareZeroExtensionInclusion (R := R) (M := N) r) :
      SquareZeroExtension R M × SquareZeroExtension R N) = _
  rfl

/- The equalizer is a commutative subring of the product, so `toAlgebra` applies. -/
instance squareZeroExtensionProductAlgebra :
    Algebra R (SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N)) :=
  RingHom.toAlgebra (squareZeroExtensionProductAlgebraMap (R := R) (M := M) (N := N))

@[simp]
theorem squareZeroExtensionProductAlgebraMap_eq_algebraMap (r : R) :
    squareZeroExtensionProductAlgebraMap (R := R) (M := M) (N := N) r =
      algebraMap R (SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N)) r :=
  rfl

/-- The product-preservation equivalence over the base ring `R`. -/
noncomputable def squareZeroExtensionProductAlgEquiv :
    SquareZeroExtension R (M × N) ≃ₐ[R]
      SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N) :=
  AlgEquiv.ofRingEquiv
    (f := squareZeroExtensionProductRingEquiv (R := R) (M := M) (N := N))
    (by
      intro r
      change squareZeroExtensionProductRingEquiv (R := R) (M := M) (N := N)
          (squareZeroExtensionInclusion (R := R) (M := M × N) r) =
        squareZeroExtensionProductAlgebraMap (R := R) (M := M) (N := N) r
      apply Subtype.ext
      exact squareZeroExtensionProductRingEquiv_inclusion
        (R := R) (M := M) (N := N) r)

@[simp]
theorem squareZeroExtensionProductAlgEquiv_apply
    (x : SquareZeroExtension R (M × N)) :
    (squareZeroExtensionProductAlgEquiv (R := R) (M := M) (N := N) x :
      SquareZeroExtension R M × SquareZeroExtension R N) =
      (squareZeroExtensionMap (LinearMap.fst R M N) x,
       squareZeroExtensionMap (LinearMap.snd R M N) x) := by
  rfl

end StacksPart06Lib
