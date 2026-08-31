/-
Copyright (c) 2026 The StacksPart06Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart06Lib Contributors
-/

import StacksPart06Lib.ProductExtensionAlgebra

/-!
# Square-zero products over a second base

The deformation-theory statement is made in a category of algebras over a
fixed base `S`.  The product equivalence is constructed above as an
`R`-algebra equivalence, where `R` is the ring being thickened.  This file
records the extra structure needed to regard the same maps as maps over an
arbitrary scalar ring `S` with an algebra structure on `R`.

The scalar maps are kept explicit rather than installed as global `Algebra`
instances.  That avoids competing instance paths while still exposing the
commutation law used by an `S`-algebra-over-`R` formulation.
-/

namespace StacksPart06Lib

universe s u v w

variable {S : Type s} {R : Type u} {M : Type v} {N : Type w}
variable [CommRing S] [CommRing R] [Algebra S R]
variable [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]

/-- The scalar map on a square-zero extension induced by `S → R`. -/
def squareZeroExtensionScalarMap (P : Type*) [AddCommGroup P]
    [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P] :
    S →+* SquareZeroExtension R P :=
  (squareZeroExtensionInclusion (R := R) (M := P)).comp (algebraMap S R)

@[simp]
theorem squareZeroExtensionScalarMap_apply (P : Type*) [AddCommGroup P]
    [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P] (s : S) :
    squareZeroExtensionScalarMap (S := S) (R := R) P s =
      squareZeroExtensionInclusion (R := R) (M := P) (algebraMap S R s) :=
  rfl

/-- The induced scalar map into the coordinate fiber product. -/
def squareZeroExtensionProductScalarMap :
    S →+* SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N) :=
  (squareZeroExtensionProductAlgebraMap (R := R) (M := M) (N := N)).comp
    (algebraMap S R)

@[simp]
theorem squareZeroExtensionProductScalarMap_apply (s : S) :
    squareZeroExtensionProductScalarMap (S := S) (R := R) (M := M) (N := N) s =
      squareZeroExtensionProductAlgebraMap (R := R) (M := M) (N := N)
        (algebraMap S R s) :=
  rfl

/-- The product equivalence commutes with the explicitly chosen `S`-scalar maps. -/
theorem squareZeroExtensionProductRingEquiv_scalar (s : S) :
    squareZeroExtensionProductRingEquiv (R := R) (M := M) (N := N)
        (squareZeroExtensionScalarMap (S := S) (R := R) (M × N) s) =
      squareZeroExtensionProductScalarMap (S := S) (R := R) (M := M) (N := N) s := by
  change squareZeroExtensionProductRingEquiv (R := R) (M := M) (N := N)
      (squareZeroExtensionInclusion (R := R) (M := M × N) (algebraMap S R s)) =
    squareZeroExtensionProductAlgebraMap (R := R) (M := M) (N := N)
      (algebraMap S R s)
  apply Subtype.ext
  exact squareZeroExtensionProductRingEquiv_inclusion (R := R) (M := M) (N := N)
    (algebraMap S R s)

/-- The left base projection is preserved by the product equivalence. -/
@[simp]
theorem squareZeroExtensionProductRingEquiv_left_base
    (x : SquareZeroExtension R (M × N)) :
    squareZeroExtensionProductLeft (R := R) (M := M) (N := N)
        (squareZeroExtensionProductRingEquiv (R := R) (M := M) (N := N) x :
          SquareZeroExtension R M × SquareZeroExtension R N) =
      squareZeroExtensionProjection (R := R) (M := M × N) x := by
  change TrivSqZeroExt.fst
      (squareZeroExtensionMap (LinearMap.fst R M N) x) = x.fst
  exact TrivSqZeroExt.fst_map _ _

/-- The right base projection is preserved by the product equivalence. -/
@[simp]
theorem squareZeroExtensionProductRingEquiv_right_base
    (x : SquareZeroExtension R (M × N)) :
    squareZeroExtensionProductRight (R := R) (M := M) (N := N)
        (squareZeroExtensionProductRingEquiv (R := R) (M := M) (N := N) x :
          SquareZeroExtension R M × SquareZeroExtension R N) =
      squareZeroExtensionProjection (R := R) (M := M × N) x := by
  change TrivSqZeroExt.fst
      (squareZeroExtensionMap (LinearMap.snd R M N) x) = x.fst
  exact TrivSqZeroExt.fst_map _ _

end StacksPart06Lib
