/-
Copyright (c) 2026 The StacksPart06Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart06Lib Contributors
-/

import StacksPart06Lib.TrivialSquareZero

/-!
# Products of trivial square-zero extensions

The product-preservation lemma in the deformation-theory blueprint identifies
`R[M × N]` with the pullback `R[M] ×_R R[N]`.  We use the equalizer
presentation of a pullback of commutative rings supplied by `RingHom.eqLocus`.
-/

namespace StacksPart06Lib

universe u v w

section

variable {R : Type u} {M : Type v} {N : Type w}

variable [CommRing R]
variable [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]

/-- The left structure map in the coordinate presentation of the pullback. -/
def squareZeroExtensionProductLeft :
    (SquareZeroExtension R M × SquareZeroExtension R N) →+* R :=
  (TrivSqZeroExt.fstHom R R M).toRingHom.comp (RingHom.fst _ _)

/-- The right structure map in the coordinate presentation of the pullback. -/
def squareZeroExtensionProductRight :
    (SquareZeroExtension R M × SquareZeroExtension R N) →+* R :=
  (TrivSqZeroExt.fstHom R R N).toRingHom.comp (RingHom.snd _ _)

/-- The coordinate realization of `R[M] ×_R R[N]`. -/
abbrev SquareZeroExtensionFiberProduct :=
  RingHom.eqLocus
    (squareZeroExtensionProductLeft (R := R) (M := M) (N := N))
    (squareZeroExtensionProductRight (R := R) (M := M) (N := N))

/-- The map from the extension of a product module to the ambient product. -/
def squareZeroExtensionProductRawMap :
    SquareZeroExtension R (M × N) →+*
      (SquareZeroExtension R M × SquareZeroExtension R N) :=
  (squareZeroExtensionMap (LinearMap.fst R M N)).toRingHom.prod
    (squareZeroExtensionMap (LinearMap.snd R M N)).toRingHom

@[simp]
theorem squareZeroExtensionProductRawMap_apply
    (x : SquareZeroExtension R (M × N)) :
    squareZeroExtensionProductRawMap (R := R) (M := M) (N := N) x =
      (squareZeroExtensionMap (LinearMap.fst R M N) x,
       squareZeroExtensionMap (LinearMap.snd R M N) x) := by
  rfl

@[simp]
theorem squareZeroExtensionProductRawMap_left_base
    (x : SquareZeroExtension R (M × N)) :
    squareZeroExtensionProductLeft (R := R) (M := M) (N := N)
        (squareZeroExtensionProductRawMap (R := R) (M := M) (N := N) x) =
      x.fst := by
  change TrivSqZeroExt.fst
    (TrivSqZeroExt.map (LinearMap.fst R M N) x) = TrivSqZeroExt.fst x
  exact TrivSqZeroExt.fst_map _ _

@[simp]
theorem squareZeroExtensionProductRawMap_right_base
    (x : SquareZeroExtension R (M × N)) :
    squareZeroExtensionProductRight (R := R) (M := M) (N := N)
        (squareZeroExtensionProductRawMap (R := R) (M := M) (N := N) x) =
      x.fst := by
  change TrivSqZeroExt.fst
    (TrivSqZeroExt.map (LinearMap.snd R M N) x) = TrivSqZeroExt.fst x
  exact TrivSqZeroExt.fst_map _ _

@[simp]
theorem squareZeroExtensionProductRawMap_mem
    (x : SquareZeroExtension R (M × N)) :
    squareZeroExtensionProductRawMap (R := R) (M := M) (N := N) x ∈
      SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N) := by
  rw [RingHom.mem_eqLocus]
  exact
    (squareZeroExtensionProductRawMap_left_base
        (R := R) (M := M) (N := N) x).trans
      (squareZeroExtensionProductRawMap_right_base
        (R := R) (M := M) (N := N) x).symm

/-- The pullback-valued ring homomorphism induced by the two projections. -/
def squareZeroExtensionProductMap :
    SquareZeroExtension R (M × N) →+*
      SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N) :=
  (squareZeroExtensionProductRawMap (R := R) (M := M) (N := N)).codRestrict _
    (squareZeroExtensionProductRawMap_mem (R := R) (M := M) (N := N))

@[simp]
theorem squareZeroExtensionProductMap_coe
    (x : SquareZeroExtension R (M × N)) :
    ((squareZeroExtensionProductMap (R := R) (M := M) (N := N) x :
      SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N)) :
      SquareZeroExtension R M × SquareZeroExtension R N) =
      (squareZeroExtensionMap (LinearMap.fst R M N) x,
       squareZeroExtensionMap (LinearMap.snd R M N) x) := by
  rfl

/-- The inverse coordinate map from the equalizer presentation. -/
def squareZeroExtensionProductInverse
    (x : SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N)) :
    SquareZeroExtension R (M × N) :=
  (x.1.1.fst, (x.1.1.snd, x.1.2.snd))

@[simp]
theorem squareZeroExtensionProductInverse_map
    (x : SquareZeroExtension R (M × N)) :
    squareZeroExtensionProductInverse (R := R) (M := M) (N := N)
      (squareZeroExtensionProductMap (R := R) (M := M) (N := N) x) = x := by
  apply TrivSqZeroExt.ext
  · change TrivSqZeroExt.fst
      (TrivSqZeroExt.map (LinearMap.fst R M N) x) = x.fst
    exact TrivSqZeroExt.fst_map _ _
  · apply Prod.ext
    · change TrivSqZeroExt.snd
        (TrivSqZeroExt.map (LinearMap.fst R M N) x) = x.snd.1
      rw [TrivSqZeroExt.snd_map]
      rfl
    · change TrivSqZeroExt.snd
        (TrivSqZeroExt.map (LinearMap.snd R M N) x) = x.snd.2
      rw [TrivSqZeroExt.snd_map]
      rfl

@[simp]
theorem squareZeroExtensionProductMap_inverse
    (x : SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N)) :
    squareZeroExtensionProductMap (R := R) (M := M) (N := N)
      (squareZeroExtensionProductInverse (R := R) (M := M) (N := N) x) = x := by
  have hx : x.1.1.fst = x.1.2.fst := by
    change squareZeroExtensionProductLeft (R := R) (M := M) (N := N) x.1 =
      squareZeroExtensionProductRight (R := R) (M := M) (N := N) x.1
    exact x.2
  apply Subtype.ext
  apply Prod.ext
  · apply TrivSqZeroExt.ext
    · change TrivSqZeroExt.fst
        (TrivSqZeroExt.map (LinearMap.fst R M N)
          (x.1.1.fst, (x.1.1.snd, x.1.2.snd))) = x.1.1.fst
      rw [TrivSqZeroExt.fst_map]
      rfl
    · change TrivSqZeroExt.snd
        (TrivSqZeroExt.map (LinearMap.fst R M N)
          (x.1.1.fst, (x.1.1.snd, x.1.2.snd))) = x.1.1.snd
      rw [TrivSqZeroExt.snd_map]
      rfl
  · apply TrivSqZeroExt.ext
    · change TrivSqZeroExt.fst
        (TrivSqZeroExt.map (LinearMap.snd R M N)
          (x.1.1.fst, (x.1.1.snd, x.1.2.snd))) = x.1.2.fst
      rw [TrivSqZeroExt.fst_map]
      exact hx
    · change TrivSqZeroExt.snd
        (TrivSqZeroExt.map (LinearMap.snd R M N)
          (x.1.1.fst, (x.1.1.snd, x.1.2.snd))) = x.1.2.snd
      rw [TrivSqZeroExt.snd_map]
      rfl

theorem squareZeroExtensionProductMap_bijective :
    Function.Bijective
      (squareZeroExtensionProductMap (R := R) (M := M) (N := N)) := by
  constructor
  · intro x y h
    have h' := congrArg
      (squareZeroExtensionProductInverse (R := R) (M := M) (N := N)) h
    simpa using h'
  · intro x
    exact
      ⟨squareZeroExtensionProductInverse (R := R) (M := M) (N := N) x,
        squareZeroExtensionProductMap_inverse
          (R := R) (M := M) (N := N) x⟩

/-- The product-preservation equivalence for trivial square-zero extensions. -/
noncomputable def squareZeroExtensionProductRingEquiv :
    SquareZeroExtension R (M × N) ≃+*
      SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N) :=
  RingEquiv.ofBijective
    (squareZeroExtensionProductMap (R := R) (M := M) (N := N))
    (squareZeroExtensionProductMap_bijective (R := R) (M := M) (N := N))

@[simp]
theorem squareZeroExtensionProductRingEquiv_apply
    (x : SquareZeroExtension R (M × N)) :
    (squareZeroExtensionProductRingEquiv (R := R) (M := M) (N := N) x :
      SquareZeroExtension R M × SquareZeroExtension R N) =
      (squareZeroExtensionMap (LinearMap.fst R M N) x,
       squareZeroExtensionMap (LinearMap.snd R M N) x) := by
  rfl

@[simp]
theorem squareZeroExtensionProductRingEquiv_inclusion (r : R) :
    (squareZeroExtensionProductRingEquiv (R := R) (M := M) (N := N)
      (squareZeroExtensionInclusion (R := R) (M := M × N) r) :
      SquareZeroExtensionFiberProduct (R := R) (M := M) (N := N)).1 =
      (squareZeroExtensionInclusion (R := R) (M := M) r,
       squareZeroExtensionInclusion (R := R) (M := N) r) := by
  apply Prod.ext <;> simp [squareZeroExtensionProductRingEquiv]

section Subsingleton

variable {P : Type w}
variable [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]
variable [Subsingleton P]

/-- A square-zero extension by a subsingleton module is the base ring. -/
noncomputable def squareZeroExtensionSubsingletonRingEquiv :
    SquareZeroExtension R P ≃+* R :=
  RingEquiv.ofBijective
    (squareZeroExtensionProjection (R := R) (M := P)).toRingHom
    (by
      constructor
      · intro x y h
        apply TrivSqZeroExt.ext
        · exact h
        · exact Subsingleton.elim _ _
      · intro r
        exact
          ⟨squareZeroExtensionInclusion (R := R) (M := P) r,
            squareZeroExtensionProjection_inclusion (R := R) (M := P) r⟩)

@[simp]
theorem squareZeroExtensionSubsingletonRingEquiv_apply
    (x : SquareZeroExtension R P) :
    squareZeroExtensionSubsingletonRingEquiv (R := R) (P := P) x = x.fst := by
  rfl

@[simp]
theorem squareZeroExtensionSubsingletonRingEquiv_inclusion (r : R) :
    squareZeroExtensionSubsingletonRingEquiv (R := R) (P := P)
      (squareZeroExtensionInclusion (R := R) (M := P) r) = r := by
  rfl

end Subsingleton

end

end StacksPart06Lib
