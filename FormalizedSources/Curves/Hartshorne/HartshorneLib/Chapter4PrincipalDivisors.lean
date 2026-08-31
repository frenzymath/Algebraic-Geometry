/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1CurveStalks
import HartshorneLib.Chapter4Curves

/-!
# Hartshorne II.6 and IV.1: principal divisors on curves

For a non-generic point of an integral smooth curve, its DVR stalk determines
an integer-valued order on nonzero rational functions. On a quasi-compact
finite-type curve, only finitely many of these orders are nonzero. This file
constructs the resulting principal divisor and records that principal
divisors form an additive subgroup of the divisor group.

The sign is the classical one: a uniformizer has order `+1`. Mathlib's adic
valuation has additive value `-1` on a uniformizer, so `orderZAt` inverts its
value after extracting the integer-valued unit.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits
open AlgebraicGeometry

namespace Hartshorne

/-!
## Orders at non-generic points
-/

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The height-one prime of a DVR stalk, represented by its maximal ideal. -/
noncomputable def stalkHeightOne (X : Scheme.{u}) [IsIntegral X] (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    IsDedekindDomain.HeightOneSpectrum (X.presheaf.stalk x) where
  asIdeal := IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  isPrime := (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).isPrime
  ne_bot := IsDiscreteValuationRing.not_a_field (X.presheaf.stalk x)

/-- The adic valuation of the function field at a non-generic point of an
integral smooth curve. -/
noncomputable def orderAt (f : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X}
    (hx : x ≠ genericPoint X) :
    Valuation X.functionField (WithZero (Multiplicative ℤ)) := by
  letI := smoothCurve_stalk_isDiscreteValuationRing f hx
  letI := smoothCurve_stalk_isDedekindDomain f hx
  exact (stalkHeightOne X x).valuation X.functionField

/-- The classical integer-valued order on units of the function field. -/
noncomputable def orderZAt (f : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X}
    (hx : x ≠ genericPoint X) : X.functionFieldˣ →* Multiplicative ℤ :=
  invMonoidHom.comp
    (WithZero.unitsWithZeroEquiv.toMonoidHom.comp
      (Units.map (orderAt f hx).toMonoidWithZeroHom.toMonoidHom))

/-- The classical order is multiplicative on powers of a rational function. -/
theorem orderZAt_pow (f : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X}
    (hx : x ≠ genericPoint X) (g : X.functionFieldˣ) (n : ℕ) :
    orderZAt f hx (g ^ n) = (orderZAt f hx g) ^ n := by
  exact map_pow (orderZAt f hx) g n

/-- `orderAt` is the adic valuation of the maximal ideal of the stalk. -/
theorem orderAt_eq_valuation (f : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X}
    (hx : x ≠ genericPoint X) :
    letI := smoothCurve_stalk_isDiscreteValuationRing f hx
    orderAt f hx = (stalkHeightOne X x).valuation X.functionField :=
  rfl

/-- A rational function represented by a section has trivial order wherever
that section is a unit. -/
theorem orderAt_eq_one_of_mem_basicOpen (f : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X}
    (hx : x ≠ genericPoint X) {U : X.Opens} (s : Γ(X, U))
    (heta : genericPoint X ∈ U) (hx_mem : x ∈ X.basicOpen s) :
    orderAt f hx ((X.presheaf.germ U (genericPoint X) heta).hom s) = 1 := by
  letI := smoothCurve_stalk_isDiscreteValuationRing f hx
  letI := smoothCurve_stalk_isDedekindDomain f hx
  have hxU : x ∈ U := X.basicOpen_le s hx_mem
  have hunit : IsUnit ((X.presheaf.germ U x hxU).hom s) :=
    (X.mem_basicOpen s x hxU).mp hx_mem
  have hord : orderAt f hx = (stalkHeightOne X x).valuation X.functionField := rfl
  have hgs : (X.presheaf.germ U (genericPoint X) heta).hom s =
      algebraMap (X.presheaf.stalk x) X.functionField
        ((X.presheaf.germ U x hxU).hom s) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact (X.presheaf.germ_stalkSpecializes_apply
      hxU ((genericPoint_spec X).specializes trivial) s).symm
  rw [hgs, hord, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact IsLocalRing.notMem_maximalIdeal.mpr hunit

/-- The classical order is zero exactly when the underlying valuation is
trivial. Multiplicative `1` represents additive order zero. -/
theorem orderZAt_eq_one_iff (f : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X}
    (hx : x ≠ genericPoint X) (g : X.functionFieldˣ) :
    orderZAt f hx g = 1 ↔ orderAt f hx (g : X.functionField) = 1 := by
  rw [orderZAt]
  simp only [MonoidHom.comp_apply, invMonoidHom_apply, inv_eq_one,
    MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff, Units.ext_iff, Units.coe_map,
    Units.val_one]
  rfl

/-- A nonzero rational function has nonzero order at only finitely many
points of a quasi-compact finite-type smooth curve. -/
theorem orderZAt_support_finite (f : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] [LocallyOfFiniteType f]
    [QuasiCompact f] (g : X.functionFieldˣ) :
    {p : {x : X // x ≠ genericPoint X} | orderZAt f p.2 g ≠ 1}.Finite := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨U, hetaU, s, hs⟩ := X.presheaf.exists_germ_eq (g : X.functionField)
  have heta_basic : genericPoint X ∈ X.basicOpen s := by
    rw [X.mem_basicOpen s (genericPoint X) hetaU, hs]
    exact g.isUnit
  have hZ : ((X.basicOpen s : Set X)ᶜ).Finite := by
    refine finite_closed_of_avoids_genericPoint
      (fun _ _ h => smoothCurve_specializes_eq_genericPoint_or_eq f h)
      (X.basicOpen s).isOpen.isClosed_compl ?_
    simpa using heta_basic
  refine (hZ.preimage (Subtype.val_injective.injOn)).subset ?_
  intro p hp
  rw [Set.mem_preimage, Set.mem_compl_iff]
  intro hmem
  apply hp
  rw [orderZAt_eq_one_iff, ← hs]
  exact orderAt_eq_one_of_mem_basicOpen f p.2 s hetaU hmem

/-!
## Principal divisors on complete smooth curves
-/

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-- The principal divisor of a nonzero rational function. -/
noncomputable def principalDivisor
    (g : X.left.functionFieldˣ) : CurveDivisor k X :=
  Finsupp.onFinset (orderZAt_support_finite X.hom g).toFinset
    (fun p => Multiplicative.toAdd (orderZAt X.hom p.2 g))
    (fun p hp => by
      rw [Set.Finite.mem_toFinset]
      exact fun he => hp (by rw [he, toAdd_one]))

/-- The coefficient of a principal divisor is the corresponding order. -/
@[simp]
theorem coeffAt_principalDivisor (g : X.left.functionFieldˣ)
    {x : X.left} (hx : x ≠ genericPoint X.left) :
    CurveDivisor.coeffAt hx (principalDivisor g) =
      Multiplicative.toAdd (orderZAt X.hom hx g) :=
  rfl

/-- Principal divisors turn multiplication of rational functions into
addition of divisors. -/
theorem principalDivisor_mul (g h : X.left.functionFieldˣ) :
    principalDivisor (g * h) = principalDivisor g + principalDivisor h := by
  apply CurveDivisor.ext_coeffAt
  intro x hx
  simp only [coeffAt_principalDivisor, CurveDivisor.coeffAt_add]
  rw [map_mul, toAdd_mul]

/-- The principal divisor of the constant function one is zero. -/
@[simp]
theorem principalDivisor_one :
    principalDivisor (1 : X.left.functionFieldˣ) = 0 := by
  apply CurveDivisor.ext_coeffAt
  intro x hx
  simp only [coeffAt_principalDivisor, map_one, toAdd_one,
    CurveDivisor.coeffAt_zero]

/-- Inverting a rational function negates its principal divisor. -/
@[simp]
theorem principalDivisor_inv (g : X.left.functionFieldˣ) :
    principalDivisor g⁻¹ = -principalDivisor g := by
  apply CurveDivisor.ext_coeffAt
  intro x hx
  simp only [coeffAt_principalDivisor, map_inv, toAdd_inv,
    CurveDivisor.coeffAt_neg]

/-- Dividing rational functions subtracts their principal divisors. -/
theorem principalDivisor_div (g h : X.left.functionFieldˣ) :
    principalDivisor (g / h) = principalDivisor g - principalDivisor h := by
  rw [div_eq_mul_inv, principalDivisor_mul, principalDivisor_inv]
  rw [sub_eq_add_neg]

/-- Principal divisors as an additive homomorphism from the multiplicative
group of rational functions, viewed additively. -/
noncomputable def principalDivisorAddHom :
    Additive (X.left.functionFieldˣ) →+ CurveDivisor k X where
  toFun g := principalDivisor (Additive.toMul g)
  map_zero' := principalDivisor_one
  map_add' g h := principalDivisor_mul (Additive.toMul g) (Additive.toMul h)

@[simp]
theorem principalDivisorAddHom_apply (g : Additive (X.left.functionFieldˣ)) :
    principalDivisorAddHom g = principalDivisor (Additive.toMul g) :=
  rfl

/-- The additive subgroup of principal divisors. -/
noncomputable def principalDivisors : AddSubgroup (CurveDivisor k X) :=
  principalDivisorAddHom.range

/-- Membership in the subgroup of principal divisors is witnessed by a
nonzero rational function. -/
theorem mem_principalDivisors_iff (D : CurveDivisor k X) :
    D ∈ principalDivisors ↔ ∃ g : X.left.functionFieldˣ, principalDivisor g = D := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨Additive.toMul g, hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨Additive.ofMul g, hg⟩

end Hartshorne
