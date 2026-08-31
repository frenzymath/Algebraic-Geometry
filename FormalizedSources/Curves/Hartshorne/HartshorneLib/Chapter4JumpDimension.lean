/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorDevissage
import HartshorneLib.Chapter4DivisorSheafZero
import HartshorneLib.Chapter4ResidueDegree

/-!
# The jump module at a closed point

The one-point quotient in divisor dévissage is canonically the residue field.
-/

set_option autoImplicit false
set_option linter.style.openClassical false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

attribute [local instance] functionFieldOverModule Scheme.overModule
  AlgebraicGeometry.Scheme.residueFieldOverModule

open scoped Classical

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-! ## Order arithmetic -/

private lemma ofAdd_neg_mul_le_iff (z : WithZero (Multiplicative ℤ)) (a m : ℤ) :
    ((Multiplicative.ofAdd (-a) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * z
        ≤ ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      ↔ z ≤ ((Multiplicative.ofAdd (m + a) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  induction z using WithZero.recZeroCoe with
  | zero => simp
  | coe w =>
    rw [← WithZero.coe_mul, WithZero.coe_le_coe, WithZero.coe_le_coe, ofAdd_neg,
      inv_mul_le_iff_le_mul, ← ofAdd_add, add_comm a m]

private lemma ord_lt_one_iff (z : WithZero (Multiplicative ℤ)) : z < 1 ↔
    z ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  induction z using WithZero.recZeroCoe with
  | zero => exact iff_of_true zero_lt_one zero_le
  | coe w =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe, WithZero.coe_le_coe, ← ofAdd_zero,
      ← ofAdd_toAdd w, Multiplicative.ofAdd_lt, Multiplicative.ofAdd_le]
    omega

/-! ## A uniformizer and the valuation shift -/

omit [IsAlgClosed k] [IsProper X.hom] in
/-- A rational function with order `ofAdd (-1)` at a chosen non-generic point. -/
lemma exists_orderAt_eq_neg_one {x : X.left} (hx : x ≠ genericPoint X.left) :
    ∃ t : X.left.functionField,
      orderAt X.hom hx t =
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
  letI := smoothCurve_stalk_isDiscreteValuationRing X.hom hx
  letI := smoothCurve_stalk_isDedekindDomain X.hom hx
  obtain ⟨t, ht⟩ := (stalkHeightOne X.left x).valuation_exists_uniformizer X.left.functionField
  exact ⟨t, ht⟩

omit [IsAlgClosed k] [IsProper X.hom] in
noncomputable def uniformizer {x : X.left} (hx : x ≠ genericPoint X.left) :
    X.left.functionField := (exists_orderAt_eq_neg_one (X := X) hx).choose

omit [IsAlgClosed k] [IsProper X.hom] in
lemma orderAt_uniformizer {x : X.left} (hx : x ≠ genericPoint X.left) :
    orderAt X.hom hx (uniformizer (X := X) hx) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) :=
  (exists_orderAt_eq_neg_one (X := X) hx).choose_spec

omit [IsAlgClosed k] [IsProper X.hom] in
lemma uniformizer_ne_zero {x : X.left} (hx : x ≠ genericPoint X.left) :
    uniformizer (X := X) hx ≠ 0 := by
  intro h
  have hord := orderAt_uniformizer (X := X) hx
  rw [h, map_zero] at hord
  exact WithZero.coe_ne_zero hord.symm

omit [IsAlgClosed k] [IsProper X.hom] in
lemma orderAt_uniformizer_zpow {x : X.left} (hx : x ≠ genericPoint X.left) (a : ℤ) :
    orderAt X.hom hx (uniformizer (X := X) hx ^ a) =
      ((Multiplicative.ofAdd (-a : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, orderAt_uniformizer, ← WithZero.coe_zpow, ← Int.ofAdd_mul, neg_one_mul]

omit [IsAlgClosed k] [IsProper X.hom] in
lemma mem_pointLattice_uniformizer_zpow_mul {x : X.left}
    (hx : x ≠ genericPoint X.left) {a n : ℤ} {g : X.left.functionField} :
    uniformizer (X := X) hx ^ a * g ∈ pointLattice (X := X) hx n ↔
      g ∈ pointLattice (X := X) hx (n + a) := by
  rw [mem_pointLattice, mem_pointLattice, map_mul, orderAt_uniformizer_zpow]
  exact ofAdd_neg_mul_le_iff (orderAt X.hom hx g) a n

omit [IsAlgClosed k] [IsProper X.hom] in
noncomputable def shiftMap {x : X.left} (hx : x ≠ genericPoint X.left) (a : ℤ) :
    ↥(pointLattice (X := X) hx a) →ₗ[k] ↥(pointLattice (X := X) hx 0) where
  toFun g := ⟨uniformizer (X := X) hx ^ a * (g : X.left.functionField), by
    rw [mem_pointLattice_uniformizer_zpow_mul, zero_add]
    exact g.2⟩
  map_add' g g' := Subtype.ext (by simp only [Submodule.coe_add]; ring)
  map_smul' r g := Subtype.ext (by
    simp only [SetLike.val_smul, RingHom.id_apply, functionFieldOverModule_smul_def]
    ring)

omit [IsAlgClosed k] [IsProper X.hom] in
@[simp] lemma shiftMap_coe {x : X.left} (hx : x ≠ genericPoint X.left) (a : ℤ)
    (g : ↥(pointLattice (X := X) hx a)) :
    (shiftMap (X := X) hx a g : X.left.functionField) =
      uniformizer (X := X) hx ^ a * (g : X.left.functionField) :=
  rfl

omit [IsAlgClosed k] [IsProper X.hom] in
lemma shiftMap_surjective {x : X.left} (hx : x ≠ genericPoint X.left) (a : ℤ) :
    Function.Surjective (shiftMap (X := X) hx a) := by
  intro h
  refine ⟨⟨uniformizer (X := X) hx ^ (-a) * (h : X.left.functionField), ?_⟩, ?_⟩
  · rw [mem_pointLattice_uniformizer_zpow_mul, add_neg_cancel]
    exact h.2
  · apply Subtype.ext
    rw [shiftMap_coe, ← mul_assoc, ← zpow_add₀ (uniformizer_ne_zero hx),
      add_neg_cancel, zpow_zero, one_mul]

/-! ## The base map to the residue field -/

omit [IsAlgClosed k] [IsProper X.hom] in
private lemma mem_pointLattice_zero_iff {x : X.left} (hx : x ≠ genericPoint X.left)
    {g : X.left.functionField} :
    g ∈ pointLattice (X := X) hx 0 ↔ orderAt X.hom hx g ≤ 1 := by
  rw [mem_pointLattice, ofAdd_zero, WithZero.coe_one]

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
lemma algebraMap_stalk_injective {x : X.left} :
    Function.Injective (algebraMap (X.left.presheaf.stalk x) X.left.functionField) :=
  IsFractionRing.injective (X.left.presheaf.stalk x) X.left.functionField

omit [IsAlgClosed k] [IsProper X.hom] in
noncomputable def preimageStalk {x : X.left} (hx : x ≠ genericPoint X.left)
    (g : ↥(pointLattice (X := X) hx 0)) : X.left.presheaf.stalk x :=
  (exists_stalk_of_order_le_one hx
    ((mem_pointLattice_zero_iff (X := X) hx).mp g.2)).choose

omit [IsAlgClosed k] [IsProper X.hom] in
lemma algebraMap_preimageStalk {x : X.left} (hx : x ≠ genericPoint X.left)
    (g : ↥(pointLattice (X := X) hx 0)) :
    algebraMap (X.left.presheaf.stalk x) X.left.functionField
      (preimageStalk (X := X) hx g) = (g : X.left.functionField) :=
  (exists_stalk_of_order_le_one hx
    ((mem_pointLattice_zero_iff (X := X) hx).mp g.2)).choose_spec

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
private lemma functionFieldOverAlgebraMap_eq_algebraMap {x : X.left}
    (r : k) :
    functionFieldOverAlgebraMap k X.left r =
      algebraMap (X.left.presheaf.stalk x) X.left.functionField
        ((X.left.presheaf.germ ⊤ x trivial).hom (X.left.overAlgebraMap k ⊤ r)) := by
  set t : Γ(X.left, ⊤) := X.left.overAlgebraMap k ⊤ r with ht
  have hspec : genericPoint X.left ⤳ x := (genericPoint_spec X.left).specializes trivial
  have hcomp := X.left.presheaf.germ_stalkSpecializes (U := ⊤) (y := x) trivial hspec
  have happ := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) t
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at happ
  exact happ.symm

noncomputable def baseHom {x : X.left} (hx : x ≠ genericPoint X.left) :
    ↥(pointLattice (X := X) hx 0) →ₗ[k] X.left.residueField x where
  toFun g := (X.left.residue x).hom (preimageStalk (X := X) hx g)
  map_add' g g' := by
    have hsum :
        algebraMap (X.left.presheaf.stalk x) X.left.functionField
            (preimageStalk (X := X) hx (g + g')) =
          algebraMap (X.left.presheaf.stalk x) X.left.functionField
            (preimageStalk (X := X) hx g + preimageStalk (X := X) hx g') := by
      rw [map_add, algebraMap_preimageStalk, algebraMap_preimageStalk,
        algebraMap_preimageStalk, Submodule.coe_add]
    rw [algebraMap_stalk_injective (X := X) hsum, map_add]
  map_smul' r g := by
    have hseam :
        algebraMap (X.left.presheaf.stalk x) X.left.functionField
            (preimageStalk (X := X) hx (r • g)) =
          algebraMap (X.left.presheaf.stalk x) X.left.functionField
            ((X.left.presheaf.germ ⊤ x trivial).hom (X.left.overAlgebraMap k ⊤ r) *
              preimageStalk (X := X) hx g) := by
      rw [map_mul, algebraMap_preimageStalk, algebraMap_preimageStalk,
        ← functionFieldOverAlgebraMap_eq_algebraMap (X := X),
        Submodule.coe_smul, functionFieldOverModule_smul_def]
    change (X.left.residue x).hom (preimageStalk (X := X) hx (r • g)) =
      (RingHom.id k) r • (X.left.residue x).hom (preimageStalk (X := X) hx g)
    rw [algebraMap_stalk_injective (X := X) hseam, map_mul, RingHom.id_apply]
    rfl

omit [IsAlgClosed k] [IsProper X.hom] in
lemma baseHom_surjective {x : X.left} (hx : x ≠ genericPoint X.left) :
    Function.Surjective (baseHom (X := X) hx) := by
  intro w
  obtain ⟨y, hy⟩ := X.left.residue_surjective x w
  refine ⟨⟨algebraMap (X.left.presheaf.stalk x) X.left.functionField y, ?_⟩, ?_⟩
  · rw [mem_pointLattice_zero_iff (X := X) hx]
    exact orderAt_algebraMap_stalk_le_one hx y
  · change (X.left.residue x).hom (preimageStalk (X := X) hx _) = w
    rw [← hy]
    congr 1
    exact algebraMap_stalk_injective (X := X)
      (algebraMap_preimageStalk (X := X) hx _)

omit [IsAlgClosed k] [IsProper X.hom] in
lemma baseHom_ker {x : X.left} (hx : x ≠ genericPoint X.left) :
    LinearMap.ker (baseHom (X := X) hx) =
      (pointLattice (X := X) hx (-1)).submoduleOf
        (pointLattice (X := X) hx 0) := by
  letI := smoothCurve_stalk_isDiscreteValuationRing X.hom hx
  letI := smoothCurve_stalk_isDedekindDomain X.hom hx
  set v₀ : IsDedekindDomain.HeightOneSpectrum (X.left.presheaf.stalk x) :=
    stalkHeightOne X.left x with hv0
  ext g
  rw [LinearMap.mem_ker]
  calc
    baseHom (X := X) hx g = 0
        ↔ preimageStalk (X := X) hx g ∈
            IsLocalRing.maximalIdeal (X.left.presheaf.stalk x) :=
      IsLocalRing.residue_eq_zero_iff (preimageStalk (X := X) hx g)
    _ ↔ orderAt X.hom hx
          (algebraMap (X.left.presheaf.stalk x) X.left.functionField
            (preimageStalk (X := X) hx g)) < 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        v₀ (preimageStalk (X := X) hx g)).symm
    _ ↔ orderAt X.hom hx (g : X.left.functionField) < 1 := by
      rw [algebraMap_preimageStalk]
    _ ↔ (g : X.left.functionField) ∈ pointLattice (X := X) hx (-1) := by
      rw [mem_pointLattice, ord_lt_one_iff]
    _ ↔ g ∈ (pointLattice (X := X) hx (-1)).submoduleOf
          (pointLattice (X := X) hx 0) := Iff.rfl

/-! ## The jump quotient -/

noncomputable def jumpToResidue {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    ↥(pointLattice (X := X) hx (CurveDivisor.coeffAt hx D)) →ₗ[k]
      X.left.residueField x :=
  (baseHom (X := X) hx).comp
    (shiftMap (X := X) hx (CurveDivisor.coeffAt hx D))

lemma jumpToResidue_surjective {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) : Function.Surjective (jumpToResidue (X := X) hx D) :=
  (baseHom_surjective (X := X) hx).comp
    (shiftMap_surjective hx (CurveDivisor.coeffAt hx D))

lemma jumpToResidue_ker {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    LinearMap.ker (jumpToResidue (X := X) hx D) =
      (pointLattice (X := X) hx (CurveDivisor.coeffAt hx D - 1)).submoduleOf
        (pointLattice (X := X) hx (CurveDivisor.coeffAt hx D)) := by
  rw [jumpToResidue, LinearMap.ker_comp, baseHom_ker]
  ext g
  simp only [Submodule.mem_comap]
  change (shiftMap (X := X) hx (CurveDivisor.coeffAt hx D) g : X.left.functionField) ∈
      pointLattice (X := X) hx (-1) ↔
    (g : X.left.functionField) ∈
      pointLattice (X := X) hx (CurveDivisor.coeffAt hx D - 1)
  rw [shiftMap_coe, mem_pointLattice_uniformizer_zpow_mul,
    show (-1 : ℤ) + CurveDivisor.coeffAt hx D =
      CurveDivisor.coeffAt hx D - 1 by ring]

/-- The one-point jump module is canonically the residue field. -/
noncomputable def jumpEquivResidueField {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) : jumpModule hx D ≃ₗ[k] X.left.residueField x :=
  (Submodule.quotEquivOfEq _ _ (jumpToResidue_ker (X := X) hx D).symm).trans
    ((jumpToResidue (X := X) hx D).quotKerEquivOfSurjective
      (jumpToResidue_surjective (X := X) hx D))

theorem finrank_jumpModule {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    Module.finrank k (jumpModule hx D) = X.left.residueDeg k x :=
  (jumpEquivResidueField (X := X) hx D).finrank_eq

theorem moduleFinite_jumpModule {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) : Module.Finite k (jumpModule hx D) := by
  letI : X.left.Over (Spec (CommRingCat.of k)) := .ofHom X.hom
  letI : SmoothOfRelativeDimension 1 (X.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  letI : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  haveI : Module.Finite k (X.left.residueField x) :=
    Scheme.residueDeg_finite (K := k) hx
  exact Module.Finite.equiv (jumpEquivResidueField (X := X) hx D).symm

end Hartshorne
