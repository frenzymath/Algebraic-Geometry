/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.Devissage
import AlgebraicJacobian.RiemannRoch.Ledger.ResidueDegree

/-!
# The jump module at a closed point is the residue field

For the curve bundle `X` (integral, smooth of relative dimension one over a field `K`), a Weil
divisor `D : X.CurveDivisor`, and a non-generic (hence closed) point `x`, this file identifies the
one-point **jump module** `J = 𝒪(D)ₓ ⧸ 𝒪(D − x)ₓ` of `Devissage.lean` with the residue field `κ(x)`
as `K`-modules, and reads off its dimension:

* `AlgebraicGeometry.jumpEquivResidueField`: the `K`-linear isomorphism `J ≃ₗ[K] κ(x)`;
* `AlgebraicGeometry.finrank_jumpModule`: `dimₖ J = [κ(x) : K] = X.residueDeg K x`;
* `AlgebraicGeometry.moduleFinite_jumpModule`: `J` is a finite `K`-module.

These are the `h⁰(sky) = residueDeg` inputs of the six-term dévissage slice.

## Mathematical route

Write `a = coeffAt hx D` and `Lₙ = pointLattice K hx n` (rational functions with `ord_x ≤ ofAdd n`),
so `J = Lₐ ⧸ (L₍ₐ₋₁₎ inside Lₐ)`.

* **Shift (`shiftMap`).** Multiplication by `tᵃ`, where `t : K(X)` is a uniformizer at `x`
  (`ord_x t = ofAdd (−1)`), carries `Lₐ` `K`-linearly onto `L₀` and `L₍ₐ₋₁₎` onto `L₍₋₁₎`.
* **Base (`baseHom`).** On `L₀ = 𝒪_{X,x}` (order `≤ 1` means integral, `exists_stalk_of_ord_le_one`)
  the residue map `𝒪_{X,x} → κ(x)` is `K`-linear and surjective with kernel the functions of order
  `< 1`, i.e. `L₍₋₁₎`.

Composing and applying the first isomorphism theorem gives `J ≃ₗ[K] κ(x)`. Finiteness of `κ(x)` is
`Scheme.residueDeg_finite`, which needs `[LocallyOfFiniteType (X ↘ Spec K)]`; that instance is
therefore assumed on both theorems (harmless downstream).

The `K`-module structures are the sealed local instances `Scheme.functionFieldOverModule` (on
`K(X)`, hence on `Lₙ` and `J`) and `Scheme.residueFieldOverModule` (on `κ(x)`), activated below
exactly as in `Devissage.lean`/`ResidueDegree.lean`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.Scheme.functionFieldOverModule
  AlgebraicGeometry.Scheme.residueFieldOverModule
  AlgebraicGeometry.Scheme.overModule

namespace AlgebraicGeometry

open Scheme

/-! ## Order arithmetic in `ℤᵐ⁰ = WithZero (Multiplicative ℤ)` -/

/-- Multiplying by `ofAdd (−a)` shifts a `≤ ofAdd m` bound to a `≤ ofAdd (m + a)` bound: the
bookkeeping behind the valuation shift `ord (tᵃ · g) = ofAdd (−a) · ord g`. -/
private lemma ofAdd_neg_mul_le_iff (z : WithZero (Multiplicative ℤ)) (a m : ℤ) :
    ((Multiplicative.ofAdd (-a) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * z
        ≤ ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      ↔ z ≤ ((Multiplicative.ofAdd (m + a) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  induction z using WithZero.recZeroCoe with
  | zero => simp
  | coe w =>
    rw [← WithZero.coe_mul, WithZero.coe_le_coe, WithZero.coe_le_coe, ofAdd_neg,
      inv_mul_le_iff_le_mul, ← ofAdd_add, add_comm a m]

/-- Discreteness of the value group: an order `< 1` is an order `≤ ofAdd (−1)`. -/
private lemma ord_lt_one_iff (z : WithZero (Multiplicative ℤ)) : z < 1 ↔
    z ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  induction z using WithZero.recZeroCoe with
  | zero => exact iff_of_true zero_lt_one zero_le
  | coe w =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe, WithZero.coe_le_coe, ← ofAdd_zero,
      ← ofAdd_toAdd w, Multiplicative.ofAdd_lt, Multiplicative.ofAdd_le]
    omega

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  {x : X} (hx : x ≠ genericPoint X) (D : X.CurveDivisor)

/-! ## A uniformizer at `x` and the valuation shift -/

/-- There is a rational function of order exactly `ofAdd (−1)` at the closed point `x`: a
uniformizer of the discrete valuation ring `𝒪_{X,x}`, obtained from
`valuation_exists_uniformizer`. -/
lemma exists_ord_eq_neg_one : ∃ t : X.functionField,
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx t
      = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hx
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hx
  exact IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer X.functionField
    (⟨IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).isPrime,
      IsDiscreteValuationRing.not_a_field (X.presheaf.stalk x)⟩ :
      IsDedekindDomain.HeightOneSpectrum (X.presheaf.stalk x))

/-- A chosen uniformizer at `x`: `ord_x (uniformizer) = ofAdd (−1)`. -/
noncomputable def uniformizer : X.functionField := (exists_ord_eq_neg_one K hx).choose

lemma ord_uniformizer :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (uniformizer K hx)
      = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
  (exists_ord_eq_neg_one K hx).choose_spec

lemma uniformizer_ne_zero : uniformizer K hx ≠ 0 := by
  intro h
  have hord := ord_uniformizer K hx
  rw [h, map_zero] at hord
  exact WithZero.coe_ne_zero hord.symm

/-- The order of `uniformizer ^ a` is `ofAdd (−a)`. -/
lemma ord_uniformizer_zpow (a : ℤ) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (uniformizer K hx ^ a)
      = ((Multiplicative.ofAdd (-a : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, ord_uniformizer, ← WithZero.coe_zpow, ← Int.ofAdd_mul, neg_one_mul]

/-- **The valuation shift on lattices.** Multiplication by `uniformizer ^ a` moves the one-point
lattice `Lₙ` to `L₍ₙ₊ₐ₎`: `tᵃ · g ∈ Lₙ ↔ g ∈ L₍ₙ₊ₐ₎`. -/
lemma mem_pointLattice_uniformizer_zpow_mul {a n : ℤ} {g : X.functionField} :
    uniformizer K hx ^ a * g ∈ pointLattice K hx n ↔ g ∈ pointLattice K hx (n + a) := by
  rw [mem_pointLattice, mem_pointLattice, map_mul, ord_uniformizer_zpow]
  exact ofAdd_neg_mul_le_iff (Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g) a n

/-- **The shift map `Lₐ → L₀`.** Multiplication by `uniformizer ^ a`, a `K`-linear map (the
`K`-action is by multiplication in the field, which commutes). -/
noncomputable def shiftMap (a : ℤ) :
    ↥(pointLattice K hx a) →ₗ[K] ↥(pointLattice K hx 0) where
  toFun g := ⟨uniformizer K hx ^ a * (g : X.functionField), by
    rw [mem_pointLattice_uniformizer_zpow_mul, zero_add]; exact g.2⟩
  map_add' g g' := Subtype.ext (by simp only [Submodule.coe_add]; ring)
  map_smul' r g := Subtype.ext (by
    simp only [SetLike.val_smul, RingHom.id_apply, functionFieldOverModule_smul_def]; ring)

@[simp] lemma shiftMap_coe (a : ℤ) (g : ↥(pointLattice K hx a)) :
    (shiftMap K hx a g : X.functionField) = uniformizer K hx ^ a * (g : X.functionField) :=
  rfl

lemma shiftMap_surjective (a : ℤ) : Function.Surjective (shiftMap K hx a) := by
  intro h
  refine ⟨⟨uniformizer K hx ^ (-a) * (h : X.functionField), ?_⟩, ?_⟩
  · rw [mem_pointLattice_uniformizer_zpow_mul, add_neg_cancel]; exact h.2
  · apply Subtype.ext
    rw [shiftMap_coe, ← mul_assoc, ← zpow_add₀ (uniformizer_ne_zero K hx), add_neg_cancel,
      zpow_zero, one_mul]

/-! ## The base map `L₀ → κ(x)` -/

/-- Membership in `L₀` is exactly integrality: `ord_x g ≤ 1`. -/
private lemma mem_pointLattice_zero_iff {g : X.functionField} :
    g ∈ pointLattice K hx 0 ↔ Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g ≤ 1 := by
  rw [mem_pointLattice, ofAdd_zero, WithZero.coe_one]

lemma algebraMap_stalk_injective :
    Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
  IsFractionRing.injective (X.presheaf.stalk x) X.functionField

/-- The (unique) preimage in the stalk `𝒪_{X,x}` of an element of `L₀` (which has order `≤ 1`, hence
is integral by `exists_stalk_of_ord_le_one`). -/
noncomputable def preimageStalk (g : ↥(pointLattice K hx 0)) : X.presheaf.stalk x :=
  (exists_stalk_of_ord_le_one K hx ((mem_pointLattice_zero_iff K hx).mp g.2)).choose

lemma algebraMap_preimageStalk (g : ↥(pointLattice K hx 0)) :
    algebraMap (X.presheaf.stalk x) X.functionField (preimageStalk K hx g)
      = (g : X.functionField) :=
  (exists_stalk_of_ord_le_one K hx ((mem_pointLattice_zero_iff K hx).mp g.2)).choose_spec

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] in
/-- The `K`-structure map factors through the stalk at `x`: `r ↦ germ_x (r · 1)` in `𝒪_{X,x}` maps
to `r · 1` in `K(X)`. Copied from the `hrw` step of `ord_functionFieldOverAlgebraMap_le_one`. -/
private lemma functionFieldOverAlgebraMap_eq_algebraMap (r : K) :
    functionFieldOverAlgebraMap K X r
      = algebraMap (X.presheaf.stalk x) X.functionField
          ((X.presheaf.germ ⊤ x trivial).hom (X.overAlgebraMap K ⊤ r)) := by
  set t : Γ(X, ⊤) := X.overAlgebraMap K ⊤ r with ht
  have hspec : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hcomp := X.presheaf.germ_stalkSpecializes (U := ⊤) (y := x) trivial hspec
  have happ := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) t
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at happ
  exact happ.symm

/-- **The base map `L₀ → κ(x)`.** A function of order `≤ 1` at `x` is the image of a stalk element;
send it to its residue. `K`-linearity follows by injectivity of `algebraMap 𝒪_{X,x} → K(X)`. -/
noncomputable def baseHom : ↥(pointLattice K hx 0) →ₗ[K] X.residueField x where
  toFun g := (X.residue x).hom (preimageStalk K hx g)
  map_add' g g' := by
    have hsum : algebraMap (X.presheaf.stalk x) X.functionField (preimageStalk K hx (g + g'))
        = algebraMap (X.presheaf.stalk x) X.functionField
            (preimageStalk K hx g + preimageStalk K hx g') := by
      rw [map_add, algebraMap_preimageStalk, algebraMap_preimageStalk, algebraMap_preimageStalk,
        Submodule.coe_add]
    rw [algebraMap_stalk_injective hsum, map_add]
  map_smul' r g := by
    have hseam : algebraMap (X.presheaf.stalk x) X.functionField (preimageStalk K hx (r • g))
        = algebraMap (X.presheaf.stalk x) X.functionField
            ((X.presheaf.germ ⊤ x trivial).hom (X.overAlgebraMap K ⊤ r)
              * preimageStalk K hx g) := by
      rw [map_mul, algebraMap_preimageStalk, algebraMap_preimageStalk,
        ← functionFieldOverAlgebraMap_eq_algebraMap, Submodule.coe_smul,
        functionFieldOverModule_smul_def]
    change (X.residue x).hom (preimageStalk K hx (r • g))
      = (RingHom.id K) r • (X.residue x).hom (preimageStalk K hx g)
    rw [algebraMap_stalk_injective hseam, map_mul, RingHom.id_apply]
    rfl

lemma baseHom_surjective : Function.Surjective (baseHom K hx) := by
  intro w
  obtain ⟨y, hy⟩ := Scheme.residue_surjective X x w
  refine ⟨⟨algebraMap (X.presheaf.stalk x) X.functionField y, ?_⟩, ?_⟩
  · rw [mem_pointLattice_zero_iff]; exact ord_algebraMap_stalk_le_one K hx y
  · change (X.residue x).hom (preimageStalk K hx _) = w
    rw [← hy]
    congr 1
    exact algebraMap_stalk_injective (algebraMap_preimageStalk K hx _)

/-- **The kernel of the base map is `L₍₋₁₎`.** Residue vanishes iff the stalk preimage lies in the
maximal ideal, i.e. has order `< 1`, i.e. order `≤ ofAdd (−1)`. -/
lemma baseHom_ker :
    LinearMap.ker (baseHom K hx)
      = (pointLattice K hx (-1)).submoduleOf (pointLattice K hx 0) := by
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hx
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hx
  set v₀ : IsDedekindDomain.HeightOneSpectrum (X.presheaf.stalk x) :=
    ⟨IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).isPrime,
      IsDiscreteValuationRing.not_a_field (X.presheaf.stalk x)⟩ with hv0
  ext g
  rw [LinearMap.mem_ker]
  calc baseHom K hx g = 0
      ↔ preimageStalk K hx g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
        IsLocalRing.residue_eq_zero_iff (preimageStalk K hx g)
    _ ↔ Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx
          (algebraMap (X.presheaf.stalk x) X.functionField (preimageStalk K hx g)) < 1 :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem v₀
          (preimageStalk K hx g)).symm
    _ ↔ Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (g : X.functionField) < 1 := by
        rw [algebraMap_preimageStalk]
    _ ↔ (g : X.functionField) ∈ pointLattice K hx (-1) := by rw [mem_pointLattice, ord_lt_one_iff]
    _ ↔ g ∈ (pointLattice K hx (-1)).submoduleOf (pointLattice K hx 0) := Iff.rfl

/-! ## The jump module is the residue field -/

/-- The composite `Lₐ → L₀ → κ(x)` (`a = coeffAt hx D`). -/
noncomputable def jumpToResidue :
    ↥(pointLattice K hx (coeffAt hx D)) →ₗ[K] X.residueField x :=
  (baseHom K hx).comp (shiftMap K hx (coeffAt hx D))

lemma jumpToResidue_surjective : Function.Surjective (jumpToResidue K hx D) :=
  (baseHom_surjective K hx).comp (shiftMap_surjective K hx (coeffAt hx D))

/-- The kernel of `jumpToResidue` is `L₍ₐ₋₁₎ ⊆ Lₐ`, the submodule defining the jump module. -/
lemma jumpToResidue_ker :
    LinearMap.ker (jumpToResidue K hx D)
      = (pointLattice K hx (coeffAt hx D - 1)).submoduleOf (pointLattice K hx (coeffAt hx D)) := by
  rw [jumpToResidue, LinearMap.ker_comp, baseHom_ker]
  ext g
  simp only [Submodule.mem_comap]
  change (shiftMap K hx (coeffAt hx D) g : X.functionField) ∈ pointLattice K hx (-1)
    ↔ (g : X.functionField) ∈ pointLattice K hx (coeffAt hx D - 1)
  rw [shiftMap_coe, mem_pointLattice_uniformizer_zpow_mul,
    show (-1 : ℤ) + coeffAt hx D = coeffAt hx D - 1 by ring]

/-- **The jump module is the residue field.** The `K`-linear isomorphism
`J = 𝒪(D)ₓ ⧸ 𝒪(D − x)ₓ ≃ₗ[K] κ(x)`, from the first isomorphism theorem applied to the surjection
`jumpToResidue` with kernel `L₍ₐ₋₁₎`. -/
noncomputable def jumpEquivResidueField : jumpModule K hx D ≃ₗ[K] X.residueField x :=
  (Submodule.quotEquivOfEq _ _ (jumpToResidue_ker K hx D).symm).trans
    ((jumpToResidue K hx D).quotKerEquivOfSurjective (jumpToResidue_surjective K hx D))

/-- **`dimₖ J = [κ(x) : K]`.** The six-term slice input `h⁰(sky) = residueDeg`. -/
theorem finrank_jumpModule [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] :
    Module.finrank K (jumpModule K hx D) = X.residueDeg K x :=
  (jumpEquivResidueField K hx D).finrank_eq

/-- **The jump module is a finite `K`-module** (its dimension `[κ(x) : K]` is finite). -/
theorem moduleFinite_jumpModule [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] :
    Module.Finite K (jumpModule K hx D) := by
  haveI : Module.Finite K (X.residueField x) := Scheme.residueDeg_finite (K := K) hx
  exact Module.Finite.equiv (jumpEquivResidueField K hx D).symm

end AlgebraicGeometry
