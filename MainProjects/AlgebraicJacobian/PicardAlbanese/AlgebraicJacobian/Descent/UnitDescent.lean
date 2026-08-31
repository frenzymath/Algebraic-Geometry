/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.InvertibleModule

/-!
# Descent data from unit 1-cocycles, and the Picard class of a cocycle

Let `A → B` be a map of commutative rings.  A **descent 1-cocycle** is a unit
`u : (B ⊗[A] B)ˣ` that is normalized along the multiplication `B ⊗[A] B → B` and satisfies
the 1-cocycle identity in `B ⊗[A] B ⊗[A] B` (`Module.IsDescentCocycle`).  Such a unit
twists the trivial descent datum on the `B`-module `B`: the coaction `x ↦ u * (x ⊗ₜ 1)`
is a descent datum in the comodule form of `AlgebraicJacobian.Descent.ModuleDescent`
(`Module.DescentDatum.ofUnit`), so for faithfully flat `A → B` it descends to an invertible
`A`-module `hu.descended` (`AlgebraicJacobian.Descent.InvertibleModule`), whose class in
mathlib's Picard group is `hu.picClass : CommRing.Pic A`.

This file develops the full calculus of `picClass`, which is the algebraic heart of the
dictionary between the Čech Picard group of an affine scheme and `CommRing.Pic`
(`AlgebraicJacobian.Picard.PicAffine`):

* `Module.IsDescentCocycle.picClass_one`: the trivial cocycle has trivial class.
* `Module.IsDescentCocycle.picClass_mul`: `picClass` is multiplicative in the cocycle.
* `Module.IsDescentCocycle.picClass_descentCoboundary_mul`: `picClass` is invariant under
  multiplication by the coboundary `β ↦ (1 ⊗ β) * (β ⊗ 1)⁻¹` of a unit `β : Bˣ`.
* `Module.IsDescentCocycle.picClass_map`: `picClass` is invariant under base change of the
  cocycle along a map `h : B →ₐ[A] B'` of faithfully flat `A`-algebras.
* `Module.IsDescentCocycle.picClass_eq_one_iff`: the class is trivial **iff** the cocycle
  is a coboundary.

Everything is pinned to a single universe `u`, matching
`AlgebraicJacobian.Descent.ModuleDescent`.
-/

universe u

open TensorProduct

namespace Module

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-! ## The simplicial ring maps in low degrees -/

/-- The first-factor inclusion `B → B ⊗[A] B`, `b ↦ b ⊗ₜ 1`. -/
abbrev descentIncl₁ : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft

/-- The second-factor inclusion `B → B ⊗[A] B`, `b ↦ 1 ⊗ₜ b`. -/
abbrev descentIncl₂ : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight

/-- The face map `B ⊗[A] B → B ⊗[A] (B ⊗[A] B)` hitting tensor positions `1, 2`:
`x ⊗ₜ y ↦ x ⊗ₜ (y ⊗ₜ 1)`. -/
noncomputable abbrev descentFace₁₂ : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
  Algebra.TensorProduct.map (AlgHom.id A B) Algebra.TensorProduct.includeLeft

/-- The face map `B ⊗[A] B → B ⊗[A] (B ⊗[A] B)` hitting tensor positions `1, 3`:
`x ⊗ₜ y ↦ x ⊗ₜ (1 ⊗ₜ y)`. -/
noncomputable abbrev descentFace₁₃ : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
  Algebra.TensorProduct.map (AlgHom.id A B) Algebra.TensorProduct.includeRight

/-- The face map `B ⊗[A] B → B ⊗[A] (B ⊗[A] B)` hitting tensor positions `2, 3`:
`w ↦ 1 ⊗ₜ w`. -/
abbrev descentFace₂₃ : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
  Algebra.TensorProduct.includeRight

variable {A B}

@[simp]
lemma descentIncl₁_apply (b : B) : descentIncl₁ A B b = b ⊗ₜ 1 := rfl

@[simp]
lemma descentIncl₂_apply (b : B) : descentIncl₂ A B b = 1 ⊗ₜ b := rfl

@[simp]
lemma descentFace₁₂_tmul (x y : B) : descentFace₁₂ A B (x ⊗ₜ y) = x ⊗ₜ (y ⊗ₜ 1) := rfl

@[simp]
lemma descentFace₁₃_tmul (x y : B) : descentFace₁₃ A B (x ⊗ₜ y) = x ⊗ₜ (1 ⊗ₜ y) := rfl

@[simp]
lemma descentFace₂₃_apply (w : B ⊗[A] B) : descentFace₂₃ A B w = 1 ⊗ₜ w := rfl

/-! ## Descent 1-cocycles -/

/-- A **descent 1-cocycle** relative to `A → B`: a unit of `B ⊗[A] B`, normalized along
the multiplication map, satisfying the 1-cocycle identity in `B ⊗[A] (B ⊗[A] B)`.  For
`B = ∏ i, A_{fᵢ}` a finite product of localizations covering `Spec A`, this is exactly a
Čech 1-cocycle of units on the cover by the basic opens `D(fᵢ)`. -/
structure IsDescentCocycle (u : (B ⊗[A] B)ˣ) : Prop where
  /-- Normalization: the multiplication `B ⊗[A] B → B` sends the cocycle to `1`. -/
  lmul'_eq_one : Algebra.TensorProduct.lmul' A (S := B) u.val = 1
  /-- The 1-cocycle identity. -/
  cocycle : descentFace₂₃ A B u.val * descentFace₁₂ A B u.val = descentFace₁₃ A B u.val

/-- The trivial unit is a descent cocycle. -/
theorem IsDescentCocycle.one : IsDescentCocycle (1 : (B ⊗[A] B)ˣ) where
  lmul'_eq_one := by simp [Algebra.TensorProduct.one_def]
  cocycle := by simp [Algebra.TensorProduct.one_def]

/-- Descent cocycles are closed under multiplication. -/
theorem IsDescentCocycle.mul {u v : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u)
    (hv : IsDescentCocycle v) : IsDescentCocycle (u * v) where
  lmul'_eq_one := by
    rw [Units.val_mul, map_mul, hu.lmul'_eq_one, hv.lmul'_eq_one, one_mul]
  cocycle := by
    simp only [Units.val_mul, map_mul]
    rw [show descentFace₂₃ A B u.val * descentFace₂₃ A B v.val *
          (descentFace₁₂ A B u.val * descentFace₁₂ A B v.val)
        = descentFace₂₃ A B u.val * descentFace₁₂ A B u.val *
          (descentFace₂₃ A B v.val * descentFace₁₂ A B v.val) by ring]
    rw [hu.cocycle, hv.cocycle]

/-! ## The descent datum of a cocycle -/

variable (u : (B ⊗[A] B)ˣ)

variable (A B) in
/-- The coaction `x ↦ u * (x ⊗ₜ 1)` associated with a unit of `B ⊗[A] B`, as a `B`-linear
map (with `B` acting on the left tensor factor of the target). -/
noncomputable def unitCoaction : B →ₗ[B] B ⊗[A] B where
  toFun x := u.val * x ⊗ₜ 1
  map_add' x y := by rw [add_tmul, mul_add]
  map_smul' b x := by
    rw [RingHom.id_apply, ← smul_tmul', mul_smul_comm]

@[simp]
lemma unitCoaction_apply (x : B) : unitCoaction A B u x = u.val * x ⊗ₜ 1 := rfl

/-- The action map `B ⊗[A] B →ₗ[B] B` of `ModuleDescent` is the multiplication map. -/
lemma actionMap_eq_lmul' (w : B ⊗[A] B) :
    actionMap A B B w = Algebra.TensorProduct.lmul' A (S := B) w := by
  induction w with
  | zero => simp
  | tmul b m => simp [smul_eq_mul]
  | add x y hx hy => simp [hx, hy]

/-- The base change to `B` of the coaction is left multiplication by `1 ⊗ₜ u` composed
with the face map `descentFace₁₂`. -/
lemma baseChange_unitCoaction (w : B ⊗[A] B) :
    ((unitCoaction A B u).restrictScalars A).baseChange B w
      = descentFace₂₃ A B u.val * descentFace₁₂ A B w := by
  induction w with
  | zero => simp
  | tmul y z =>
    -- LHS = `y ⊗ₜ (u * (z ⊗ₜ 1))`; RHS = `(1 ⊗ₜ u) * (y ⊗ₜ (z ⊗ₜ 1))`, equal by
    -- `Algebra.TensorProduct.tmul_mul_tmul` and `one_mul`.
    simp only [LinearMap.baseChange_tmul, LinearMap.coe_restrictScalars, unitCoaction_apply,
      descentFace₂₃_apply, descentFace₁₂_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

/-- The base change to `B` of `x ↦ 1 ⊗ₜ x` is the face map `descentFace₁₃`. -/
lemma baseChange_mk_one (w : B ⊗[A] B) :
    (TensorProduct.mk A B B 1).baseChange B w = descentFace₁₃ A B w := by
  induction w with
  | zero => simp
  | tmul y z => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The descent datum on the `B`-module `B` associated with a descent 1-cocycle: the
coaction is `x ↦ u * (x ⊗ₜ 1)`; counitality is the normalization and coassociativity is
the cocycle identity. -/
noncomputable def DescentDatum.ofUnit (hu : IsDescentCocycle u) : DescentDatum A B B where
  coaction := unitCoaction A B u
  counit m := by
    rw [unitCoaction_apply, actionMap_eq_lmul', map_mul, hu.lmul'_eq_one, one_mul,
      Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
  coassoc m := by
    -- after rewriting, both sides are `descentFace₁₃ u * (m ⊗ₜ (1 ⊗ₜ 1))`
    rw [unitCoaction_apply, baseChange_unitCoaction, baseChange_mk_one, map_mul,
      ← mul_assoc, hu.cocycle, map_mul]
    simp only [descentFace₁₂_tmul, descentFace₁₃_tmul]

@[simp]
lemma ofUnit_coaction (hu : IsDescentCocycle u) :
    (DescentDatum.ofUnit u hu).coaction = unitCoaction A B u := rfl

/-- The descended `A`-module of a descent 1-cocycle: the submodule of `x : B` with
`u * (x ⊗ₜ 1) = 1 ⊗ₜ x`. -/
noncomputable def IsDescentCocycle.descended {u : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u) :
    Submodule A B :=
  (DescentDatum.ofUnit u hu).descended

lemma IsDescentCocycle.mem_descended {u : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u) {m : B} :
    m ∈ hu.descended ↔ u.val * m ⊗ₜ 1 = 1 ⊗ₜ m :=
  DescentDatum.mem_descended _

/-! ## The Picard class of a cocycle -/

section picClass

variable [Module.FaithfullyFlat A B]

/-- The descended module of a descent cocycle along a faithfully flat `A → B` is an
invertible `A`-module. -/
instance IsDescentCocycle.invertible_descended {u : (B ⊗[A] B)ˣ}
    (hu : IsDescentCocycle u) : Module.Invertible A hu.descended :=
  (DescentDatum.ofUnit u hu).invertible_descended

/-- The class in the Picard group of `A` of the module descended from a descent
1-cocycle relative to a faithfully flat `A → B`. -/
noncomputable def IsDescentCocycle.picClass {u : (B ⊗[A] B)ˣ}
    (hu : IsDescentCocycle u) : CommRing.Pic A :=
  CommRing.Pic.mk A hu.descended

/-- The descended module of the trivial cocycle is `A` itself (Amitsur exactness in
degree `0`). -/
noncomputable def descendedOneEquiv :
    (IsDescentCocycle.one (A := A) (B := B)).descended ≃ₗ[A] A := by
  -- Route: `(DescentDatum.ofUnit 1 .one).equivDescended e he |>.symm` with
  -- `e : B ⊗[A] A ≃ₗ[B] B := AlgebraTensorModule.rid A B B`; the compatibility `he` is the
  -- computation `(a • b) ⊗ₜ 1 = b ⊗ₜ (a • 1)` (`tmul_smul` and `smul_tmul'`) on pure
  -- tensors, extended by linearity via `TensorProduct.induction_on`.
  refine ((DescentDatum.ofUnit 1 IsDescentCocycle.one).equivDescended
    (AlgebraTensorModule.rid A B B) fun x => ?_).symm
  induction x with
  | zero => simp
  | tmul b a =>
      simp only [ofUnit_coaction, unitCoaction_apply, Units.val_one, one_mul,
        DescentDatum.baseChange_coaction, LinearMap.baseChange_tmul,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, AlgebraTensorModule.rid_tmul,
        TensorProduct.mk_apply, tmul_smul, smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp]
theorem IsDescentCocycle.picClass_one :
    (IsDescentCocycle.one (A := A) (B := B)).picClass = 1 :=
  CommRing.Pic.mk_eq_one_iff.mpr ⟨descendedOneEquiv⟩

/-- Auxiliary `B`-linear equivalence `B ⊗[A] (M₀ ⊗[A] N₀) ≃ₗ[B] B` for `descendedMulEquiv`:
distribute the base change over the tensor product, apply the two descent equivalences and
multiply out.  On pure tensors it is `b ⊗ₜ (m ⊗ₜ n) ↦ b * m * n` (`descendedMulAux_tmul`). -/
private noncomputable def descendedMulAux {u v : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u)
    (hv : IsDescentCocycle v) :
    B ⊗[A] (hu.descended ⊗[A] hv.descended) ≃ₗ[B] B :=
  ((AlgebraTensorModule.distribBaseChange A B hu.descended hv.descended).trans
    (TensorProduct.congr (DescentDatum.ofUnit u hu).descentEquiv
      (DescentDatum.ofUnit v hv).descentEquiv)).trans (TensorProduct.lid B B)

@[simp]
private lemma descendedMulAux_tmul {u v : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u)
    (hv : IsDescentCocycle v) (b : B) (m : hu.descended) (n : hv.descended) :
    descendedMulAux hu hv (b ⊗ₜ (m ⊗ₜ n)) = b * m * n := by
  change (b • (m : B)) • ((1 : B) • (n : B)) = b * m * n
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, one_mul]

/-- The descended module is multiplicative in the cocycle: `descended (u * v)` is the
tensor product of `descended u` and `descended v`. -/
noncomputable def descendedMulEquiv {u v : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u)
    (hv : IsDescentCocycle v) :
    (hu.descended ⊗[A] hv.descended) ≃ₗ[A] (hu.mul hv).descended := by
  -- Route: `equivDescended (DescentDatum.ofUnit (u*v) (hu.mul hv)) e he` where
  -- `e : B ⊗[A] (M ⊗[A] N) ≃ₗ[B] B` is the composite
  -- `AlgebraTensorModule.distribBaseChange` ≪≫ congr (descentEquiv hu) (descentEquiv hv)
  --   ≪≫ (B ⊗[B] B ≃ B)`,
  -- which on pure tensors is `b ⊗ₜ (m ⊗ₜ n) ↦ b * m * n`.  The compatibility `he` reduces
  -- on pure tensors to the ring computation
  -- `(u*v) * (b*m*n ⊗ₜ 1) = (b ⊗ₜ 1) * (u * (m ⊗ₜ 1)) * (v * (n ⊗ₜ 1))
  --   = (b ⊗ₜ 1) * (1 ⊗ₜ m) * (1 ⊗ₜ n) = b ⊗ₜ (m*n)`
  -- using `hu.mem_descended`/`hv.mem_descended` for the members `m, n`.
  refine (DescentDatum.ofUnit (u * v) (hu.mul hv)).equivDescended
    (N := hu.descended ⊗[A] hv.descended) (descendedMulAux hu hv) fun x => ?_
  induction x with
  | zero => simp
  | tmul b p =>
      induction p with
      | zero => simp
      | tmul m n =>
          have hm : u.val * ((m : B) ⊗ₜ[A] (1 : B)) = 1 ⊗ₜ (m : B) := hu.mem_descended.mp m.2
          have hn : v.val * ((n : B) ⊗ₜ[A] (1 : B)) = 1 ⊗ₜ (n : B) := hv.mem_descended.mp n.2
          simp only [ofUnit_coaction, unitCoaction_apply, DescentDatum.baseChange_coaction,
            LinearMap.baseChange_tmul, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
            TensorProduct.mk_apply, descendedMulAux_tmul, one_mul, Units.val_mul]
          have h1 : (b * (m : B) * (n : B)) ⊗ₜ[A] (1 : B)
              = (b ⊗ₜ[A] (1 : B)) * ((m : B) ⊗ₜ[A] (1 : B)) * ((n : B) ⊗ₜ[A] (1 : B)) := by
            simp [Algebra.TensorProduct.tmul_mul_tmul]
          have h2 : b ⊗ₜ[A] ((m : B) * (n : B))
              = (b ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] (m : B)) * ((1 : B) ⊗ₜ[A] (n : B)) := by
            simp [Algebra.TensorProduct.tmul_mul_tmul]
          rw [h1, h2]
          linear_combination (v.val * (b ⊗ₜ[A] (1 : B)) * ((n : B) ⊗ₜ[A] (1 : B))) * hm
            + ((b ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] (m : B))) * hn
      | add p q hp hq => simp only [tmul_add, map_add, hp, hq]
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp]
theorem IsDescentCocycle.picClass_mul {u v : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u)
    (hv : IsDescentCocycle v) :
    (hu.mul hv).picClass = hu.picClass * hv.picClass := by
  rw [picClass, picClass, picClass, ← CommRing.Pic.mk_tensor]
  exact CommRing.Pic.mk_eq_mk_iff.mpr ⟨(descendedMulEquiv hu hv).symm⟩

end picClass

/-! ## Coboundaries -/

variable (A B) in
/-- The descent coboundary of a unit `β : Bˣ`: the unit `(1 ⊗ₜ β) * (β ⊗ₜ 1)⁻¹` of
`B ⊗[A] B`. -/
noncomputable def descentCoboundary (β : Bˣ) : (B ⊗[A] B)ˣ :=
  Units.map (descentIncl₂ A B).toRingHom.toMonoidHom β
    * (Units.map (descentIncl₁ A B).toRingHom.toMonoidHom β)⁻¹

lemma descentCoboundary_val (β : Bˣ) :
    (descentCoboundary A B β).val = (1 ⊗ₜ β.val) * ((β⁻¹).val ⊗ₜ 1) := rfl

/-- Coboundaries are descent cocycles. -/
theorem isDescentCocycle_descentCoboundary (β : Bˣ) :
    IsDescentCocycle (descentCoboundary A B β) where
  lmul'_eq_one := by
    -- `lmul' ((1 ⊗ β)(β⁻¹ ⊗ 1)) = β * β⁻¹ = 1`.
    rw [descentCoboundary_val, map_mul, Algebra.TensorProduct.lmul'_apply_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, one_mul, mul_one, Units.mul_inv]
  cocycle := by
    -- Writing `j₁ β = β ⊗ 1 ⊗ 1`, `j₂ β = 1 ⊗ β ⊗ 1`, `j₃ β = 1 ⊗ 1 ⊗ β`, the three
    -- faces of the coboundary are `descentFace₂₃ c = j₃β * (j₂β)⁻¹`,
    -- `descentFace₁₂ c = j₂β * (j₁β)⁻¹`, `descentFace₁₃ c = j₃β * (j₁β)⁻¹`, and the
    -- cocycle identity is the telescoping product.
    rw [descentCoboundary_val]
    simp only [descentFace₂₃_apply, descentFace₁₂_tmul, descentFace₁₃_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Units.inv_mul]

/-- Multiplying a cocycle by a coboundary does not change the descended module: the
twist is `m ↦ β * m`. -/
noncomputable def descendedCoboundaryMulEquiv (β : Bˣ) {u : (B ⊗[A] B)ˣ}
    (hu : IsDescentCocycle u) :
    hu.descended ≃ₗ[A] ((isDescentCocycle_descentCoboundary β).mul hu).descended := by
  -- `m ∈ descended u` iff `u * (m ⊗ₜ 1) = 1 ⊗ₜ m`; then
  -- `(c * u) * ((β*m) ⊗ₜ 1) = (1 ⊗ₜ β) * (β⁻¹ ⊗ₜ 1) * (β ⊗ₜ 1) * (u * (m ⊗ₜ 1))
  --   = (1 ⊗ₜ β) * (1 ⊗ₜ m) = 1 ⊗ₜ (β*m)`,
  -- so multiplication by `β` (with inverse `β⁻¹`) is a bijection between the two
  -- submodules, `A`-linear since `β • ·` commutes with the `A`-action.
  have hββ : (((β⁻¹).val ⊗ₜ[A] (1 : B)) * (β.val ⊗ₜ[A] (1 : B)) : B ⊗[A] B) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, mul_one,
      ← Algebra.TensorProduct.one_def]
  have hββ' : (((1 : B) ⊗ₜ[A] (β⁻¹).val) * ((1 : B) ⊗ₜ[A] β.val) : B ⊗[A] B) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, one_mul,
      ← Algebra.TensorProduct.one_def]
  have hmem : ∀ m : hu.descended,
      β.val * (m : B) ∈ ((isDescentCocycle_descentCoboundary β).mul hu).descended := by
    intro m
    have hm : u.val * ((m : B) ⊗ₜ[A] (1 : B)) = 1 ⊗ₜ (m : B) := hu.mem_descended.mp m.2
    rw [IsDescentCocycle.mem_descended, Units.val_mul, descentCoboundary_val,
      show (β.val * (m : B)) ⊗ₜ[A] (1 : B)
          = (β.val ⊗ₜ[A] (1 : B)) * ((m : B) ⊗ₜ[A] (1 : B)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one],
      show (1 : B) ⊗ₜ[A] (β.val * (m : B))
          = ((1 : B) ⊗ₜ[A] β.val) * ((1 : B) ⊗ₜ[A] (m : B)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
    linear_combination
      (((1 : B) ⊗ₜ[A] β.val) * ((β⁻¹).val ⊗ₜ[A] (1 : B)) * (β.val ⊗ₜ[A] (1 : B))) * hm
        + (((1 : B) ⊗ₜ[A] β.val) * ((1 : B) ⊗ₜ[A] (m : B))) * hββ
  have hmem' : ∀ m : ((isDescentCocycle_descentCoboundary β).mul hu).descended,
      (β⁻¹).val * (m : B) ∈ hu.descended := by
    intro m
    have hm' : (descentCoboundary A B β * u).val * ((m : B) ⊗ₜ[A] (1 : B)) = 1 ⊗ₜ (m : B) :=
      ((isDescentCocycle_descentCoboundary β).mul hu).mem_descended.mp m.2
    rw [Units.val_mul, descentCoboundary_val] at hm'
    rw [hu.mem_descended,
      show ((β⁻¹).val * (m : B)) ⊗ₜ[A] (1 : B)
          = ((β⁻¹).val ⊗ₜ[A] (1 : B)) * ((m : B) ⊗ₜ[A] (1 : B)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one],
      show (1 : B) ⊗ₜ[A] ((β⁻¹).val * (m : B))
          = ((1 : B) ⊗ₜ[A] (β⁻¹).val) * ((1 : B) ⊗ₜ[A] (m : B)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
    linear_combination ((1 : B) ⊗ₜ[A] (β⁻¹).val) * hm'
      - (((β⁻¹).val ⊗ₜ[A] (1 : B)) * u.val * ((m : B) ⊗ₜ[A] (1 : B))) * hββ'
  exact
    { toFun := fun m => ⟨β.val * (m : B), hmem m⟩
      map_add' := fun m m' => Subtype.ext (by
        change β.val * ((m : B) + (m' : B)) = β.val * (m : B) + β.val * (m' : B)
        rw [mul_add])
      map_smul' := fun a m => Subtype.ext (by
        change β.val * (a • (m : B)) = a • (β.val * (m : B))
        rw [mul_smul_comm])
      invFun := fun m => ⟨(β⁻¹).val * (m : B), hmem' m⟩
      left_inv := fun m => Subtype.ext (by
        change (β⁻¹).val * (β.val * (m : B)) = (m : B)
        rw [← mul_assoc, Units.inv_mul, one_mul])
      right_inv := fun m => Subtype.ext (by
        change β.val * ((β⁻¹).val * (m : B)) = (m : B)
        rw [← mul_assoc, Units.mul_inv, one_mul]) }

section picClass

variable [Module.FaithfullyFlat A B]

@[simp]
theorem IsDescentCocycle.picClass_descentCoboundary_mul (β : Bˣ) {u : (B ⊗[A] B)ˣ}
    (hu : IsDescentCocycle u) :
    ((isDescentCocycle_descentCoboundary β).mul hu).picClass = hu.picClass :=
  (CommRing.Pic.mk_eq_mk_iff.mpr ⟨(descendedCoboundaryMulEquiv β hu).symm⟩)

/-- A descent cocycle whose descended module is free is a coboundary; the coboundary unit
is the image in `B` of a generator. -/
theorem IsDescentCocycle.eq_descentCoboundary_of_equiv {u : (B ⊗[A] B)ˣ}
    (hu : IsDescentCocycle u) (e : hu.descended ≃ₗ[A] A) :
    ∃ β : Bˣ, u = descentCoboundary A B β := by
  -- Let `m₀ := (e.symm 1 : B)`.  The composite
  -- `B ≃ B ⊗[A] A ≃ B ⊗[A] descended u ≃ B`  (rid⁻¹, base change of `e.symm`,
  -- `descentEquiv (DescentDatum.ofUnit u hu)`) is `b ↦ b * m₀` and is bijective, so
  -- surjectivity at `1` provides `c` with `m₀ * c = 1` and `m₀` is a unit `β`.
  -- Membership `m₀ ∈ descended u` says `u * (m₀ ⊗ₜ 1) = 1 ⊗ₜ m₀`, i.e.
  -- `u * (descentIncl₁ β) = descentIncl₂ β`, i.e. `u = descentCoboundary β` by `Units.ext`.
  have key : ∀ b : B,
      ((AlgebraTensorModule.rid A B B).symm.trans
        ((LinearEquiv.baseChange A B A hu.descended e.symm).trans
          (DescentDatum.ofUnit u hu).descentEquiv)) b
        = b * ((e.symm 1 : hu.descended) : B) :=
    fun b => rfl
  obtain ⟨b₁, hb₁⟩ := ((AlgebraTensorModule.rid A B B).symm.trans
    ((LinearEquiv.baseChange A B A hu.descended e.symm).trans
      (DescentDatum.ofUnit u hu).descentEquiv)).surjective 1
  rw [key] at hb₁
  obtain ⟨β, hβ⟩ : IsUnit ((e.symm 1 : hu.descended) : B) :=
    IsUnit.of_mul_eq_one b₁ (by rw [mul_comm]; exact hb₁)
  have hmem : u.val * (((e.symm 1 : hu.descended) : B) ⊗ₜ[A] (1 : B))
      = 1 ⊗ₜ ((e.symm 1 : hu.descended) : B) := hu.mem_descended.mp (e.symm 1).2
  rw [← hβ] at hmem
  have hββ : ((β.val ⊗ₜ[A] (1 : B)) * ((β⁻¹).val ⊗ₜ[A] (1 : B)) : B ⊗[A] B) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, mul_one,
      ← Algebra.TensorProduct.one_def]
  refine ⟨β, Units.ext ?_⟩
  rw [descentCoboundary_val]
  linear_combination ((β⁻¹).val ⊗ₜ[A] (1 : B)) * hmem - u.val * hββ

/-- `picClass` only depends on the cocycle, not on the proof witness. -/
theorem IsDescentCocycle.picClass_congr {u v : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u)
    (hv : IsDescentCocycle v) (huv : u = v) : hu.picClass = hv.picClass := by
  subst huv; rfl

/-- **Triviality detection**: the Picard class of a descent cocycle is trivial iff the
cocycle is a coboundary. -/
theorem IsDescentCocycle.picClass_eq_one_iff {u : (B ⊗[A] B)ˣ} (hu : IsDescentCocycle u) :
    hu.picClass = 1 ↔ ∃ β : Bˣ, u = descentCoboundary A B β := by
  constructor
  · intro h1
    exact hu.eq_descentCoboundary_of_equiv (CommRing.Pic.mk_eq_one_iff.mp h1).some
  · rintro ⟨β, rfl⟩
    have h := IsDescentCocycle.picClass_descentCoboundary_mul (A := A) (B := B) β
      IsDescentCocycle.one
    rw [IsDescentCocycle.picClass_one] at h
    exact (IsDescentCocycle.picClass_congr _ _ (mul_one _).symm).trans h

end picClass


end Module
