/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.UnitDescentBaseChange

/-!
# Descent in stages for unit 1-cocycles

Continuation of `AlgebraicJacobian.Descent.UnitDescent`,
`AlgebraicJacobian.Descent.UnitDescentMap` and
`AlgebraicJacobian.Descent.UnitDescentBaseChange`.  Here the cover is factored through an
intermediate ring: for a tower of commutative rings `A → B → P` we relate `A`-descent along
the composite `A → P` with `B`-descent along `B → P`.

Let `π : P ⊗[A] P →ₐ[A] P ⊗[B] P` be the canonical **collapse** map `x ⊗ y ↦ x ⊗ y`
(`Module.tensorCollapse`).  Given an `A`-descent 1-cocycle `v : (P ⊗[A] P)ˣ`:

* its collapse `Units.map π v` is a `B`-descent 1-cocycle
  (`Module.IsDescentCocycle.collapse`);
* the `A`-descended module of `v` is contained in the `B`-descended module of the collapse
  (`Module.descended_le_descended_collapse`);
* for faithfully flat `A → B` and `B → P`, the `A`-descended module base-changes to the
  `B`-descended module of the collapse
  (`Module.descendedCollapseEquiv : B ⊗[A] descended v ≃ₗ[B] descended (collapse v)`);
* hence the Picard classes correspond under `CommRing.Pic.mapAlgebra A B`
  (`Module.IsDescentCocycle.picClass_collapse`).

The two-layer descent data (the Zariski cover cocycle and the comparison of the two
pullbacks over `B`) are carried by the *single* unit `v`, with all coherence subsumed in
`IsDescentCocycle v`.  This is brick ε2 of the assembly of étale separatedness of the
relative Picard functor (Kleiman, *The Picard Scheme*, Theorem 2.5(1)): it splices a class
trivialized on an étale cover `B` with the descent datum descended from the double cover
`B ⊗[A] B`.

The proofs of `descendedCollapseEquiv` mirror `Module.descendedMapEquiv` and
`Module.descendedBaseChangeEquiv`: the descended module of the collapsed cocycle is
recognized by `Module.DescentDatum.equivDescended`, fed with the composite of
`AlgebraTensorModule.cancelBaseChange` and the `A`-descent equivalence of `v`.  Faithful
flatness of the composite `A → P`, needed for that descent equivalence, is obtained from the
two given instances by transitivity (`Module.FaithfullyFlat.trans`).
-/

universe u

set_option autoImplicit false

open TensorProduct

namespace Module

variable {A B P : Type u} [CommRing A] [CommRing B] [CommRing P]
variable [Algebra A B] [Algebra A P] [Algebra B P] [IsScalarTower A B P]

/-! ## The collapse maps on tensor squares and cubes -/

variable (A B P) in
/-- The canonical collapse map `P ⊗[A] P →ₐ[A] P ⊗[B] P`, `x ⊗ y ↦ x ⊗ y`, for a tower
`A → B → P`: it identifies the two `A`-bilinear factors as `B`-bilinear. -/
noncomputable def tensorCollapse : P ⊗[A] P →ₐ[A] P ⊗[B] P :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : P →ₐ[B] P ⊗[B] P).restrictScalars A)
    ((Algebra.TensorProduct.includeRight : P →ₐ[B] P ⊗[B] P).restrictScalars A)
    fun _ _ => Commute.all _ _

@[simp]
lemma tensorCollapse_tmul (x y : P) :
    tensorCollapse A B P (x ⊗ₜ[A] y) = x ⊗ₜ[B] y := by
  simp [tensorCollapse]

variable (A B P) in
/-- The collapse map on tensor cubes `P ⊗[A] (P ⊗[A] P) →ₐ[A] P ⊗[B] (P ⊗[B] P)`,
`x ⊗ (y ⊗ z) ↦ x ⊗ (y ⊗ z)`: the receptacle for the collapse of the three face maps. -/
noncomputable def tensorCubeCollapse :
    P ⊗[A] (P ⊗[A] P) →ₐ[A] P ⊗[B] (P ⊗[B] P) :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft :
      P →ₐ[B] P ⊗[B] (P ⊗[B] P)).restrictScalars A)
    (((Algebra.TensorProduct.includeRight :
      (P ⊗[B] P) →ₐ[B] P ⊗[B] (P ⊗[B] P)).restrictScalars A).comp
      (tensorCollapse A B P))
    fun _ _ => Commute.all _ _

@[simp]
lemma tensorCubeCollapse_tmul (x y z : P) :
    tensorCubeCollapse A B P (x ⊗ₜ[A] (y ⊗ₜ[A] z)) = x ⊗ₜ[B] (y ⊗ₜ[B] z) := by
  simp [tensorCubeCollapse]

/-! ## Collapse of a descent cocycle -/

/-- The collapse of an `A`-descent 1-cocycle `v : (P ⊗[A] P)ˣ` along the tower `A → B → P`
is a `B`-descent 1-cocycle for the cover `B → P`. -/
theorem IsDescentCocycle.collapse {v : (P ⊗[A] P)ˣ} (hv : IsDescentCocycle v) :
    IsDescentCocycle (Units.map (tensorCollapse A B P).toRingHom.toMonoidHom v) := by
  -- Naturality: `lmul' ∘ π = lmul'` and `descentFaceᵢⱼ ∘ π = π₃ ∘ descentFaceᵢⱼ` (with the
  -- cube collapse `π₃`), each checked on pure tensors; apply to the two conditions of `hv`.
  have hlmul : ∀ w : P ⊗[A] P,
      Algebra.TensorProduct.lmul' B (S := P) (tensorCollapse A B P w)
        = Algebra.TensorProduct.lmul' A (S := P) w := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp [Algebra.TensorProduct.lmul'_apply_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hface₁₂ : ∀ w : P ⊗[A] P,
      descentFace₁₂ B P (tensorCollapse A B P w)
        = tensorCubeCollapse A B P (descentFace₁₂ A P w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hface₁₃ : ∀ w : P ⊗[A] P,
      descentFace₁₃ B P (tensorCollapse A B P w)
        = tensorCubeCollapse A B P (descentFace₁₃ A P w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hface₂₃ : ∀ w : P ⊗[A] P,
      descentFace₂₃ B P (tensorCollapse A B P w)
        = tensorCubeCollapse A B P (descentFace₂₃ A P w) := by
    intro w
    induction w with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  constructor
  · change Algebra.TensorProduct.lmul' B (S := P) (tensorCollapse A B P v.val) = 1
    rw [hlmul, hv.lmul'_eq_one]
  · change descentFace₂₃ B P (tensorCollapse A B P v.val)
        * descentFace₁₂ B P (tensorCollapse A B P v.val)
      = descentFace₁₃ B P (tensorCollapse A B P v.val)
    rw [hface₂₃, hface₁₂, hface₁₃, ← map_mul, hv.cocycle]

/-- The `A`-descended module of `v` is contained in the `B`-descended module of the
collapse: apply the collapse map to the membership equation. -/
theorem descended_le_descended_collapse {v : (P ⊗[A] P)ˣ} (hv : IsDescentCocycle v) :
    hv.descended ≤ (hv.collapse (B := B)).descended.restrictScalars A := by
  intro m hm
  rw [Submodule.restrictScalars_mem, IsDescentCocycle.mem_descended]
  rw [IsDescentCocycle.mem_descended] at hm
  have h := congrArg (tensorCollapse A B P) hm
  rw [map_mul, tensorCollapse_tmul, tensorCollapse_tmul] at h
  exact h

/-! ## Descent in stages of the descended module -/

section faithfullyFlat

-- The composite `[Module.FaithfullyFlat A P]` is derivable from the two stages via
-- `Module.FaithfullyFlat.trans A B P`; it is taken as an explicit instance because it is
-- needed in the *type* of `picClass_collapse` (`hv.picClass : CommRing.Pic A`), where a
-- `haveI` cannot reach and a `local instance` is rejected for synthesization order (the
-- intermediate ring `B` is not determined by `FaithfullyFlat A P`).
variable [Module.FaithfullyFlat A B] [Module.FaithfullyFlat B P] [Module.FaithfullyFlat A P]

/-- **Descent in stages for the descended module.**  For a tower `A → B → P` with
`A → B` and `B → P` faithfully flat, the base change to `B` of the `A`-descended module of
`v` is the `B`-descended module of the collapsed cocycle; the map is `b ⊗ m ↦ b • m`. -/
noncomputable def descendedCollapseEquiv {v : (P ⊗[A] P)ˣ} (hv : IsDescentCocycle v) :
    (B ⊗[A] hv.descended) ≃ₗ[B] (hv.collapse (B := B)).descended := by
  refine (DescentDatum.ofUnit _ (hv.collapse (B := B))).equivDescended
    (N := B ⊗[A] hv.descended)
    ((AlgebraTensorModule.cancelBaseChange A B P P hv.descended).trans
      (DescentDatum.ofUnit v hv).descentEquiv)
    fun x => ?_
  induction x with
  | zero => simp
  | tmul b' w =>
      induction w with
      | zero => simp
      | tmul b m =>
          have h : tensorCollapse A B P v.val * ((m : P) ⊗ₜ[B] (1 : P))
              = 1 ⊗ₜ[B] (m : P) := by
            have := congrArg (tensorCollapse A B P) (hv.mem_descended.mp m.2)
            rwa [map_mul, tensorCollapse_tmul, tensorCollapse_tmul] at this
          simp only [LinearEquiv.trans_apply, AlgebraTensorModule.cancelBaseChange_tmul,
            ofUnit_coaction, unitCoaction_apply,
            DescentDatum.baseChange_coaction, LinearMap.baseChange_tmul,
            LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, TensorProduct.mk_apply]
          change tensorCollapse A B P v.val * (((b • b') • (m : P)) ⊗ₜ[B] (1 : P))
              = b' ⊗ₜ[B] ((b • (1 : P)) • (m : P))
          simp only [smul_eq_mul]
          rw [show (b • (1 : P)) * (m : P) = b • (m : P) by rw [smul_mul_assoc, one_mul]]
          rw [show ((b • b') * (m : P)) ⊗ₜ[B] (1 : P)
                = ((b • b') ⊗ₜ[B] (1 : P)) * ((m : P) ⊗ₜ[B] (1 : P)) by
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
          rw [show b' ⊗ₜ[B] (b • (m : P))
                = ((b • b') ⊗ₜ[B] (1 : P)) * ((1 : P) ⊗ₜ[B] (m : P)) by
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← smul_tmul]]
          linear_combination ((b • b') ⊗ₜ[B] (1 : P)) * h
      | add x y hx hy =>
          simp only [tmul_add, map_add] at hx hy ⊢
          rw [hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

-- `[Module.FaithfullyFlat A B]` is kept in the signature for symmetry with the descent-tower
-- setup even though `FaithfullyFlat B P` and `FaithfullyFlat A P` already suffice here, so the
-- `unusedSectionVars` linter is silenced for this declaration.
set_option linter.unusedSectionVars false in
/-- **Naturality of the Picard class under descent in stages**: the class of the collapsed
cocycle over `B` is the image of the class over `A` under `CommRing.Pic.mapAlgebra A B`. -/
theorem IsDescentCocycle.picClass_collapse {v : (P ⊗[A] P)ˣ} (hv : IsDescentCocycle v) :
    (hv.collapse (B := B)).picClass
      = CommRing.Pic.mapAlgebra A B hv.picClass := by
  rw [IsDescentCocycle.picClass, IsDescentCocycle.picClass,
    CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_mk_iff]
  exact ⟨(descendedCollapseEquiv hv).symm.trans
    (AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (CommRing.Pic.mk.linearEquiv A hv.descended).symm)⟩

end faithfullyFlat

end Module
