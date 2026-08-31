/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Faithfully flat descent of modules

Let `A → B` be a map of commutative rings and let `M` be a `B`-module.  This file defines
descent data on `M` relative to `A → B`, constructs the descended `A`-module `M₀` as an
equalizer submodule of `M`, and proves the two fundamental theorems of flat descent for
modules:

* **effectivity**: if `B` is flat over `A`, the canonical comparison map
  `B ⊗[A] M₀ → M` is an isomorphism;
* **uniqueness**: if `B` is faithfully flat over `A`, then any `A`-module `N` equipped with
  a `B`-module isomorphism `B ⊗[A] N ≃ M` matching the descent datum is canonically
  isomorphic to `M₀`.  The engine is the degree `≤ 1` exactness of the Amitsur complex
  `0 → N → B ⊗[A] N ⇉ B ⊗[A] B ⊗[A] N`.

## Design notes

* **Comodule form of a descent datum.**  Classically a descent datum on `M` is a
  `B ⊗[A] B`-module isomorphism `φ : M ⊗[A] B ≃ B ⊗[A] M` satisfying a cocycle condition
  over the triple tensor product.  We use the equivalent *comodule* (Sweedler-coring)
  presentation: a `B`-linear coaction `δ : M →ₗ[B] B ⊗[A] M` (with `B` acting on the left
  tensor factor of the target) such that
  - (`counit`) the action map `B ⊗[A] M → M`, `b ⊗ₜ m ↦ b • m`, retracts `δ`, and
  - (`coassoc`) the two natural liftings of `δ` to `B ⊗[A] B ⊗[A] M` agree on the image
    of `δ`.

  The dictionary: given `φ`, set `δ m := φ (m ⊗ₜ 1)`; then `B ⊗ B`-linearity of `φ` makes
  `δ` `B`-linear and recovers `φ` via `φ (m ⊗ₜ b) = (1 ⊗ b) • δ m`, the cocycle condition
  becomes `coassoc`, and the standard normalization becomes `counit`.  Conversely the `φ`
  associated to a coaction is automatically invertible.  This presentation avoids putting
  (several!) `B ⊗[A] B`-module structures on `B ⊗[A] M` and `M ⊗[A] B`, which do not exist
  as mathlib instances.  For a unit `u : (B ⊗[A] B)ˣ` whose associated `φ` is
  `u • ·` on `M = B`, the coaction is `δ x = u.val * (x ⊗ₜ 1)`.

* **The descended module** is the equalizer `M₀ = {m : M | δ m = 1 ⊗ₜ m}`, an `A`-submodule
  of `M`, realized as the kernel of the `A`-linear map `δ - (1 ⊗ₜ ·)`.

* **Effectivity requires only flatness.**  The comparison `B ⊗[A] M₀ → M` is an isomorphism
  whenever `B` is flat over `A`: the counit and coassociativity laws make the augmented
  complex `M₀ → M ⇉ B ⊗[A] M` contractible after applying `B ⊗[A] -` (the contraction being
  the action maps), and flatness identifies `B ⊗[A] M₀` with the corresponding kernel.
  Faithful flatness enters only for uniqueness (the Amitsur exactness `N ≅ (B ⊗[A] N)₀`).

* Everything is pinned to a single universe `u`; multi-universe binders interact badly with
  the tensor-product instance search in downstream files.

## Main declarations

* `Module.actionMap A B M : B ⊗[A] M →ₗ[B] M`: the action map `b ⊗ₜ m ↦ b • m`.
* `Module.DescentDatum A B M`: descent data on the `B`-module `M` relative to `A → B`,
  in comodule form.
* `Module.DescentDatum.baseChange A B N`: the canonical descent datum on `B ⊗[A] N`.
* `Module.DescentDatum.descended`: the descended `A`-submodule `M₀`.
* `Module.DescentDatum.comparison`: the canonical map `B ⊗[A] M₀ →ₗ[B] M`, `b ⊗ₜ m ↦ b • m`.
* `Module.DescentDatum.comparison_bijective`: **effectivity** — `comparison` is bijective
  when `B` is a flat `A`-module.
* `Module.DescentDatum.descentEquiv : B ⊗[A] M₀ ≃ₗ[B] M`: the comparison isomorphism.
* `Module.DescentDatum.exact_mk_coactionSub`: degree `≤ 1` **Amitsur exactness** for a
  faithfully flat `A → B`.
* `Module.DescentDatum.unitEquiv : N ≃ₗ[A] (baseChange A B N).descended`: the unit of
  descent is an isomorphism (faithfully flat case).
* `Module.DescentDatum.equivDescended`: **uniqueness** — an `A`-module `N` with a
  datum-compatible isomorphism `B ⊗[A] N ≃ₗ[B] M` is canonically `A`-isomorphic to `M₀`.
  Two descents of the same datum are therefore canonically isomorphic.
-/

universe u

open TensorProduct

namespace Module

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (M : Type u) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- The `B`-linear action map `B ⊗[A] M →ₗ[B] M`, `b ⊗ₜ m ↦ b • m`, of a `B`-module `M`. -/
noncomputable def actionMap : B ⊗[A] M →ₗ[B] M :=
  LinearMap.liftBaseChange B (LinearMap.id (R := A) (M := M))

@[simp] theorem actionMap_tmul (b : B) (m : M) : actionMap A B M (b ⊗ₜ m) = b • m := rfl

theorem actionMap_one_tmul (m : M) : actionMap A B M (1 ⊗ₜ m) = m := by simp

variable {A B M}

section actionMap

variable {X Y : Type u} [AddCommGroup X] [Module A X]

/-- Naturality of the action map in `B`-linear maps. -/
theorem actionMap_baseChange [Module B X] [IsScalarTower A B X]
    [AddCommGroup Y] [Module A Y] [Module B Y] [IsScalarTower A B Y]
    (g : X →ₗ[B] Y) (x : B ⊗[A] X) :
    actionMap A B Y ((g.restrictScalars A).baseChange B x) = g (actionMap A B X x) := by
  induction x with
  | zero => simp
  | tmul b m => simp
  | add x y hx hy => simp [hx, hy]

/-- The action map of `B ⊗[A] X` retracts the base change of `x ↦ 1 ⊗ₜ x`. -/
theorem actionMap_baseChange_mk (x : B ⊗[A] X) :
    actionMap A B (B ⊗[A] X) ((TensorProduct.mk A B X 1).baseChange B x) = x := by
  induction x with
  | zero => simp
  | tmul b m => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp [hx, hy]

end actionMap

variable (A B M) in
/-- A descent datum on a `B`-module `M` relative to `A → B`, in comodule (Sweedler-coring)
form: a `B`-linear coaction `δ : M → B ⊗[A] M` (`B` acting through the left tensor factor
of the target) that is counital and coassociative.  This is equivalent to the classical
formulation via a `B ⊗[A] B`-linear cocycle isomorphism `M ⊗[A] B ≃ B ⊗[A] M`; see the
module docstring for the dictionary. -/
structure DescentDatum where
  /-- The coaction of the descent datum. -/
  coaction : M →ₗ[B] B ⊗[A] M
  /-- The action map retracts the coaction. -/
  counit (m : M) : actionMap A B M (coaction m) = m
  /-- Coassociativity: the two liftings of the coaction to `B ⊗[A] B ⊗[A] M` agree on
  coaction values.  In the classical dictionary this is the cocycle condition. -/
  coassoc (m : M) :
    (coaction.restrictScalars A).baseChange B (coaction m) =
      (TensorProduct.mk A B M 1).baseChange B (coaction m)

namespace DescentDatum

variable (A B) in
/-- The canonical descent datum on a base change `B ⊗[A] N`, with coaction
`b ⊗ₜ n ↦ b ⊗ₜ 1 ⊗ₜ n`. -/
@[simps coaction]
noncomputable def baseChange (N : Type u) [AddCommGroup N] [Module A N] :
    DescentDatum A B (B ⊗[A] N) where
  coaction := (TensorProduct.mk A B N 1).baseChange B
  counit x := by
    induction x with
    | zero => simp
    | tmul b n => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp [hx, hy]
  coassoc x := by
    induction x with
    | zero => simp
    | tmul b n => simp
    | add x y hx hy => simp only [map_add, hx, hy]

variable (D : DescentDatum A B M)

/-- The `A`-linear difference between the coaction and the canonical map `m ↦ 1 ⊗ₜ m`;
its kernel is the descended module. -/
def coactionSub : M →ₗ[A] B ⊗[A] M :=
  D.coaction.restrictScalars A - TensorProduct.mk A B M 1

@[simp] theorem coactionSub_apply (m : M) : D.coactionSub m = D.coaction m - 1 ⊗ₜ m := rfl

/-- The descended `A`-module of a descent datum: the equalizer
`M₀ = {m : M | δ m = 1 ⊗ₜ m}`. -/
def descended : Submodule A M := LinearMap.ker D.coactionSub

theorem mem_descended {m : M} : m ∈ D.descended ↔ D.coaction m = 1 ⊗ₜ m := by
  rw [descended, LinearMap.mem_ker, coactionSub_apply, sub_eq_zero]

/-- The canonical comparison map `B ⊗[A] M₀ →ₗ[B] M`, `b ⊗ₜ m ↦ b • m`.  Flat descent
(`comparison_bijective`) asserts this is an isomorphism when `B` is flat over `A`. -/
noncomputable def comparison : B ⊗[A] D.descended →ₗ[B] M :=
  LinearMap.liftBaseChange B D.descended.subtype

@[simp] theorem comparison_tmul (b : B) (m : D.descended) :
    D.comparison (b ⊗ₜ m) = b • (m : M) := rfl

theorem comparison_eq_actionMap (x : B ⊗[A] D.descended) :
    D.comparison x = actionMap A B M (D.descended.subtype.lTensor B x) := by
  induction x with
  | zero => simp
  | tmul b m => simp
  | add x y hx hy => simp [hx, hy]

private theorem coactionSub_lTensor_apply (x : B ⊗[A] M) :
    D.coactionSub.lTensor B x =
      (D.coaction.restrictScalars A).baseChange B x -
        (TensorProduct.mk A B M 1).baseChange B x := by
  induction x with
  | zero => simp
  | tmul b m => simp [TensorProduct.tmul_sub]
  | add x y hx hy =>
      simp only [map_add, hx, hy]
      abel

/-- The coaction retracts onto the kernel of `coactionSub ⊗ B`: any `x : B ⊗[A] M` on which
the two liftings agree is a coaction value, namely of `actionMap x`.  This is the
contracting-homotopy computation at the heart of both effectivity and Amitsur exactness. -/
theorem coaction_actionMap {x : B ⊗[A] M}
    (hx : (D.coaction.restrictScalars A).baseChange B x =
      (TensorProduct.mk A B M 1).baseChange B x) :
    D.coaction (actionMap A B M x) = x :=
  (actionMap_baseChange D.coaction x).symm.trans <| by rw [hx, actionMap_baseChange_mk]

/-- **Effectivity of flat descent for modules**: for `B` flat over `A`, the canonical map
`B ⊗[A] M₀ → M` out of the descended module is bijective. -/
theorem comparison_bijective [Module.Flat A B] : Function.Bijective D.comparison := by
  have hexact : Function.Exact (D.descended.subtype.lTensor B) (D.coactionSub.lTensor B) :=
    Module.Flat.lTensor_exact B D.coactionSub.exact_subtype_ker_map
  have hinj : Function.Injective (D.descended.subtype.lTensor B) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ D.descended.injective_subtype
  have key : ∀ y : B ⊗[A] D.descended,
      D.coaction (D.comparison y) = D.descended.subtype.lTensor B y := by
    intro y
    rw [comparison_eq_actionMap]
    refine D.coaction_actionMap (sub_eq_zero.mp ?_)
    rw [← coactionSub_lTensor_apply]
    exact hexact.apply_apply_eq_zero y
  constructor
  · intro y z hyz
    exact hinj (by rw [← key, ← key, hyz])
  · intro m
    have hm : D.coactionSub.lTensor B (D.coaction m) = 0 := by
      rw [coactionSub_lTensor_apply, D.coassoc m, sub_self]
    obtain ⟨y, hy⟩ := (hexact _).mp hm
    refine ⟨y, ?_⟩
    have hcoact : D.coaction (D.comparison y) = D.coaction m := by rw [key y, hy]
    have := congrArg (actionMap A B M) hcoact
    rwa [D.counit, D.counit] at this

/-- The comparison isomorphism `B ⊗[A] M₀ ≃ₗ[B] M` of flat descent. -/
noncomputable def descentEquiv [Module.Flat A B] : B ⊗[A] D.descended ≃ₗ[B] M :=
  LinearEquiv.ofBijective D.comparison D.comparison_bijective

@[simp] theorem descentEquiv_tmul [Module.Flat A B] (b : B) (m : D.descended) :
    D.descentEquiv (b ⊗ₜ m) = b • (m : M) := rfl

section Amitsur

variable [Module.FaithfullyFlat A B]

/-- **Amitsur exactness in degrees `≤ 1`**: for a faithfully flat `A → B` and any
`A`-module `N`, the sequence `0 → N → B ⊗[A] N ⇉ B ⊗[A] B ⊗[A] N` is exact; here the pair
of arrows is encoded by the single map `coactionSub` of the canonical descent datum, whose
kernel is the equalizer. -/
theorem exact_mk_coactionSub (N : Type u) [AddCommGroup N] [Module A N] :
    Function.Exact (TensorProduct.mk A B N 1) (baseChange A B N).coactionSub := by
  apply (Module.FaithfullyFlat.lTensor_exact_iff_exact A B _ _).mp
  intro z
  constructor
  · intro hz
    refine ⟨actionMap A B (B ⊗[A] N) z, ?_⟩
    have hx := (baseChange A B N).coaction_actionMap (x := z) (sub_eq_zero.mp (by
      rw [← coactionSub_lTensor_apply]; exact hz))
    rw [baseChange_coaction] at hx
    rw [← LinearMap.baseChange_eq_ltensor]
    exact hx
  · rintro ⟨x, rfl⟩
    rw [coactionSub_lTensor_apply, sub_eq_zero]
    induction x with
    | zero => simp
    | tmul b n => simp
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The unit of descent: for a faithfully flat `A → B`, the canonical map identifies an
`A`-module `N` with the descended module of the canonical descent datum on `B ⊗[A] N`.
This is the degree `0` consequence of Amitsur exactness. -/
noncomputable def unitEquiv (N : Type u) [AddCommGroup N] [Module A N] :
    N ≃ₗ[A] (baseChange A B N).descended := by
  refine LinearEquiv.ofBijective
    ((TensorProduct.mk A B N 1).codRestrict (baseChange A B N).descended fun n => ?_)
    ⟨fun n n' h => ?_, fun y => ?_⟩
  · rw [mem_descended]
    simp
  · exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) N
      (congrArg Subtype.val h)
  · have h0 : (baseChange A B N).coactionSub (y : B ⊗[A] N) = 0 := LinearMap.mem_ker.mp y.2
    obtain ⟨n, hn⟩ := (exact_mk_coactionSub N (y : B ⊗[A] N)).mp h0
    exact ⟨n, Subtype.ext hn⟩

@[simp] theorem unitEquiv_apply_coe (N : Type u) [AddCommGroup N] [Module A N] (n : N) :
    (unitEquiv (A := A) (B := B) N n : B ⊗[A] N) = 1 ⊗ₜ n := rfl

variable {N : Type u} [AddCommGroup N] [Module A N]

/-- **Uniqueness of descent**: if `N` is an `A`-module and `e : B ⊗[A] N ≃ₗ[B] M`
intertwines the canonical descent datum on `B ⊗[A] N` with `D`, then `N` is canonically
`A`-isomorphic to the descended module of `D`.  In particular two descents of the same
datum are canonically isomorphic (compose one such equivalence with the inverse of the
other). -/
noncomputable def equivDescended (e : (B ⊗[A] N) ≃ₗ[B] M)
    (he : ∀ x : B ⊗[A] N,
      D.coaction (e x) = ((e : B ⊗[A] N →ₗ[B] M).restrictScalars A).baseChange B
        ((baseChange A B N).coaction x)) :
    N ≃ₗ[A] D.descended := by
  refine (unitEquiv N).trans <|
    ((e.restrictScalars A).submoduleMap (baseChange A B N).descended).trans
      (LinearEquiv.ofEq _ _ ?_)
  have hinj : Function.Injective
      (((e : B ⊗[A] N →ₗ[B] M).restrictScalars A).baseChange B) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ e.injective
  ext m
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_descended] at hx ⊢
    change D.coaction (e x) = 1 ⊗ₜ (e x)
    rw [he x, hx]
    simp
  · intro hm
    refine ⟨e.symm m, ?_, e.apply_symm_apply m⟩
    rw [mem_descended] at hm ⊢
    apply hinj
    have := he (e.symm m)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this, hm]
    simp

@[simp] theorem equivDescended_apply_coe (e : (B ⊗[A] N) ≃ₗ[B] M)
    (he : ∀ x : B ⊗[A] N,
      D.coaction (e x) = ((e : B ⊗[A] N →ₗ[B] M).restrictScalars A).baseChange B
        ((baseChange A B N).coaction x)) (n : N) :
    (D.equivDescended e he n : M) = e (1 ⊗ₜ n) := rfl

end Amitsur

end DescentDatum

end Module
