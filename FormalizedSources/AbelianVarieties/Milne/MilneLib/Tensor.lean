/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

import MilneLib.Nakayama
import MilneLib.Stalk

/-!
# Tensor evaluation

The canonical evaluation map from a scalar extension tensor product sends a
pure tensor `s ⊗ m` to the scalar action `s • m`.
-/

open scoped TensorProduct
open CategoryTheory
open AlgebraicGeometry
open Opposite

namespace MilneLib

noncomputable def tensorProductEval
    (R S M : Type*)
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M]
    [IsScalarTower R S M] :
    S ⊗[R] M →ₗ[S] M :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.restrictScalarsₗ R S M M S ∘ₗ LinearMap.lsmul S M)

@[simp]
theorem tensorProductEval_tmul
    (R S M : Type*)
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M]
    [IsScalarTower R S M]
    (s : S) (m : M) :
    tensorProductEval R S M (s ⊗ₜ[R] m) = s • m := by
  rfl

/-
The pure-tensor formula characterizes the evaluation map.  This is useful when
an evaluation map is constructed by a different universal-property interface.
-/
theorem tensorProductEval_eq_of_tmul
    (R S M : Type*)
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M]
    [IsScalarTower R S M]
    (f : S ⊗[R] M →ₗ[S] M)
    (h : ∀ s m, f (s ⊗ₜ[R] m) = s • m) :
    f = tensorProductEval R S M := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => exact h s m
  | add x y hx hy => simp [hx, hy]

/-!
## Tensoring with a ring quotient

The quotient/residue fibre that occurs in Milne I.5.11 is canonically the
quotient of the module by the corresponding ideal action.  This is a small
MilneLib-facing alias for Mathlib's universal-property construction, together
with the formulas needed to use it on pure tensors and quotient maps.
-/

/-- The canonical equivalence
`(R ⧸ I) ⊗[R] M ≃ₗ[R] M ⧸ (I • ⊤)`.

This re-exports Mathlib's `TensorProduct.quotTensorEquivQuotSMul` under the
MilneLib namespace so residue-fibre arguments can use a project-local API.
-/
noncomputable def quotTensorEquivQuotSMul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
  TensorProduct.quotTensorEquivQuotSMul M I

/-- The quotient--tensor equivalence for the residue field of a local ring.

This is the local form used to compare a residue fibre with reduction modulo
the maximal ideal. -/
noncomputable def residueFieldTensorEquivQuotSMul
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] :
    IsLocalRing.ResidueField R ⊗[R] M ≃ₗ[R]
      M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) :=
  quotTensorEquivQuotSMul (M := M) (IsLocalRing.maximalIdeal R)

@[simp]
theorem quotTensorEquivQuotSMul_mk_tmul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (r : R) (x : M) :
    quotTensorEquivQuotSMul (M := M) I (Ideal.Quotient.mk I r ⊗ₜ[R] x) =
      Submodule.Quotient.mk (r • x) := by
  exact TensorProduct.quotTensorEquivQuotSMul_mk_tmul (M := M) I r x

theorem quotTensorEquivQuotSMul_comp_mkQ_rTensor
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    quotTensorEquivQuotSMul (M := M) I ∘ₗ I.mkQ.rTensor M =
      (I • (⊤ : Submodule R M)).mkQ ∘ₗ TensorProduct.lid R M := by
  exact TensorProduct.quotTensorEquivQuotSMul_comp_mkQ_rTensor (M := M) I

/-!
## Residue fibres of scheme modules

The stalk of a scheme module is naturally a module over the local structure
ring.  This wrapper exposes the preceding quotient--tensor equivalence with
the scheme notation, so residue-fibre arguments can stay at the sheaf level.
-/

/-- The canonical module structure on the stalk of a scheme module over the
corresponding structure-sheaf stalk. -/
noncomputable abbrev schemeModuleStalkModule
    {X : Scheme.{u}} (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    F.val x

/-- The `X.presheaf.stalk x`-linear map induced by a morphism of scheme
modules.  The two `letI` binders make the canonical stalk module structures
explicit, since the scheme-module and presheaf presentations use different
typeclass paths for the same structure. -/
noncomputable def schemeModuleStalkLinearMap
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (x : X) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
      schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
      schemeModuleStalkModule N x
    (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) →ₗ[↑(X.presheaf.stalk x)]
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) := by
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
    schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
    schemeModuleStalkModule N x
  exact PresheafOfModules.stalkLinearMap (R := X.presheaf) f.val x

@[simp]
theorem schemeModuleStalkLinearMap_germ
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (x : X)
    (U : X.Opens) (hx : x ∈ U)
    (s : (↑(M.val.obj (op U)) : Type u)) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
      schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
      schemeModuleStalkModule N x
    schemeModuleStalkLinearMap f x
        ((ConcreteCategory.hom (TopCat.Presheaf.germ M.val.presheaf U x hx)) s) =
      (ConcreteCategory.hom (TopCat.Presheaf.germ N.val.presheaf U x hx))
        ((ConcreteCategory.hom (f.val.app (op U))) s) := by
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
    schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
    schemeModuleStalkModule N x
  exact PresheafOfModules.stalkLinearMap_germ f.val x U hx s

/-- An isomorphism on the underlying additive stalks gives a bijective linear
map on the stalks of scheme modules. -/
theorem schemeModuleStalkLinearMap_bijective_of_isIso
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (x : X)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      f.mapPresheaf)) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
      schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
      schemeModuleStalkModule N x
    Function.Bijective (schemeModuleStalkLinearMap f x) := by
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
    schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
    schemeModuleStalkModule N x
  change Function.Bijective ⇑(ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.mapPresheaf))
  exact ConcreteCategory.bijective_of_isIso _

/-- The stalkwise linear equivalence induced by an isomorphism of scheme
modules on the underlying additive stalks. -/
noncomputable def schemeModuleStalkLinearEquivOfIsIso
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (x : X)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      f.mapPresheaf)) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
      schemeModuleStalkModule M x
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
      schemeModuleStalkModule N x
    (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) ≃ₗ[↑(X.presheaf.stalk x)]
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) := by
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) : Type u) :=
    schemeModuleStalkModule M x
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk N.val.presheaf x) : Type u) :=
    schemeModuleStalkModule N x
  exact LinearEquiv.ofBijective (schemeModuleStalkLinearMap f x)
    (schemeModuleStalkLinearMap_bijective_of_isIso f x h)

/-- The residue fibre of a scheme module is the stalk modulo the maximal-ideal
action.  The source is written as tensoring the stalk with its residue field,
which is the form used by base-change arguments. -/
noncomputable def schemeModuleStalkResidueTensorEquiv
    {X : Scheme.{u}} (F : X.Modules) (x : X) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
      schemeModuleStalkModule F x
    IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) ≃ₗ[
          X.presheaf.stalk x]
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) ⧸
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
          (⊤ : Submodule (X.presheaf.stalk x)
            (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u))) := by
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    schemeModuleStalkModule F x
  exact residueFieldTensorEquivQuotSMul

@[simp]
theorem schemeModuleStalkResidueTensorEquiv_mk_tmul
    {X : Scheme.{u}} (F : X.Modules) (x : X)
    (r : X.presheaf.stalk x)
    (m : (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u)) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
      schemeModuleStalkModule F x
    schemeModuleStalkResidueTensorEquiv F x
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) r
          ⊗ₜ[X.presheaf.stalk x] m) =
      Submodule.Quotient.mk (r • m) := by
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u) :=
    schemeModuleStalkModule F x
  exact quotTensorEquivQuotSMul_mk_tmul
    (M := (↑(TopCat.Presheaf.stalk F.val.presheaf x) : Type u))
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) r m

/-! The quotient model is functorial for maps preserving the ideal action. -/

/-- The tensor--quotient equivalence commutes with a linear map that carries
the `I`-action submodule into the target `I`-action submodule. -/
theorem quotTensorEquivQuotSMul_naturality
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (I : Ideal R) (f : M →ₗ[R] N)
    (hI : I • (⊤ : Submodule R M) ≤
      (I • (⊤ : Submodule R N)).comap f) :
    (quotTensorEquivQuotSMul (M := N) I).toLinearMap ∘ₗ
        (f.lTensor (R ⧸ I)) =
      ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f hI) ∘ₗ
        (quotTensorEquivQuotSMul (M := M) I).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp [LinearMap.comp_apply]
  | add x y hx hy =>
      simpa only [map_add, LinearMap.comp_apply] using
        congrArg₂ (fun a b => a + b) hx hy

/-!
## Surjectivity on residue fibres

The tensor--quotient equivalence transports surjectivity of a scalar-extension
map to surjectivity of the corresponding map between ideal quotients.  The
local form below is the residue-fibre spelling used with Nakayama's lemma.
-/

/-- Surjectivity is preserved by the tensor--quotient equivalences. -/
theorem LinearMap.surjective_lTensor_iff_surjective_mapQ
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N)
    (hI : I • (⊤ : Submodule R M) ≤
      (I • (⊤ : Submodule R N)).comap f) :
    Function.Surjective (f.lTensor (R ⧸ I)) ↔
      Function.Surjective
        ((I • (⊤ : Submodule R M)).mapQ
          (I • (⊤ : Submodule R N)) f hI) := by
  let eM := quotTensorEquivQuotSMul (M := M) I
  let eN := quotTensorEquivQuotSMul (M := N) I
  let qf := (I • (⊤ : Submodule R M)).mapQ
      (I • (⊤ : Submodule R N)) f hI
  have hnat :
      eN.toLinearMap ∘ₗ (f.lTensor (R ⧸ I)) =
        qf ∘ₗ eM.toLinearMap :=
    quotTensorEquivQuotSMul_naturality I f hI
  constructor
  · intro hf y
    obtain ⟨z, hz⟩ := eN.surjective y
    obtain ⟨w, hw⟩ := hf z
    refine ⟨eM w, ?_⟩
    have hcomp := congrArg (fun g => g w) hnat
    change eN ((f.lTensor (R ⧸ I)) w) = qf (eM w) at hcomp
    rw [hw] at hcomp
    exact hcomp.symm.trans hz
  · intro hq z
    obtain ⟨wq, hwq⟩ := hq (eN z)
    obtain ⟨t, ht⟩ := eM.surjective wq
    refine ⟨t, ?_⟩
    apply eN.injective
    have hcomp := congrArg (fun g => g t) hnat
    change eN ((f.lTensor (R ⧸ I)) t) = qf (eM t) at hcomp
    rw [ht, hwq] at hcomp
    exact hcomp

/-- For a local ring, surjectivity on the residue-field tensor fibre is
equivalent to surjectivity after quotienting by the maximal-ideal action. -/
theorem LinearMap.surjective_lTensor_residueField_iff_surjective_residue
    {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Surjective (f.lTensor (IsLocalRing.ResidueField R)) ↔
      Function.Surjective
        (((IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)).mkQ) ∘ₗ f) := by
  let I := IsLocalRing.maximalIdeal R
  change Function.Surjective (f.lTensor (R ⧸ I)) ↔
      Function.Surjective (((I • (⊤ : Submodule R N)).mkQ) ∘ₗ f)
  have hI : I • (⊤ : Submodule R M) ≤
      (I • (⊤ : Submodule R N)).comap f := by
    rw [Submodule.smul_le]
    intro r hr m hm
    change f (r • m) ∈ I • (⊤ : Submodule R N)
    rw [f.map_smul]
    exact Submodule.smul_mem_smul hr trivial
  let qf := (I • (⊤ : Submodule R M)).mapQ
      (I • (⊤ : Submodule R N)) f hI
  have hq :
      Function.Surjective (f.lTensor (R ⧸ I)) ↔ Function.Surjective qf :=
    LinearMap.surjective_lTensor_iff_surjective_mapQ I f hI
  have hrel :
      qf ∘ₗ (I • (⊤ : Submodule R M)).mkQ =
      (I • (⊤ : Submodule R N)).mkQ ∘ₗ f :=
    Submodule.mapQ_mkQ _ _ f
  constructor
  · intro h
    have hqsurj : Function.Surjective qf := hq.mp h
    intro y
    obtain ⟨z, hz⟩ := hqsurj y
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) z
    refine ⟨x, ?_⟩
    have he := congrArg (fun g => g x) hrel
    calc
      ((I • (⊤ : Submodule R N)).mkQ ∘ₗ f) x =
          qf ((I • (⊤ : Submodule R M)).mkQ x) := he.symm
      _ = qf z := congrArg qf hx
      _ = y := hz
  · intro h
    apply hq.mpr
    intro y
    obtain ⟨x, hx⟩ := h y
    refine ⟨(I • (⊤ : Submodule R M)).mkQ x, ?_⟩
    have he := congrArg (fun g => g x) hrel
    calc
      qf ((I • (⊤ : Submodule R M)).mkQ x) =
          ((I • (⊤ : Submodule R N)).mkQ ∘ₗ f) x := he
      _ = y := hx

/-- The finite-target Nakayama step can therefore be stated directly for the
residue-field scalar extension. -/
theorem LinearMap.surjective_lTensor_residueField_iff_surjective
    {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N) :
    Function.Surjective (f.lTensor (IsLocalRing.ResidueField R)) ↔
      Function.Surjective f := by
  exact (surjective_lTensor_residueField_iff_surjective_residue f).trans
    (MilneLib.LinearMap.surjective_iff_surjective_residue f).symm

end MilneLib
