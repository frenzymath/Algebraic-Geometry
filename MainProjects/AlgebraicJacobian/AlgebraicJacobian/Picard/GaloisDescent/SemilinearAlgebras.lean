/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GaloisDescent.SemilinearModules

/-!
# Galois descent for semilinear algebras (the affine heart of `G2`)

This file upgrades the module-level Speiser descent of
`AlgebraicJacobian.Picard.GaloisDescent.SemilinearModules` to **algebras**: it is the
affine heart `G2(b)` of the finite Galois quotient engine of the Picard
representability campaign (`informal/pic-representability-campaign.md`, cluster `G`).

Let `L/K` be a finite Galois extension with group `Γ = Gal(L/K) = L ≃ₐ[K] L`, and let
`A` be an `L`-algebra carrying a `Γ`-action by **ring** automorphisms
(`MulSemiringAction (L ≃ₐ[K] L) A`) that is **semilinear** over the Galois action on
`L` (`IsSemilinear K L A`, the landed module-level class; for a ring action it is
equivalent to `γ • algebraMap L A a = algebraMap L A (γ a)`, see `smul_algebraMap`
and `isSemilinear_of_smul_algebraMap`).

## Main definitions and results

* `SemilinearAction.invariantsSubalgebra K L A : Subalgebra K A` — the invariants
  `A^Γ` as a `K`-subalgebra (its underlying `K`-submodule is
  `SemilinearAction.invariants K L A`, definitionally).
* `SemilinearAction.descentAlgEquiv : L ⊗[K] A^Γ ≃ₐ[L] A` — **Speiser's theorem,
  algebra form**: the invariants are a `K`-form of `A` *as an algebra*.  Deduced from
  the module-level `descentEquiv`; in particular it does **not** use Noether-style
  invariant finiteness (the campaign's explicit prohibition), and `A` is arbitrary
  (no finiteness hypotheses).
* `Algebra.TensorProduct.mem_range_includeRight_iff_forall_map_eq` — for the
  left-factor Galois action on a base change `L ⊗[K] B` of any `K`-algebra `B`, the
  fixed points are exactly `1 ⊗ B`.
* `SemilinearAction.invariantAlgHomEquiv` — **the affine Hom property**:
  `Hom_{K-alg}(A^Γ, B) ≃ Hom_{L-alg}(A, L ⊗[K] B)^Γ` for every `K`-algebra `B`.
  Taking `B = Γ(T, 𝒪_T)` for an affine `K`-scheme `T = Spec B` this is precisely
  `Hom_K(T, Spec A^Γ) ≅ Hom_L(T_L, Spec A)^Γ`, the `T`-points statement of the
  Galois quotient `Spec A^Γ = (Spec A)/Γ` (scheme-level translation in
  `AlgebraicJacobian.Picard.FiniteGaloisQuotient`).

The equivariance condition on `f : A →ₐ[L] L ⊗[K] B` is pinned inverse-free as
`IsEquivariantAlgHom`: `f (γ • x) = (γ ⊗ id) (f x)` for all `γ, x`.

Campaign reference: milestone `G2(b)` of `informal/pic-representability-campaign.md`
(Kleiman FGA-explained §4, Milne JV §4 use finite Galois descent to build `Pic_{C/k}`
from `Pic_{C_{k'}/k'}`; this brick is curve-agnostic and reusable for
`Sym^d`/Albanese).
-/

universe u v w

open scoped TensorProduct
open Module

namespace AlgebraicJacobian.GaloisDescent

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable (A : Type v) [CommRing A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
variable [MulSemiringAction (L ≃ₐ[K] L) A]

namespace SemilinearAction

/-! ## Ring-level semilinearity -/

section RingSemilinear

omit [Algebra K A] [IsScalarTower K L A] in
/-- For a `Γ`-action by ring automorphisms, semilinearity over the Galois action on
`L` specialises on the image of `L` to `γ • algebraMap L A a = algebraMap L A (γ a)`. -/
theorem smul_algebraMap [IsSemilinear K L A] (γ : L ≃ₐ[K] L) (a : L) :
    γ • (algebraMap L A a) = algebraMap L A (γ a) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    smul_smul_apply, smul_one]

omit [Algebra K A] [IsScalarTower K L A] in
/-- Conversely, a ring action satisfying `γ • algebraMap L A a = algebraMap L A (γ a)`
is semilinear.  This is the practical constructor for `IsSemilinear` on algebras. -/
theorem isSemilinear_of_smul_algebraMap
    (h : ∀ (γ : L ≃ₐ[K] L) (a : L), γ • (algebraMap L A a) = algebraMap L A (γ a)) :
    IsSemilinear K L A where
  smul_smul' γ a v := by
    rw [Algebra.smul_def, smul_mul', h, ← Algebra.smul_def]

/-- The Galois action on `A` commutes with the `K`-scalar action (the Galois group
fixes `K`).  Enables mathlib's `FixedPoints.subalgebra`-style API. -/
instance [IsSemilinear K L A] : SMulCommClass (L ≃ₐ[K] L) K A where
  smul_comm γ c x := by
    rw [← IsScalarTower.algebraMap_smul L c x, smul_smul_apply, AlgEquiv.commutes,
      IsScalarTower.algebraMap_smul]

end RingSemilinear

/-! ## The invariant subalgebra -/

section InvariantsSubalgebra

variable [IsSemilinear K L A]

/-- The invariants `A^Γ` of a semilinear `Gal(L/K)`-action by ring automorphisms, as
a `K`-subalgebra of `A`.  Its underlying `K`-submodule is
`SemilinearAction.invariants K L A` (`toSubmodule_invariantsSubalgebra`). -/
def invariantsSubalgebra : Subalgebra K A where
  carrier := {a | ∀ σ : L ≃ₐ[K] L, σ • a = a}
  mul_mem' {x y} hx hy σ := by rw [smul_mul', hx σ, hy σ]
  one_mem' σ := smul_one σ
  add_mem' {x y} hx hy σ := by rw [smul_add, hx σ, hy σ]
  zero_mem' σ := smul_zero σ
  algebraMap_mem' r σ := by
    rw [IsScalarTower.algebraMap_apply K L A, smul_algebraMap K L A, AlgEquiv.commutes]

@[simp] lemma mem_invariantsSubalgebra {a : A} :
    a ∈ invariantsSubalgebra K L A ↔ ∀ σ : L ≃ₐ[K] L, σ • a = a := Iff.rfl

@[simp] lemma toSubmodule_invariantsSubalgebra :
    Subalgebra.toSubmodule (invariantsSubalgebra K L A) = invariants K L A := rfl

/-- The tautological `K`-linear equivalence between the subalgebra invariants and the
module-level invariants (same carrier). -/
def invariantsLinearEquiv :
    (invariantsSubalgebra K L A) ≃ₗ[K] (invariants K L A) where
  toFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma invariantsLinearEquiv_coe (x : invariantsSubalgebra K L A) :
    ((invariantsLinearEquiv K L A x : invariants K L A) : A) = (x : A) := rfl

end InvariantsSubalgebra

/-! ## Speiser's theorem, algebra form -/

section DescentAlgEquiv

variable [IsSemilinear K L A]

/-- The descent map `L ⊗[K] A^Γ →ₐ[L] A`, `a ⊗ w ↦ a • w`, as an `L`-algebra
homomorphism (the `L`-linear extension of the inclusion `A^Γ ↪ A`).  Its underlying
map agrees with the module-level `SemilinearAction.descentMap`. -/
noncomputable def descentAlgHom : L ⊗[K] (invariantsSubalgebra K L A) →ₐ[L] A :=
  AlgHom.liftEquiv K L _ A (invariantsSubalgebra K L A).val

@[simp] lemma descentAlgHom_tmul (a : L) (w : invariantsSubalgebra K L A) :
    descentAlgHom K L A (a ⊗ₜ[K] w) = a • (w : A) := rfl

variable [FiniteDimensional K L] [IsGalois K L]

/-- **Speiser's theorem, algebra form (bijectivity).**  Deduced from the module-level
`descentMap_bijective` — never via invariant finiteness. -/
theorem descentAlgHom_bijective : Function.Bijective (descentAlgHom K L A) := by
  have heq : ⇑(descentAlgHom K L A) = ⇑(descentMap K L A) ∘
      ⇑(TensorProduct.congr (LinearEquiv.refl K L) (invariantsLinearEquiv K L A)) := by
    funext y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a w =>
        simp only [Function.comp_apply, descentAlgHom_tmul, TensorProduct.congr_tmul,
          LinearEquiv.refl_apply, descentMap_tmul, invariantsLinearEquiv_coe]
    | add x y hx hy => simp only [map_add, hx, hy, Function.comp_apply]
  rw [heq]
  exact (descentMap_bijective K L A).comp (TensorProduct.congr _ _).bijective

/-- **Speiser's theorem, algebra form.**  For a finite Galois extension `L/K` and an
`L`-algebra `A` with a semilinear `Gal(L/K)`-action by ring automorphisms, the descent
map is an `L`-algebra isomorphism `L ⊗[K] A^Γ ≃ₐ[L] A`: the invariant subalgebra is a
`K`-form of `A`. -/
noncomputable def descentAlgEquiv : L ⊗[K] (invariantsSubalgebra K L A) ≃ₐ[L] A :=
  AlgEquiv.ofBijective (descentAlgHom K L A) (descentAlgHom_bijective K L A)

@[simp] lemma descentAlgEquiv_tmul (a : L) (w : invariantsSubalgebra K L A) :
    descentAlgEquiv K L A (a ⊗ₜ[K] w) = a • (w : A) := rfl

lemma descentAlgEquiv_symm_coe (w : invariantsSubalgebra K L A) :
    (descentAlgEquiv K L A).symm (w : A) = 1 ⊗ₜ[K] w := by
  rw [AlgEquiv.symm_apply_eq, descentAlgEquiv_tmul, one_smul]

/-- Galois equivariance of the descent isomorphism: the left-factor action `γ ⊗ id`
on `L ⊗[K] A^Γ` corresponds to the given action on `A`. -/
theorem descentAlgEquiv_map_left (γ : L ≃ₐ[K] L)
    (y : L ⊗[K] (invariantsSubalgebra K L A)) :
    descentAlgEquiv K L A
        (Algebra.TensorProduct.map (γ : L →ₐ[K] L) (AlgHom.id K _) y)
      = γ • descentAlgEquiv K L A y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a w =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, AlgEquiv.coe_algHom,
        descentAlgEquiv_tmul, descentAlgEquiv_tmul, smul_smul_apply, w.2 γ]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

end DescentAlgEquiv

end SemilinearAction

/-! ## Fixed points of the left-factor Galois action on a base change

For any `K`-algebra `B`, the Galois group acts on `L ⊗[K] B` through the left factor
(`γ ⊗ id`); the fixed points are exactly the image of `includeRight : B → L ⊗[K] B`.
This is the "trivially-descended" case of Speiser, proved directly by a
basis-coordinate computation (any `K`-basis of `B` base-changes to an `L`-basis whose
coordinates transform by `γ`). -/

section BaseChangeFixedPoints

variable [FiniteDimensional K L] [IsGalois K L]
variable (B : Type w) [CommRing B] [Algebra K B]

omit [FiniteDimensional K L] [IsGalois K L] in
open Algebra.TensorProduct in
/-- Coordinates of the left-factor Galois action: in the base-changed basis
`1 ⊗ bᵢ` of `L ⊗[K] B`, the action `γ ⊗ id` acts on coordinates by `γ`. -/
lemma repr_map_left_baseChange {ι : Type*} (b : Basis ι K B) (γ : L ≃ₐ[K] L)
    (x : L ⊗[K] B) (i : ι) :
    (b.baseChange L).repr (map (γ : L →ₐ[K] L) (AlgHom.id K B) x) i
      = γ ((b.baseChange L).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l y =>
      rw [map_tmul, AlgHom.coe_id, id_eq, AlgEquiv.coe_algHom,
        Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, map_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

open Algebra.TensorProduct in
/-- **Fixed points of the base change.**  For the left-factor Galois action on
`L ⊗[K] B`, an element is fixed by all `γ ⊗ id` iff it lies in `1 ⊗ B`. -/
theorem mem_range_includeRight_iff_forall_map_eq (x : L ⊗[K] B) :
    x ∈ (includeRight : B →ₐ[K] L ⊗[K] B).range
      ↔ ∀ γ : L ≃ₐ[K] L, map (γ : L →ₐ[K] L) (AlgHom.id K B) x = x := by
  constructor
  · rintro ⟨y, rfl⟩ γ
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [includeRight_apply, map_tmul, map_one, AlgHom.coe_id, id_eq]
  · intro hx
    classical
    let b := Module.Free.chooseBasis K B
    set bb := b.baseChange L with hbb
    have hfix : ∀ i, ∀ γ : L ≃ₐ[K] L, γ (bb.repr x i) = bb.repr x i := by
      intro i γ
      conv_rhs => rw [← hx γ]
      rw [repr_map_left_baseChange K L B b γ x i]
    have hmem : ∀ i, ∃ c : K, algebraMap K L c = bb.repr x i := fun i =>
      (IsGalois.mem_range_algebraMap_iff_fixed (bb.repr x i)).mpr (hfix i)
    choose c hc using hmem
    refine ⟨(bb.repr x).sum fun i _ => c i • b i, ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [includeRight_apply]
    conv_rhs => rw [← bb.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_smul, ← hc i, ← algebraMap_smul L (c i) ((1 : L) ⊗ₜ[K] b i),
      hbb, Basis.baseChange_apply]

end BaseChangeFixedPoints

namespace SemilinearAction

/-! ## The affine Hom property

`Hom_{K-alg}(A^Γ, B) ≃ Hom_{L-alg}(A, L ⊗[K] B)^Γ` for every `K`-algebra `B`.  With
`B = Γ(T, 𝒪_T)`, `T = Spec B`, this is the `T`-points property of the affine Galois
quotient `Spec (A^Γ)`. -/

section HomProperty

variable [IsSemilinear K L A]
variable (B : Type w) [CommRing B] [Algebra K B]

/-- Equivariance for an `L`-algebra map `f : A → L ⊗[K] B` (with the left-factor
Galois action on the target): `f (γ • x) = (γ ⊗ id) (f x)`.  This is the invariance
of `f` under the natural `Γ`-action `f ↦ (γ ⊗ id) ∘ f ∘ γ⁻¹` on homs, pinned
inverse-free. -/
def IsEquivariantAlgHom (f : A →ₐ[L] L ⊗[K] B) : Prop :=
  ∀ (γ : L ≃ₐ[K] L) (x : A),
    f (γ • x) = Algebra.TensorProduct.map (γ : L →ₐ[K] L) (AlgHom.id K B) (f x)

variable [FiniteDimensional K L] [IsGalois K L]

/-- Extension of scalars of a `K`-algebra map on the invariants, through the descent
isomorphism: `A ≃ L ⊗ A^Γ → L ⊗ B`. -/
noncomputable def extendScalarsAlgHom (g : invariantsSubalgebra K L A →ₐ[K] B) :
    A →ₐ[L] L ⊗[K] B :=
  (Algebra.TensorProduct.map (AlgHom.id L L) g).comp
    (descentAlgEquiv K L A).symm.toAlgHom

@[simp] lemma extendScalarsAlgHom_coe (g : invariantsSubalgebra K L A →ₐ[K] B)
    (w : invariantsSubalgebra K L A) :
    extendScalarsAlgHom K L A B g (w : A)
      = Algebra.TensorProduct.includeRight (g w) := by
  rw [extendScalarsAlgHom, AlgHom.comp_apply, AlgEquiv.coe_algHom,
    descentAlgEquiv_symm_coe, Algebra.TensorProduct.map_tmul, map_one,
    Algebra.TensorProduct.includeRight_apply]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Naturality: the left-factor action commutes with `id ⊗ g`. -/
lemma map_left_map_right_comm (γ : L ≃ₐ[K] L) (g : invariantsSubalgebra K L A →ₐ[K] B)
    (y : L ⊗[K] (invariantsSubalgebra K L A)) :
    Algebra.TensorProduct.map (AlgHom.id L L) g
        (Algebra.TensorProduct.map (γ : L →ₐ[K] L) (AlgHom.id K _) y)
      = Algebra.TensorProduct.map (γ : L →ₐ[K] L) (AlgHom.id K B)
        (Algebra.TensorProduct.map (AlgHom.id L L) g y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a w => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The extension of scalars of an invariants-level map is equivariant. -/
theorem isEquivariantAlgHom_extendScalarsAlgHom (g : invariantsSubalgebra K L A →ₐ[K] B) :
    IsEquivariantAlgHom K L A B (extendScalarsAlgHom K L A B g) := by
  intro γ x
  have h1 : (descentAlgEquiv K L A).symm (γ • x)
      = Algebra.TensorProduct.map (γ : L →ₐ[K] L) (AlgHom.id K _)
          ((descentAlgEquiv K L A).symm x) := by
    apply (descentAlgEquiv K L A).injective
    rw [AlgEquiv.apply_symm_apply, descentAlgEquiv_map_left, AlgEquiv.apply_symm_apply]
  rw [extendScalarsAlgHom, AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom,
    h1, map_left_map_right_comm]

omit [FiniteDimensional K L] in
lemma includeRight_injective' :
    Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B) :=
  Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective K L)

/-- An equivariant `L`-algebra map sends invariants into `1 ⊗ B`. -/
lemma isEquivariantAlgHom_coe_mem_range {f : A →ₐ[L] L ⊗[K] B}
    (hf : IsEquivariantAlgHom K L A B f) (w : invariantsSubalgebra K L A) :
    f (w : A) ∈ (Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B).range := by
  rw [mem_range_includeRight_iff_forall_map_eq]
  intro γ
  rw [← hf γ (w : A), w.2 γ]

/-- Restriction of an equivariant `L`-algebra map `A → L ⊗[K] B` to the invariants,
landing in `B` (through `1 ⊗ B`). -/
noncomputable def restrictInvariantsAlgHom (f : A →ₐ[L] L ⊗[K] B)
    (hf : IsEquivariantAlgHom K L A B f) : invariantsSubalgebra K L A →ₐ[K] B :=
  ((AlgEquiv.ofInjective _ (includeRight_injective' K L B)).symm.toAlgHom).comp
    (((f.restrictScalars K).comp (invariantsSubalgebra K L A).val).codRestrict
      (Algebra.TensorProduct.includeRight :
        B →ₐ[K] L ⊗[K] B).range
      fun w => isEquivariantAlgHom_coe_mem_range K L A B hf w)

@[simp] lemma includeRight_restrictInvariantsAlgHom (f : A →ₐ[L] L ⊗[K] B)
    (hf : IsEquivariantAlgHom K L A B f) (w : invariantsSubalgebra K L A) :
    Algebra.TensorProduct.includeRight (restrictInvariantsAlgHom K L A B f hf w)
      = f (w : A) := by
  have key : ∀ y : (Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B).range,
      Algebra.TensorProduct.includeRight
        ((AlgEquiv.ofInjective _ (includeRight_injective' K L B)).symm y) = (y : L ⊗[K] B) := by
    intro y
    conv_rhs => rw [← AlgEquiv.apply_symm_apply
      (AlgEquiv.ofInjective _ (includeRight_injective' K L B)) y]
    rw [AlgEquiv.ofInjective_apply]
  rw [restrictInvariantsAlgHom, AlgHom.comp_apply, AlgEquiv.coe_algHom, key]
  rfl

/-- **The affine Hom property (Speiser descent for homs).**  For every `K`-algebra
`B`, `K`-algebra maps `A^Γ → B` correspond to equivariant `L`-algebra maps
`A → L ⊗[K] B`.  With `B = Γ(T, 𝒪_T)` for affine `T` this is
`Hom_K(T, Spec A^Γ) ≅ Hom_L(T ×_K Spec L, Spec A)^Γ`. -/
noncomputable def invariantAlgHomEquiv :
    (invariantsSubalgebra K L A →ₐ[K] B) ≃
      {f : A →ₐ[L] L ⊗[K] B // IsEquivariantAlgHom K L A B f} where
  toFun g := ⟨extendScalarsAlgHom K L A B g,
    isEquivariantAlgHom_extendScalarsAlgHom K L A B g⟩
  invFun f := restrictInvariantsAlgHom K L A B f.1 f.2
  left_inv g := by
    ext w
    apply includeRight_injective' K L B
    rw [includeRight_restrictInvariantsAlgHom, extendScalarsAlgHom_coe]
  right_inv f := by
    refine Subtype.ext ?_
    apply AlgHom.toLinearMap_injective
    apply LinearMap.ext_on (span_invariants_eq_top K L A)
    intro x hx
    have hx' : x ∈ invariantsSubalgebra K L A := hx
    change extendScalarsAlgHom K L A B (restrictInvariantsAlgHom K L A B f.1 f.2) x = f.1 x
    have hxw : x = ((⟨x, hx'⟩ : invariantsSubalgebra K L A) : A) := rfl
    rw [hxw, extendScalarsAlgHom_coe, includeRight_restrictInvariantsAlgHom]

end HomProperty

end SemilinearAction

end AlgebraicJacobian.GaloisDescent
