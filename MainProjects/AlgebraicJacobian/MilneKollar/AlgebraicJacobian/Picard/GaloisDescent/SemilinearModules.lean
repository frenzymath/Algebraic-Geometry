/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Std.Tactic.BVDecide.LRAT.Internal.Clause

/-!
# Galois descent for semilinear representations (Speiser's theorem)

This file supplies the **finite Galois descent** substrate for the FGA Picard-scheme
representability campaign (`instHasPicScheme`, cluster `G` of
`informal/pic-representability-campaign.md`): milestone `G2(b)` (Speiser's
semilinear descent) and its consumers `G1`/`G3`.

Let `L/K` be a finite Galois extension with group `G = Gal(L/K) = L ≃ₐ[K] L`, and
let `V` be an `L`-vector space equipped with a **semilinear** `G`-action, i.e. an
additive `G`-action with
`σ • (a • v) = σ a • (σ • v)` for `σ ∈ G`, `a ∈ L`, `v ∈ V` (`IsSemilinear`).
The `K`-subspace of invariants `V^G` (`SemilinearAction.invariants`) is a `K`-form
of `V`: the canonical `L`-linear map

`descentMap : L ⊗[K] V^G → V`,  `a ⊗ v ↦ a • v`

is an **isomorphism** (`descentEquiv`), so `dim_K V^G = dim_L V`. This is Speiser's
theorem — Galois descent for vector spaces — the algebraic heart of the finite
Galois quotient engine `G2`.

## Main definitions and results

* `IsSemilinear K L V` — the semilinearity hypothesis on a `G`-action.
* `SemilinearAction.invariants K L V : Submodule K V` — the fixed subspace `V^G`.
* `SemilinearAction.avg K L a v : V` — the averaging element `∑_σ σ a • (σ • v)`,
  which always lies in `V^G` (`avg_mem_invariants`).
* `SemilinearAction.descentMap K L V : L ⊗[K] V^G →ₗ[L] V` — the descent map.
* `SemilinearAction.descentMap_bijective` / `descentEquiv` — Speiser's theorem.

## Mathlib inputs

The linear-algebra heart is **Dedekind's independence of characters**
(`linearIndependent_algHom_toLinearMap`): the `K`-algebra homomorphisms `L →ₐ[K] L`
are `L`-linearly independent as `K`-linear maps.  Combined with the finite-field
count `AlgHom.card`, the "Galois matrix" `(σ (b i))_{σ, i}` of a `K`-basis `b` of
`L` is invertible over `L`, which powers both directions of the descent isomorphism.

Campaign reference: milestone `G2` of `informal/pic-representability-campaign.md`
(Kleiman §4 uses finite Galois descent to build `Pic_{C/k}` from `Pic_{C_{k'}/k'}`;
this brick is field-agnostic and reused for `Sym^d`/Albanese).
-/

universe u v

open scoped TensorProduct
open Module

namespace AlgebraicJacobian.GaloisDescent

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable (V : Type v) [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
variable [DistribMulAction (L ≃ₐ[K] L) V]

/-- A **semilinear** `Gal(L/K)`-action on an `L`-module `V`: the additive `G`-action
is compatible with the `L`-scalar action twisted by `σ`, i.e.
`σ • (a • v) = σ a • (σ • v)`. -/
class IsSemilinear : Prop where
  /-- The semilinearity relation `σ • (a • v) = σ a • (σ • v)`. -/
  smul_smul' (σ : L ≃ₐ[K] L) (a : L) (v : V) : σ • (a • v) = σ a • σ • v

/-! ## The Galois matrix

Dedekind's independence of characters, transported through evaluation at a
`K`-basis `b` of `L`, says the "rows" of the Galois matrix `(σ (b i))_{σ, i}` are
`L`-linearly independent in `ι → L`; since their number equals `dim_L (ι → L)`
they span.  From this we deduce the annihilation criterion
`galoisMatrix_eq_zero_of`, which powers both directions of Speiser descent. -/

section GaloisCore

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {ι : Type*}

/-- Evaluation of a `K`-linear endomorphism of `L` at a basis, as an `L`-linear map
`(L →ₗ[K] L) →ₗ[L] (ι → L)`, `f ↦ (i ↦ f (b i))`. -/
noncomputable def evalAtBasis (b : Basis ι K L) : (L →ₗ[K] L) →ₗ[L] (ι → L) where
  toFun f i := f (b i)
  map_add' f g := by ext i; simp
  map_smul' c f := by ext i; simp

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp] lemma evalAtBasis_apply (b : Basis ι K L) (f : L →ₗ[K] L) (i : ι) :
    evalAtBasis b f i = f (b i) := rfl

omit [FiniteDimensional K L] [IsGalois K L] in
lemma evalAtBasis_ker (b : Basis ι K L) : LinearMap.ker (evalAtBasis b) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro f hf
  refine b.ext fun i => ?_
  have h0 : evalAtBasis b f i = 0 := by rw [hf]; rfl
  simpa using h0

omit [FiniteDimensional K L] [IsGalois K L] in
/-- **Dedekind independence, matrix form.** The rows `σ ↦ (i ↦ σ (b i))` of the
Galois matrix are `L`-linearly independent in `ι → L`. -/
theorem galoisRow_linearIndependent (b : Basis ι K L) :
    LinearIndependent L (fun σ : L ≃ₐ[K] L => (fun i => σ (b i) : ι → L)) := by
  have hAlg : LinearIndependent L (fun f : L →ₐ[K] L => f.toLinearMap) :=
    linearIndependent_algHom_toLinearMap K L L
  have hEquiv : LinearIndependent L
      (fun σ : L ≃ₐ[K] L => ((σ : L →ₐ[K] L)).toLinearMap) :=
    hAlg.comp (fun σ : L ≃ₐ[K] L => (σ : L →ₐ[K] L)) AlgEquiv.coe_algHom_injective
  have hmap := hEquiv.map' (evalAtBasis b) (evalAtBasis_ker b)
  have hfun : (fun σ : L ≃ₐ[K] L => (fun i => σ (b i) : ι → L))
      = (evalAtBasis b) ∘ (fun σ : L ≃ₐ[K] L => ((σ : L →ₐ[K] L)).toLinearMap) := by
    funext σ i; simp
  rw [hfun]; exact hmap

/-- The rows of the Galois matrix span `ι → L` over `L`. -/
theorem galoisRow_span [Finite ι] (b : Basis ι K L) :
    Submodule.span L (Set.range (fun σ : L ≃ₐ[K] L => (fun i => σ (b i) : ι → L))) = ⊤ := by
  haveI := Fintype.ofFinite ι
  haveI : Nonempty ι := b.index_nonempty
  refine (galoisRow_linearIndependent b).span_eq_top_of_card_eq_finrank ?_
  have h1 : Fintype.card (L ≃ₐ[K] L) = Fintype.card ι := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank K L, finrank_eq_card_basis b]
  rw [Module.finrank_fintype_fun_eq_card, h1]

/-- **The Galois-matrix annihilation criterion.** For any `L`-module `W` and
vectors `t : ι → W`: if `∑_i σ (b i) • t i = 0` for every `σ ∈ Gal(L/K)`, then all
`t i = 0`.  With `W = V` this gives injectivity of the descent map; with `W = L`
it gives independence of the Galois-matrix columns (hence surjectivity). -/
theorem galoisMatrix_eq_zero_of [Fintype ι]
    {W : Type*} [AddCommGroup W] [Module L W]
    (b : Basis ι K L) (t : ι → W)
    (h : ∀ σ : L ≃ₐ[K] L, ∑ i, σ (b i) • t i = 0) (j : ι) : t j = 0 := by
  classical
  have hmem : (Pi.single j (1 : L) : ι → L) ∈ Submodule.span L
      (Set.range (fun σ : L ≃ₐ[K] L => (fun i => σ (b i) : ι → L))) := by
    rw [galoisRow_span]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hcoord : ∀ i, (Pi.single j (1 : L) : ι → L) i = ∑ σ : L ≃ₐ[K] L, c σ * σ (b i) := by
    intro i
    have := congrFun hc i
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this.symm
  calc t j = ∑ i, (Pi.single j (1 : L) : ι → L) i • t i := by
            simp [Pi.single_apply, Finset.sum_ite_eq']
    _ = ∑ i, (∑ σ : L ≃ₐ[K] L, c σ * σ (b i)) • t i := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [hcoord i]
    _ = ∑ σ : L ≃ₐ[K] L, c σ • ∑ i, σ (b i) • t i := by
            simp_rw [Finset.sum_smul, mul_smul]
            rw [Finset.sum_comm]
            simp_rw [← Finset.smul_sum]
    _ = 0 := by simp [h]

/-- The columns of the Galois matrix span `(L ≃ₐ[K] L) → L` over `L`.  Deduced from
column independence (`galoisMatrix_eq_zero_of` with `W = L`) and the cardinality
count.  Powers surjectivity of the descent map. -/
theorem galoisCol_span [Finite ι] (b : Basis ι K L) :
    Submodule.span L
      (Set.range (fun i : ι => (fun σ => σ (b i) : (L ≃ₐ[K] L) → L))) = ⊤ := by
  classical
  haveI := Fintype.ofFinite ι
  haveI : Nonempty ι := b.index_nonempty
  have hindep : LinearIndependent L
      (fun i : ι => (fun σ => σ (b i) : (L ≃ₐ[K] L) → L)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    refine galoisMatrix_eq_zero_of b g fun σ => ?_
    have h2 := congrFun hg σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2
    simpa [smul_eq_mul, mul_comm] using h2
  refine hindep.span_eq_top_of_card_eq_finrank ?_
  have h1 : Fintype.card ι = Fintype.card (L ≃ₐ[K] L) := by
    rw [← Nat.card_eq_fintype_card (α := L ≃ₐ[K] L), IsGalois.card_aut_eq_finrank K L,
      finrank_eq_card_basis b]
  rw [Module.finrank_fintype_fun_eq_card, h1]

/-- From an `L`-basis `b` of `L` and a `K`-module `W`: the `K`-linear map
`(ι → W) → L ⊗[K] W`, `t ↦ ∑ i, b i ⊗ₜ t i`.  It is surjective, exhibiting
`L ⊗[K] W` as spanned by the tensors `b i ⊗ₜ w`. -/
noncomputable def tensorFromPi [Fintype ι] {W : Type*} [AddCommGroup W] [Module K W]
    (b : Basis ι K L) : (ι → W) →ₗ[K] L ⊗[K] W :=
  ∑ i, (TensorProduct.mk K L W (b i)).comp (LinearMap.proj i)

omit [FiniteDimensional K L] [IsGalois K L] in
lemma tensorFromPi_apply [Fintype ι] {W : Type*} [AddCommGroup W] [Module K W]
    (b : Basis ι K L) (t : ι → W) :
    tensorFromPi b t = ∑ i, b i ⊗ₜ[K] t i := by
  simp [tensorFromPi, LinearMap.sum_apply]

omit [FiniteDimensional K L] [IsGalois K L] in
lemma tensorFromPi_surjective [Fintype ι] {W : Type*} [AddCommGroup W] [Module K W]
    (b : Basis ι K L) : Function.Surjective (tensorFromPi (W := W) b) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp [tensorFromPi_apply]⟩
  | tmul a w =>
      refine ⟨fun i => b.repr a i • w, ?_⟩
      rw [tensorFromPi_apply]
      conv_rhs => rw [← Basis.sum_repr b a]
      rw [TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun i _ => (TensorProduct.smul_tmul _ _ _).symm
  | add x y hx hy =>
      obtain ⟨tx, rfl⟩ := hx
      obtain ⟨ty, rfl⟩ := hy
      exact ⟨tx + ty, by rw [map_add]⟩

end GaloisCore

namespace SemilinearAction

variable {K L V}

omit [Module K V] [IsScalarTower K L V] in
lemma smul_smul_apply [IsSemilinear K L V]
    (σ : L ≃ₐ[K] L) (a : L) (v : V) : σ • (a • v) = σ a • σ • v :=
  IsSemilinear.smul_smul' σ a v

variable (K L V)

/-- The `K`-subspace `V^G` of `Gal(L/K)`-invariant vectors. It is a `K`-submodule
(not `L`) because the `G`-action is only `K`-semilinear. -/
def invariants [IsSemilinear K L V] : Submodule K V where
  carrier := {v | ∀ σ : L ≃ₐ[K] L, σ • v = v}
  add_mem' {x y} hx hy σ := by rw [smul_add, hx, hy]
  zero_mem' σ := smul_zero σ
  smul_mem' c v hv σ := by
    -- `c : K` acts through `L`; `σ` fixes `K`, so it fixes `c • v`.
    rw [← IsScalarTower.algebraMap_smul L c v, smul_smul_apply, AlgEquiv.commutes, hv]

@[simp] lemma mem_invariants [IsSemilinear K L V] {v : V} :
    v ∈ invariants K L V ↔ ∀ σ : L ≃ₐ[K] L, σ • v = v := Iff.rfl

variable {V}

/-- The **averaging** element `∑_σ σ a • (σ • v)`.  For every `a : L` and `v : V`
it lies in the invariants `V^G` (`avg_mem_invariants`); ranging `a` over `L` it
produces enough invariants to span `V` over `L` (`span_avg_eq_top`). -/
noncomputable def avg [FiniteDimensional K L] (a : L) (v : V) : V :=
  ∑ σ : L ≃ₐ[K] L, σ a • σ • v

variable {K L}

lemma avg_mem_invariants [FiniteDimensional K L] [IsSemilinear K L V] (a : L) (v : V) :
    avg K L a v ∈ invariants K L V := by
  intro τ
  have hτ : τ • avg K L a v = ∑ σ : L ≃ₐ[K] L, (τ * σ) a • (τ * σ) • v := by
    rw [avg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_smul_apply, ← mul_smul, ← AlgEquiv.mul_apply]
  rw [hτ, avg]
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => σ a • σ • v)

variable (K L V)

/-- The **descent map** `L ⊗[K] V^G →ₗ[L] V`, `a ⊗ v ↦ a • v`, the `L`-linear
extension of the `K`-linear inclusion `V^G ↪ V`.  Speiser's theorem
(`descentMap_bijective`) is that it is bijective. -/
noncomputable def descentMap [IsSemilinear K L V] :
    L ⊗[K] (invariants K L V) →ₗ[L] V :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton L _ (invariants K L V).subtype)

@[simp] lemma descentMap_tmul [IsSemilinear K L V] (a : L) (w : invariants K L V) :
    descentMap K L V (a ⊗ₜ[K] w) = a • (w : V) := by
  simp [descentMap, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply]

/-! ## Speiser's theorem: the descent map is an isomorphism -/

variable [FiniteDimensional K L] [IsGalois K L]

/-- **Surjectivity direction.** The invariants `V^G` span `V` over `L`.  For each
`v` and each basis vector `b i`, the averaged element `avg (b i) v` is invariant,
and `v` is recovered as an `L`-combination of these because the columns of the
Galois matrix span (`galoisCol_span`). -/
theorem span_invariants_eq_top [IsSemilinear K L V] :
    Submodule.span L ((invariants K L V : Set V)) = ⊤ := by
  classical
  rw [Submodule.eq_top_iff']
  intro v
  set b := finBasis K L with hb
  set Ψ : ((L ≃ₐ[K] L) → L) →ₗ[L] V :=
    Fintype.linearCombination L (fun σ => σ • v) with hΨ
  have hv : Ψ (Pi.single (1 : L ≃ₐ[K] L) (1 : L)) = v := by
    simp [hΨ, Fintype.linearCombination_apply_single, one_smul]
  have hcol : (Pi.single (1 : L ≃ₐ[K] L) (1 : L)) ∈ Submodule.span L
      (Set.range (fun i => (fun σ => σ (b i) : (L ≃ₐ[K] L) → L))) := by
    rw [galoisCol_span b]; trivial
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hcol
  have hΨcol : ∀ i, Ψ (fun σ => σ (b i)) = avg K L (b i) v := fun i => by
    rw [hΨ, Fintype.linearCombination_apply]; rfl
  have hveq : ∑ i, e i • avg K L (b i) v = v := by
    calc ∑ i, e i • avg K L (b i) v
        = ∑ i, e i • Ψ (fun σ => σ (b i)) := by
            refine Finset.sum_congr rfl fun i _ => ?_; rw [hΨcol i]
      _ = Ψ (∑ i, e i • fun σ => σ (b i)) := by rw [map_sum]; simp_rw [map_smul]
      _ = Ψ (Pi.single 1 1) := by rw [he]
      _ = v := hv
  rw [← hveq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (avg_mem_invariants (b i) v))

/-- **Surjectivity of the descent map** `L ⊗[K] V^G → V`. -/
theorem descentMap_surjective [IsSemilinear K L V] :
    Function.Surjective (descentMap K L V) := by
  rw [← LinearMap.range_eq_top]
  refine top_le_iff.mp ?_
  rw [← span_invariants_eq_top K L V]
  refine Submodule.span_le.mpr ?_
  intro x hx
  exact ⟨1 ⊗ₜ[K] (⟨x, hx⟩ : invariants K L V), by simp⟩

/-- **Injectivity of the descent map** `L ⊗[K] V^G → V`.  Writing an element via the
basis `b` of `L` as `∑ i, b i ⊗ t i` (`tensorFromPi_surjective`), the image
`∑ i, b i • t i = 0` and the invariance of the `t i` feed the Galois-matrix
annihilation criterion `galoisMatrix_eq_zero_of`, forcing every `t i = 0`. -/
theorem descentMap_injective [IsSemilinear K L V] :
    Function.Injective (descentMap K L V) := by
  classical
  set b := finBasis K L with hb
  -- The composite `t ↦ descentMap (∑ i, b i ⊗ t i) = ∑ i, b i • t i` is injective.
  have hcompose : ∀ t : Fin (finrank K L) → invariants K L V,
      descentMap K L V (tensorFromPi b t) = ∑ i, b i • ((t i : V)) := by
    intro t
    rw [tensorFromPi_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => descentMap_tmul K L V (b i) (t i)
  have hcomp_inj : Function.Injective
      (fun t : Fin (finrank K L) → invariants K L V => descentMap K L V (tensorFromPi b t)) := by
    intro t s hts
    replace hts : ∑ i, b i • ((t i : V)) = ∑ i, b i • ((s i : V)) := by
      rw [← hcompose, ← hcompose]; exact hts
    funext j
    have hu : ∀ σ : L ≃ₐ[K] L, ∑ i, σ (b i) • ((t i : V) - (s i : V)) = 0 := by
      intro σ
      have hdiff : ∑ i, b i • ((t i : V) - (s i : V)) = 0 := by
        simp_rw [smul_sub, Finset.sum_sub_distrib, hts, sub_self]
      have key : σ • (∑ i, b i • ((t i : V) - (s i : V)))
          = ∑ i, σ (b i) • ((t i : V) - (s i : V)) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul_apply]
        congr 1
        rw [smul_sub, (t i).property σ, (s i).property σ]
      rw [← key, hdiff, smul_zero]
    have hzero := galoisMatrix_eq_zero_of b (fun i => (t i : V) - (s i : V)) hu j
    exact Subtype.ext (sub_eq_zero.mp hzero)
  intro x y hxy
  obtain ⟨t, rfl⟩ := tensorFromPi_surjective b x
  obtain ⟨s, rfl⟩ := tensorFromPi_surjective b y
  exact congrArg (tensorFromPi b) (hcomp_inj hxy)

/-- **Speiser's theorem, bijectivity.** The descent map `L ⊗[K] V^G → V` is
bijective. -/
theorem descentMap_bijective [IsSemilinear K L V] :
    Function.Bijective (descentMap K L V) :=
  ⟨descentMap_injective K L V, descentMap_surjective K L V⟩

/-- **Speiser's theorem.** For a finite Galois extension `L/K` and an `L`-vector
space `V` with a semilinear `Gal(L/K)`-action, the descent map is an `L`-linear
isomorphism `L ⊗[K] V^G ≃ₗ[L] V`.  Thus `V^G` is a `K`-form of `V`. -/
noncomputable def descentEquiv [IsSemilinear K L V] :
    L ⊗[K] (invariants K L V) ≃ₗ[L] V :=
  LinearEquiv.ofBijective (descentMap K L V) (descentMap_bijective K L V)

@[simp] lemma descentEquiv_tmul [IsSemilinear K L V] (a : L) (w : invariants K L V) :
    descentEquiv K L V (a ⊗ₜ[K] w) = a • (w : V) :=
  descentMap_tmul K L V a w

/-- **Corollary (Galois descent of dimension).** `dim_K V^G = dim_L V`: the
invariants `V^G` form a `K`-form of the semilinear representation `V`. -/
theorem finrank_invariants [IsSemilinear K L V] :
    Module.finrank K (invariants K L V) = Module.finrank L V := by
  have h := (descentEquiv K L V).finrank_eq
  rwa [Module.finrank_baseChange] at h

end SemilinearAction

/-! ## The regular representation

The natural `Gal(L/K)`-action on `L` itself is semilinear, and its invariants are
`K` (Artin), so `descentEquiv` specialises to the base-change isomorphism
`L ⊗[K] L^{Gal} ≃ L`.  This confirms the framework on the universal example. -/

/-- The natural `Gal(L/K)`-action on `L` (apply the automorphism) is semilinear for
the `L`-module structure of `L` on itself. -/
instance : IsSemilinear K L L where
  smul_smul' σ a b := by simp [smul_eq_mul, AlgEquiv.smul_def]

end AlgebraicJacobian.GaloisDescent
