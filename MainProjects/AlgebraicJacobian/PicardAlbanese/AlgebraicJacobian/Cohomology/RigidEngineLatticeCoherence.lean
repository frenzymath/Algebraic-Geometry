/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RigidEngineLatticeModelHom
import AlgebraicJacobian.Cohomology.RigidEngineLatticeSixTerm

/-!
# RE-1b — the coherence theorems COH-1 and COH-0

The two coherence keystones of the rigid two-term pushforward engine
(`informal/w4-rigid-engine-worksheet.md` §1.2, §2.2), for a two-lattice pair `P` whose
chart lattices are finite over the coordinate actions
(`Module.Finite R[X] (Module.AEval' P.t₀)`, the spelling pinned in
`…RigidEngineLatticeModelHom`):

* **COH-1** (`TwoLatticePair.moduleFinite_h1`) — over **any** commutative ring `R`
  (no Noetherian hypothesis!), `H¹(P)` is a finite `R`-module: `H¹` is right exact in
  the pair, so the finite model surjection carries the finite monomial window
  `H¹(⊕ᵢ 𝒪(mᵢ))` onto `H¹(P)`. Direct — no snake.
* **COH-0** (`TwoLatticePair.moduleFinite_h0`) — over Noetherian `R`, `H⁰(P)` is a
  finite `R`-module. Route: the kernel pair `K` of the model surjection `E ↠ P`
  (componentwise kernels with restricted actions; its localization axioms hold by
  clearing denominators in `E` and pushing by a power of the coordinate through the
  defect annihilation of the quotient side) is again a pair with finite lattices — a
  submodule of the finite free `R[X]`-lattice of `E`, Noetherian by Hilbert's basis
  theorem. The six-term sequence of `0 → K → E → P → 0`
  (`…RigidEngineLatticeSixTerm`) then exhibits `H⁰(P)` as an extension of a submodule
  of the COH-1-finite `H¹(K)` (finite by Noetherianity of `R`) by a quotient of the
  finite `H⁰(E)`.

Noetherianity is consumed **only** by COH-0, exactly as flagged by the worksheet
(discipline rule 4); COH-1, and hence the vanishing/openness exports downstream, hold
relative to an arbitrary test ring.

## Main declarations

* `TwoLatticePair.Hom.kernelPair` — the kernel pair of a map of pairs;
  `Hom.kernelPairIncl` — its inclusion; `Hom.isShortExact_kernelPairIncl` — the short
  exact sequence `0 → K → P → P' → 0` for a componentwise surjective map.
* `TwoLatticePair.Hom.moduleFinite_aeval_kernelPair_t₀`/`…_t₁` — kernel lattices of a
  map out of a finite pair are finite over `R[X]` (Noetherian `R`).
* `TwoLatticePair.moduleFinite_h1` — **COH-1**.
* `TwoLatticePair.moduleFinite_h0` — **COH-0**.
-/

set_option autoImplicit false

universe u

open Polynomial

namespace TwoLatticePair

variable {R : Type u} [CommRing R]
variable {M₀ M₁ N M₀' M₁' N' : Type*}
variable [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup N]
variable [Module R M₀] [Module R M₁] [Module R N]
variable [AddCommGroup M₀'] [AddCommGroup M₁'] [AddCommGroup N']
variable [Module R M₀'] [Module R M₁'] [Module R N']
variable {P : TwoLatticePair R M₀ M₁ N} {P' : TwoLatticePair R M₀' M₁' N'}

namespace Hom

/-- (Implementation) Powers of a restricted endomorphism restrict the powers. -/
private lemma pow_restrict_coe {M : Type*} [AddCommGroup M] [Module R M]
    (e : Module.End R M) {q : Submodule R M} (hq : ∀ x ∈ q, e x ∈ q) (k : ℕ) (z : ↥q) :
    (((e.restrict hq) ^ k) z : M) = (e ^ k) (z : M) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ']
    simp only [Module.End.mul_apply]
    rw [LinearMap.coe_restrict_apply, ih]

/-! ### The kernel pair of a map of pairs -/

/-- **The kernel pair** of a map of two-lattice pairs: the componentwise kernels with
the restricted coordinate and localization actions. The denominator-clearing axioms
hold by clearing denominators in the source and pushing by a power of the coordinate
through the defect annihilation of the target (worksheet §2.2, the COH-0 kernel
construction). -/
noncomputable def kernelPair (f : P.Hom P') :
    TwoLatticePair R ↥(LinearMap.ker f.hom₀) ↥(LinearMap.ker f.hom₁)
      ↥(LinearMap.ker f.homN) where
  t₀ := P.t₀.restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [f.comm_t₀, hx, map_zero]
  t₁ := P.t₁.restrict fun y hy => by
    rw [LinearMap.mem_ker] at hy ⊢
    rw [f.comm_t₁, hy, map_zero]
  tN :=
    { val := P.tN.val.restrict fun n hn => by
        rw [LinearMap.mem_ker] at hn ⊢
        rw [f.comm_tN, hn, map_zero]
      inv := P.tN.inv.restrict fun n hn => by
        rw [LinearMap.mem_ker] at hn ⊢
        rw [f.comm_tN_inv, hn, map_zero]
      val_inv := LinearMap.ext fun z => Subtype.ext (P.tN_val_inv_apply (z : N))
      inv_val := LinearMap.ext fun z => Subtype.ext (P.tN_inv_val_apply (z : N)) }
  ι₀ := P.ι₀.restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [f.comm_ι₀, hx, map_zero]
  ι₁ := P.ι₁.restrict fun y hy => by
    rw [LinearMap.mem_ker] at hy ⊢
    rw [f.comm_ι₁, hy, map_zero]
  ι₀_comm := fun x => Subtype.ext (P.ι₀_comm (x : M₀))
  ι₁_comm := fun y => Subtype.ext (P.ι₁_comm (y : M₁))
  denom₀ := fun n => by
    obtain ⟨k, x, hx⟩ := P.denom₀ (n : N)
    have hx0 : P'.ι₀ (f.hom₀ x) = 0 := by
      rw [← f.comm_ι₀, ← hx, f.comm_tN_pow, LinearMap.mem_ker.mp n.prop, map_zero]
    obtain ⟨j, hj⟩ := P'.ann₀ (f.hom₀ x) hx0
    refine ⟨j + k, ⟨(P.t₀ ^ j) x, LinearMap.mem_ker.mpr (by rw [f.comm_t₀_pow, hj])⟩, ?_⟩
    apply Subtype.ext
    rw [pow_restrict_coe, LinearMap.coe_restrict_apply]
    rw [pow_add, Module.End.mul_apply, hx, ← P.ι₀_pow_comm]
  denom₁ := fun n => by
    obtain ⟨k, y, hy⟩ := P.denom₁ (n : N)
    have hy0 : P'.ι₁ (f.hom₁ y) = 0 := by
      rw [← f.comm_ι₁, ← hy, f.comm_tN_inv_pow, LinearMap.mem_ker.mp n.prop, map_zero]
    obtain ⟨j, hj⟩ := P'.ann₁ (f.hom₁ y) hy0
    refine ⟨j + k, ⟨(P.t₁ ^ j) y, LinearMap.mem_ker.mpr (by rw [f.comm_t₁_pow, hj])⟩, ?_⟩
    apply Subtype.ext
    rw [pow_restrict_coe, LinearMap.coe_restrict_apply]
    rw [pow_add, Module.End.mul_apply, hy, ← P.ι₁_pow_comm]
  ann₀ := fun x hx => by
    have hx' : P.ι₀ (x : M₀) = 0 := by
      have := congrArg (Subtype.val) hx
      rwa [LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] at this
    obtain ⟨j, hj⟩ := P.ann₀ (x : M₀) hx'
    exact ⟨j, Subtype.ext (by rw [pow_restrict_coe, hj, ZeroMemClass.coe_zero])⟩
  ann₁ := fun y hy => by
    have hy' : P.ι₁ (y : M₁) = 0 := by
      have := congrArg (Subtype.val) hy
      rwa [LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] at this
    obtain ⟨j, hj⟩ := P.ann₁ (y : M₁) hy'
    exact ⟨j, Subtype.ext (by rw [pow_restrict_coe, hj, ZeroMemClass.coe_zero])⟩

/-- The inclusion of the kernel pair. -/
noncomputable def kernelPairIncl (f : P.Hom P') : (kernelPair f).Hom P where
  hom₀ := (LinearMap.ker f.hom₀).subtype
  hom₁ := (LinearMap.ker f.hom₁).subtype
  homN := (LinearMap.ker f.homN).subtype
  comm_t₀ := fun _ => rfl
  comm_t₁ := fun _ => rfl
  comm_tN := fun _ => rfl
  comm_ι₀ := fun _ => rfl
  comm_ι₁ := fun _ => rfl

/-- A componentwise surjective map of pairs sits in the short exact sequence
`0 → kernelPair f → P → P' → 0`. -/
theorem isShortExact_kernelPairIncl (f : P.Hom P') (h₀ : Function.Surjective f.hom₀)
    (h₁ : Function.Surjective f.hom₁) (hN : Function.Surjective f.homN) :
    IsShortExact (kernelPairIncl f) f where
  injective₀ := Submodule.injective_subtype _
  injective₁ := Submodule.injective_subtype _
  injectiveN := Submodule.injective_subtype _
  surjective₀ := h₀
  surjective₁ := h₁
  surjectiveN := hN
  exact₀ := Submodule.range_subtype _
  exact₁ := Submodule.range_subtype _
  exactN := Submodule.range_subtype _

/-! ### Kernel lattices are finite over Noetherian rings -/

/-- Over a Noetherian ring, the chart-0 kernel lattice of a map out of a finite pair is
again finite over `R[X]`: it is a submodule of a finite module over the Noetherian ring
`R[X]` (Hilbert's basis theorem). -/
theorem moduleFinite_aeval_kernelPair_t₀ [IsNoetherianRing R]
    [Module.Finite R[X] (Module.AEval' P.t₀)] (f : P.Hom P') :
    Module.Finite R[X] (Module.AEval' (kernelPair f).t₀) := by
  let g : Module.AEval' (kernelPair f).t₀ →ₗ[R[X]] Module.AEval' P.t₀ :=
    LinearMap.ofAEval (kernelPair f).t₀
      ((Module.AEval'.of P.t₀).toLinearMap ∘ₗ (LinearMap.ker f.hom₀).subtype)
      fun z => (Module.AEval'.X_smul_of P.t₀ (z : M₀)).symm
  have hg : Function.Injective g := fun z w h =>
    (Module.AEval'.of (kernelPair f).t₀).symm.injective
      (Subtype.ext ((Module.AEval'.of P.t₀).injective h))
  haveI : IsNoetherian R[X] (Module.AEval' P.t₀) :=
    isNoetherian_of_isNoetherianRing_of_finite R[X] _
  haveI : IsNoetherian R[X] (Module.AEval' (kernelPair f).t₀) :=
    isNoetherian_of_injective g hg
  infer_instance

/-- Over a Noetherian ring, the chart-1 kernel lattice of a map out of a finite pair is
again finite over `R[X]`. -/
theorem moduleFinite_aeval_kernelPair_t₁ [IsNoetherianRing R]
    [Module.Finite R[X] (Module.AEval' P.t₁)] (f : P.Hom P') :
    Module.Finite R[X] (Module.AEval' (kernelPair f).t₁) := by
  let g : Module.AEval' (kernelPair f).t₁ →ₗ[R[X]] Module.AEval' P.t₁ :=
    LinearMap.ofAEval (kernelPair f).t₁
      ((Module.AEval'.of P.t₁).toLinearMap ∘ₗ (LinearMap.ker f.hom₁).subtype)
      fun z => (Module.AEval'.X_smul_of P.t₁ (z : M₁)).symm
  have hg : Function.Injective g := fun z w h =>
    (Module.AEval'.of (kernelPair f).t₁).symm.injective
      (Subtype.ext ((Module.AEval'.of P.t₁).injective h))
  haveI : IsNoetherian R[X] (Module.AEval' P.t₁) :=
    isNoetherian_of_isNoetherianRing_of_finite R[X] _
  haveI : IsNoetherian R[X] (Module.AEval' (kernelPair f).t₁) :=
    isNoetherian_of_injective g hg
  infer_instance

end Hom

/-! ### The coherence theorems -/

variable (P) in
/-- **COH-1, coherence in degree one** (worksheet §1.2, §2.2): for a two-lattice pair
with finite chart lattices over **any** commutative ring `R` — no Noetherian
hypothesis — `H¹(P)` is a finite `R`-module. The finite model surjection is surjective
on overlap modules, so `H¹(P)` is a quotient of the finite monomial window
`H¹(⊕ᵢ 𝒪(mᵢ))`. -/
theorem moduleFinite_h1
    [Module.Finite R[X] (Module.AEval' P.t₀)] [Module.Finite R[X] (Module.AEval' P.t₁)] :
    Module.Finite R P.H1 := by
  obtain ⟨ι, _, m, f, -, -, hN⟩ := P.exists_hom_model_surjective
  haveI := moduleFinite_h1_model R ι m
  exact Module.Finite.of_surjective f.h1Map (f.h1Map_surjective hN)

variable (P) in
/-- **COH-0, coherence in degree zero** (worksheet §1.2, §2.2): for a two-lattice pair
with finite chart lattices over a **Noetherian** ring `R`, `H⁰(P)` is a finite
`R`-module. Via the six-term sequence of the kernel pair of the model surjection:
`H⁰(P)` is an extension of a submodule of the COH-1-finite `H¹(K)` by a quotient of the
finite window `H⁰(E)`. -/
theorem moduleFinite_h0 [IsNoetherianRing R]
    [Module.Finite R[X] (Module.AEval' P.t₀)] [Module.Finite R[X] (Module.AEval' P.t₁)] :
    Module.Finite R ↥P.H0 := by
  obtain ⟨ι, _, m, f, h₀, h₁, hN⟩ := P.exists_hom_model_surjective
  have hse := Hom.isShortExact_kernelPairIncl f h₀ h₁ hN
  -- `H¹` of the kernel pair is finite (COH-1 for `K`), hence Noetherian over `R`.
  haveI := Hom.moduleFinite_aeval_kernelPair_t₀ f
  haveI := Hom.moduleFinite_aeval_kernelPair_t₁ f
  haveI : Module.Finite R (Hom.kernelPair f).H1 := moduleFinite_h1 (Hom.kernelPair f)
  -- `H⁰` of the model is finite: the degree window.
  haveI := moduleFinite_h0_model R ι m
  -- The extension bookkeeping along the connecting map.
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker hse.delta ?_ ?_
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq, ← hse.range_h0Map_eq_ker_delta, LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top

end TwoLatticePair
