/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Fibrewise regularity — the `lm:ctn`-lite slicing lemmas (DAT-A2 core)

**THE SHARED TOR-LEMMA HOME** for the Wave-4 DATUM campaign (`informal/spec-dat-a.md`
§1; coordination rule of the DAT-A/DD-1 lanes): Kleiman `lm:ctn` (iii)⟹(i)
(`references/kleiman-picard-src/kleiman-picard.tex` 1786–1815) in a Tor-free spelling —

> over a Noetherian base `R`, an `R`-linear endomorphism of a **flat** module that is
> injective on every residue-field fibre is injective;

in particular an element of a flat `R`-algebra whose image in every residue-field fibre
is a nonzerodivisor is a nonzerodivisor (`fibrewise-regular + flat ⟹ regular`).

The paper's Tor/local-flatness-criterion computation is replaced by a **Noetherian
induction on ideals** with the predicate `P I := ∀ x, φ x ∈ I•⊤ → x ∈ I•⊤`:

* `I = ⊤` is trivial; at a **prime** `p` the fibre hypothesis applies directly, through
  the injection `M ⧸ p•⊤ ↪ M ⊗ κ(p)` (flatness of `M` against
  `R⧸p ↪ κ(p)`, `Module.Flat.mem_smul_top_of_tmul_residueField_one_eq_zero`) — no
  inductive hypothesis is consumed;
* at a **non-prime** `I ≠ ⊤`, pick `a·b ∈ I` with `a, b ∉ I`; then `I ⊔ (a)` and the
  colon `(I : a)` are both strictly larger, and the **flat colon lemma**
  (`Module.Flat.mem_colon_smul_top_of_smul_mem_smul_top`: for flat `M`,
  `a•x ∈ I•⊤ ⟹ x ∈ (I : a)•⊤`) splices the two inductive hypotheses together.

Both flat inputs are *injectivity of a composite* through
`TensorProduct.tensorQuotEquivQuotSMul` — no `Function.Exact`, no Tor, no local
criterion of flatness. Mathlib does not have the slicing criterion in any form
(searched 2026-07-17; only the converse directions exist:
`IsSMulRegular.of_isLocalization`, `IsWeaklyRegular.of_flat`).

`[IsNoetherianRing R]` is route-consistent: the DAT-1 engine keystone
(`datumRigidEngine`) already assumes it, and (V-rel-B) runs over the RE-5 Noetherian
descent stage.

## Seam (DD-1a) — do not duplicate elsewhere

The *other* half of `lm:ctn` used by the DAT-D lane — (i)⟹ base-change stability of a
regular element with **flat quotient** (`0 → B → B → B/(f) → 0` with `B/(f)` flat stays
exact after `⊗_R R'`; tex 1747–1770, dat-d-worksheet §1.2 DD-1a) — belongs in THIS file
when the DD-1 lane lands it.

## Main declarations

* `Module.Flat.mem_colon_smul_top_of_smul_mem_smul_top` — the flat colon lemma;
* `Module.Flat.mem_smul_top_of_tmul_residueField_one_eq_zero` — the prime-fibre kernel
  computation `ker (M → M ⊗ κ(p)) = p•⊤` (the ⊇ half is
  `tmul_residueField_one_eq_zero_of_mem_smul_top`, no flatness);
* `Module.Flat.injective_of_forall_rTensor_residueField_injective` — **the core**;
* `Module.Flat.mem_nonZeroDivisors_of_forall_tmul_residueField` — the ring form
  (fibrewise-regular + flat ⟹ regular), consumed by DAT-A2's geometry layer and DD-R.
-/

set_option autoImplicit false

universe u v

open scoped TensorProduct Pointwise

section ColonLemma

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The multiplication-by-`a` map `R ⧸ (I : a) →ₗ[R] R ⧸ I`. It is injective by the
definition of the colon ideal (`mapQSMul_injective`). -/
private noncomputable def mapQSMul (I : Ideal R) (a : R) :
    (R ⧸ Submodule.colon I {a}) →ₗ[R] (R ⧸ I) :=
  Submodule.mapQ (Submodule.colon I {a}) I (LinearMap.lsmul R R a)
    (fun r hr => by
      have : r • a ∈ I := Submodule.mem_colon_singleton.mp hr
      simpa [LinearMap.lsmul_apply, smul_eq_mul, mul_comm] using this)

private lemma mapQSMul_mk (I : Ideal R) (a : R) (r : R) :
    mapQSMul I a (Submodule.Quotient.mk r) = Submodule.Quotient.mk (a * r) := by
  rw [mapQSMul, Submodule.mapQ_apply, LinearMap.lsmul_apply, smul_eq_mul]

private lemma mapQSMul_injective (I : Ideal R) (a : R) :
    Function.Injective (mapQSMul I a) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, mapQSMul_mk, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_colon_singleton,
    smul_eq_mul, mul_comm]
  exact hx

/-- **The flat colon lemma**: over a flat module, dividing a smul-membership
`a • x ∈ I • ⊤` by `a` lands in the colon ideal: `x ∈ (I : a) • ⊤`. Injectivity of
`R ⧸ (I : a) → R ⧸ I` is preserved by `− ⊗ M`, and under
`TensorProduct.tensorQuotEquivQuotSMul` the tensored map reads
`x mod (I : a)•⊤ ↦ a•x mod I•⊤`. -/
theorem Module.Flat.mem_colon_smul_top_of_smul_mem_smul_top [Module.Flat R M]
    (I : Ideal R) (a : R) {x : M} (h : a • x ∈ I • (⊤ : Submodule R M)) :
    x ∈ Submodule.colon I {a} • (⊤ : Submodule R M) := by
  set J : Ideal R := Submodule.colon I {a} with hJ
  -- chase `mk x` through `M ⧸ J•⊤ ≃ M ⊗ (R⧸J) → M ⊗ (R⧸I) ≃ M ⧸ I•⊤`
  have h1 : (TensorProduct.tensorQuotEquivQuotSMul M J).symm
      (Submodule.Quotient.mk x) = x ⊗ₜ[R] (1 : R ⧸ J) :=
    TensorProduct.tensorQuotEquivQuotSMul_symm_mk J x
  have h2 : (LinearMap.lTensor M (mapQSMul I a)) (x ⊗ₜ[R] (1 : R ⧸ J))
      = x ⊗ₜ[R] (Submodule.Quotient.mk a : R ⧸ I) := by
    rw [LinearMap.lTensor_tmul]
    congr 1
    rw [show (1 : R ⧸ J) = Submodule.Quotient.mk (1 : R) from rfl, mapQSMul_mk, mul_one]
  have h3 : (TensorProduct.tensorQuotEquivQuotSMul M I)
      (x ⊗ₜ[R] (Submodule.Quotient.mk a : R ⧸ I)) = Submodule.Quotient.mk (a • x) :=
    TensorProduct.tensorQuotEquivQuotSMul_tmul_mk I x a
  -- the middle image vanishes
  have h4 : (LinearMap.lTensor M (mapQSMul I a)) (x ⊗ₜ[R] (1 : R ⧸ J)) = 0 := by
    rw [h2]
    apply (TensorProduct.tensorQuotEquivQuotSMul M I).injective
    rw [h3, map_zero, Submodule.Quotient.mk_eq_zero]
    exact h
  -- flatness: the middle map is injective, so the left input vanishes
  have h5 : (x ⊗ₜ[R] (1 : R ⧸ J) : M ⊗[R] (R ⧸ J)) = 0 :=
    Module.Flat.lTensor_preserves_injective_linearMap (mapQSMul I a)
      (mapQSMul_injective I a) (by rw [h4, map_zero])
  have hmk : (Submodule.Quotient.mk x : M ⧸ (J • (⊤ : Submodule R M))) = 0 :=
    (TensorProduct.tensorQuotEquivQuotSMul M J).symm.injective
      (by rw [h1, h5, map_zero])
  rwa [Submodule.Quotient.mk_eq_zero] at hmk

end ColonLemma

section ResidueFibre

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Elements of `p • ⊤` die in the residue-field fibre: `x ∈ p•⊤ ⟹ x ⊗ 1 = 0` in
`M ⊗[R] κ(p)`. (No flatness.) -/
theorem tmul_residueField_one_eq_zero_of_mem_smul_top (p : Ideal R) [p.IsPrime] {x : M}
    (hx : x ∈ p • (⊤ : Submodule R M)) :
    (x ⊗ₜ[R] (1 : p.ResidueField) : M ⊗[R] p.ResidueField) = 0 := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun y z hy hz => ?_)
  · rw [TensorProduct.smul_tmul]
    have h1 : r • (1 : p.ResidueField) = algebraMap R p.ResidueField r := by
      rw [Algebra.smul_def, mul_one]
    rw [h1, Ideal.algebraMap_residueField_eq_zero.mpr hr, TensorProduct.tmul_zero]
  · rw [TensorProduct.add_tmul, hy, hz, add_zero]

/-- **The prime-fibre kernel computation** (the flat half): for flat `M` and a prime
`p`, `x ⊗ 1 = 0` in `M ⊗[R] κ(p)` forces `x ∈ p • ⊤`. The map
`M ⧸ p•⊤ ≃ M ⊗ (R⧸p) → M ⊗ κ(p)` is injective because `R⧸p ↪ κ(p)` is and `M` is
flat. -/
theorem Module.Flat.mem_smul_top_of_tmul_residueField_one_eq_zero [Module.Flat R M]
    (p : Ideal R) [p.IsPrime] {x : M}
    (hx : (x ⊗ₜ[R] (1 : p.ResidueField) : M ⊗[R] p.ResidueField) = 0) :
    x ∈ p • (⊤ : Submodule R M) := by
  set f : (R ⧸ p) →ₗ[R] p.ResidueField :=
    (Algebra.linearMap (R ⧸ p) p.ResidueField).restrictScalars R with hf
  have hfinj : Function.Injective f := by
    intro u v huv
    exact Ideal.injective_algebraMap_quotient_residueField p huv
  have h1 : (TensorProduct.tensorQuotEquivQuotSMul M p).symm
      (Submodule.Quotient.mk x) = x ⊗ₜ[R] (1 : R ⧸ p) :=
    TensorProduct.tensorQuotEquivQuotSMul_symm_mk p x
  have h2 : (LinearMap.lTensor M f) (x ⊗ₜ[R] (1 : R ⧸ p))
      = x ⊗ₜ[R] (1 : p.ResidueField) := by
    rw [LinearMap.lTensor_tmul]
    congr 1
    rw [hf]
    simp
  have h5 : (x ⊗ₜ[R] (1 : R ⧸ p) : M ⊗[R] (R ⧸ p)) = 0 :=
    Module.Flat.lTensor_preserves_injective_linearMap f hfinj
      (by rw [h2, hx, map_zero])
  have hmk : (Submodule.Quotient.mk x : M ⧸ (p • (⊤ : Submodule R M))) = 0 :=
    (TensorProduct.tensorQuotEquivQuotSMul M p).symm.injective
      (by rw [h1, h5, map_zero])
  rwa [Submodule.Quotient.mk_eq_zero] at hmk

end ResidueFibre

section Core

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **The `lm:ctn`-lite slicing criterion, endomorphism form** (Kleiman `lm:ctn`
(iii)⟹(i), Tor-free; DAT-A2 core): over a Noetherian ring `R`, an `R`-linear
endomorphism of a flat module that is injective on every residue-field fibre is
injective. Noetherian induction on ideals with `P I := ∀ x, φ x ∈ I•⊤ → x ∈ I•⊤`; the
fibre hypothesis fires at the primes, the flat colon lemma splices the non-primes. -/
theorem Module.Flat.injective_of_forall_rTensor_residueField_injective
    [IsNoetherianRing R] [Module.Flat R M] (φ : M →ₗ[R] M)
    (hfib : ∀ p : PrimeSpectrum R,
      Function.Injective (φ.rTensor p.asIdeal.ResidueField)) :
    Function.Injective φ := by
  have key : ∀ I : Ideal R, ∀ x : M,
      φ x ∈ I • (⊤ : Submodule R M) → x ∈ I • (⊤ : Submodule R M) := by
    intro I₀
    refine IsNoetherian.induction
      (P := fun I : Ideal R => ∀ x : M,
        φ x ∈ I • (⊤ : Submodule R M) → x ∈ I • (⊤ : Submodule R M))
      (fun I IH => ?_) I₀
    intro x hx
    by_cases htop : I = ⊤
    · rw [htop, Submodule.top_smul]
      exact Submodule.mem_top
    by_cases hp : Ideal.IsPrime I
    · -- the prime case: the fibre hypothesis, no inductive hypothesis
      haveI := hp
      have h1 : (φ.rTensor (Ideal.ResidueField I))
          (x ⊗ₜ[R] (1 : Ideal.ResidueField I)) = 0 := by
        rw [LinearMap.rTensor_tmul]
        exact tmul_residueField_one_eq_zero_of_mem_smul_top I hx
      have h2 : (x ⊗ₜ[R] (1 : Ideal.ResidueField I) :
          M ⊗[R] Ideal.ResidueField I) = 0 :=
        hfib ⟨I, hp⟩ (by rw [h1, map_zero] :
          (φ.rTensor (Ideal.ResidueField I)) (x ⊗ₜ[R] (1 : Ideal.ResidueField I)) =
            (φ.rTensor (Ideal.ResidueField I)) 0)
      exact Module.Flat.mem_smul_top_of_tmul_residueField_one_eq_zero I h2
    · -- the non-prime case: splice two strictly larger ideals
      obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b : R, a * b ∈ I ∧ a ∉ I ∧ b ∉ I := by
        by_contra hcon
        refine hp ⟨htop, fun {u v} huv => ?_⟩
        by_cases hu : u ∈ I
        · exact Or.inl hu
        by_cases hv : v ∈ I
        · exact Or.inr hv
        exact absurd ⟨u, v, huv, hu, hv⟩ hcon
      -- `J₁ = I ⊔ (a) > I`
      have hJ₁gt : I < I ⊔ Ideal.span {a} :=
        lt_of_le_of_ne le_sup_left (fun h => ha (by
          rw [h]
          exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)))
      -- `J₂ = (I : a) > I`
      have hJ₂le : I ≤ Submodule.colon I {a} := fun r hr =>
        Submodule.mem_colon_singleton.mpr
          (by rw [smul_eq_mul]; exact Ideal.mul_mem_right a I hr)
      have hJ₂gt : I < Submodule.colon I {a} :=
        lt_of_le_of_ne hJ₂le (fun h => hb (by
          rw [h]
          exact Submodule.mem_colon_singleton.mpr
            (by rw [smul_eq_mul, mul_comm]; exact hab)))
      -- split `x = y + a•z` with `y ∈ I•⊤` through `P (I ⊔ (a))`
      have hx₁ : x ∈ (I ⊔ Ideal.span {a}) • (⊤ : Submodule R M) :=
        IH _ hJ₁gt x (Submodule.smul_mono_left le_sup_left hx)
      rw [Submodule.sup_smul, Submodule.ideal_span_singleton_smul] at hx₁
      obtain ⟨y, hy, z', hz', rfl⟩ := Submodule.mem_sup.mp hx₁
      obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists z' a
        (⊤ : Submodule R M)).mp hz'
      -- `φ y ∈ I•⊤`, hence `a • φ z ∈ I•⊤`
      have hφy : φ y ∈ I • (⊤ : Submodule R M) := by
        have hmap := Submodule.map_smul'' I (⊤ : Submodule R M) φ
        have : φ y ∈ Submodule.map φ (I • (⊤ : Submodule R M)) :=
          Submodule.mem_map_of_mem hy
        rw [hmap] at this
        exact smul_mono_right I
          (le_top : Submodule.map φ (⊤ : Submodule R M) ≤ ⊤) this
      have haz : a • φ z ∈ I • (⊤ : Submodule R M) := by
        have hsum : φ y + a • φ z ∈ I • (⊤ : Submodule R M) := by
          have : φ (y + a • z) = φ y + a • φ z := by rw [map_add, map_smul]
          rwa [this] at hx
        simpa using Submodule.sub_mem _ hsum hφy
      -- the flat colon lemma + `P ((I : a))`
      have hz₂ : z ∈ Submodule.colon I {a} • (⊤ : Submodule R M) :=
        IH _ hJ₂gt z
          (Module.Flat.mem_colon_smul_top_of_smul_mem_smul_top I a haz)
      -- `a • ((I : a)•⊤) ≤ I•⊤`
      have haz₂ : a • z ∈ I • (⊤ : Submodule R M) := by
        have hsub : ∀ w ∈ Submodule.colon I {a} • (⊤ : Submodule R M),
            a • w ∈ I • (⊤ : Submodule R M) := by
          intro w hw
          refine Submodule.smul_induction_on hw (fun r hr m _ => ?_)
            (fun u v hu hv => ?_)
          · have hra : r * a ∈ I := by
              have := Submodule.mem_colon_singleton.mp hr
              rwa [smul_eq_mul] at this
            rw [smul_smul, mul_comm a r]
            exact Submodule.smul_mem_smul hra Submodule.mem_top
          · rw [smul_add]
            exact Submodule.add_mem _ hu hv
        exact hsub z hz₂
      exact Submodule.add_mem _ hy haz₂
  intro u v huv
  have hsub : φ (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hmem : u - v ∈ (⊥ : Ideal R) • (⊤ : Submodule R M) :=
    key ⊥ (u - v) (by rw [hsub, Submodule.bot_smul]; exact Submodule.zero_mem _)
  rw [Submodule.bot_smul, Submodule.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

end Core

section RingForm

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

/-- The right-tensor of multiplication-by-`s` is multiplication by `s ⊗ 1` on the
tensor-product algebra. -/
theorem rTensor_mulLeft_eq_mulLeft_tmul (S : Type u) [CommRing S] [Algebra R S]
    (s : A) :
    (LinearMap.mulLeft R s).rTensor S =
      LinearMap.mulLeft R (s ⊗ₜ[R] (1 : S) : A ⊗[R] S) := by
  refine TensorProduct.ext' (fun a c => ?_)
  rw [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- **The `lm:ctn`-lite slicing criterion, ring form** (fibrewise-regular + flat ⟹
regular; DAT-A2 core, DD-R's bridge): over a Noetherian ring `R`, an element of a flat
`R`-algebra whose image `s ⊗ 1` is a nonzerodivisor in every residue-field fibre
`A ⊗[R] κ(p)` is a nonzerodivisor. -/
theorem Module.Flat.mem_nonZeroDivisors_of_forall_tmul_residueField
    [IsNoetherianRing R] [Module.Flat R A] {s : A}
    (hfib : ∀ p : PrimeSpectrum R,
      (s ⊗ₜ[R] (1 : p.asIdeal.ResidueField) : A ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors (A ⊗[R] p.asIdeal.ResidueField)) :
    s ∈ nonZeroDivisors A := by
  have hinj : Function.Injective (LinearMap.mulLeft R s) := by
    refine Module.Flat.injective_of_forall_rTensor_residueField_injective
      (LinearMap.mulLeft R s) (fun p => ?_)
    rw [rTensor_mulLeft_eq_mulLeft_tmul p.asIdeal.ResidueField s]
    intro u v huv
    have hzero : (u - v) * (s ⊗ₜ[R] (1 : p.asIdeal.ResidueField)) = 0 := by
      rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply] at huv
      rw [sub_mul, mul_comm u, mul_comm v, huv, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp (hfib p)).2 (u - v) hzero)
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro z hz
    have hmul : LinearMap.mulLeft R s z = LinearMap.mulLeft R s 0 := by
      rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, mul_zero]
      exact hz
    exact hinj hmul
  · intro z hz
    have hmul : LinearMap.mulLeft R s z = LinearMap.mulLeft R s 0 := by
      rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, mul_zero, mul_comm]
      exact hz
    exact hinj hmul

end RingForm
