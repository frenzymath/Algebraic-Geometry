/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Base change of kernels and regular elements from flat cokernels (the `lm:ctn`-lite home)

Pure module algebra (no schemes), the shared Tor-lemma home of the DAT-D/DAT-A lanes
(`informal/spec-dd-1.md` §2; Kleiman `lm:ctn`, tex 1747–1815, made cheap by carrying
flatness as data). Everything here is applications of mathlib's purity gift
`LinearMap.lTensor_injective_of_exact_of_flat` (a short exact sequence with flat last
term stays left-exact under any `⊗`).

For a linear map `δ : M →ₗ[R] N` whose two cokernels are flat — `M ⧸ ker δ` (≅ the
image) and `N ⧸ range δ` — the kernel of `δ` commutes with arbitrary base change:

* `LinearMap.ker_lTensor_eq_of_flat_coker`: `ker (δ ⊗ A) = range ((ker δ).subtype ⊗ A)`
  for every module `A` (with the `Function.Exact` form
  `LinearMap.exact_lTensor_of_flat_coker`);
* `LinearMap.tensorKer_bijective_of_flat_coker` /
  `LinearMap.tensorKerEquivOfFlatCoker`: the canonical comparison map
  `LinearMap.tensorKer` — the SAME map as mathlib's flat-base-change case
  `LinearMap.tensorKerEquiv`, so downstream sees one seam with two sufficient
  conditions — is an isomorphism `R' ⊗[R] ker δ ≃ₗ[R'] ker (𝟙 ⊗ δ)`. The DD-1
  certificate consumes this on the glued colength module `W(d) = ker (δ⁻ − δ⁺)`, whose
  certificate clauses (c3)/(c4) are exactly the two flatness hypotheses.
* `Algebra.TensorProduct.includeRight_mem_nonZeroDivisors_of_flat_coker`: a regular
  element `f ∈ B⁰` of an `R`-algebra with `B ⧸ (f)` flat over `R` stays regular in
  `R' ⊗[R] B` for every `R`-algebra `R'` — the DD-1a `hreg` discharge and the shape
  shared with DAT-A2's germ-regularity bridge (one home, no duplication; DAT-A2's
  fibrewise⟹relative direction is also welcome in this file).
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace LinearMap

section KerBaseChange

variable {R : Type u} [CommRing R]
variable {M N : Type u} [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]
variable (δ : M →ₗ[R] N)

/-- **Purity of the kernel from a flat image**: if `M ⧸ ker δ` is `R`-flat, then the
inclusion of `ker δ` stays injective after tensoring with any module. -/
theorem lTensor_ker_subtype_injective_of_flat_coker
    [Module.Flat R (M ⧸ LinearMap.ker δ)]
    (A : Type u) [AddCommGroup A] [Module R A] :
    Function.Injective ((LinearMap.ker δ).subtype.lTensor A) :=
  lTensor_injective_of_exact_of_flat (LinearMap.ker δ).mkQ
    (Submodule.mkQ_surjective _) (LinearMap.ker δ).subtype
    (Submodule.injective_subtype _) (exact_subtype_mkQ _) A

/-- The map `M ⧸ ker δ → N` induced by `δ`. -/
private noncomputable def barMap : M ⧸ LinearMap.ker δ →ₗ[R] N :=
  (LinearMap.ker δ).liftQ δ le_rfl

private lemma barMap_injective : Function.Injective (barMap δ) := by
  rw [← LinearMap.ker_eq_bot, barMap, Submodule.ker_liftQ]
  simp

private lemma barMap_comp_mkQ : (barMap δ).comp (LinearMap.ker δ).mkQ = δ :=
  Submodule.liftQ_mkQ _ _ _

/-- **Purity of the image from a flat cokernel**: if `N ⧸ range δ` is `R`-flat, then
the induced injection `M ⧸ ker δ → N` stays injective after tensoring with any
module. -/
private theorem lTensor_barMap_injective_of_flat_coker
    [Module.Flat R (N ⧸ LinearMap.range δ)]
    (A : Type u) [AddCommGroup A] [Module R A] :
    Function.Injective ((barMap δ).lTensor A) := by
  refine lTensor_injective_of_exact_of_flat (LinearMap.range δ).mkQ
    (Submodule.mkQ_surjective _) (barMap δ) (barMap_injective δ) ?_ A
  rw [LinearMap.exact_iff, Submodule.ker_mkQ, barMap, Submodule.range_liftQ]

/-- **Kernel base change from flat cokernels** (the `lm:ctn`-lite keystone, plain
`lTensor` form): if both `M ⧸ ker δ` and `N ⧸ range δ` are `R`-flat, then for any
module `A`, `ker (δ ⊗ A) = range ((ker δ).subtype ⊗ A)`. -/
theorem ker_lTensor_eq_of_flat_coker
    [Module.Flat R (M ⧸ LinearMap.ker δ)] [Module.Flat R (N ⧸ LinearMap.range δ)]
    (A : Type u) [AddCommGroup A] [Module R A] :
    LinearMap.ker (δ.lTensor A)
      = LinearMap.range ((LinearMap.ker δ).subtype.lTensor A) := by
  have hcomp : δ.lTensor A
      = ((barMap δ).lTensor A).comp ((LinearMap.ker δ).mkQ.lTensor A) := by
    rw [← LinearMap.lTensor_comp, barMap_comp_mkQ]
  have hex : Function.Exact ((LinearMap.ker δ).subtype.lTensor A)
      ((LinearMap.ker δ).mkQ.lTensor A) :=
    lTensor_exact A (exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
  rw [hcomp, LinearMap.ker_comp,
    LinearMap.ker_eq_bot.mpr (lTensor_barMap_injective_of_flat_coker δ A),
    Submodule.comap_bot, LinearMap.exact_iff.mp hex]

variable {δ} in
/-- `ker_lTensor_eq_of_flat_coker` in `Function.Exact` form. -/
theorem exact_lTensor_of_flat_coker
    [Module.Flat R (M ⧸ LinearMap.ker δ)] [Module.Flat R (N ⧸ LinearMap.range δ)]
    (A : Type u) [AddCommGroup A] [Module R A] :
    Function.Exact ((LinearMap.ker δ).subtype.lTensor A) (δ.lTensor A) := by
  rw [LinearMap.exact_iff]
  exact ker_lTensor_eq_of_flat_coker δ A

variable (R' : Type u) [CommRing R'] [Algebra R R']

/-- **Kernel base change from flat cokernels, comparison form**: the canonical map
`LinearMap.tensorKer : R' ⊗[R] ker δ →ₗ[R'] ker (𝟙 ⊗ δ)` — the same comparison map as
mathlib's flat-base-change `LinearMap.tensorKerEquiv` — is bijective as soon as the two
cokernels of `δ` are flat (no hypothesis on `R'` at all). -/
theorem tensorKer_bijective_of_flat_coker
    [Module.Flat R (M ⧸ LinearMap.ker δ)] [Module.Flat R (N ⧸ LinearMap.range δ)] :
    Function.Bijective (LinearMap.tensorKer R' R' δ) := by
  constructor
  · intro x y hxy
    have hcoe := congrArg Subtype.val hxy
    rw [LinearMap.tensorKer_coe, LinearMap.tensorKer_coe] at hcoe
    exact lTensor_ker_subtype_injective_of_flat_coker δ R' hcoe
  · rintro ⟨z, hz⟩
    have hz' : z ∈ LinearMap.range ((LinearMap.ker δ).subtype.lTensor R') := by
      rw [← ker_lTensor_eq_of_flat_coker δ R']
      exact hz
    obtain ⟨w, hw⟩ := hz'
    exact ⟨w, Subtype.ext (by rw [LinearMap.tensorKer_coe, hw])⟩

/-- `tensorKer_bijective_of_flat_coker`, packaged as a linear equivalence
`R' ⊗[R] ker δ ≃ₗ[R'] ker (𝟙 ⊗ δ)`. -/
noncomputable def tensorKerEquivOfFlatCoker
    [Module.Flat R (M ⧸ LinearMap.ker δ)] [Module.Flat R (N ⧸ LinearMap.range δ)] :
    R' ⊗[R] (LinearMap.ker δ) ≃ₗ[R']
      LinearMap.ker (AlgebraTensorModule.lTensor R' R' δ) :=
  LinearEquiv.ofBijective (LinearMap.tensorKer R' R' δ)
    (tensorKer_bijective_of_flat_coker δ R')

@[simp]
theorem tensorKerEquivOfFlatCoker_apply
    [Module.Flat R (M ⧸ LinearMap.ker δ)] [Module.Flat R (N ⧸ LinearMap.range δ)]
    (x : R' ⊗[R] (LinearMap.ker δ)) :
    tensorKerEquivOfFlatCoker δ R' x = LinearMap.tensorKer R' R' δ x :=
  rfl

end KerBaseChange

end LinearMap

namespace Algebra.TensorProduct

section RegularBaseChange

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
variable {B : Type u} [CommRing B] [Algebra R B]

/-- Multiplication by `f` on `R' ⊗[R] B` is the `lTensor` of multiplication by `f`
on `B`. -/
private lemma mul_includeRight_eq_lTensor_mulLeft (f : B) (x : R' ⊗[R] B) :
    (includeRight (R := R) (A := R') (B := B)) f * x
      = (LinearMap.mulLeft R f).lTensor R' x := by
  induction x with
  | zero => rw [mul_zero, map_zero]
  | tmul r b =>
      rw [includeRight_apply, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [mul_add, map_add, hx, hy]

/-- **Regular elements stay regular after any base change, from a flat cokernel**
(the DD-1a `hreg` discharge; Kleiman `lm:ctn` (i)⟹(iii) made cheap): if `f` is a
nonzerodivisor of the `R`-algebra `B` and the colength module `B ⧸ (f)` is flat over
`R`, then the image of `f` in `R' ⊗[R] B` is a nonzerodivisor, for EVERY `R`-algebra
`R'` — no flatness of `R'` and no Noetherian hypothesis. -/
theorem includeRight_mem_nonZeroDivisors_of_flat_coker (f : B)
    (hf : f ∈ nonZeroDivisors B)
    [Module.Flat R (B ⧸ Ideal.span {f})] :
    (includeRight (R := R) (A := R') (B := B)) f ∈ nonZeroDivisors (R' ⊗[R] B) := by
  have hinj : Function.Injective ((LinearMap.mulLeft R f).lTensor R') := by
    refine LinearMap.lTensor_injective_of_exact_of_flat
      (Ideal.Quotient.mkₐ R (Ideal.span {f})).toLinearMap
      Ideal.Quotient.mk_surjective (LinearMap.mulLeft R f) ?_ ?_ R'
    · intro x y hxy
      simp only [LinearMap.mulLeft_apply] at hxy
      have hsub : f * (x - y) = 0 := by rw [mul_sub, hxy, sub_self]
      exact sub_eq_zero.mp ((mul_left_mem_nonZeroDivisors_eq_zero_iff hf).mp hsub)
    · intro y
      constructor
      · intro hy
        have hmem : y ∈ Ideal.span {f} := by
          rwa [← Ideal.Quotient.eq_zero_iff_mem]
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
        exact ⟨c, by rw [LinearMap.mulLeft_apply, mul_comm, hc]⟩
      · rintro ⟨c, rfl⟩
        have hmem : f * c ∈ Ideal.span {f} :=
          Ideal.mem_span_singleton'.mpr ⟨c, mul_comm c f⟩
        simp only [AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
          Ideal.Quotient.mkₐ_eq_mk]
        exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have h0 : (LinearMap.mulLeft R f).lTensor R' x = 0 := by
    rw [← mul_includeRight_eq_lTensor_mulLeft R', mul_comm]
    exact hx
  have hz : (LinearMap.mulLeft R f).lTensor R' x
      = (LinearMap.mulLeft R f).lTensor R' 0 := by rw [h0, map_zero]
  exact hinj hz

end RegularBaseChange

end Algebra.TensorProduct
