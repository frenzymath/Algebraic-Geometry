/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Chi
import AlgebraicJacobian.Algebra.DedekindColength

/-!
# The six-term cohomology slice of a short exact sequence of sheaves

For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of sheaves of `R`-modules on a small
site, this file packages — **once, and elementwise** — the degree-`≤ 1` slice of the long
exact cohomology sequence

    0 → H⁰X₁ → H⁰X₂ → H⁰X₃ →δ→ H¹X₁ → H¹X₂ → H¹X₃

obtained from mathlib's covariant `Ext`-sequence for the cohomology carrier
`Sheaf.HModule = Ext(constModuleSheaf, ·)`: the connecting map `HModule.delta`, the four
`Function.Exact` facts, injectivity at the left end and surjectivity of `H¹X₁ → H¹X₂`
when `H¹X₃` vanishes.

On top of the slice sit the two consumers of the χ-ledger:

* **finiteness transfer** (`HModule.moduleFinite_middle`, `moduleFinite_left_zero`,
  `moduleFinite_left_succ`): dimension bookkeeping between the terms of the sequence,
  via the division-ring extension lemma `FiniteDimensional.of_exact`;
* **additivity of χ** (`Sheaf.chi_eq_add_of_shortExact`): when `H¹X₃ = 0` and the five
  remaining modules are finite, `χ X₂ = χ X₁ + χ X₃` — the alternating-sum identity
  `AlgebraicGeometry.finrank_alt_sum_eq_zero_of_exact₅` applied to the slice.

The transports from mathlib's `(mk₀ f).postcomp`-spelling to `HModule.map` are definitional
(`Ext`-postcomposition on both sides); each slot of the slice is nevertheless a named
lemma, so downstream files never re-derive the sequence inline.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

section FiniteDimensional

variable {K V₁ V₂ V₃ : Type*} [DivisionRing K]
  [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

/-- **Extension lemma for finite dimensionality.** If `V₁ → V₂ → V₃` is exact at `V₂` and
the outer terms are finite-dimensional, so is the middle: the kernel of `V₂ → V₃` is the
image of the finite `V₁`, and the coimage embeds into the finite `V₃`. (Mathlib's
`Module.Finite.of_exact` asks for surjectivity of the second map; over a division ring the
corestriction to the range removes that hypothesis.) -/
theorem FiniteDimensional.of_exact (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃)
    (h : Function.Exact f g) [FiniteDimensional K V₁] [FiniteDimensional K V₃] :
    FiniteDimensional K V₂ := by
  have hexact : Function.Exact f g.rangeRestrict := fun y => by
    rw [← h y]
    exact ⟨fun hy => congrArg Subtype.val hy, fun hy => Subtype.ext hy⟩
  exact Module.Finite.of_exact hexact g.surjective_rangeRestrict

end FiniteDimensional

namespace CategoryTheory.Sheaf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Type u} [CommRing R] [HasSheafify J (ModuleCat.{u} R)]
  {S : ShortComplex (Sheaf J (ModuleCat.{u} R))}

namespace HModule

/-- **The connecting homomorphism** `δ : Hⁿ⁰(X₃) →ₗ[R] Hⁿ¹(X₁)` (`n₀ + 1 = n₁`) of a short
exact sequence of sheaves of `R`-modules: postcomposition with the extension class of the
sequence. -/
noncomputable def delta (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    HModule S.X₃ n₀ →ₗ[R] HModule S.X₁ n₁ :=
  hS.extClass.postcompOfLinear R (constModuleSheaf J R) h

/-- Exactness of `Hⁿ(X₁) → Hⁿ(X₂) → Hⁿ(X₃)` at `Hⁿ(X₂)`, elementwise
(`Abelian.Ext.covariant_sequence_exact₂'` transported to `HModule.map`). -/
theorem exact_map_f_map_g (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (map S.f n) (map S.g n) := by
  have h := Abelian.Ext.covariant_sequence_exact₂' (constModuleSheaf J R) hS n
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Exactness of `Hⁿ⁰(X₂) → Hⁿ⁰(X₃) →δ→ Hⁿ¹(X₁)` at `Hⁿ⁰(X₃)`, elementwise
(`Abelian.Ext.covariant_sequence_exact₃'` transported to `HModule.map`/`HModule.delta`). -/
theorem exact_map_g_delta (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    Function.Exact (map S.g n₀) (delta hS h) := by
  have h' := Abelian.Ext.covariant_sequence_exact₃' (constModuleSheaf J R) hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at h'
  exact h'

/-- Exactness of `Hⁿ⁰(X₃) →δ→ Hⁿ¹(X₁) → Hⁿ¹(X₂)` at `Hⁿ¹(X₁)`, elementwise
(`Abelian.Ext.covariant_sequence_exact₁'` transported to `HModule.map`/`HModule.delta`). -/
theorem exact_delta_map_f (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) :
    Function.Exact (delta hS h) (map S.f n₁) := by
  have h' := Abelian.Ext.covariant_sequence_exact₁' (constModuleSheaf J R) hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at h'
  exact h'

/-- **Left end of the slice**: `H⁰(X₁) → H⁰(X₂)` is injective when `X₁ ⟶ X₂` is a
monomorphism (mathlib's `Abelian.Ext.postcomp_mk₀_injective_of_mono`). -/
theorem injective_map_f_zero (hS : S.ShortExact) :
    Function.Injective (map S.f 0) :=
  haveI := hS.mono_f
  Abelian.Ext.postcomp_mk₀_injective_of_mono (constModuleSheaf J R) S.f

/-- **Right end of the slice**: `Hⁿ(X₁) → Hⁿ(X₂)` is surjective when `Hⁿ(X₃)` vanishes
(exactness at `Hⁿ(X₂)` plus triviality of the next term). -/
theorem surjective_map_f (hS : S.ShortExact) (n : ℕ) [Subsingleton (HModule S.X₃ n)] :
    Function.Surjective (map S.f n) := fun y =>
  (exact_map_f_map_g hS n y).mp (Subsingleton.elim _ 0)

/-- **Right exactness on degree-zero cohomology**: `H⁰(X₂) → H⁰(X₃)` is
surjective when `H¹(X₁)` vanishes. -/
theorem surjective_map_g_zero (hS : S.ShortExact) [Subsingleton (HModule S.X₁ 1)] :
    Function.Surjective (map S.g 0) := fun y =>
  (exact_map_g_delta hS rfl y).mp (Subsingleton.elim _ 0)

/-- The degree-zero right-exactness statement on sections over a terminal object of the
site. -/
theorem surjective_app_g_zero (hS : S.ShortExact) {T : C} (hT : IsTerminal T)
    [Subsingleton (HModule S.X₁ 1)] :
    Function.Surjective (S.g.hom.app (op T)).hom := by
  intro y
  obtain ⟨x, hx⟩ := surjective_map_g_zero hS
    ((linearEquiv₀ J hT S.X₃).symm y)
  refine ⟨linearEquiv₀ J hT S.X₂ x, ?_⟩
  rw [linearEquiv₀_naturality (hT := hT) (f := S.g), hx,
    LinearEquiv.apply_symm_apply]

/-- If `H¹(F)` vanishes, the cokernel projection of a monomorphism `F ⟶ G` is
surjective on sections over a terminal object. -/
theorem cokernelπ_app_surjective_of_subsingleton_h1
    {F G : Sheaf J (ModuleCat.{u} R)} (ι : F ⟶ G) [Mono ι]
    {T : C} (hT : IsTerminal T) [Subsingleton (HModule F 1)] :
    Function.Surjective ((cokernel.π ι).hom.app (op T)).hom := by
  let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι) }
  exact surjective_app_g_zero hS hT

section FinitenessTransfer

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Type u} [Field R] [HasSheafify J (ModuleCat.{u} R)]
  {S : ShortComplex (Sheaf J (ModuleCat.{u} R))}

/-- **Finiteness of the middle cohomology**: if `Hⁿ(X₁)` and `Hⁿ(X₃)` are finite, so is
`Hⁿ(X₂)` (extension lemma along the exact slice). -/
theorem moduleFinite_middle (hS : S.ShortExact) (n : ℕ)
    [Module.Finite R (HModule S.X₁ n)] [Module.Finite R (HModule S.X₃ n)] :
    Module.Finite R (HModule S.X₂ n) :=
  FiniteDimensional.of_exact (map S.f n) (map S.g n) (exact_map_f_map_g hS n)

/-- **Finiteness of the left cohomology in degree zero**: `H⁰(X₁)` embeds in `H⁰(X₂)`, so
finiteness descends. -/
theorem moduleFinite_left_zero (hS : S.ShortExact) [Module.Finite R (HModule S.X₂ 0)] :
    Module.Finite R (HModule S.X₁ 0) :=
  FiniteDimensional.of_injective (map S.f 0) (injective_map_f_zero hS)

/-- **Finiteness of the left cohomology in positive degree**: `Hⁿ¹(X₁)` is an extension of
a submodule of the finite `Hⁿ¹(X₂)` by the image of the finite `Hⁿ⁰(X₃)` (exactness of the
slice at `Hⁿ¹(X₁)`). -/
theorem moduleFinite_left_succ (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    [Module.Finite R (HModule S.X₃ n₀)] [Module.Finite R (HModule S.X₂ n₁)] :
    Module.Finite R (HModule S.X₁ n₁) :=
  FiniteDimensional.of_exact (delta hS h) (map S.f n₁) (exact_delta_map_f hS h)

end FinitenessTransfer

end HModule

section ChiAdditivity

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Type u} [Field R] [HasSheafify J (ModuleCat.{u} R)]
  {S : ShortComplex (Sheaf J (ModuleCat.{u} R))}

/-- **Additivity of the Euler characteristic** along a short exact sequence of sheaves of
`R`-modules whose third term has vanishing `H¹`: `χ X₂ = χ X₁ + χ X₃`. This is the
alternating-sum identity for the five-term exact slice
`0 → H⁰X₁ → H⁰X₂ → H⁰X₃ → H¹X₁ → H¹X₂ → 0`. -/
theorem chi_eq_add_of_shortExact (hS : S.ShortExact)
    [Module.Finite R (HModule S.X₁ 0)] [Module.Finite R (HModule S.X₂ 0)]
    [Module.Finite R (HModule S.X₃ 0)] [Module.Finite R (HModule S.X₁ 1)]
    [Module.Finite R (HModule S.X₂ 1)] [Subsingleton (HModule S.X₃ 1)] :
    chi S.X₂ = chi S.X₁ + chi S.X₃ := by
  have hone : (0 : ℕ) + 1 = 1 := rfl
  have halt := AlgebraicGeometry.finrank_alt_sum_eq_zero_of_exact₅
    (HModule.map S.f 0) (HModule.map S.g 0) (HModule.delta hS hone) (HModule.map S.f 1)
    (HModule.injective_map_f_zero hS) (HModule.exact_map_f_map_g hS 0)
    (HModule.exact_map_g_delta hS hone) (HModule.exact_delta_map_f hS hone)
    (HModule.surjective_map_f hS 1)
  have h3 : h1 S.X₃ = 0 := h1_eq_zero inferInstance
  rw [chi, chi, chi, h3]
  unfold h0 h1
  omega

end ChiAdditivity

end CategoryTheory.Sheaf
