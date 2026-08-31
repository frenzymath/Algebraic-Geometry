/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RigidEngineLattice
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# RE-1a — the six-term exact sequence of a short exact sequence of two-lattice pairs

For a short exact sequence of two-lattice pairs `0 → P → P' → P'' → 0`
(`TwoLatticePair.IsShortExact`: componentwise injective/surjective/exact on the two chart
lattices and the overlap module), this file constructs the connecting homomorphism
`∂ : H⁰(P'') →ₗ[R] H¹(P)` (`IsShortExact.delta`) and proves the **six-term exact
sequence** — the entire long exact cohomology sequence of the two-term Čech complexes
(two-term complexes have no `H²`, worksheet §2.6):

`0 → H⁰(P) → H⁰(P') → H⁰(P'') → H¹(P) → H¹(P') → H¹(P'') → 0`

The snake is hand-rolled on the two-term complexes (no homology API, per the worksheet's
fallback (ii) and the kernel-discipline house rules): the connecting map is obtained by
descending the chase `e ↦ [φN⁻¹ (diff e)]` along the surjection
`{e ∈ C⁰(P') | diff e ∈ ker ψN} ↠ H⁰(P'')`, and each exactness statement is an element
chase against the characterizing property `IsShortExact.delta_apply`.

## Main declarations

* `TwoLatticePair.IsShortExact` — componentwise short exactness of a pair of pair maps.
* `TwoLatticePair.IsShortExact.delta` — the connecting homomorphism
  `H⁰(P'') →ₗ[R] H¹(P)`; `delta_apply` — its characterizing property.
* the six exactness statements: `h0Map_injective`, `range_h0Map_eq_ker_h0Map`,
  `range_h0Map_eq_ker_delta`, `range_delta_eq_ker_h1Map`, `range_h1Map_eq_ker_h1Map`,
  `h1Map_surjective`.

This is consumed by the coherence theorem COH-0
(`AlgebraicJacobian.Cohomology.RigidEngineLatticeCoherence`) with `P` the kernel pair of
the model surjection.
-/

set_option autoImplicit false

universe u

namespace TwoLatticePair

variable {R : Type u} [CommRing R]
variable {M₀ M₁ N M₀' M₁' N' M₀'' M₁'' N'' : Type*}
variable [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup N]
variable [Module R M₀] [Module R M₁] [Module R N]
variable [AddCommGroup M₀'] [AddCommGroup M₁'] [AddCommGroup N']
variable [Module R M₀'] [Module R M₁'] [Module R N']
variable [AddCommGroup M₀''] [AddCommGroup M₁''] [AddCommGroup N'']
variable [Module R M₀''] [Module R M₁''] [Module R N'']
variable {P : TwoLatticePair R M₀ M₁ N} {P' : TwoLatticePair R M₀' M₁' N'}
variable {P'' : TwoLatticePair R M₀'' M₁'' N''}

/-- A **short exact sequence of two-lattice pairs** `0 → P → P' → P'' → 0`:
the maps of pairs `φ : P ⟶ P'` and `ψ : P' ⟶ P''` are componentwise injective,
surjective, and exact in the middle, on both chart lattices and on the overlap module. -/
structure IsShortExact (φ : P.Hom P') (ψ : P'.Hom P'') : Prop where
  /-- Injectivity on the chart-0 lattice. -/
  injective₀ : Function.Injective φ.hom₀
  /-- Injectivity on the chart-1 lattice. -/
  injective₁ : Function.Injective φ.hom₁
  /-- Injectivity on the overlap module. -/
  injectiveN : Function.Injective φ.homN
  /-- Surjectivity on the chart-0 lattice. -/
  surjective₀ : Function.Surjective ψ.hom₀
  /-- Surjectivity on the chart-1 lattice. -/
  surjective₁ : Function.Surjective ψ.hom₁
  /-- Surjectivity on the overlap module. -/
  surjectiveN : Function.Surjective ψ.homN
  /-- Exactness on the chart-0 lattice. -/
  exact₀ : LinearMap.range φ.hom₀ = LinearMap.ker ψ.hom₀
  /-- Exactness on the chart-1 lattice. -/
  exact₁ : LinearMap.range φ.hom₁ = LinearMap.ker ψ.hom₁
  /-- Exactness on the overlap module. -/
  exactN : LinearMap.range φ.homN = LinearMap.ker ψ.homN

namespace IsShortExact

variable {φ : P.Hom P'} {ψ : P'.Hom P''}

lemma comp_zero₀ (h : IsShortExact φ ψ) (x : M₀) : ψ.hom₀ (φ.hom₀ x) = 0 :=
  LinearMap.mem_ker.mp (h.exact₀ ▸ LinearMap.mem_range_self φ.hom₀ x)

lemma comp_zero₁ (h : IsShortExact φ ψ) (y : M₁) : ψ.hom₁ (φ.hom₁ y) = 0 :=
  LinearMap.mem_ker.mp (h.exact₁ ▸ LinearMap.mem_range_self φ.hom₁ y)

lemma comp_zeroN (h : IsShortExact φ ψ) (n : N) : ψ.homN (φ.homN n) = 0 :=
  LinearMap.mem_ker.mp (h.exactN ▸ LinearMap.mem_range_self φ.homN n)

/-! ### The connecting homomorphism -/

variable (ψ) in
/-- (Implementation) The domain of the connecting-map chase: middle cochains whose
differential maps into the kernel of `ψ` on the overlap. -/
private def deltaDom : Submodule R (M₀' × M₁') := LinearMap.ker (ψ.homN ∘ₗ P'.diff)

variable (ψ) in
private lemma mem_deltaDom {z : M₀' × M₁'} :
    z ∈ deltaDom ψ ↔ ψ.homN (P'.diff z) = 0 :=
  LinearMap.mem_ker

variable (ψ) in
/-- (Implementation) The projection of the chase domain onto `H⁰(P'')`. -/
private def deltaProj : ↥(deltaDom ψ) →ₗ[R] ↥P''.H0 :=
  (ψ.hom₀.prodMap ψ.hom₁).restrict fun z hz => by
    refine P''.mem_H0.mpr ?_
    rw [LinearMap.prodMap_apply, Hom.diff_comm]
    exact (mem_deltaDom ψ).mp hz

private lemma deltaProj_surjective (h : IsShortExact φ ψ) :
    Function.Surjective (deltaProj ψ) := by
  rintro ⟨⟨z₀, z₁⟩, hz⟩
  obtain ⟨e₀, he₀⟩ := h.surjective₀ z₀
  obtain ⟨e₁, he₁⟩ := h.surjective₁ z₁
  refine ⟨⟨(e₀, e₁), (mem_deltaDom ψ).mpr ?_⟩, ?_⟩
  · calc ψ.homN (P'.diff (e₀, e₁))
        = P''.diff (ψ.hom₀ e₀, ψ.hom₁ e₁) := (Hom.diff_comm ψ (e₀, e₁)).symm
      _ = P''.diff (z₀, z₁) := by rw [he₀, he₁]
      _ = 0 := P''.mem_H0.mp hz
  · exact Subtype.ext (Prod.ext he₀ he₁)

/-- (Implementation) The differential of the chase domain, corestricted to the image
of the overlap module of `P`. -/
private def deltaDiff (h : IsShortExact φ ψ) :
    ↥(deltaDom ψ) →ₗ[R] ↥(LinearMap.range φ.homN) :=
  P'.diff.restrict fun z hz => by
    rw [h.exactN]
    exact LinearMap.mem_ker.mpr ((mem_deltaDom ψ).mp hz)

private lemma deltaDiff_coe (h : IsShortExact φ ψ) (z : ↥(deltaDom ψ)) :
    (deltaDiff h z : N') = P'.diff z.val := rfl

/-- (Implementation) The connecting chase `e ↦ [φN⁻¹ (diff e)]`, before descending. -/
private noncomputable def deltaToH1 (h : IsShortExact φ ψ) : ↥(deltaDom ψ) →ₗ[R] P.H1 :=
  P.imageLattice.mkQ ∘ₗ
    (LinearEquiv.ofInjective φ.homN h.injectiveN).symm.toLinearMap ∘ₗ deltaDiff h

private lemma deltaToH1_apply (h : IsShortExact φ ψ) (z : ↥(deltaDom ψ)) (n : N)
    (hn : φ.homN n = P'.diff z.val) :
    deltaToH1 h z = Submodule.Quotient.mk n := by
  have hkey : (LinearEquiv.ofInjective φ.homN h.injectiveN).symm (deltaDiff h z) = n := by
    apply h.injectiveN
    rw [LinearEquiv.ofInjective_symm_apply, hn]
    exact deltaDiff_coe h z
  calc deltaToH1 h z
      = P.imageLattice.mkQ
        ((LinearEquiv.ofInjective φ.homN h.injectiveN).symm (deltaDiff h z)) := rfl
    _ = Submodule.Quotient.mk n := by rw [hkey, Submodule.mkQ_apply]

private lemma ker_deltaProj_le (h : IsShortExact φ ψ) :
    LinearMap.ker (deltaProj ψ) ≤ LinearMap.ker (deltaToH1 h) := by
  rintro ⟨⟨e₀, e₁⟩, he⟩ hker
  have hval : (ψ.hom₀ e₀, ψ.hom₁ e₁) = (0 : M₀'' × M₁'') := by
    have h0 := congrArg Subtype.val (LinearMap.mem_ker.mp hker)
    rw [ZeroMemClass.coe_zero] at h0
    exact h0
  have h₀ : ψ.hom₀ e₀ = 0 := congrArg Prod.fst hval
  have h₁ : ψ.hom₁ e₁ = 0 := congrArg Prod.snd hval
  obtain ⟨a, ha⟩ : e₀ ∈ LinearMap.range φ.hom₀ := by
    rw [h.exact₀]; exact LinearMap.mem_ker.mpr h₀
  obtain ⟨b, hb⟩ : e₁ ∈ LinearMap.range φ.hom₁ := by
    rw [h.exact₁]; exact LinearMap.mem_ker.mpr h₁
  refine LinearMap.mem_ker.mpr ?_
  have hn : φ.homN (P.diff (a, b)) = P'.diff (e₀, e₁) := by
    rw [← Hom.diff_comm φ (a, b)]
    change P'.diff (φ.hom₀ a, φ.hom₁ b) = P'.diff (e₀, e₁)
    rw [ha, hb]
  rw [deltaToH1_apply h _ _ hn, Submodule.Quotient.mk_eq_zero, ← P.range_diff_eq]
  exact LinearMap.mem_range_self _ (a, b)

/-- **The connecting homomorphism** `∂ : H⁰(P'') →ₗ[R] H¹(P)` of a short exact sequence
of two-lattice pairs: the hand-rolled snake on the two-term Čech complexes. Its
characterizing property is `IsShortExact.delta_apply`. -/
noncomputable def delta (h : IsShortExact φ ψ) : ↥P''.H0 →ₗ[R] P.H1 :=
  Submodule.liftQ (LinearMap.ker (deltaProj ψ)) (deltaToH1 h) (ker_deltaProj_le h) ∘ₗ
    ((deltaProj ψ).quotKerEquivOfSurjective (deltaProj_surjective h)).symm.toLinearMap

/-- **The characterizing property of the connecting homomorphism**: if `(e₀, e₁)` is a
componentwise `ψ`-lift of the `H⁰(P'')`-class `z` and `n` is the (unique) `φ`-preimage of
its differential, then `∂ z = [n]`. -/
theorem delta_apply (h : IsShortExact φ ψ) (z : ↥P''.H0) (e₀ : M₀') (e₁ : M₁') (n : N)
    (he₀ : ψ.hom₀ e₀ = (z : M₀'' × M₁'').1) (he₁ : ψ.hom₁ e₁ = (z : M₀'' × M₁'').2)
    (hn : φ.homN n = P'.diff (e₀, e₁)) :
    h.delta z = Submodule.Quotient.mk n := by
  have hmem : (e₀, e₁) ∈ deltaDom ψ := (mem_deltaDom ψ).mpr (by
    rw [← hn]; exact h.comp_zeroN n)
  have hproj : deltaProj ψ ⟨(e₀, e₁), hmem⟩ = z := Subtype.ext (Prod.ext he₀ he₁)
  have hquot : ((deltaProj ψ).quotKerEquivOfSurjective (deltaProj_surjective h)).symm z
      = Submodule.Quotient.mk ⟨(e₀, e₁), hmem⟩ := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    exact hproj.symm
  calc h.delta z
      = Submodule.liftQ (LinearMap.ker (deltaProj ψ)) (deltaToH1 h) (ker_deltaProj_le h)
        (((deltaProj ψ).quotKerEquivOfSurjective (deltaProj_surjective h)).symm z) := rfl
    _ = deltaToH1 h ⟨(e₀, e₁), hmem⟩ := by rw [hquot, Submodule.liftQ_apply]
    _ = Submodule.Quotient.mk n := deltaToH1_apply h _ n hn

/-- (Implementation) Every `H⁰(P'')`-class admits a componentwise lift together with a
`φ`-preimage of its differential. -/
private lemma exists_lift (h : IsShortExact φ ψ) (z : ↥P''.H0) :
    ∃ (e₀ : M₀') (e₁ : M₁') (n : N), ψ.hom₀ e₀ = (z : M₀'' × M₁'').1 ∧
      ψ.hom₁ e₁ = (z : M₀'' × M₁'').2 ∧ φ.homN n = P'.diff (e₀, e₁) := by
  obtain ⟨e₀, he₀⟩ := h.surjective₀ (z : M₀'' × M₁'').1
  obtain ⟨e₁, he₁⟩ := h.surjective₁ (z : M₀'' × M₁'').2
  have hker : P'.diff (e₀, e₁) ∈ LinearMap.range φ.homN := by
    rw [h.exactN]
    refine LinearMap.mem_ker.mpr ?_
    calc ψ.homN (P'.diff (e₀, e₁))
        = P''.diff (ψ.hom₀ e₀, ψ.hom₁ e₁) := (Hom.diff_comm ψ (e₀, e₁)).symm
      _ = P''.diff ((z : M₀'' × M₁'').1, (z : M₀'' × M₁'').2) := by rw [he₀, he₁]
      _ = 0 := P''.mem_H0.mp z.prop
  obtain ⟨n, hn⟩ := hker
  exact ⟨e₀, e₁, n, he₀, he₁, hn⟩

/-! ### The six-term exact sequence -/

/-- Exactness at the left end: `H⁰(P) → H⁰(P')` is injective. -/
theorem h0Map_injective (h : IsShortExact φ ψ) : Function.Injective φ.h0Map := by
  intro z w hzw
  have hval := congrArg Subtype.val hzw
  apply Subtype.ext
  apply Prod.ext
  · exact h.injective₀ (congrArg Prod.fst hval)
  · exact h.injective₁ (congrArg Prod.snd hval)

/-- Exactness at `H⁰(P')`. -/
theorem range_h0Map_eq_ker_h0Map (h : IsShortExact φ ψ) :
    LinearMap.range φ.h0Map = LinearMap.ker ψ.h0Map := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    refine LinearMap.mem_ker.mpr (Subtype.ext ?_)
    apply Prod.ext
    · exact h.comp_zero₀ _
    · exact h.comp_zero₁ _
  · intro z hz
    have hval := congrArg Subtype.val (LinearMap.mem_ker.mp hz)
    rw [ZeroMemClass.coe_zero] at hval
    have h₀ : ψ.hom₀ (z : M₀' × M₁').1 = 0 := congrArg Prod.fst hval
    have h₁ : ψ.hom₁ (z : M₀' × M₁').2 = 0 := congrArg Prod.snd hval
    obtain ⟨a, ha⟩ : (z : M₀' × M₁').1 ∈ LinearMap.range φ.hom₀ := by
      rw [h.exact₀]; exact LinearMap.mem_ker.mpr h₀
    obtain ⟨b, hb⟩ : (z : M₀' × M₁').2 ∈ LinearMap.range φ.hom₁ := by
      rw [h.exact₁]; exact LinearMap.mem_ker.mpr h₁
    have hmem : (a, b) ∈ P.H0 := by
      refine P.mem_H0.mpr (h.injectiveN ?_)
      rw [map_zero, ← Hom.diff_comm φ (a, b)]
      change P'.diff (φ.hom₀ a, φ.hom₁ b) = 0
      rw [ha, hb]
      exact P'.mem_H0.mp z.prop
    exact ⟨⟨(a, b), hmem⟩, Subtype.ext (Prod.ext ha hb)⟩

/-- Exactness at `H⁰(P'')`. -/
theorem range_h0Map_eq_ker_delta (h : IsShortExact φ ψ) :
    LinearMap.range ψ.h0Map = LinearMap.ker h.delta := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    have hz := h.delta_apply (ψ.h0Map w) (w : M₀' × M₁').1 (w : M₀' × M₁').2 0 rfl rfl
      (by rw [map_zero]; exact (P'.mem_H0.mp w.prop).symm)
    rw [hz]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.zero_mem _)
  · intro z hz
    obtain ⟨e₀, e₁, n, he₀, he₁, hn⟩ := exists_lift h z
    have hdelta := h.delta_apply z e₀ e₁ n he₀ he₁ hn
    rw [LinearMap.mem_ker.mp hz] at hdelta
    have hn0 : n ∈ P.imageLattice := (Submodule.Quotient.mk_eq_zero _).mp hdelta.symm
    rw [← P.range_diff_eq] at hn0
    obtain ⟨⟨a, b⟩, hab⟩ := hn0
    have hw : (e₀ - φ.hom₀ a, e₁ - φ.hom₁ b) ∈ P'.H0 := by
      refine P'.mem_H0.mpr ?_
      have key1 : P'.ι₀ e₀ - P'.ι₁ e₁ = φ.homN n := by rw [hn]; rfl
      have key2 : P'.ι₀ (φ.hom₀ a) - P'.ι₁ (φ.hom₁ b) = φ.homN n := by
        rw [← hab]
        exact Hom.diff_comm φ (a, b)
      change P'.ι₀ (e₀ - φ.hom₀ a) - P'.ι₁ (e₁ - φ.hom₁ b) = 0
      rw [map_sub, map_sub, sub_sub_sub_comm, key1, key2, sub_self]
    refine ⟨⟨(e₀ - φ.hom₀ a, e₁ - φ.hom₁ b), hw⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change ψ.hom₀ (e₀ - φ.hom₀ a) = (z : M₀'' × M₁'').1
      rw [map_sub, h.comp_zero₀, sub_zero, he₀]
    · change ψ.hom₁ (e₁ - φ.hom₁ b) = (z : M₀'' × M₁'').2
      rw [map_sub, h.comp_zero₁, sub_zero, he₁]

/-- Exactness at `H¹(P)`. -/
theorem range_delta_eq_ker_h1Map (h : IsShortExact φ ψ) :
    LinearMap.range h.delta = LinearMap.ker φ.h1Map := by
  apply le_antisymm
  · rintro c ⟨z, rfl⟩
    obtain ⟨e₀, e₁, n, he₀, he₁, hn⟩ := exists_lift h z
    refine LinearMap.mem_ker.mpr ?_
    rw [h.delta_apply z e₀ e₁ n he₀ he₁ hn, Hom.h1Map_mk, hn,
      Submodule.Quotient.mk_eq_zero, ← P'.range_diff_eq]
    exact LinearMap.mem_range_self _ (e₀, e₁)
  · intro c hc
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have h0 : φ.homN n ∈ P'.imageLattice := by
      have hm := LinearMap.mem_ker.mp hc
      rw [Hom.h1Map_mk] at hm
      exact (Submodule.Quotient.mk_eq_zero _).mp hm
    rw [← P'.range_diff_eq] at h0
    obtain ⟨⟨e₀, e₁⟩, he⟩ := h0
    have hz : (ψ.hom₀ e₀, ψ.hom₁ e₁) ∈ P''.H0 := by
      refine P''.mem_H0.mpr ?_
      calc P''.diff (ψ.hom₀ e₀, ψ.hom₁ e₁)
          = ψ.homN (P'.diff (e₀, e₁)) := Hom.diff_comm ψ (e₀, e₁)
        _ = ψ.homN (φ.homN n) := by rw [he]
        _ = 0 := h.comp_zeroN n
    exact ⟨⟨(ψ.hom₀ e₀, ψ.hom₁ e₁), hz⟩,
      h.delta_apply ⟨(ψ.hom₀ e₀, ψ.hom₁ e₁), hz⟩ e₀ e₁ n rfl rfl he.symm⟩

/-- Exactness at `H¹(P')`. -/
theorem range_h1Map_eq_ker_h1Map (h : IsShortExact φ ψ) :
    LinearMap.range φ.h1Map = LinearMap.ker ψ.h1Map := by
  apply le_antisymm
  · rintro c ⟨d, rfl⟩
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ d
    refine LinearMap.mem_ker.mpr ?_
    rw [Hom.h1Map_mk, Hom.h1Map_mk, h.comp_zeroN n]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.zero_mem _)
  · intro c hc
    obtain ⟨n', rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have h0 : ψ.homN n' ∈ P''.imageLattice := by
      have hm := LinearMap.mem_ker.mp hc
      rw [Hom.h1Map_mk] at hm
      exact (Submodule.Quotient.mk_eq_zero _).mp hm
    rw [← P''.range_diff_eq] at h0
    obtain ⟨⟨z₀, z₁⟩, hz⟩ := h0
    obtain ⟨e₀, he₀⟩ := h.surjective₀ z₀
    obtain ⟨e₁, he₁⟩ := h.surjective₁ z₁
    obtain ⟨w, hw⟩ : n' - P'.diff (e₀, e₁) ∈ LinearMap.range φ.homN := by
      rw [h.exactN]
      refine LinearMap.mem_ker.mpr ?_
      have hd : ψ.homN (P'.diff (e₀, e₁)) = ψ.homN n' := by
        calc ψ.homN (P'.diff (e₀, e₁))
            = P''.diff (ψ.hom₀ e₀, ψ.hom₁ e₁) := (Hom.diff_comm ψ (e₀, e₁)).symm
          _ = P''.diff (z₀, z₁) := by rw [he₀, he₁]
          _ = ψ.homN n' := hz
      rw [map_sub, hd, sub_self]
    refine ⟨Submodule.Quotient.mk w, ?_⟩
    have hmk : Submodule.Quotient.mk (p := P'.imageLattice) (P'.diff (e₀, e₁)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (by
        rw [← P'.range_diff_eq]; exact LinearMap.mem_range_self _ (e₀, e₁))
    rw [Hom.h1Map_mk, hw, Submodule.Quotient.mk_sub, hmk, sub_zero]

/-- Exactness at the right end: `H¹(P') → H¹(P'')` is surjective. -/
theorem h1Map_surjective (h : IsShortExact φ ψ) : Function.Surjective ψ.h1Map :=
  Hom.h1Map_surjective ψ h.surjectiveN

end IsShortExact

end TwoLatticePair
