/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# The fibre-descent kit for the relative `hwin` (DDR-8 follow-up)

Pure algebra + one affine-scheme lemma consumed by `Picard/DivSchemeMonoBridgeRel.lean`
(the `hwin` closer of `Picard/DivSchemeMonoBridge.lean`):

* `exists_smul_mem_smul_top_of_one_tmul_eq_zero` — the kernel of
  `B → κ(s) ⊗[R] B` is the `s`-saturation: `1 ⊗ b = 0` forces `t • b ∈ s·B` for some
  `t ∉ s`.  Route: `κ(s) ⊗[R] B ≅ κ(s) ⊗[R⧸s] ((R⧸s) ⊗[R] B)` (`cancelBaseChange`),
  where the outer factor is a localized module of the fraction field
  (`isLocalizedModule_iff_isBaseChange` + `TensorProduct.isBaseChange`), and
  `(R⧸s) ⊗[R] B ≅ B ⧸ s·B` (`quotTensorEquivQuotSMul`).
* `exists_smul_mem_sup_map_of_one_tmul_mem_map` — **fibre descent of ideal
  membership**: if `1 ⊗ f` lies in the extension of `I ⊆ B` to the residue-field fibre
  `κ(s) ⊗[R] B`, then `t • f ∈ I ⊔ s·B` for some `t ∉ s` — clear the `κ(s)`
  denominators (`IsLocalization.surj` on `Frac(R⧸s)`), then cancel the kernel by the
  saturation lemma.  No hypotheses on `B` beyond `[Algebra R B]`.
* `IsAffineOpen.mem_of_germ_mem_map` — **the affine local-global principle for ideal
  membership**: a section of an affine open lies in an ideal `J` of `Γ(U)` as soon as
  its germ lies in the extension of `J` at every point of `U`.  The colon ideal
  `(J : f)` cannot fit inside a maximal ideal `q`: at the point of `q`
  (`fromSpec`), the stalk is the localization at `q` (`isLocalization_stalk'`), where
  the germ hypothesis produces `u, v ∉ q` with `(v·u)·f ∈ J`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open TensorProduct

namespace AlgebraicGeometry

/-! ## The kernel of `B → κ(s) ⊗[R] B` is the `s`-saturation -/

section FibreDescent

variable {R : Type u} [CommRing R] (s : Ideal R) [s.IsPrime]
variable {B : Type u} [CommRing B] [Algebra R B]

/-- Every element of the residue-field fibre is, after multiplication by a base
denominator outside the prime, a pure tensor with left factor `1`. -/
theorem exists_notMem_smul_eq_one_tmul
    (x : s.ResidueField ⊗[R] B) :
    ∃ r : R, r ∉ s ∧ ∃ b : B,
      r • x = (1 : s.ResidueField) ⊗ₜ[R] b := by
  have hsprime : s.IsPrime := inferInstance
  induction x using TensorProduct.induction_on with
  | zero =>
      exact ⟨1, s.primeCompl.one_mem, 0, by simp⟩
  | tmul c b =>
      obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective c
      obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective s.primeCompl y
      refine ⟨t, t.2, a • b, ?_⟩
      have ht : (t : R) • (IsLocalRing.residue (Localization.AtPrime s)
            (IsLocalization.mk' (Localization.AtPrime s) a t)) =
          algebraMap R s.ResidueField a := by
        rw [Algebra.smul_def,
          IsScalarTower.algebraMap_apply R (Localization.AtPrime s) s.ResidueField,
          IsLocalRing.ResidueField.algebraMap_eq, ← map_mul, IsLocalization.mk'_spec',
          ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      calc
        (t : R) • (IsLocalRing.residue (Localization.AtPrime s)
              (IsLocalization.mk' (Localization.AtPrime s) a t) ⊗ₜ[R] b) =
            ((t : R) • IsLocalRing.residue (Localization.AtPrime s)
              (IsLocalization.mk' (Localization.AtPrime s) a t)) ⊗ₜ[R] b := by
                rw [TensorProduct.smul_tmul']
        _ = (algebraMap R s.ResidueField a) ⊗ₜ[R] b := by rw [ht]
        _ = (a • (1 : s.ResidueField)) ⊗ₜ[R] b := by
              rw [Algebra.algebraMap_eq_smul_one]
        _ = (1 : s.ResidueField) ⊗ₜ[R] (a • b) := TensorProduct.smul_tmul a 1 b
  | add x y hx hy =>
      obtain ⟨rx, hrx, bx, hbx⟩ := hx
      obtain ⟨ry, hry, by', hby⟩ := hy
      refine ⟨rx * ry, fun hmem => (hsprime.mem_or_mem hmem).elim hrx hry,
        ry • bx + rx • by', ?_⟩
      rw [TensorProduct.tmul_add, smul_add]
      congr 1
      · rw [mul_comm, mul_smul, hbx, TensorProduct.tmul_smul]
      · rw [mul_smul, hby, TensorProduct.tmul_smul]

/-- **The kernel of the residue-field fibre map is the `s`-saturation** (pure algebra,
any `R`-algebra `B`): if `1 ⊗ b` vanishes in `κ(s) ⊗[R] B`, then `t • b ∈ s·B` for some
`t ∉ s`.  Factor through `(R⧸s) ⊗[R] B`: the outer tensor with `κ(s) = Frac(R⧸s)` is a
localized module, so vanishing is torsion; the inner quotient is `B ⧸ s·B`. -/
theorem exists_smul_mem_smul_top_of_one_tmul_eq_zero {b : B}
    (hb : (1 : s.ResidueField) ⊗ₜ[R] b = 0) :
    ∃ t : R, t ∉ s ∧ t • b ∈ s • (⊤ : Submodule R B) := by
  -- move to the two-step spelling through `R ⧸ s`
  have hcan : (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ s)
      s.ResidueField s.ResidueField B)
      ((1 : s.ResidueField) ⊗ₜ[R ⧸ s] ((1 : R ⧸ s) ⊗ₜ[R] b))
      = (1 : s.ResidueField) ⊗ₜ[R] b := by
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  have h0 : (1 : s.ResidueField) ⊗ₜ[R ⧸ s] ((1 : R ⧸ s) ⊗ₜ[R] b)
      = (0 : s.ResidueField ⊗[R ⧸ s] ((R ⧸ s) ⊗[R] B)) := by
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ s)
      s.ResidueField s.ResidueField B).injective
    rw [hcan, map_zero, hb]
  -- the outer tensor is a localized module of `Frac(R ⧸ s)`
  haveI hlocmod : IsLocalizedModule (nonZeroDivisors (R ⧸ s))
      (TensorProduct.mk (R ⧸ s) s.ResidueField ((R ⧸ s) ⊗[R] B) 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (R ⧸ s)) s.ResidueField _).mpr
      (TensorProduct.isBaseChange _ _ _)
  have hmk : (TensorProduct.mk (R ⧸ s) s.ResidueField ((R ⧸ s) ⊗[R] B) 1)
      ((1 : R ⧸ s) ⊗ₜ[R] b)
      = (TensorProduct.mk (R ⧸ s) s.ResidueField ((R ⧸ s) ⊗[R] B) 1) 0 := by
    rw [map_zero]
    exact h0
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
    (S := nonZeroDivisors (R ⧸ s)) hmk
  rw [smul_zero] at hc
  -- lift the torsion scalar to `R`
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (c : R ⧸ s)
  refine ⟨t, fun hts => ?_, ?_⟩
  · -- `t ∈ s` would make the nonzerodivisor `c` zero
    have hc0 : (c : R ⧸ s) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp c.2
    exact hc0 (ht ▸ Ideal.Quotient.eq_zero_iff_mem.mpr hts)
  · -- `c • (1 ⊗ b) = (mk t) ⊗ b`, then read off through the quotient identification
    have hct : (Ideal.Quotient.mk s t) ⊗ₜ[R] b = (0 : (R ⧸ s) ⊗[R] B) := by
      have h1 : (c : R ⧸ s) • ((1 : R ⧸ s) ⊗ₜ[R] b) = (c : R ⧸ s) ⊗ₜ[R] b := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, ← h1]
      exact hc
    have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul B s) hct
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, map_zero] at hq
    exact (Submodule.Quotient.mk_eq_zero _).mp hq

/-- **Fibre descent of ideal membership** (the `κ(s)`-to-`R` leg of the relative
`hwin`): if `1 ⊗ f` lies in the extension of an ideal `I ⊆ B` to the residue-field
fibre `κ(s) ⊗[R] B`, then some multiple `t • f` with `t ∉ s` lies in `I ⊔ s·B`.
Clear denominators with `IsLocalization.surj` on `Frac(R ⧸ s)` and cancel the kernel
through the saturation lemma. -/
theorem exists_smul_mem_sup_map_of_one_tmul_mem_map {I : Ideal B} {f : B}
    (hf : (1 : s.ResidueField) ⊗ₜ[R] f ∈ Ideal.map
      (Algebra.TensorProduct.includeRight (R := R) (A := s.ResidueField) (B := B)) I) :
    ∃ t : R, t ∉ s ∧ t • f ∈ I ⊔ Ideal.map (algebraMap R B) s := by
  set I' : Ideal B := I ⊔ Ideal.map (algebraMap R B) s with hI'
  have hprime : s.IsPrime := inferInstance
  -- combining two denominator-free representatives additively
  have hadd : ∀ (y₁ y₂ : s.ResidueField ⊗[R] B) (t₁ t₂ : R) (b₁ b₂ : B),
      t₁ ∉ s → t₂ ∉ s → b₁ ∈ I' → b₂ ∈ I' →
      t₁ • y₁ = (1 : s.ResidueField) ⊗ₜ[R] b₁ →
      t₂ • y₂ = (1 : s.ResidueField) ⊗ₜ[R] b₂ →
      ∃ (t : R) (b : B), t ∉ s ∧ b ∈ I' ∧
        t • (y₁ + y₂) = (1 : s.ResidueField) ⊗ₜ[R] b := by
    intro y₁ y₂ t₁ t₂ b₁ b₂ ht₁ ht₂ hb₁ hb₂ he₁ he₂
    refine ⟨t₁ * t₂, t₂ • b₁ + t₁ • b₂, fun hmem => ?_,
      I'.add_mem (I'.smul_of_tower_mem t₂ hb₁) (I'.smul_of_tower_mem t₁ hb₂), ?_⟩
    · rcases hprime.mem_or_mem hmem with h | h
      exacts [ht₁ h, ht₂ h]
    · have hA : (t₁ * t₂) • y₁ = (1 : s.ResidueField) ⊗ₜ[R] (t₂ • b₁) := by
        rw [mul_comm, mul_smul, he₁, TensorProduct.tmul_smul]
      have hB : (t₁ * t₂) • y₂ = (1 : s.ResidueField) ⊗ₜ[R] (t₁ • b₂) := by
        rw [mul_smul, he₂, TensorProduct.tmul_smul]
      rw [smul_add, hA, hB, TensorProduct.tmul_add]
  -- the saturation set: elements with a denominator-free representative in `I'`
  have hsat : ∀ y ∈ Ideal.map
      (Algebra.TensorProduct.includeRight (R := R) (A := s.ResidueField) (B := B)) I,
      ∃ (t : R) (b : B), t ∉ s ∧ b ∈ I' ∧ t • y = (1 : s.ResidueField) ⊗ₜ[R] b := by
    intro y hy
    rw [Ideal.map, Ideal.span] at hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · -- generators: the image of `I`
      rintro _ ⟨b₀, hb₀, rfl⟩
      exact ⟨1, b₀, s.primeCompl.one_mem, Ideal.mem_sup_left hb₀, by
        rw [one_smul, Algebra.TensorProduct.includeRight_apply]⟩
    · exact ⟨1, 0, s.primeCompl.one_mem, I'.zero_mem, by
        rw [one_smul, TensorProduct.tmul_zero]⟩
    · -- additivity: multiply the two denominators
      rintro y₁ y₂ - - ⟨t₁, b₁, ht₁, hb₁, he₁⟩ ⟨t₂, b₂, ht₂, hb₂, he₂⟩
      exact hadd y₁ y₂ t₁ t₂ b₁ b₂ ht₁ ht₂ hb₁ hb₂ he₁ he₂
    · -- absorption of ring multiplication: clear the scalar's denominator
      rintro g y - ⟨t, b, ht, hb, he⟩
      have hmul : ∀ g' : s.ResidueField ⊗[R] B,
          ∃ (t' : R) (b' : B), t' ∉ s ∧ b' ∈ I' ∧
            t' • (g' * ((1 : s.ResidueField) ⊗ₜ[R] b)) = (1 : s.ResidueField) ⊗ₜ[R] b' := by
        intro g'
        induction g' with
        | zero => exact ⟨1, 0, s.primeCompl.one_mem, I'.zero_mem, by
            rw [one_smul, zero_mul, TensorProduct.tmul_zero]⟩
        | add g₁ g₂ h₁ h₂ =>
          obtain ⟨t₁, b₁, ht₁, hb₁, he₁⟩ := h₁
          obtain ⟨t₂, b₂, ht₂, hb₂, he₂⟩ := h₂
          have hd : (g₁ + g₂) * ((1 : s.ResidueField) ⊗ₜ[R] b)
              = g₁ * ((1 : s.ResidueField) ⊗ₜ[R] b)
                + g₂ * ((1 : s.ResidueField) ⊗ₜ[R] b) := add_mul _ _ _
          rw [hd]
          exact hadd _ _ t₁ t₂ b₁ b₂ ht₁ ht₂ hb₁ hb₂ he₁ he₂
        | tmul c b'' =>
          -- clear the `κ(s)` denominator of `c`
          obtain ⟨⟨a, d⟩, had⟩ := IsLocalization.surj (nonZeroDivisors (R ⧸ s)) c
          obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective a
          obtain ⟨d₀, hd₀⟩ := Ideal.Quotient.mk_surjective (d : R ⧸ s)
          have hd₀s : d₀ ∉ s := fun hmem => mem_nonZeroDivisors_iff_ne_zero.mp d.2
            (hd₀ ▸ Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
          refine ⟨d₀, a₀ • (b'' * b), hd₀s,
            I'.smul_of_tower_mem a₀ (I'.mul_mem_left b'' hb), ?_⟩
          have hmt : (c ⊗ₜ[R] b'') * ((1 : s.ResidueField) ⊗ₜ[R] b)
              = c ⊗ₜ[R] (b'' * b) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
          have hdc : d₀ • c = algebraMap R s.ResidueField a₀ := by
            have h1 : d₀ • c = algebraMap (R ⧸ s) s.ResidueField (d : R ⧸ s) * c := by
              rw [← hd₀, Ideal.algebraMap_quotient_residueField_mk,
                Algebra.smul_def]
            rw [h1, mul_comm, had, ← ha₀,
              Ideal.algebraMap_quotient_residueField_mk]
          have hfin : d₀ • (c ⊗ₜ[R] (b'' * b))
              = (1 : s.ResidueField) ⊗ₜ[R] (a₀ • (b'' * b)) := by
            rw [TensorProduct.smul_tmul', hdc, Algebra.algebraMap_eq_smul_one,
              TensorProduct.smul_tmul]
          rw [hmt, hfin]
      obtain ⟨t', b', ht', hb', he'⟩ := hmul g
      refine ⟨t' * t, b', fun hmem => ?_, hb', ?_⟩
      · rcases hprime.mem_or_mem hmem with h | h
        exacts [ht' h, ht h]
      · have h1 : (t' * t) • (g • y) = t' • (g * (t • y)) := by
          rw [smul_eq_mul, mul_smul, mul_smul_comm]
        rw [h1, he, he']
  obtain ⟨t, b, ht, hb, he⟩ := hsat _ hf
  have hker : (1 : s.ResidueField) ⊗ₜ[R] (t • f - b) = 0 := by
    rw [TensorProduct.tmul_sub, TensorProduct.tmul_smul, he, sub_self]
  obtain ⟨t', ht', hmem⟩ := exists_smul_mem_smul_top_of_one_tmul_eq_zero s hker
  refine ⟨t' * t, fun hmem' => ?_, ?_⟩
  · rcases hprime.mem_or_mem hmem' with h | h
    exacts [ht' h, ht h]
  · have h1 : (t' * t) • f = t' • b + t' • (t • f - b) := by
      rw [← smul_add, add_sub_cancel, mul_smul]
    rw [h1]
    refine I'.add_mem (I'.smul_of_tower_mem t' hb) ?_
    rw [Ideal.smul_top_eq_map] at hmem
    exact Ideal.mem_sup_right hmem

/-- Descend principal ideal membership which holds only locally at a point of the
residue-field fibre.  The first denominator is a fibre-chart element; clearing it to a
pure tensor and then applying `exists_smul_mem_sup_map_of_one_tmul_mem_map` produces one
total-space denominator outside `q`. -/
theorem exists_notMem_mul_mem_sup_map_of_fibre_local
    (q : Ideal B) [q.IsPrime]
    {B' : Type u} [CommRing B'] [Algebra s.ResidueField B']
    (e : s.ResidueField ⊗[R] B ≃ₐ[s.ResidueField] B')
    (q' : Ideal B') [q'.IsPrime]
    (hq : ∀ b : B,
      e.toLinearMap ((1 : s.ResidueField) ⊗ₜ[R] b) ∈ q' ↔ b ∈ q)
    {a b : B}
    (hlocal : ∃ d : B', d ∉ q' ∧
      d * e.toLinearMap ((1 : s.ResidueField) ⊗ₜ[R] a) ∈
        Ideal.span {e.toLinearMap ((1 : s.ResidueField) ⊗ₜ[R] b)}) :
    ∃ r : B, r ∉ q ∧
      r * a ∈ Ideal.span {b} ⊔
        Ideal.map (algebraMap R B) (Ideal.comap (algebraMap R B) q) := by
  have hqprime : q.IsPrime := inferInstance
  have hq'prime : q'.IsPrime := inferInstance
  have hscalar (t : R) :
      e.toLinearMap ((1 : s.ResidueField) ⊗ₜ[R] algebraMap R B t) =
        algebraMap s.ResidueField B' (algebraMap R s.ResidueField t) := by
    change e ((1 : s.ResidueField) ⊗ₜ[R] algebraMap R B t) = _
    calc
      e ((1 : s.ResidueField) ⊗ₜ[R] algebraMap R B t) =
          e ((1 : s.ResidueField) ⊗ₜ[R] (t • (1 : B))) := by
            rw [Algebra.smul_def, mul_one]
      _ = e ((t • (1 : s.ResidueField)) ⊗ₜ[R] (1 : B)) := by
            rw [TensorProduct.smul_tmul]
      _ = e (algebraMap s.ResidueField (s.ResidueField ⊗[R] B)
            (algebraMap R s.ResidueField t)) := by
            rw [Algebra.smul_def, mul_one]
            rfl
      _ = algebraMap s.ResidueField B' (algebraMap R s.ResidueField t) := e.commutes _
  have hsq : s = Ideal.comap (algebraMap R B) q := by
    ext t
    constructor
    · intro ht
      apply (hq (algebraMap R B t)).1
      rw [hscalar, Ideal.algebraMap_residueField_eq_zero.mpr ht]
      simp
    · intro ht
      have ht' : algebraMap s.ResidueField B' (algebraMap R s.ResidueField t) ∈ q' := by
        rw [← hscalar]
        exact (hq (algebraMap R B t)).2 ht
      by_contra hts
      have huK : IsUnit (algebraMap R s.ResidueField t) :=
        (isUnit_iff_ne_zero).2 fun hzero =>
          hts (Ideal.algebraMap_residueField_eq_zero.mp hzero)
      obtain ⟨u, hu⟩ := huK.map (algebraMap s.ResidueField B')
      have hone : (1 : B') ∈ q' := by
        rw [← u.inv_mul]
        exact q'.mul_mem_left (↑u⁻¹) (hu ▸ ht')
      exact hq'prime.ne_top ((Ideal.eq_top_iff_one q').mpr hone)
  obtain ⟨d, hdq, hda⟩ := hlocal
  obtain ⟨t, ht, c, htc⟩ :=
    exists_notMem_smul_eq_one_tmul s (e.symm d)
  have htc' : e ((1 : s.ResidueField) ⊗ₜ[R] c) =
      algebraMap s.ResidueField B' (algebraMap R s.ResidueField t) * d := by
    rw [← htc, ← IsScalarTower.algebraMap_smul s.ResidueField t (e.symm d),
      map_smul, Algebra.smul_def, e.apply_symm_apply]
  have htcLinear : e.toLinearMap ((1 : s.ResidueField) ⊗ₜ[R] c) =
      algebraMap s.ResidueField B' (algebraMap R s.ResidueField t) * d := htc'
  have hcq : c ∉ q := by
    intro hc
    have hmem : e.toLinearMap ((1 : s.ResidueField) ⊗ₜ[R] c) ∈ q' := (hq c).2 hc
    rw [htcLinear] at hmem
    rcases hq'prime.mem_or_mem hmem with ht' | hd'
    · have htK : algebraMap R s.ResidueField t ≠ 0 := fun hzero =>
          ht (Ideal.algebraMap_residueField_eq_zero.mp hzero)
      have huK : IsUnit (algebraMap R s.ResidueField t) :=
        (isUnit_iff_ne_zero).2 htK
      obtain ⟨u, hu⟩ := huK.map (algebraMap s.ResidueField B')
      have hone : (1 : B') ∈ q' := by
        rw [← u.inv_mul]
        exact q'.mul_mem_left (↑u⁻¹) (hu ▸ ht')
      exact hq'prime.ne_top ((Ideal.eq_top_iff_one q').mpr hone)
    · exact hdq hd'
  obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton.mp hda
  obtain ⟨d'', rfl⟩ := e.surjective d'
  change d * e ((1 : s.ResidueField) ⊗ₜ[R] a) =
    e ((1 : s.ResidueField) ⊗ₜ[R] b) * e d'' at hd'
  have hfibre : (1 : s.ResidueField) ⊗ₜ[R] (c * a) ∈
      Ideal.map (Algebra.TensorProduct.includeRight
        (R := R) (A := s.ResidueField) (B := B)) (Ideal.span {b}) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    refine ⟨(algebraMap s.ResidueField (s.ResidueField ⊗[R] B)
        (algebraMap R s.ResidueField t)) * d'', e.injective ?_⟩
    simp only [map_mul, Algebra.TensorProduct.includeRight_apply]
    calc
      e ((1 : s.ResidueField) ⊗ₜ[R] (c * a)) =
          e ((1 : s.ResidueField) ⊗ₜ[R] c) *
            e ((1 : s.ResidueField) ⊗ₜ[R] a) := by
              rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      _ = (algebraMap s.ResidueField B' (algebraMap R s.ResidueField t) * d) *
            e ((1 : s.ResidueField) ⊗ₜ[R] a) := by rw [htc']
      _ = algebraMap s.ResidueField B' (algebraMap R s.ResidueField t) *
            (e ((1 : s.ResidueField) ⊗ₜ[R] b) * e d'') := by
              rw [mul_assoc, hd']
      _ = e ((1 : s.ResidueField) ⊗ₜ[R] b) *
            (e (algebraMap s.ResidueField (s.ResidueField ⊗[R] B)
              (algebraMap R s.ResidueField t)) * e d'') := by
                rw [e.commutes]
                ring
  obtain ⟨t', ht', htca⟩ :=
    exists_smul_mem_sup_map_of_one_tmul_mem_map s hfibre
  refine ⟨algebraMap R B t' * c, ?_, ?_⟩
  · intro hmem
    rcases hqprime.mem_or_mem hmem with htq | hcq'
    · exact ht' (by
        rw [hsq]
        exact htq)
    · exact hcq hcq'
  · simpa only [Algebra.smul_def, mul_assoc, hsq] using htca

end FibreDescent

/-! ## The affine local-global principle for ideal membership -/

section LocalGlobal

variable {X : Scheme.{u}} {U : X.Opens}

/-- **The affine local-global principle for ideal membership**: a section over an affine
open lies in an ideal `J ⊆ Γ(U)` as soon as its germ lies in the extension of `J` at
every point of `U`.  The colon ideal `(J : f)` cannot fit in a maximal ideal `q`: at
the point of `q` the stalk is the localization at `q`, where the germ hypothesis
produces `u, v ∉ q` with `(v·u)·f ∈ J`. -/
theorem IsAffineOpen.mem_of_germ_mem_map (hU : IsAffineOpen U) {J : Ideal Γ(X, U)}
    {f : Γ(X, U)}
    (h : ∀ (z : X) (hz : z ∈ U),
      (X.presheaf.germ U z hz).hom f ∈ J.map (X.presheaf.germ U z hz).hom) :
    f ∈ J := by
  by_cases hone : J.colon {f} = ⊤
  · have h1 : (1 : Γ(X, U)) ∈ J.colon {f} := hone ▸ Submodule.mem_top
    simpa using Submodule.mem_colon_singleton.mp h1
  obtain ⟨q, hqmax, hq⟩ := Ideal.exists_le_maximal _ hone
  set y : PrimeSpectrum Γ(X, U) := ⟨q, hqmax.isPrime⟩
  have hz : hU.fromSpec.base y ∈ U := by
    have h0 : hU.fromSpec.base y ∈ Set.range hU.fromSpec.base := Set.mem_range_self y
    rwa [hU.range_fromSpec] at h0
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec.base y)) :=
    X.presheaf.algebra_section_stalk ⟨hU.fromSpec.base y, hz⟩
  haveI hloc := hU.isLocalization_stalk' y hz
  have halg : (X.presheaf.germ U (hU.fromSpec.base y) hz).hom
      = algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec.base y)) := rfl
  have hmem := h (hU.fromSpec.base y) hz
  rw [halg] at hmem
  obtain ⟨⟨⟨b, hb⟩, u⟩, hbu⟩ :=
    (IsLocalization.mem_map_algebraMap_iff y.asIdeal.primeCompl _).mp hmem
  have hkey : algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec.base y)) (f * ↑u)
      = algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec.base y)) b := by
    rw [map_mul]
    exact hbu
  obtain ⟨v, hv⟩ := (IsLocalization.eq_iff_exists y.asIdeal.primeCompl _).mp hkey
  have hcolon : (↑v * ↑u : Γ(X, U)) ∈ J.colon {f} := by
    rw [Submodule.mem_colon_singleton]
    change (↑v * ↑u : Γ(X, U)) * f ∈ J
    have h2 : (↑v * ↑u : Γ(X, U)) * f = ↑v * (f * ↑u) := by ring
    rw [h2, hv]
    exact J.mul_mem_left _ hb
  have hvu : (↑v * ↑u : Γ(X, U)) ∈ y.asIdeal.primeCompl :=
    y.asIdeal.primeCompl.mul_mem v.2 u.2
  exact absurd (hq hcolon) hvu

end LocalGlobal

end AlgebraicGeometry
