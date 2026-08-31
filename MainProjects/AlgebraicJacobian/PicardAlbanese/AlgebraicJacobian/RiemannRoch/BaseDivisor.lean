/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.SectionSpaces

/-!
# DD-F brick 1 — the base divisor of a subspace of `H⁰(𝒪(A))`

The normalization vocabulary of the P-fib route (`informal/dat-d-worksheet.md` §3.3 F1,
`informal/dd-f-probe-verdict.md` inventory brick 1): for a subspace `T ⊆ H⁰(𝒪(A))` of the
global sections of a divisor sheaf with a nonzero element, the **base divisor**
`bd(T) = ∑ₓ min_{0 ≠ f ∈ T} (A + div f)ₓ · x` records, at each closed point, the deepest
common zero of the shifted divisors `A + div f ≥ 0`. Provided:

* `Scheme.baseDivisorAt` — the pointwise minimum, as a `ℕ`-valued `sInf` (well-defined
  since `T ⊆ H⁰(𝒪(A))` makes every `A + div f` effective);
* `Scheme.baseDivisor` — the assembled Weil divisor, finitely supported because it is
  bounded by any one `A + div f₀`;
* `baseDivisor_nonneg`, `coeffAt_baseDivisor` — effectivity and the pointwise value;
* `baseDivisorAt_le_coeffAt` — the lower-bound property (`bd(T) ≤ A + div f` for every
  nonzero `f ∈ T`);
* `exists_coeffAt_eq_baseDivisorAt` — the **achiever**: at every closed point some
  nonzero `f ∈ T` attains the minimum (`Nat.sInf_mem`);
* `le_divisorSections_sub_baseDivisor` — `T ⊆ H⁰(𝒪(A − bd T))`;
* `exists_achiever_baseDivisor_sub` — **no residual base point**: relative to
  `A − bd T`, the subspace `T` has an exact-order element at every closed point. This is
  the `hbpf` input of the bpf-span lemma (F3-core).

Everything is `ord`/`coeffAt` calculus on `mem_divisorSections_top_iff`; no cohomology.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.Scheme.functionFieldOverModule
  AlgebraicGeometry.Scheme.overModule

namespace AlgebraicGeometry

open Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-! ## The pointwise minimum -/

/-- The candidate multiplicities of the base divisor of `T` relative to `A` at the closed
point `p`: the values `(A + div f)ₚ` over nonzero `f ∈ T`, truncated to `ℕ` (faithful once
`T ⊆ H⁰(𝒪(A))`, which makes every `A + div f` effective). -/
def Scheme.baseDivisorSet (T : Submodule K X.functionField) (A : X.CurveDivisor)
    (p : {x : X // x ≠ genericPoint X}) : Set ℕ :=
  {n : ℕ | ∃ (f : X.functionField) (_ : f ∈ T) (hf : f ≠ 0),
    (coeffAt p.2
      (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf))).toNat = n}

/-- **The base multiplicity of `T` relative to `A` at a closed point**: the minimum of
`(A + div f)ₚ` over nonzero `f ∈ T`. -/
noncomputable def Scheme.baseDivisorAt (T : Submodule K X.functionField)
    (A : X.CurveDivisor) (p : {x : X // x ≠ genericPoint X}) : ℕ :=
  sInf (Scheme.baseDivisorSet K T A p)

lemma Scheme.baseDivisorSet_nonempty {T : Submodule K X.functionField}
    (A : X.CurveDivisor) (hT : ∃ f ∈ T, f ≠ 0) (p : {x : X // x ≠ genericPoint X}) :
    (Scheme.baseDivisorSet K T A p).Nonempty := by
  obtain ⟨f, hfT, hf⟩ := hT
  exact ⟨_, f, hfT, hf, rfl⟩

/-! ## The assembled base divisor -/

/-- **The base divisor `bd(T)` of a subspace `T` relative to `A`**: the Weil divisor of
pointwise base multiplicities. Finitely supported because `0 ≤ bd(T)ₚ ≤ (A + div f₀)ₚ`
for the chosen nonzero `f₀ ∈ T`. -/
noncomputable def Scheme.baseDivisor (T : Submodule K X.functionField)
    (A : X.CurveDivisor) (hT : ∃ f ∈ T, f ≠ 0) : X.CurveDivisor :=
  Finsupp.onFinset
    (toFinsupp (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K))
      (Units.mk0 hT.choose hT.choose_spec.2))).support
    (fun p => (Scheme.baseDivisorAt K T A p : ℤ))
    (fun p hp => by
      rw [Finsupp.mem_support_iff]
      intro hzero
      apply hp
      have hle : Scheme.baseDivisorAt K T A p
          ≤ (coeffAt p.2 (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K))
              (Units.mk0 hT.choose hT.choose_spec.2))).toNat :=
        Nat.sInf_le ⟨hT.choose, hT.choose_spec.1, hT.choose_spec.2, rfl⟩
      have hc : coeffAt p.2 (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K))
          (Units.mk0 hT.choose hT.choose_spec.2)) = 0 := hzero
      omega)

/-- The pointwise value of the base divisor is the base multiplicity. -/
lemma Scheme.coeffAt_baseDivisor {T : Submodule K X.functionField} {A : X.CurveDivisor}
    (hT : ∃ f ∈ T, f ≠ 0) {x : X} (hx : x ≠ genericPoint X) :
    coeffAt hx (Scheme.baseDivisor K T A hT)
      = (Scheme.baseDivisorAt K T A ⟨x, hx⟩ : ℤ) :=
  rfl

/-- **The base divisor is effective.** -/
lemma Scheme.baseDivisor_nonneg {T : Submodule K X.functionField} {A : X.CurveDivisor}
    (hT : ∃ f ∈ T, f ≠ 0) : 0 ≤ Scheme.baseDivisor K T A hT := by
  refine CurveDivisor.le_iff_coeffAt.mpr (fun x hx => ?_)
  rw [CurveDivisor.coeffAt_zero, Scheme.coeffAt_baseDivisor K hT hx]
  positivity

/-! ## The lower-bound and achiever properties -/

/-- Under `T ⊆ H⁰(𝒪(A))`, the shifted divisor `A + div f` of a nonzero `f ∈ T` is
effective at every closed point. -/
lemma Scheme.coeffAt_add_divOf_nonneg {T : Submodule K X.functionField}
    {A : X.CurveDivisor} (hTA : T ≤ divisorSections K A ⊤) {f : X.functionField}
    (hfT : f ∈ T) (hf : f ≠ 0) {x : X} (hx : x ≠ genericPoint X) :
    0 ≤ coeffAt hx
      (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) := by
  have hmem := hTA hfT
  rw [mem_divisorSections_top_iff K hf] at hmem
  have h := CurveDivisor.le_iff_coeffAt.mp hmem x hx
  rwa [CurveDivisor.coeffAt_zero] at h

/-- **The lower-bound property of the base divisor**: `bd(T) ≤ A + div f` pointwise, for
every nonzero `f ∈ T`. -/
lemma Scheme.baseDivisorAt_le_coeffAt {T : Submodule K X.functionField}
    {A : X.CurveDivisor} (hTA : T ≤ divisorSections K A ⊤) {f : X.functionField}
    (hfT : f ∈ T) (hf : f ≠ 0) {x : X} (hx : x ≠ genericPoint X) :
    (Scheme.baseDivisorAt K T A ⟨x, hx⟩ : ℤ)
      ≤ coeffAt hx
          (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) := by
  have h1 : Scheme.baseDivisorAt K T A ⟨x, hx⟩
      ≤ (coeffAt hx
          (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf))).toNat :=
    Nat.sInf_le ⟨f, hfT, hf, rfl⟩
  have h2 := Scheme.coeffAt_add_divOf_nonneg K hTA hfT hf hx
  omega

/-- **The achiever**: at every closed point, some nonzero `f ∈ T` attains the base
multiplicity: `(A + div f)ₓ = bd(T)ₓ`. -/
lemma Scheme.exists_coeffAt_eq_baseDivisorAt {T : Submodule K X.functionField}
    {A : X.CurveDivisor} (hTA : T ≤ divisorSections K A ⊤) (hT : ∃ f ∈ T, f ≠ 0)
    {x : X} (hx : x ≠ genericPoint X) :
    ∃ (f : X.functionField) (_ : f ∈ T) (hf : f ≠ 0),
      coeffAt hx (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf))
        = (Scheme.baseDivisorAt K T A ⟨x, hx⟩ : ℤ) := by
  have hmem : Scheme.baseDivisorAt K T A ⟨x, hx⟩ ∈ Scheme.baseDivisorSet K T A ⟨x, hx⟩ :=
    Nat.sInf_mem (Scheme.baseDivisorSet_nonempty K A hT ⟨x, hx⟩)
  obtain ⟨f, hfT, hf, heq⟩ := hmem
  refine ⟨f, hfT, hf, ?_⟩
  have h2 := Scheme.coeffAt_add_divOf_nonneg K hTA hfT hf hx
  omega

/-! ## The normalization: `T ⊆ H⁰(𝒪(A − bd T))` with no residual base point -/

/-- **The base-divisor normalization**: `T ⊆ H⁰(𝒪(A − bd T))` — every nonzero `f ∈ T`
has `(A − bd T) + div f ≥ 0` because `bd(T)` is a pointwise minimum. -/
theorem Scheme.le_divisorSections_sub_baseDivisor {T : Submodule K X.functionField}
    {A : X.CurveDivisor} (hTA : T ≤ divisorSections K A ⊤) (hT : ∃ f ∈ T, f ≠ 0) :
    T ≤ divisorSections K (A - Scheme.baseDivisor K T A hT) ⊤ := by
  intro f hfT
  by_cases hf : f = 0
  · subst hf
    exact Submodule.zero_mem _
  · rw [mem_divisorSections_top_iff K hf]
    refine CurveDivisor.le_iff_coeffAt.mpr (fun x hx => ?_)
    rw [CurveDivisor.coeffAt_zero, CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub,
      Scheme.coeffAt_baseDivisor K hT hx]
    have h4 := Scheme.baseDivisorAt_le_coeffAt K hTA hfT hf hx
    rw [CurveDivisor.coeffAt_add] at h4
    omega

/-- **No residual base point** (the `hbpf` input of the bpf-span lemma): relative to the
normalized divisor `A − bd T`, the subspace `T` has an exact-order element at every
closed point: `((A − bd T) + div f)ₓ = 0`. -/
theorem Scheme.exists_achiever_baseDivisor_sub {T : Submodule K X.functionField}
    {A : X.CurveDivisor} (hTA : T ≤ divisorSections K A ⊤) (hT : ∃ f ∈ T, f ≠ 0)
    {x : X} (hx : x ≠ genericPoint X) :
    ∃ (f : X.functionField) (_ : f ∈ T) (hf : f ≠ 0),
      coeffAt hx ((A - Scheme.baseDivisor K T A hT)
        + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) = 0 := by
  obtain ⟨f, hfT, hf, heq⟩ := Scheme.exists_coeffAt_eq_baseDivisorAt K hTA hT hx
  refine ⟨f, hfT, hf, ?_⟩
  rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub,
    Scheme.coeffAt_baseDivisor K hT hx]
  rw [CurveDivisor.coeffAt_add] at heq
  omega

/-- **No residual base multiplicity after normalization**: once the base divisor of a
nonzero subspace `T ≤ H⁰(𝒪(A))` is removed from `A`, the same subspace has base
multiplicity zero at every closed point. -/
theorem Scheme.baseDivisorAt_sub_baseDivisor_eq_zero
    {T : Submodule K X.functionField} {A : X.CurveDivisor}
    (hTA : T ≤ divisorSections K A ⊤) (hT : ∃ f ∈ T, f ≠ 0)
    {x : X} (hx : x ≠ genericPoint X) :
    Scheme.baseDivisorAt K T (A - Scheme.baseDivisor K T A hT) ⟨x, hx⟩ = 0 := by
  have hnormalized := Scheme.le_divisorSections_sub_baseDivisor K hTA hT
  obtain ⟨f, hfT, hf, hcoeff⟩ := Scheme.exists_achiever_baseDivisor_sub K hTA hT hx
  have hle := Scheme.baseDivisorAt_le_coeffAt K hnormalized hfT hf hx
  rw [hcoeff] at hle
  omega

end AlgebraicGeometry
