/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.FLVFiberToolkit
import AlgebraicJacobian.Cohomology.TwoCover
import AlgebraicJacobian.Cohomology.AffineVanishingQcoh

/-!
# FLV-1 — the twist lattices of `𝒪(D + n·F)` on the π-two-cover

This is the Wave-4 **fibrewise-large-twist-vanishing** lattice brick (`informal/w4-flv-worksheet.md`
§2.1, brick FLV-1). It records, as *submodule identities in the function field* `K(Y)` (the D1
discipline), how the section lattices of the twisted divisor sheaf `𝒪(D + n·F)` behave on the
pinned affine two-cover `V₀ = π⁻¹ D₊(X₀)`, `V₁ = π⁻¹ D₊(X₁)`, where `F = fiberWeilDivisor π` is the
fiber divisor of FLV-0 and `u = fiberCoordUnit π` its equation:

* over `V₁` and over the overlap `V₀ ⊓ V₁` the lattice is **unchanged** (`= 𝒪(D)`), since `F`
  is supported off `V₁` (`divisorSections_add_nsmul_fiberWeilDivisor_chart₁`,
  `..._overlap`);
* over `V₀` the lattice is `u⁻ⁿ · 𝒪(D)(V₀)` (the `mulEquivDivisorSheaf` mechanism, section level:
  `divisorSections_add_nsmul_fiberWeilDivisor_chart₀`), a submodule that **grows** with `n`.

From these the two-cover Čech `H¹` denominators
`Aₙ := 𝒪(D)(V₁)|N ⊔ (u⁻ⁿ · 𝒪(D)(V₀))|N` inside `N := 𝒪(D)(V₀ ⊓ V₁)` form an **increasing chain**
(`fiberLattice_mono`) that **exhausts** `N` (`iSup_fiberLattice`) — the pole-clearing at the finite
fiber over `[1 : 0]` — which is the endgame the exhaustion brick (FLV-3) consumes.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

section Lattice

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  (π : Y ⟶ P1 K) [IsDominant π]

/-! ## Coefficient bookkeeping for the twist -/

/-- The coefficient of an `ℕ`-multiple of a divisor scales linearly. -/
private lemma coeffAt_nsmul (n : ℕ) (D : Y.CurveDivisor) {x : Y} (hx : x ≠ genericPoint Y) :
    coeffAt hx (n • D) = (n : ℤ) * coeffAt hx D := by
  induction n with
  | zero => rw [zero_smul, CurveDivisor.coeffAt_zero, Nat.cast_zero, zero_mul]
  | succ m ih => rw [succ_nsmul, CurveDivisor.coeffAt_add, ih, Nat.cast_succ]; ring

/-- The divisor bound depends only on the coefficient at the point. -/
private lemma divisorBound_congr {A B : Y.CurveDivisor} {x : Y} (hx : x ≠ genericPoint Y)
    (h : coeffAt hx A = coeffAt hx B) : Scheme.divisorBound A hx = Scheme.divisorBound B hx :=
  congrArg (fun m : Multiplicative ℤ => (m : WithZero (Multiplicative ℤ)))
    (congrArg Multiplicative.ofAdd h)

/-- On `V₁` the twisted divisor `D + n·F` has the same coefficients as `D`: `F` vanishes there. -/
private lemma coeffAt_add_nsmul_of_mem_chart₁ (D : Y.CurveDivisor) (n : ℕ) {x : Y}
    (hx : x ≠ genericPoint Y) (hxV₁ : x ∈ fiberChart₁ π) :
    coeffAt hx (D + n • fiberWeilDivisor π) = coeffAt hx D := by
  rw [CurveDivisor.coeffAt_add, coeffAt_nsmul,
    fiberWeilDivisor_coeffAt_of_mem_chart₁ π hx hxV₁, mul_zero, add_zero]

/-! ## The constant lattices: over `V₁` and over the overlap -/

/-- **The lattice over `V₁` is unchanged by the twist.** Since `F` is supported off `V₁`, the
sections of `𝒪(D + n·F)` over `V₁ = π⁻¹ D₊(X₁)` coincide with those of `𝒪(D)`. -/
theorem divisorSections_add_nsmul_fiberWeilDivisor_chart₁ (D : Y.CurveDivisor) (n : ℕ) :
    divisorSections K (D + n • fiberWeilDivisor π) (fiberChart₁ π)
      = divisorSections K D (fiberChart₁ π) := by
  have hne : (fiberChart₁ π : Set Y).Nonempty :=
    ⟨genericPoint Y, (genericPoint_mem_preimage_inf π).2⟩
  rw [divisorSections_of_nonempty K hne, divisorSections_of_nonempty K hne]
  have hbound : ∀ (x : Y) (hx : x ≠ genericPoint Y), x ∈ fiberChart₁ π →
      Scheme.divisorBound (D + n • fiberWeilDivisor π) hx = Scheme.divisorBound D hx :=
    fun x hx hxV₁ => divisorBound_congr hx (coeffAt_add_nsmul_of_mem_chart₁ π D n hx hxV₁)
  refine Submodule.ext (fun g => ?_)
  rw [mem_boundedSections, mem_boundedSections]
  constructor
  · intro h x hx hxU; rw [← hbound x hx hxU]; exact h x hx hxU
  · intro h x hx hxU; rw [hbound x hx hxU]; exact h x hx hxU

/-- **The lattice over the overlap is unchanged by the twist.** The overlap `V₀ ⊓ V₁` lies in `V₁`,
where `F` vanishes, so `𝒪(D + n·F)(V₀ ⊓ V₁) = 𝒪(D)(V₀ ⊓ V₁) =: N`, the fixed ambient of the Čech
`H¹` quotient. -/
theorem divisorSections_add_nsmul_fiberWeilDivisor_overlap (D : Y.CurveDivisor) (n : ℕ) :
    divisorSections K (D + n • fiberWeilDivisor π) (fiberChart₀ π ⊓ fiberChart₁ π)
      = divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π) := by
  have hne : ((fiberChart₀ π ⊓ fiberChart₁ π : Y.Opens) : Set Y).Nonempty :=
    ⟨genericPoint Y, genericPoint_mem_preimage_inf π⟩
  rw [divisorSections_of_nonempty K hne, divisorSections_of_nonempty K hne]
  have hbound : ∀ (x : Y) (hx : x ≠ genericPoint Y), x ∈ fiberChart₀ π ⊓ fiberChart₁ π →
      Scheme.divisorBound (D + n • fiberWeilDivisor π) hx = Scheme.divisorBound D hx :=
    fun x hx hxU => divisorBound_congr hx (coeffAt_add_nsmul_of_mem_chart₁ π D n hx hxU.2)
  refine Submodule.ext (fun g => ?_)
  rw [mem_boundedSections, mem_boundedSections]
  constructor
  · intro h x hx hxU; rw [← hbound x hx hxU]; exact h x hx hxU
  · intro h x hx hxU; rw [hbound x hx hxU]; exact h x hx hxU

/-! ## The growing lattice over `V₀` -/

/-- The classical order of `v⁻¹` is the negative of that of `v`, coefficient-wise. -/
private lemma coeffAt_divOf_inv (v : Y.functionFieldˣ) {x : Y} (hx : x ≠ genericPoint Y) :
    coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) v⁻¹) =
      - coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) v) := by
  have h : Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) v⁻¹
      + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) v = 0 := by
    rw [← Scheme.divOf_mul (Y ↘ Spec (CommRingCat.of K)), inv_mul_cancel,
      Scheme.divOf_one (Y ↘ Spec (CommRingCat.of K))]
  have hc := congrArg (coeffAt hx) h
  rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_zero] at hc
  linarith

/-- The classical order of `vⁿ` scales linearly. -/
private lemma coeffAt_divOf_pow (v : Y.functionFieldˣ) (n : ℕ) {x : Y} (hx : x ≠ genericPoint Y) :
    coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (v ^ n)) =
      (n : ℤ) * coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) v) := by
  induction n with
  | zero => rw [pow_zero, Scheme.divOf_one, CurveDivisor.coeffAt_zero, Nat.cast_zero, zero_mul]
  | succ m ih =>
    rw [pow_succ, Scheme.divOf_mul, CurveDivisor.coeffAt_add, ih, Nat.cast_succ]; ring

/-- **The lattice over `V₀` grows as `u⁻ⁿ · 𝒪(D)(V₀)`.** Multiplication by `u⁻ⁿ = fiberCoordUnit π
⁻ⁿ` carries `𝒪(D)(V₀)` isomorphically onto `𝒪(D + n·F)(V₀)`: the `mulEquivDivisorSheaf` mechanism
at the section level, the source of the growing denominator of the Čech `H¹` quotient. -/
theorem divisorSections_add_nsmul_fiberWeilDivisor_chart₀ (D : Y.CurveDivisor) (n : ℕ) :
    divisorSections K (D + n • fiberWeilDivisor π) (fiberChart₀ π)
      = Submodule.map (mulByUnit K ((fiberCoordUnit π)⁻¹ ^ n)).toLinearMap
          (divisorSections K D (fiberChart₀ π)) := by
  have hne : (fiberChart₀ π : Set Y).Nonempty :=
    ⟨genericPoint Y, (genericPoint_mem_preimage_inf π).1⟩
  set w : Y.functionFieldˣ := (fiberCoordUnit π)⁻¹ ^ n with hw
  -- coefficientwise, `D + n·F` agrees with `D - div w` on `V₀`.
  have hcoeff : ∀ (x : Y) (hx : x ≠ genericPoint Y), x ∈ fiberChart₀ π →
      coeffAt hx (D + n • fiberWeilDivisor π)
        = coeffAt hx (D - Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) w) := by
    intro x hx hxV₀
    rw [CurveDivisor.coeffAt_add, coeffAt_nsmul, CurveDivisor.coeffAt_sub, hw,
      coeffAt_divOf_pow, coeffAt_divOf_inv,
      fiberWeilDivisor_coeffAt_of_mem_chart₀ π hx hxV₀]
    ring
  -- hence the two bounded lattices coincide.
  have hbdd : Scheme.boundedSections K (D + n • fiberWeilDivisor π) (fiberChart₀ π)
      = Scheme.boundedSections K (D - Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) w)
        (fiberChart₀ π) := by
    refine Submodule.ext (fun g => ?_)
    rw [Scheme.mem_boundedSections, Scheme.mem_boundedSections]
    refine forall_congr' (fun x => forall_congr' (fun hx => imp_congr_right (fun hxV₀ => ?_)))
    rw [divisorBound_congr hx (hcoeff x hx hxV₀)]
  rw [divisorSections_of_nonempty K hne, hbdd]
  -- multiplication by `w` identifies `𝒪(D - div w)(V₀)` with `w · 𝒪(D)(V₀)`.
  refine Submodule.ext (fun y => ?_)
  rw [Submodule.mem_map]
  constructor
  · intro hy
    refine ⟨(↑w⁻¹ : Y.functionField) * y, ?_, ?_⟩
    · rw [divisorSections_of_nonempty K hne, ← Scheme.mem_boundedSections_mul_iff K w D,
        ← mul_assoc, Units.mul_inv, one_mul]
      exact hy
    · simp only [Scheme.mulByUnit_apply, LinearEquiv.coe_coe, ← mul_assoc, Units.mul_inv, one_mul]
  · rintro ⟨h, hh, rfl⟩
    rw [divisorSections_of_nonempty K hne] at hh
    simp only [Scheme.mulByUnit_apply, LinearEquiv.coe_coe]
    exact (Scheme.mem_boundedSections_mul_iff K w D (h : Y.functionField)).mpr hh

/-! ## The Čech-`H¹` denominator lattice `Aₙ` and its ladder -/

/-- **The two-cover Čech `H¹` denominator lattice** `Aₙ` of `𝒪(D + n·F)`: the join, inside the
function field, of the section lattices over `V₀` and `V₁`. As submodules of `N = 𝒪(D)(V₀ ⊓ V₁)`
(`fiberLattice_le_overlap`) these are exactly the images of the restriction maps of the two-cover
Čech complex, so `N ⧸ Aₙ` is the two-cover `H¹` (the identification the exhaustion endgame,
FLV-3, consumes). -/
noncomputable def fiberLattice (D : Y.CurveDivisor) (n : ℕ) : Submodule K Y.functionField :=
  divisorSections K (D + n • fiberWeilDivisor π) (fiberChart₀ π)
    ⊔ divisorSections K (D + n • fiberWeilDivisor π) (fiberChart₁ π)

/-- **`Aₙ` lies in the ambient `N = 𝒪(D)(V₀ ⊓ V₁)`.** Both section lattices restrict into the
overlap sections, which the twist leaves fixed (`..._overlap`). -/
theorem fiberLattice_le_overlap (D : Y.CurveDivisor) (n : ℕ) :
    fiberLattice π D n ≤ divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π) := by
  have hov : ((fiberChart₀ π ⊓ fiberChart₁ π : Y.Opens) : Set Y).Nonempty :=
    ⟨genericPoint Y, genericPoint_mem_preimage_inf π⟩
  refine sup_le ?_ ?_
  · refine (divisorSections_antitone K inf_le_left hov).trans ?_
    rw [divisorSections_add_nsmul_fiberWeilDivisor_overlap π D n]
  · refine (divisorSections_antitone K inf_le_right hov).trans ?_
    rw [divisorSections_add_nsmul_fiberWeilDivisor_overlap π D n]

/-- **The lattice ladder is increasing.** `Aₙ ≤ Aₙ₊₁`: over `V₀` the twist bound relaxes (`F` is
effective, so `D + n·F ≤ D + (n+1)·F`), and over `V₁` the lattice is constant. -/
theorem fiberLattice_mono (D : Y.CurveDivisor) (n : ℕ) :
    fiberLattice π D n ≤ fiberLattice π D (n + 1) := by
  have hle : D + n • fiberWeilDivisor π ≤ D + (n + 1) • fiberWeilDivisor π := by
    refine Finsupp.le_def.mpr (fun p => ?_)
    change coeffAt p.2 (D + n • fiberWeilDivisor π)
      ≤ coeffAt p.2 (D + (n + 1) • fiberWeilDivisor π)
    rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_add, coeffAt_nsmul, coeffAt_nsmul]
    have hF : 0 ≤ coeffAt p.2 (fiberWeilDivisor π) := by
      rw [fiberWeilDivisor_coeffAt π p.2]; exact le_max_right _ _
    have hmul : (n : ℤ) * coeffAt p.2 (fiberWeilDivisor π)
        ≤ ((n : ℤ) + 1) * coeffAt p.2 (fiberWeilDivisor π) :=
      mul_le_mul_of_nonneg_right (by linarith) hF
    push_cast
    linarith
  refine sup_le_sup ?_ ?_
  · exact divisorSections_mono K hle (fiberChart₀ π)
  · exact divisorSections_mono K hle (fiberChart₁ π)

/-! ## Exhaustion of `N` by the ladder -/

/-- The divisor bound `≤`-comparison at a point reduces to the pointwise coefficient
`≤`-comparison in `ℤ`. -/
private lemma divisorBound_le_iff {A B : Y.CurveDivisor} {x : Y} (hx : x ≠ genericPoint Y) :
    Scheme.divisorBound A hx ≤ Scheme.divisorBound B hx ↔ coeffAt hx A ≤ coeffAt hx B := by
  simp only [Scheme.divisorBound, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  rfl

/-- Membership of a *nonzero* rational function `s` in a bounded lattice, read through its
principal divisor: `s ∈ 𝒪(A)(U)` iff `-div(s) ≤ A` at every point of `U`. -/
private lemma mem_boundedSections_unit_iff (s : Y.functionFieldˣ) (A : Y.CurveDivisor)
    (U : Y.Opens) :
    (s : Y.functionField) ∈ Scheme.boundedSections K A U ↔
      ∀ (x : Y) (hx : x ≠ genericPoint Y), x ∈ U →
        - coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) s) ≤ coeffAt hx A := by
  rw [Scheme.mem_boundedSections]
  refine forall_congr' (fun x => forall_congr' (fun hx => imp_congr_right (fun _ => ?_)))
  rw [Scheme.ord_val_eq K s hx, divisorBound_le_iff hx, CurveDivisor.coeffAt_neg]

/-- On `V₀` the twist coefficient is that of `div u` (nonnegative), and `≥ 1` off `V₁`. -/
private lemma coeffAt_add_nsmul_chart₀ (D : Y.CurveDivisor) (n : ℕ) {x : Y}
    (hx : x ≠ genericPoint Y) (_hxV₀ : x ∈ fiberChart₀ π) :
    coeffAt hx (D + n • fiberWeilDivisor π) =
      coeffAt hx D + (n : ℤ) * coeffAt hx (fiberWeilDivisor π) := by
  rw [CurveDivisor.coeffAt_add, coeffAt_nsmul]

/-- **Exhaustion.** The increasing ladder `Aₙ` fills the ambient overlap lattice
`N = 𝒪(D)(V₀ ⊓ V₁)`: any overlap section clears its finitely many poles on the fiber over
`[1 : 0]` after multiplying by a large enough power of the fiber equation `u`. This is the
pole-clearing endgame the exhaustion brick (FLV-3) turns into `H¹`-vanishing. -/
theorem iSup_fiberLattice (D : Y.CurveDivisor) :
    ⨆ n, fiberLattice π D n = divisorSections K D (fiberChart₀ π ⊓ fiberChart₁ π) := by
  classical
  refine le_antisymm (iSup_le (fun n => fiberLattice_le_overlap π D n)) ?_
  have hovne : ((fiberChart₀ π ⊓ fiberChart₁ π : Y.Opens) : Set Y).Nonempty :=
    ⟨genericPoint Y, genericPoint_mem_preimage_inf π⟩
  intro s hs
  by_cases hs0 : s = 0
  · rw [hs0]; exact Submodule.zero_mem _
  -- treat `s` as a unit and read `N`-membership as a pointwise bound on `-div s`.
  set s' : Y.functionFieldˣ := Units.mk0 s hs0 with hs'def
  have hsval : (s' : Y.functionField) = s := rfl
  rw [divisorSections_of_nonempty K hovne] at hs
  have hsN := (mem_boundedSections_unit_iff s' D (fiberChart₀ π ⊓ fiberChart₁ π)).mp (hsval ▸ hs)
  -- the finite set of points, and the per-point pole-clearing budget.
  set Z : Finset {x : Y // x ≠ genericPoint Y} :=
    (toFinsupp D).support ∪ (toFinsupp (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) s')).support
    with hZ
  set g : {x : Y // x ≠ genericPoint Y} → ℕ := fun p =>
    (- coeffAt p.2 (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) s') - coeffAt p.2 D).toNat with hg
  set n : ℕ := Z.sup g with hn
  -- `s ∈ Aₙ`: it lies in the `V₀` lattice.
  refine Submodule.mem_iSup_of_mem n (Submodule.mem_sup_left ?_)
  have hV₀ne : (fiberChart₀ π : Set Y).Nonempty :=
    ⟨genericPoint Y, (genericPoint_mem_preimage_inf π).1⟩
  rw [divisorSections_of_nonempty K hV₀ne, ← hsval,
    mem_boundedSections_unit_iff s' (D + n • fiberWeilDivisor π) (fiberChart₀ π)]
  intro x hx hxV₀
  rw [coeffAt_add_nsmul_chart₀ π D n hx hxV₀]
  by_cases hxV₁ : x ∈ fiberChart₁ π
  · -- overlap point: `F` vanishes, use the `N`-bound directly.
    have hF0 : coeffAt hx (fiberWeilDivisor π) = 0 :=
      fiberWeilDivisor_coeffAt_of_mem_chart₁ π hx hxV₁
    rw [hF0, mul_zero, add_zero]
    exact hsN x hx ⟨hxV₀, hxV₁⟩
  · -- fiber point: `coeffAt F ≥ 1`, so a large `n` clears the pole.
    have hF1 : 1 ≤ coeffAt hx (fiberWeilDivisor π) := by
      rw [fiberWeilDivisor_coeffAt_of_mem_chart₀ π hx hxV₀]
      exact one_le_fiberCoordUnit_coeffAt_divOf_of_notMem_chart₁ π hx hxV₀ hxV₁
    by_cases hxZ : (⟨x, hx⟩ : {q : Y // q ≠ genericPoint Y}) ∈ Z
    · have hle : g ⟨x, hx⟩ ≤ n := by rw [hn]; exact Finset.le_sup hxZ
      have hle2 : (- coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) s')
          - coeffAt hx D).toNat ≤ n := hle
      have h1 : - coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) s') - coeffAt hx D
          ≤ (n : ℤ) := le_trans (Int.self_le_toNat _) (by exact_mod_cast hle2)
      have h2 : (n : ℤ) ≤ (n : ℤ) * coeffAt hx (fiberWeilDivisor π) := by
        nlinarith [hF1, Nat.cast_nonneg (α := ℤ) n]
      linarith
    · -- outside the support: both coefficients vanish.
      have hD0 : coeffAt hx D = 0 := by
        by_contra h; exact hxZ (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h))
      have hs0' : coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) s') = 0 := by
        by_contra h; exact hxZ (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr h))
      rw [hD0, hs0', neg_zero]
      have : (0 : ℤ) ≤ (n : ℤ) * coeffAt hx (fiberWeilDivisor π) :=
        mul_nonneg (Nat.cast_nonneg n) (by linarith)
      linarith

end Lattice

end AlgebraicGeometry
