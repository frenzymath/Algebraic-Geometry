/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4TwoLattice
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The inverse-pair Laurent ladder

The two-lattice quotient engine is phrased using a Laurent-polynomial action.  In
geometric applications the action is usually presented instead by two inverse
sections `t` and `u` of an overlap ring.  This file proves the conversion: a
localization statement gives a two-sided ladder spanning the overlap, and a
finite ladder window then generates the quotient.
-/

set_option autoImplicit false

universe u

open Submodule

namespace Hartshorne
namespace LaurentLadder

variable {k : Type u} [Field k] {M : Type u} [CommRing M] [Algebra k M]

/-- Iterated stability: a submodule stable under multiplication by `t` is stable
under every natural power of `t`. -/
lemma pow_mul_mem {N : Submodule k M} {t : M} (h : ∀ a ∈ N, t * a ∈ N)
    (n : ℕ) {a : M} (ha : a ∈ N) : t ^ n * a ∈ N := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    have hrw : t ^ (n + 1) * a = t * (t ^ n * a) := by ring
    rw [hrw]
    exact h _ ih

/-- If `t` and `u` are inverse, a localization statement turns the two
one-sided power ladders into a spanning set. -/
theorem span_ladder_of_pow_mul_mem_span {t u : M} (htu : t * u = 1) (s : Set M)
    (H : ∀ m : M, ∃ n : ℕ,
      t ^ n * m ∈ Submodule.span k (⋃ j : ℕ, (fun z : M => t ^ j * z) '' s)) :
    ⊤ ≤ Submodule.span k
      ((⋃ j : ℕ, (fun z : M => t ^ j * z) '' s) ∪
        (⋃ j : ℕ, (fun z : M => u ^ j * z) '' s)) := by
  have hpow : ∀ n : ℕ, u ^ n * t ^ n = 1 := fun n => by
    rw [← mul_pow, mul_comm u t, htu, one_pow]
  intro m _
  obtain ⟨n, hn⟩ := H m
  have hm : m = u ^ n * (t ^ n * m) := by
    rw [← mul_assoc, hpow, one_mul]
  have hmem : u ^ n * (t ^ n * m) ∈
      Submodule.map (LinearMap.mulLeft k (u ^ n))
        (Submodule.span k (⋃ j : ℕ, (fun z : M => t ^ j * z) '' s)) :=
    Submodule.mem_map_of_mem hn
  rw [Submodule.map_span, ← hm] at hmem
  refine Submodule.span_le.mpr ?_ hmem
  rintro _ ⟨z, hz, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_image] at hz
  obtain ⟨j, a, ha, rfl⟩ := hz
  simp only [LinearMap.mulLeft_apply]
  rcases le_or_gt n j with hnj | hjn
  · have key : u ^ n * (t ^ j * a) = t ^ (j - n) * a := by
      have hj : t ^ j = t ^ n * t ^ (j - n) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        u ^ n * (t ^ j * a) =
            (u ^ n * t ^ n) * (t ^ (j - n) * a) := by rw [hj]; ring
        _ = t ^ (j - n) * a := by rw [hpow, one_mul]
    rw [key]
    exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_iUnion.mpr
      ⟨j - n, Set.mem_image_of_mem _ ha⟩))
  · have key : u ^ n * (t ^ j * a) = u ^ (n - j) * a := by
      have hn' : u ^ n = u ^ (n - j) * u ^ j := by
        rw [← pow_add]
        congr 1
        omega
      calc
        u ^ n * (t ^ j * a) =
            u ^ (n - j) * ((u ^ j * t ^ j) * a) := by rw [hn']; ring
        _ = u ^ (n - j) * a := by rw [hpow, one_mul]
    rw [key]
    exact Submodule.subset_span (Set.mem_union_right _ (Set.mem_iUnion.mpr
      ⟨n - j, Set.mem_image_of_mem _ ha⟩))

/-- A finite two-sided ladder gives a finite quotient by two stable submodules.
This is the inverse-pair form of the Laurent two-lattice argument and is useful
when the Laurent action comes from actual coordinate sections. -/
theorem moduleFinite_quotient_of_laurent_pair {t u : M}
    {N₀ N₁ : Submodule k M}
    (h₀ : ∀ a ∈ N₀, t * a ∈ N₀) (h₁ : ∀ a ∈ N₁, u * a ∈ N₁)
    {s : Set M} (hs : s.Finite) (hsN₀ : s ⊆ N₀)
    (hspan : ⊤ ≤ Submodule.span k
      ((⋃ j : ℕ, (fun z : M => t ^ j * z) '' s) ∪
        (⋃ j : ℕ, (fun z : M => u ^ j * z) '' s)))
    (hext : ∀ a ∈ s, ∃ n : ℕ, u ^ n * a ∈ N₁) :
    Module.Finite k (M ⧸ (N₀ ⊔ N₁)) := by
  classical
  set B : M → ℕ := fun a => if h : a ∈ s then (hext a h).choose else 0 with hB
  set N : ℕ := hs.toFinset.sup B with hNdef
  have hBmem : ∀ a ∈ s, u ^ B a * a ∈ N₁ := by
    intro a ha
    simp only [hB, dif_pos ha]
    exact (hext a ha).choose_spec
  have hN₁ : ∀ a ∈ s, ∀ n : ℕ, B a ≤ n → u ^ n * a ∈ N₁ := by
    intro a ha n hn
    have hrw : u ^ n * a = u ^ (n - B a) * (u ^ B a * a) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    rw [hrw]
    exact pow_mul_mem h₁ _ (hBmem a ha)
  set T : Set M := ⋃ j ∈ Finset.range N, (fun z : M => u ^ j * z) '' s with hT
  have hTfin : T.Finite :=
    Set.Finite.biUnion (Finset.range N).finite_toSet fun j _ => hs.image _
  have hkey : N₀ ⊔ N₁ ⊔ Submodule.span k T = ⊤ := by
    refine le_antisymm le_top (hspan.trans (Submodule.span_le.mpr ?_))
    rintro z (hz | hz) <;> simp only [Set.mem_iUnion, Set.mem_image] at hz
    · obtain ⟨j, a, ha, rfl⟩ := hz
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (pow_mul_mem h₀ j
        (hsN₀ ha)))
    · obtain ⟨j, a, ha, rfl⟩ := hz
      rcases lt_or_ge j N with hj | hj
      · refine Submodule.mem_sup_right (Submodule.subset_span ?_)
        simp only [hT, Set.mem_iUnion, Set.mem_image]
        exact ⟨j, Finset.mem_range.mpr hj, a, ha, rfl⟩
      · refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
        exact hN₁ a ha j (le_trans (Finset.le_sup (hs.mem_toFinset.mpr ha)) hj)
  have himg : Submodule.span k ((N₀ ⊔ N₁).mkQ '' T) = ⊤ := by
    rw [Submodule.span_image]
    have h1 : Submodule.map (N₀ ⊔ N₁).mkQ (N₀ ⊔ N₁) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨y, hy, rfl⟩
      simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hy
    have h2 := congrArg (Submodule.map (N₀ ⊔ N₁).mkQ) hkey
    rw [Submodule.map_sup, h1, bot_sup_eq, Submodule.map_top,
      Submodule.range_mkQ] at h2
    exact h2
  have hfg : (⊤ : Submodule k (M ⧸ (N₀ ⊔ N₁))).FG :=
    ⟨(hTfin.image _).toFinset, by
      rw [Set.Finite.coe_toFinset]
      exact himg⟩
  exact ⟨hfg⟩

end LaurentLadder
end Hartshorne
