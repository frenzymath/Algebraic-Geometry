/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.SectionSpaces
import AlgebraicJacobian.RiemannRoch.FLVClass

/-!
# DD-F brick 4 — the sum-intersection lemma

The workhorse of the bpf-span route (`informal/dd-f-probe-verdict.md` §3c and the
formalization simplification recorded on the roadmap): for divisors `C₁, C₂` whose four
lattice levels `C₁, C₂, C₁ ⊓ C₂, C₁ ⊔ C₂` all have vanishing `H¹`,

  `H⁰(𝒪(C₁)) + H⁰(𝒪(C₂)) = H⁰(𝒪(C₁ ⊔ C₂))`  (`divisorSections_sup`),

by the exact dimension count: `dim(U + V) = dim U + dim V − dim(U ∩ V)`, the intersection
identity `U ∩ V = H⁰(𝒪(C₁ ⊓ C₂))` (pure `ord` calculus, `divisorSections_inf`), the rank
anchor `h⁰ = deg + χ` at all four levels, and the lattice degree balance
`deg ⊓ + deg ⊔ = deg + deg`.

This single lemma replaces both the pairwise Koszul SES and the Artinian restriction
algebra of the probe's route (3c)–(3e): the pairwise spans `h₁V₀ + h_iV₀`, the descent to
the base locus `E`, and the tower steps at each point of `E` are all instances (the probe
route's `H⁰`-right-exactness is subsumed by the dimension count).

The iterated form `finsetSup_divisorSections_sub` sums a finite family
`H⁰(𝒪(C − E i))` of effective depths `E i ≤ Bnd` under a uniform window
(`H¹(𝒪(C − G)) = 0` for all `0 ≤ G ≤ Bnd`) into `H⁰(𝒪(C − ⨅ᵢ E i))` — the probe's
"iterating, `span(Σ h_iV₀) = H⁰(N + sF − ⋀ E_i)`" and the final sum over the points of
`E`, in one lemma.

Divisor-lattice distribution helpers (`sub_inf`, `sub_sup`) are provided here.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.Scheme.functionFieldOverModule
  AlgebraicGeometry.Scheme.overModule

namespace AlgebraicGeometry

open Scheme

/-! ## Lattice distribution of subtraction -/

section LatticeSub

variable {X : Scheme.{u}} [IsIntegral X]

/-- Subtraction turns pointwise minima into maxima: `C − (D₁ ⊓ D₂) = (C − D₁) ⊔ (C − D₂)`. -/
lemma Scheme.CurveDivisor.sub_inf (C D₁ D₂ : X.CurveDivisor) :
    C - (D₁ ⊓ D₂) = (C - D₁) ⊔ (C - D₂) := by
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  rw [CurveDivisor.coeffAt_sub, Scheme.CurveDivisor.coeffAt_inf,
    Scheme.CurveDivisor.coeffAt_sup, CurveDivisor.coeffAt_sub, CurveDivisor.coeffAt_sub]
  omega

/-- Subtraction turns pointwise maxima into minima: `C − (D₁ ⊔ D₂) = (C − D₁) ⊓ (C − D₂)`. -/
lemma Scheme.CurveDivisor.sub_sup (C D₁ D₂ : X.CurveDivisor) :
    C - (D₁ ⊔ D₂) = (C - D₁) ⊓ (C - D₂) := by
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  rw [CurveDivisor.coeffAt_sub, Scheme.CurveDivisor.coeffAt_sup,
    Scheme.CurveDivisor.coeffAt_inf, CurveDivisor.coeffAt_sub, CurveDivisor.coeffAt_sub]
  omega

end LatticeSub

/-! ## The sum-intersection workhorse -/

section Workhorse

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- **The sum-intersection lemma** (★, the workhorse of the bpf-span route): if all four
lattice levels of `C₁, C₂` are in-window (`H¹ = 0`), then
`H⁰(𝒪(C₁)) + H⁰(𝒪(C₂)) = H⁰(𝒪(C₁ ⊔ C₂))`. The `≤` is `ord` monotonicity; equality is the
dimension count through `H⁰(𝒪(C₁)) ∩ H⁰(𝒪(C₂)) = H⁰(𝒪(C₁ ⊓ C₂))`, the rank anchor
`h⁰ = deg + χ`, and `deg ⊓ + deg ⊔ = deg + deg`. -/
theorem divisorSections_sup (C₁ C₂ : X.CurveDivisor)
    (h1 : Subsingleton (Sheaf.HModule (X.divisorSheaf K C₁) 1))
    (h2 : Subsingleton (Sheaf.HModule (X.divisorSheaf K C₂) 1))
    (hinf : Subsingleton (Sheaf.HModule (X.divisorSheaf K (C₁ ⊓ C₂)) 1))
    (hsup : Subsingleton (Sheaf.HModule (X.divisorSheaf K (C₁ ⊔ C₂)) 1)) :
    divisorSections K C₁ ⊤ ⊔ divisorSections K C₂ ⊤
      = divisorSections K (C₁ ⊔ C₂) ⊤ := by
  have hle : divisorSections K C₁ ⊤ ⊔ divisorSections K C₂ ⊤
      ≤ divisorSections K (C₁ ⊔ C₂) ⊤ :=
    sup_le (divisorSections_mono K le_sup_left ⊤) (divisorSections_mono K le_sup_right ⊤)
  -- the dimension count
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq
    (divisorSections K C₁ ⊤) (divisorSections K C₂ ⊤)
  rw [divisorSections_inf K C₁ C₂] at hkey
  have hb1 := finrank_divisorSections_top K C₁
  have hb2 := finrank_divisorSections_top K C₂
  have hbinf := finrank_divisorSections_top K (C₁ ⊓ C₂)
  have hbsup := finrank_divisorSections_top K (C₁ ⊔ C₂)
  have ha1 := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := K) C₁ h1
  have ha2 := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := K) C₂ h2
  have hainf := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := K) (C₁ ⊓ C₂) hinf
  have hasup := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := K) (C₁ ⊔ C₂) hsup
  have hdeg := Scheme.CurveDivisor.deg_inf_add_deg_sup K C₁ C₂
  -- `finrank (U ⊔ V) = h⁰(𝒪(C₁ ⊔ C₂))`
  have hcount : Module.finrank K
      ↥(divisorSections K C₁ ⊤ ⊔ divisorSections K C₂ ⊤)
      = Sheaf.h0 (X.divisorSheaf K (C₁ ⊔ C₂)) := by
    omega
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [← hbsup] at hcount
  omega

end Workhorse

/-! ## The iterated form -/

section Iterated

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- **The iterated sum-intersection lemma**: for a finite nonempty family of effective
depths `E i ≤ Bnd` under the uniform window `H¹(𝒪(C − G)) = 0` for all `0 ≤ G ≤ Bnd`,

  `Σᵢ H⁰(𝒪(C − E i)) = H⁰(𝒪(C − ⨅ᵢ E i))`.

Induction over the finset; every lattice level appearing (pairwise sups/infs of partial
infima) stays effective and `≤ Bnd`, so the uniform window discharges all four
hypotheses of the workhorse at each step. -/
theorem finsetSup_divisorSections_sub {ι : Type u} (S : Finset ι) (hS : S.Nonempty)
    (C Bnd : X.CurveDivisor) (E : ι → X.CurveDivisor)
    (hE0 : ∀ i ∈ S, 0 ≤ E i) (hEB : ∀ i ∈ S, E i ≤ Bnd)
    (hwin : ∀ G : X.CurveDivisor, 0 ≤ G → G ≤ Bnd →
      Subsingleton (Sheaf.HModule (X.divisorSheaf K (C - G)) 1)) :
    S.sup (fun i => divisorSections K (C - E i) ⊤)
      = divisorSections K (C - S.inf' hS E) ⊤ := by
  classical
  induction S using Finset.cons_induction with
  | empty => exact absurd hS (by simp)
  | cons a s ha ih =>
    by_cases hs : s.Nonempty
    · have hE0' : ∀ i ∈ s, 0 ≤ E i := fun i hi => hE0 i (Finset.mem_cons_of_mem hi)
      have hEB' : ∀ i ∈ s, E i ≤ Bnd := fun i hi => hEB i (Finset.mem_cons_of_mem hi)
      have haE0 : 0 ≤ E a := hE0 a (Finset.mem_cons_self a s)
      have haEB : E a ≤ Bnd := hEB a (Finset.mem_cons_self a s)
      have hrec := ih hs hE0' hEB'
      -- the running infimum of the tail
      set G : X.CurveDivisor := s.inf' hs E with hG
      have hG0 : 0 ≤ G := Finset.le_inf' hs E hE0'
      have hGB : G ≤ Bnd := by
        obtain ⟨j, hj⟩ := hs
        exact le_trans (Finset.inf'_le E hj) (hEB' j hj)
      have hsup : (C - E a) ⊔ (C - G) = C - (E a ⊓ G) :=
        (Scheme.CurveDivisor.sub_inf C (E a) G).symm
      have hinf : (C - E a) ⊓ (C - G) = C - (E a ⊔ G) :=
        (Scheme.CurveDivisor.sub_sup C (E a) G).symm
      have h1 := hwin (E a) haE0 haEB
      have h2 := hwin G hG0 hGB
      have hinfw : Subsingleton
          (Sheaf.HModule (X.divisorSheaf K ((C - E a) ⊓ (C - G))) 1) := by
        rw [hinf]
        exact hwin (E a ⊔ G) (le_trans haE0 le_sup_left) (sup_le haEB hGB)
      have hsupw : Subsingleton
          (Sheaf.HModule (X.divisorSheaf K ((C - E a) ⊔ (C - G))) 1) := by
        rw [hsup]
        exact hwin (E a ⊓ G) (le_inf haE0 hG0) (le_trans inf_le_left haEB)
      have hstep := divisorSections_sup K (C - E a) (C - G) h1 h2 hinfw hsupw
      have hcons : (Finset.cons a s ha).inf' hS E = E a ⊓ G := by
        rw [hG]
        exact Finset.inf'_cons hs E
      rw [Finset.sup_cons, hrec, hstep, hsup, hcons]
    · -- the tail is empty: the cons is a singleton
      have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst hse
      have hone : (Finset.cons a ∅ ha).inf' hS E = E a := by simp
      rw [Finset.sup_cons, Finset.sup_empty, sup_bot_eq, hone]

end Iterated

end AlgebraicGeometry
