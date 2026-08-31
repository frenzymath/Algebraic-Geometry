/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.BaseDivisor
import AlgebraicJacobian.RiemannRoch.SumIntersection
import AlgebraicJacobian.RiemannRoch.AnnihilatorKernel

/-!
# DD-F — the two engines of the bpf-span lemma (descent and tower)

The two window-generic submodule engines of the F3-core proof
(`informal/dd-f-probe-verdict.md` §3c–3e, in the sum-intersection formalization route):

* **the descent engine** `Scheme.descent_baseDivisor_le` (probe 3c): if a submodule `W`
  contains `H⁰(𝒪(C − (A + div h)))` for every nonzero `h` in a subspace `N_L ⊆ H⁰(𝒪(A))`,
  then it contains `H⁰(𝒪(C − bd(N_L)))` — starting from any one `A + div h₁` and
  intersecting with achievers `A + div h_x` one point at a time, each step a
  sum-intersection at levels of depth `≤ 2·deg A`;
* **the tower engine** `Scheme.multiplier_tower_le` (probe 3e, de-Artinianized): for an
  exact-order element `fx` at `x` (`(N₀ + div fx)ₓ = 0`, `N₀ + div fx ≥ 0`),

  `H⁰(𝒪(N₀ + A − E + n·x)) ⊆ H⁰(𝒪(N₀ + A − E)) + fx · H⁰(𝒪(A))`  for `n ≤ Eₓ`,

  climbing the multiplicity of `x` one step at a time: each step is a sum-intersection
  whose second summand is the `fx`-shift of an `A`-window level (this is where the FULL
  multiplier space is spent — the jump of the `A`-side matches the jump of the target,
  which a pencil's 2-dimensional image cannot do once `deg A ≥ 2`; worksheet §3.6(a)).

Both engines take their windows as hypotheses on the divisor levels they visit; the
ledger arithmetic that discharges them lives in the keystone file `BpfSpan.lean`. No `π`,
no ledger constants appear here.
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

/-! ## Pointwise helpers -/

section Helpers

/-- `E ≤ G` gives effectivity of the difference `G − E`. -/
lemma Scheme.CurveDivisor.sub_nonneg_of_le {E G : X.CurveDivisor} (h : E ≤ G) :
    0 ≤ G - E := by
  refine CurveDivisor.le_iff_coeffAt.mpr (fun x hx => ?_)
  have := CurveDivisor.le_iff_coeffAt.mp h x hx
  rw [CurveDivisor.coeffAt_zero, CurveDivisor.coeffAt_sub]
  omega

/-- Two comparable distinct divisors differ strictly at some closed point. -/
lemma Scheme.CurveDivisor.exists_coeffAt_lt_of_le_of_ne {E G : X.CurveDivisor}
    (hle : E ≤ G) (hne : G ≠ E) :
    ∃ (x : X) (hx : x ≠ genericPoint X), coeffAt hx E < coeffAt hx G := by
  by_contra hno
  simp only [not_exists, not_lt] at hno
  refine hne (CurveDivisor.ext_coeffAt (fun x hx => ?_))
  exact le_antisymm (hno x hx) (CurveDivisor.le_iff_coeffAt.mp hle x hx)

omit [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- A nonzero effective divisor has positive degree. -/
lemma Scheme.CurveDivisor.deg_pos_of_nonneg_of_ne_zero {G : X.CurveDivisor}
    (hG0 : 0 ≤ G) (hne : G ≠ 0) : 0 < CurveDivisor.deg K G := by
  rcases lt_or_ge 0 (CurveDivisor.deg K G) with h | h
  · exact h
  · exact absurd (Scheme.CurveDivisor.eq_zero_of_deg_le_zero K hG0 h) hne

/-- `coeffAt` distributes over finite infima of divisors. -/
lemma Scheme.CurveDivisor.coeffAt_finsetInf' {ι : Type u} (S : Finset ι)
    (hS : S.Nonempty) (E : ι → X.CurveDivisor) {x : X} (hx : x ≠ genericPoint X) :
    coeffAt hx (S.inf' hS E) = S.inf' hS (fun i => coeffAt hx (E i)) :=
  Finset.apply_inf'_eq_inf'_comp hS (fun D => coeffAt hx D)
    (fun _ _ => Scheme.CurveDivisor.coeffAt_inf hx _ _)

end Helpers

/-! ## The descent engine (probe 3c) -/

section Descent

variable [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-- **The descent engine** (probe 3c): a submodule `W` containing every
`H⁰(𝒪(C − (A + div h)))` for `0 ≠ h ∈ N_L ⊆ H⁰(𝒪(A))` contains
`H⁰(𝒪(C − bd(N_L)))`, provided every level `C − G` with `0 ≤ G`, `deg G ≤ 2 deg A` is
in-window. Strong induction on `deg (G − bd(N_L))`: intersect the running depth `G` with
an achiever `A + div h_x` at a point where `G` still exceeds the base divisor; the
sum-intersection lemma keeps the union inside `W`. -/
theorem Scheme.descent_baseDivisor_le (C A : X.CurveDivisor)
    (hAdeg : 0 ≤ CurveDivisor.deg K A)
    (NL : Submodule K X.functionField) (hNL : ∃ f ∈ NL, f ≠ 0)
    (hNLle : NL ≤ divisorSections K A ⊤)
    (hwin : ∀ G : X.CurveDivisor, 0 ≤ G →
      CurveDivisor.deg K G ≤ 2 * CurveDivisor.deg K A →
      Subsingleton (Sheaf.HModule (X.divisorSheaf K (C - G)) 1))
    (W : Submodule K X.functionField)
    (hW : ∀ (h : X.functionField) (_ : h ∈ NL) (hne : h ≠ 0),
      divisorSections K
        (C - (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 h hne))) ⊤ ≤ W) :
    divisorSections K (C - Scheme.baseDivisor K NL A hNL) ⊤ ≤ W := by
  classical
  set E : X.CurveDivisor := Scheme.baseDivisor K NL A hNL with hEdef
  have hE0 : 0 ≤ E := Scheme.baseDivisor_nonneg K hNL
  -- the shifted divisors of nonzero elements of `N_L`
  have hAh0 : ∀ (h : X.functionField) (_ : h ∈ NL) (hne : h ≠ 0),
      0 ≤ A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 h hne) := by
    intro h hh hne
    exact (mem_divisorSections_top_iff K hne).mp (hNLle hh)
  have hAhdeg : ∀ (h : X.functionField) (_ : h ∈ NL) (hne : h ≠ 0),
      CurveDivisor.deg K
        (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 h hne))
        = CurveDivisor.deg K A := by
    intro h hh hne
    rw [CurveDivisor.deg_add, deg_divOf K, add_zero]
  have hEleAh : ∀ (h : X.functionField) (hh : h ∈ NL) (hne : h ≠ 0),
      E ≤ A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 h hne) := by
    intro h hh hne
    refine CurveDivisor.le_iff_coeffAt.mpr (fun x hx => ?_)
    rw [hEdef, Scheme.coeffAt_baseDivisor K hNL hx]
    exact Scheme.baseDivisorAt_le_coeffAt K hNLle hh hne hx
  -- strong induction on the excess degree
  have main : ∀ (n : ℕ) (G : X.CurveDivisor), 0 ≤ G → E ≤ G →
      (∃ (h₀ : X.functionField) (_ : h₀ ∈ NL) (hne₀ : h₀ ≠ 0),
        G ≤ A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 h₀ hne₀)) →
      (CurveDivisor.deg K (G - E)).toNat = n →
      divisorSections K (C - G) ⊤ ≤ W →
      divisorSections K (C - E) ⊤ ≤ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G hG0 hEG hGb hdegn hGW
      by_cases hGE : G = E
      · rwa [hGE] at hGW
      · -- a point where `G` still exceeds the base divisor, and an achiever there
        obtain ⟨x, hx, hxlt⟩ :=
          Scheme.CurveDivisor.exists_coeffAt_lt_of_le_of_ne hEG hGE
        obtain ⟨hf, hhf, hnef, hach⟩ :=
          Scheme.exists_coeffAt_eq_baseDivisorAt K hNLle hNL hx
        set Ax : X.CurveDivisor :=
          A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 hf hnef) with hAx
        have hAx0 : 0 ≤ Ax := hAh0 hf hhf hnef
        have hAxdeg : CurveDivisor.deg K Ax = CurveDivisor.deg K A :=
          hAhdeg hf hhf hnef
        have hAxx : coeffAt hx Ax = coeffAt hx E := by
          rw [hAx, hach, hEdef, Scheme.coeffAt_baseDivisor K hNL hx]
        obtain ⟨h₀, hh₀, hne₀, hGle⟩ := hGb
        have hdegG : CurveDivisor.deg K G ≤ CurveDivisor.deg K A :=
          le_trans (Scheme.CurveDivisor.deg_mono K hGle) (le_of_eq (hAhdeg h₀ hh₀ hne₀))
        -- the four windows of the sum-intersection step
        have hinf0 : 0 ≤ G ⊓ Ax := le_inf hG0 hAx0
        have hdeginf : CurveDivisor.deg K (G ⊓ Ax) ≤ CurveDivisor.deg K A :=
          le_trans (Scheme.CurveDivisor.deg_mono K inf_le_left) hdegG
        have hdegsup : CurveDivisor.deg K (G ⊔ Ax) ≤ 2 * CurveDivisor.deg K A := by
          have hbal := Scheme.CurveDivisor.deg_inf_add_deg_sup K G Ax
          have hnn := Scheme.CurveDivisor.deg_nonneg K hinf0
          omega
        have w1 := hwin G hG0 (by omega)
        have w2 := hwin Ax hAx0 (by omega)
        have wsup : Subsingleton
            (Sheaf.HModule (X.divisorSheaf K ((C - G) ⊔ (C - Ax))) 1) := by
          rw [← Scheme.CurveDivisor.sub_inf]
          exact hwin (G ⊓ Ax) hinf0 (by omega)
        have winf : Subsingleton
            (Sheaf.HModule (X.divisorSheaf K ((C - G) ⊓ (C - Ax))) 1) := by
          rw [← Scheme.CurveDivisor.sub_sup]
          exact hwin (G ⊔ Ax) (le_trans hG0 le_sup_left) hdegsup
        have hstep := divisorSections_sup K (C - G) (C - Ax) w1 w2 winf wsup
        rw [← Scheme.CurveDivisor.sub_inf] at hstep
        -- the union is still inside `W`
        have hnew : divisorSections K (C - (G ⊓ Ax)) ⊤ ≤ W := by
          rw [← hstep]
          exact sup_le hGW (hW hf hhf hnef)
        -- the excess degree strictly dropped
        have hxmin : coeffAt hx (G ⊓ Ax) = coeffAt hx E := by
          rw [Scheme.CurveDivisor.coeffAt_inf, hAxx]
          omega
        have hsub0 : 0 ≤ G - (G ⊓ Ax) :=
          Scheme.CurveDivisor.sub_nonneg_of_le inf_le_left
        have hsubne : G - (G ⊓ Ax) ≠ 0 := by
          intro h0
          have := congrArg (fun D => coeffAt hx D) h0
          simp only [CurveDivisor.coeffAt_sub, CurveDivisor.coeffAt_zero] at this
          omega
        have hdrop : 0 < CurveDivisor.deg K (G - (G ⊓ Ax)) :=
          Scheme.CurveDivisor.deg_pos_of_nonneg_of_ne_zero K hsub0 hsubne
        have hd1 : 0 ≤ CurveDivisor.deg K (G - E) :=
          Scheme.CurveDivisor.deg_nonneg K (Scheme.CurveDivisor.sub_nonneg_of_le hEG)
        have hd2 : 0 ≤ CurveDivisor.deg K ((G ⊓ Ax) - E) :=
          Scheme.CurveDivisor.deg_nonneg K
            (Scheme.CurveDivisor.sub_nonneg_of_le (le_inf hEG (hEleAh hf hhf hnef)))
        have hdiff : CurveDivisor.deg K (G - E)
            = CurveDivisor.deg K ((G ⊓ Ax) - E) + CurveDivisor.deg K (G - (G ⊓ Ax)) := by
          rw [Scheme.CurveDivisor.deg_sub', Scheme.CurveDivisor.deg_sub',
            Scheme.CurveDivisor.deg_sub']
          ring
        have hlt : (CurveDivisor.deg K ((G ⊓ Ax) - E)).toNat < n := by
          omega
        exact ih _ hlt (G ⊓ Ax) hinf0 (le_inf hEG (hEleAh hf hhf hnef))
          ⟨hf, hhf, hnef, inf_le_right⟩ rfl hnew
  obtain ⟨h₁, hh₁, hne₁⟩ := hNL
  exact main _ _ (hAh0 h₁ hh₁ hne₁) (hEleAh h₁ hh₁ hne₁)
    ⟨h₁, hh₁, hne₁, le_refl _⟩ rfl (hW h₁ hh₁ hne₁)

end Descent

/-! ## The tower engine (probe 3e) -/

section Tower

variable [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-- **The tower engine** (probe 3e, de-Artinianized): let `fx` be exact of order `−N₀` at
`x` (`N₀ + div fx ≥ 0` with coefficient `0` at `x`). Then for `n ≤ Eₓ`,

`H⁰(𝒪(N₀ + A − E + n·x)) ⊆ H⁰(𝒪(N₀ + A − E)) + fx · H⁰(𝒪(A))`,

by induction on `n`: each step is one sum-intersection whose second summand is the
`fx`-shift of the level `A − E + (j+1)·x` (contained in `H⁰(𝒪(A))` as long as
`j + 1 ≤ Eₓ`). The windows are hypotheses on the two ladders of levels visited. -/
theorem Scheme.multiplier_tower_le (N₀ A E : X.CurveDivisor) (hE0 : 0 ≤ E)
    {x : X} (hx : x ≠ genericPoint X)
    {fx : X.functionField} (hfx : fx ≠ 0)
    (hfxmem : 0 ≤ N₀ + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 fx hfx))
    (hfxord : coeffAt hx
      (N₀ + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 fx hfx)) = 0)
    (n : ℕ) (hn : (n : ℤ) ≤ coeffAt hx E)
    (hwinB : ∀ j : ℕ, j ≤ n → Subsingleton (Sheaf.HModule
      (X.divisorSheaf K (N₀ + A - E + CurveDivisor.single hx (j : ℤ))) 1))
    (hwinA : ∀ j : ℕ, j ≤ n → Subsingleton (Sheaf.HModule
      (X.divisorSheaf K ((A - E + CurveDivisor.single hx (j : ℤ))
        - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 fx hfx))) 1)) :
    divisorSections K (N₀ + A - E + CurveDivisor.single hx (n : ℤ)) ⊤
      ≤ divisorSections K (N₀ + A - E) ⊤
        ⊔ Submodule.map (Scheme.mulLinear K fx) (divisorSections K A ⊤) := by
  classical
  set dv : X.CurveDivisor :=
    Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 fx hfx) with hdv
  induction n with
  | zero =>
    have hzero : CurveDivisor.single hx ((0 : ℕ) : ℤ) = 0 := by
      rw [Nat.cast_zero]
      exact Finsupp.single_zero _
    rw [hzero, add_zero]
    exact le_sup_left
  | succ j ihj =>
    have hjn : (j : ℤ) ≤ coeffAt hx E := by
      have : ((j + 1 : ℕ) : ℤ) ≤ coeffAt hx E := hn
      omega
    have ihj' := ihj hjn (fun i hi => hwinB i (Nat.le_succ_of_le hi))
      (fun i hi => hwinA i (Nat.le_succ_of_le hi))
    -- the two summands of the step
    set C₁ : X.CurveDivisor := N₀ + A - E + CurveDivisor.single hx (j : ℤ) with hC₁
    set C₂ : X.CurveDivisor :=
      (A - E + CurveDivisor.single hx ((j + 1 : ℕ) : ℤ)) - dv with hC₂
    -- coefficient bookkeeping of the exact-order shift
    have hdvx : coeffAt hx (N₀ + dv) = 0 := hfxord
    have hdv0 : ∀ (y : X) (hy : y ≠ genericPoint X), 0 ≤ coeffAt hy (N₀ + dv) := by
      intro y hy
      have := CurveDivisor.le_iff_coeffAt.mp hfxmem y hy
      rwa [CurveDivisor.coeffAt_zero] at this
    -- the lattice identities of the step
    have hsupid : C₁ ⊔ C₂ = N₀ + A - E + CurveDivisor.single hx ((j + 1 : ℕ) : ℤ) := by
      refine CurveDivisor.ext_coeffAt (fun y hy => ?_)
      rw [Scheme.CurveDivisor.coeffAt_sup, hC₁, hC₂]
      by_cases hyx : y = x
      · subst hyx
        have hx' : hy = hx := rfl
        rw [hx'] at *
        simp only [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub,
          CurveDivisor.coeffAt_single_self]
        have h0 := hdvx
        rw [CurveDivisor.coeffAt_add] at h0
        push_cast
        omega
      · simp only [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub,
          CurveDivisor.coeffAt_single_of_ne hx hy hyx]
        have h0 := hdv0 y hy
        rw [CurveDivisor.coeffAt_add] at h0
        omega
    have hinfid : C₁ ⊓ C₂ = (A - E + CurveDivisor.single hx (j : ℤ)) - dv := by
      refine CurveDivisor.ext_coeffAt (fun y hy => ?_)
      rw [Scheme.CurveDivisor.coeffAt_inf, hC₁, hC₂]
      by_cases hyx : y = x
      · subst hyx
        have hx' : hy = hx := rfl
        rw [hx'] at *
        simp only [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub,
          CurveDivisor.coeffAt_single_self]
        have h0 := hdvx
        rw [CurveDivisor.coeffAt_add] at h0
        push_cast
        omega
      · simp only [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub,
          CurveDivisor.coeffAt_single_of_ne hx hy hyx]
        have h0 := hdv0 y hy
        rw [CurveDivisor.coeffAt_add] at h0
        omega
    -- the four windows
    have w1 : Subsingleton (Sheaf.HModule (X.divisorSheaf K C₁) 1) :=
      hwinB j (Nat.le_succ j)
    have w2 : Subsingleton (Sheaf.HModule (X.divisorSheaf K C₂) 1) :=
      hwinA (j + 1) (le_refl _)
    have winf : Subsingleton (Sheaf.HModule (X.divisorSheaf K (C₁ ⊓ C₂)) 1) := by
      rw [hinfid]
      exact hwinA j (Nat.le_succ j)
    have wsup : Subsingleton (Sheaf.HModule (X.divisorSheaf K (C₁ ⊔ C₂)) 1) := by
      rw [hsupid]
      exact hwinB (j + 1) (le_refl _)
    have hstep := divisorSections_sup K C₁ C₂ w1 w2 winf wsup
    rw [hsupid] at hstep
    rw [← hstep]
    -- the first summand: induction hypothesis
    refine sup_le (le_trans ihj' le_rfl) ?_
    -- the second summand: the `fx`-shift of an `A`-window level
    have hshift := map_mulLinear_divisorSections_top K hfx
      (A - E + CurveDivisor.single hx ((j + 1 : ℕ) : ℤ))
    have hC₂eq : divisorSections K C₂ ⊤
        = Submodule.map (Scheme.mulLinear K fx)
            (divisorSections K (A - E + CurveDivisor.single hx ((j + 1 : ℕ) : ℤ)) ⊤) := by
      rw [hshift, hC₂, hdv]
    rw [hC₂eq]
    have hlevel : A - E + CurveDivisor.single hx ((j + 1 : ℕ) : ℤ) ≤ A := by
      refine CurveDivisor.le_iff_coeffAt.mpr (fun y hy => ?_)
      by_cases hyx : y = x
      · subst hyx
        have hx' : hy = hx := rfl
        rw [hx'] at *
        simp only [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub,
          CurveDivisor.coeffAt_single_self]
        push_cast
        omega
      · simp only [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub,
          CurveDivisor.coeffAt_single_of_ne hx hy hyx]
        have hE0y := CurveDivisor.le_iff_coeffAt.mp hE0 y hy
        rw [CurveDivisor.coeffAt_zero] at hE0y
        omega
    refine le_trans (Submodule.map_mono (divisorSections_mono K hlevel ⊤)) le_sup_right

end Tower

end AlgebraicGeometry
