/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.FLVVanishing
import AlgebraicJacobian.RiemannRoch.ClassCohomology
import AlgebraicJacobian.RiemannRoch.ChiLedger
import AlgebraicJacobian.RiemannRoch.ChiSlice
import AlgebraicJacobian.Curve.MapToP1
import AlgebraicJacobian.Cohomology.FinitenessP1

/-!
# FLV-4 — the class form and the remaining witnesses

The final brick of the Wave-4 fibrewise-large-twist-vanishing campaign
(`informal/w4-flv-worksheet.md`, sub-brick FLV-4). It carries three obligations left open by
the FLV-2+3 landing (the vanishing headline `FLVVanishing.lean`):

## 1. The surjectivity witness (`0 < deg (fiberWeilDivisor π)` unconditionally)

`AlgebraicGeometry.surjective_of_isFinite_of_isDominant`: a finite dominant morphism is
surjective (a closed map with dense range hits everything). Feeding the surjection the
`ℙ¹`-point `[1 : 0]` (`P1.exists_mem_chartOpen_zero_notMem_one`, the origin of the chart
`D₊(X₀)` off the chart `D₊(X₁)`) produces a fiber point `x₀ ∈ V₀ ∖ V₁`, which discharges the
pole-existence witness of `AlgebraicGeometry.fiberWeilDivisor_deg_pos_of_notMem_chart₁`
unconditionally: `AlgebraicGeometry.zero_lt_deg_fiberWeilDivisor`, `0 < deg F`.

## 2. The class form (`informal/w4-flv-worksheet.md` §§1.2, 2.5)

`AlgebraicGeometry.exists_subsingleton_hModule_one_of_one_le_classDeg_of_isFinite_toP1`: for a
finite dominant `π : Y ⟶ ℙ¹` and any Čech Picard classes `l`, `θ` with `1 ≤ classDeg θ`, the
degree-one cohomology of `𝒪(D)` vanishes for **every** divisor `D` of class `l · θⁿ`, for all
large `n`. The reduction of the worksheet §2.5, in the simplified `m = m₀` form:

* run FLV-fiber (`subsingleton_hModule_divisorSheaf_one_of_isFinite_toP1`) on a divisor `D₀`
  realizing `l`: `Subsingleton H¹(𝒪(D₀ + m₀·F))`, `F` the fiber divisor, `d' := deg F ≥ 1`;
* for `n` large, the residual class `θⁿ · (𝒪(F))⁻ᵐ⁰` has degree `≥ 1 − χ(𝒪)`, so the Riemann
  inequality (`riemann_inequality`) gives a nonzero global section, hence an **effective**
  witness `E` of that class (`exists_effective_of_picClass`);
* `D₀ + m₀·F + E` is in class `l · θⁿ`; peeling `E` point-by-point transports `Subsingleton`
  up the landed dévissage surjections (`peel_effective`, from `Sheaf.HModule.surjective_map_f`);
* witness-independence (W6-lite `subsingleton_hModule_one_of_picClass_eq`) upgrades the single
  witness `D₀ + m₀·F + E` to every `D` of the class.

The rank corollary `AlgebraicGeometry.h0_eq_deg_add_chi_of_subsingleton_hModule_one` records the
CBC-3 anchor `h⁰(𝒪(D)) = deg D + χ(𝒪)` under the vanishing.

Both statements above take the finite dominant map as an explicit hypothesis, matching the shape
of the landed FLV-fiber `subsingleton_hModule_divisorSheaf_one_of_isFinite_toP1`. The curve layer
`C_K` satisfies every abstract-bundle instance, so a consumer holding a finite dominant
`π : C_K ⟶ ℙ¹` applies the class form directly.

## 3. Frontier: the dominance discharge for the *constructed* map

Specializing the class form to the curve layer with **no** external map hypothesis would require
`IsDominant` for the `π` produced by `AlgebraicJacobian.Curve.MapToP1.exists_isFinite_toP1`. That
map is dominant (its construction sends the generic point to the generic point via transcendence),
but the fact is internal to `Curve/RationalToP1.lean` and not exported; re-deriving it from the
exported `IsFinite π` alone needs the stalk-integrality/transcendence argument
(`𝒪_{ℙ¹,π(η)} → K(C)` finite and `K(C)` a field force `𝒪_{ℙ¹,π(η)}` to be a field, i.e. `π(η)`
generic), which lives outside this brick's write scope (the landed `Curve/` files). Deferred; the
consumer supplies `[IsDominant π]` with the finite map it already constructs for the fiber
geometry.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

open Scheme

/-! ## Divisor-bound comparison (public re-derivation) -/

section Bound

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [IsIntegral X]

/-- The divisor-bound comparison at a point reduces to the pointwise coefficient comparison in
`ℤ`: `divisorBound A ≤ divisorBound B ↔ coeffAt A ≤ coeffAt B`. (Public re-derivation of the
`divisorBound`/`coeffAt` translation used across the fiber toolkit.) -/
lemma divisorBound_le_iff {A B : X.CurveDivisor} {x : X} (hx : x ≠ genericPoint X) :
    Scheme.divisorBound A hx ≤ Scheme.divisorBound B hx ↔
      coeffAt hx A ≤ coeffAt hx B := by
  simp only [Scheme.divisorBound, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  rfl

end Bound

/-! ## Class arithmetic -/

section ClassArith

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- The Čech Picard class of a multiple divisor is the power of the class:
`𝒪(n·D) = 𝒪(D)ⁿ`. -/
lemma picClass_nsmul (D : X.CurveDivisor) (n : ℕ) :
    CurveDivisor.picClass K (n • D) = CurveDivisor.picClass K D ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, CurveDivisor.picClass_zero]
  | succ n ih => rw [succ_nsmul, CurveDivisor.picClass_add, ih, pow_succ]

variable [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-- The degree of a power of a Čech Picard class is the multiple of the degree:
`classDeg (Lⁿ) = n · classDeg L`. -/
lemma classDeg_pow (L : X.CechPic) (n : ℕ) :
    classDeg K (L ^ n) = n * classDeg K L := by
  induction n with
  | zero => rw [pow_zero, classDeg_one, Nat.cast_zero, zero_mul]
  | succ n ih => rw [pow_succ, classDeg_mul, ih, Nat.cast_succ]; ring

end ClassArith

/-! ## The surjectivity witness (`0 < deg F`) -/

section Witness

/-- **A `ℙ¹`-point off the chart `D₊(X₁)`.** The origin `[1 : 0]` of the chart `D₊(X₀)`: the
prime containing the chart coordinate `X₁/X₀` (a non-unit — it is the polynomial variable),
whose image lies in `D₊(X₀)` but not in `D₊(X₁)`. This is the point whose (nonempty, by
surjectivity) fiber supplies the pole witness of the fiber divisor. -/
theorem exists_mem_chartOpen_zero_notMem_one (k : Type u) [Field k] :
    ∃ z : P1 k, z ∈ P1.chartOpen k 0 ∧ z ∉ P1.chartOpen k 1 := by
  have hpre : (P1.chartι k 0) ⁻¹ᵁ P1.chartOpen k 1
      = PrimeSpectrum.basicOpen (P1.chartCoord k 0 1) := by
    change (Proj.awayι (homogeneousSubmodule (Fin 2) k) (X 0) (P1.X_mem k 0) one_pos)
        ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 2) k) (X 1) = _
    rw [Proj.awayι_preimage_basicOpen (homogeneousSubmodule (Fin 2) k)
        (P1.X_mem k 0) one_pos (P1.X_mem k 1) one_pos,
      P1.isLocalizationElem_X_eq k 0 1]
  have hnu : ¬ IsUnit (P1.chartCoord k 0 1) := by
    intro h
    have h2 := h.map (P1.awayAlgEquiv k P1.fin_zero_ne_one)
    rw [P1.awayAlgEquiv_chartCoord] at h2
    exact Polynomial.not_isUnit_X h2
  have hspan : Ideal.span {P1.chartCoord k 0 1} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hnu
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hspan
  have hpmem : P1.chartCoord k 0 1 ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨(P1.chartι k 0).base ⟨M, hM.isPrime⟩, ?_, ?_⟩
  · rw [← P1.opensRange_chartι k 0]
    exact ⟨⟨M, hM.isPrime⟩, rfl⟩
  · intro hz
    have hmem : (⟨M, hM.isPrime⟩ :
        PrimeSpectrum (Away (homogeneousSubmodule (Fin 2) k) (X 0)))
        ∈ (P1.chartι k 0) ⁻¹ᵁ P1.chartOpen k 1 := hz
    rw [hpre] at hmem
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hmem hpmem

/-- **A finite dominant morphism is surjective.** Finiteness makes `π` a closed map, so its
range is closed; dominance makes the range dense; a closed dense set is everything. -/
theorem surjective_of_isFinite_of_isDominant {X Y : Scheme.{u}} (π : X ⟶ Y)
    [IsFinite π] [IsDominant π] : Function.Surjective π.base := by
  have hclosed : IsClosed (Set.range π.base) := π.isClosedMap.isClosed_range
  haveI : Surjective π := surjective_of_isDominant_of_isClosed_range π hclosed
  exact π.surjective

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]

/-- **The pole-existence witness, unconditional.** For a **finite** dominant `π : Y ⟶ ℙ¹`, the
fiber divisor `F = fiberWeilDivisor π` has strictly positive degree: surjectivity of `π` (finite
dominant) produces a point `x₀` over `[1 : 0] ∈ V₀ ∖ V₁`, discharging the fiber witness of
`AlgebraicGeometry.fiberWeilDivisor_deg_pos_of_notMem_chart₁`. This is the FLV-4 obligation that
frees the fibrewise vanishing from its pole-existence hypothesis. -/
theorem zero_lt_deg_fiberWeilDivisor (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π] :
    0 < CurveDivisor.deg K (fiberWeilDivisor π) := by
  obtain ⟨z, hz0, hz1⟩ := exists_mem_chartOpen_zero_notMem_one K
  obtain ⟨x₀, hx₀⟩ := surjective_of_isFinite_of_isDominant π z
  have hxV₀ : x₀ ∈ fiberChart₀ π := by
    change π.base x₀ ∈ P1.chartOpen K 0; rw [hx₀]; exact hz0
  have hxV₁ : x₀ ∉ fiberChart₁ π := by
    change ¬ π.base x₀ ∈ P1.chartOpen K 1; rw [hx₀]; exact hz1
  have hx₀η : x₀ ≠ genericPoint Y := fun h =>
    hxV₁ (by rw [h]; exact (genericPoint_mem_preimage_inf π).2)
  exact fiberWeilDivisor_deg_pos_of_notMem_chart₁ π hx₀η hxV₀ hxV₁

end Witness

/-! ## The effective witness -/

section Effective

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-- **An effective witness of a class of large degree.** If a Weil divisor `W` has
`1 ≤ deg W + χ(𝒪)` then its Čech Picard class is realized by an **effective** divisor. The
Riemann inequality (`riemann_inequality`) forces a nonzero global section `f` of `𝒪(W)`, i.e.
`f ∈ K(X)ˣ` with `W + div f ≥ 0`; that shift is effective and of the same class
(`CurveDivisor.picClass_divOf`). -/
lemma exists_effective_of_picClass (W : X.CurveDivisor)
    (hW : 1 ≤ CurveDivisor.deg K W + Sheaf.chi (X.moduleKSheaf K)) :
    ∃ E : X.CurveDivisor, 0 ≤ E ∧ CurveDivisor.picClass K E = CurveDivisor.picClass K W := by
  -- `h⁰(𝒪(W)) ≥ 1`, so `H⁰` is nontrivial.
  have hfr : 0 < Module.finrank K (Sheaf.HModule (X.divisorSheaf K W) 0) := by
    have h1 : (1 : ℤ) ≤ (Sheaf.h0 (X.divisorSheaf K W) : ℤ) :=
      le_trans hW (riemann_inequality K W)
    have : 0 < Sheaf.h0 (X.divisorSheaf K W) := by omega
    exact this
  haveI : Nontrivial (Sheaf.HModule (X.divisorSheaf K W) 0) :=
    Module.nontrivial_of_finrank_pos hfr
  -- a nonzero global section `g ∈ 𝒪(W)(⊤) ⊆ K(X)`.
  obtain ⟨t, ht⟩ := exists_ne (0 : Sheaf.HModule (X.divisorSheaf K W) 0)
  set s := (Sheaf.HModule.linearEquiv₀ (Opens.grothendieckTopology (X : TopCat))
    (isTerminalTop : IsTerminal (⊤ : X.Opens)) (X.divisorSheaf K W)) t with hs
  have hsne : s ≠ 0 := by
    rw [hs]; exact (LinearEquiv.map_ne_zero_iff _).mpr ht
  set g : X.functionField := divisorVal K s with hg
  have hgmem : g ∈ divisorSections K W ⊤ := divisorVal_mem K s
  have hgne : g ≠ 0 := by
    intro h
    exact hsne (divisorSection_ext K
      (show divisorVal K s = divisorVal K (0 : _) from by rw [← hg, h]; rfl))
  -- the unit `u` and the effective shift.
  set u : X.functionFieldˣ := Units.mk0 g hgne with hu
  have huval : (u : X.functionField) = g := rfl
  refine ⟨W + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) u, ?_, ?_⟩
  · -- effectivity: `coeffAt (W + div u) ≥ 0` from the pole bound
    refine Finsupp.le_def.mpr (fun p => ?_)
    change (0 : ℤ) ≤ coeffAt p.2 (W + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) u)
    have htop : ((⊤ : X.Opens) : Set X).Nonempty := ⟨genericPoint X, trivial⟩
    have hb := (mem_divisorSections_of_nonempty K htop).mp hgmem p.1 p.2 trivial
    rw [← huval, Scheme.ord_val_eq K u p.2, divisorBound_le_iff p.2,
      CurveDivisor.coeffAt_neg] at hb
    rw [CurveDivisor.coeffAt_add]
    omega
  · -- same class
    rw [CurveDivisor.picClass_add, CurveDivisor.picClass_divOf, mul_one]

end Effective

/-! ## Effective peeling of `Subsingleton H¹` -/

section Peel

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **Peeling one point.** Vanishing of `H¹(𝒪(B))` transports to `H¹(𝒪(B + x))` along the
landed dévissage surjection `H¹(𝒪(B)) ↠ H¹(𝒪(B + x))` (`Sheaf.HModule.surjective_map_f` on
`devissageSES`, whose skyscraper cokernel has vanishing `H¹`). -/
lemma peel_single {x : X} (hx : x ≠ genericPoint X) (B : X.CurveDivisor)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K B) 1)) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K (B + CurveDivisor.single hx 1)) 1) := by
  set D : X.CurveDivisor := B + CurveDivisor.single hx 1 with hD
  have hBD : devissageDivisor hx D = B := by rw [devissageDivisor_eq_sub, hD]; abel
  haveI : Subsingleton (Sheaf.HModule (devissageSES K hx D).X₃ 1) :=
    skyModule_subsingleton_hModule_one x (jumpModule K hx D)
  have hsurj := Sheaf.HModule.surjective_map_f (devissageSES_shortExact K hx D) 1
  have hsub : Subsingleton (Sheaf.HModule (X.divisorSheaf K (devissageDivisor hx D)) 1) := by
    rw [hBD]; exact h
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  exact congrArg _ (hsub.elim a' b')

/-- **Peeling a multiple of a point.** Iterating `peel_single`: `Subsingleton H¹(𝒪(A))`
transports to `Subsingleton H¹(𝒪(A + n·x))`. -/
lemma peel_nsmul_single {x : X} (hx : x ≠ genericPoint X) (A : X.CurveDivisor) (n : ℕ)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K A) 1)) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K (A + n • CurveDivisor.single hx 1)) 1) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hstep := peel_single hx (A + n • CurveDivisor.single hx 1) ih
    have heq : A + n • CurveDivisor.single hx 1 + CurveDivisor.single hx 1
        = A + (n + 1) • CurveDivisor.single hx 1 := by
      rw [succ_nsmul]; abel
    rwa [heq] at hstep

/-- **Effective peeling.** Vanishing of `H¹(𝒪(A))` transports to `H¹(𝒪(A + E))` for any
effective divisor `E`: peel the finitely many points of `E` one multiplicity-block at a time,
by induction on the size of the support. -/
lemma peel_effective (A E : X.CurveDivisor) (hE : 0 ≤ E)
    (h : Subsingleton (Sheaf.HModule (X.divisorSheaf K A) 1)) :
    Subsingleton (Sheaf.HModule (X.divisorSheaf K (A + E)) 1) := by
  suffices H : ∀ (n : ℕ) (E : X.CurveDivisor), 0 ≤ E →
      (toFinsupp E).support.card = n →
      Subsingleton (Sheaf.HModule (X.divisorSheaf K (A + E)) 1) from H _ E hE rfl
  intro n
  induction n with
  | zero =>
    intro E hE hc
    have hE0 : E = 0 :=
      Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp hc)
    rw [hE0, add_zero]; exact h
  | succ n ih =>
    intro E hE hc
    classical
    have hne : (toFinsupp E).support.Nonempty := by
      rw [← Finset.card_pos, hc]; exact Nat.succ_pos n
    obtain ⟨p, hp⟩ := hne
    set b : ℤ := toFinsupp E p with hb
    have hb_nonneg : 0 ≤ b := Finsupp.le_def.mp hE p
    have hbpos : 0 < b := lt_of_le_of_ne hb_nonneg (Ne.symm (Finsupp.mem_support_iff.mp hp))
    set E' : X.CurveDivisor := Finsupp.erase p (toFinsupp E) with hE'
    have hdecomp : CurveDivisor.single p.2 b + E' = E := by
      rw [hE', hb]
      exact Finsupp.single_add_erase p (toFinsupp E)
    have hE'nonneg : 0 ≤ E' := by
      rw [hE']
      refine Finsupp.le_def.mpr (fun q => ?_)
      by_cases hq : q = p
      · subst hq; rw [Finsupp.erase_same]; rfl
      · rw [Finsupp.erase_ne hq]; exact Finsupp.le_def.mp hE q
    have hcard : (toFinsupp E').support.card = n := by
      have hEF : toFinsupp E' = Finsupp.erase p (toFinsupp E) := rfl
      rw [hEF, Finsupp.support_erase, Finset.card_erase_of_mem hp, hc, Nat.succ_sub_one]
    have hrec := ih E' hE'nonneg hcard
    have hsingle : CurveDivisor.single p.2 b = b.toNat • CurveDivisor.single p.2 1 := by
      rw [CurveDivisor.nsmul_single_one, Int.toNat_of_nonneg hb_nonneg]
    have hsplit : A + E = (A + E') + b.toNat • CurveDivisor.single p.2 1 := by
      rw [← hdecomp, ← hsingle]; abel
    rw [hsplit]
    exact peel_nsmul_single p.2 (A + E') b.toNat hrec

end Peel

/-! ## The class form -/

section ClassForm

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]

/-- **FLV-class (conditional on a finite dominant map)** — the worksheet's outer statement
(`informal/w4-flv-worksheet.md` §§1.2, 2.5). For a finite dominant `π : Y ⟶ ℙ¹` compatible with
the structure morphisms, and Čech Picard classes `l`, `θ` with `1 ≤ classDeg θ`: the degree-one
cohomology of `𝒪(D)` vanishes for **every** Weil divisor `D` of class `l · θⁿ`, for all
sufficiently large `n`. The bound `n₀` is per-class and non-effective.

The reduction (§2.5, in the simplified `m = m₀` form): FLV-fiber
(`subsingleton_hModule_divisorSheaf_one_of_isFinite_toP1`) vanishes `H¹(𝒪(D₀ + m₀·F))` for `D₀`
realizing `l` and `F` the fiber divisor (`0 < deg F` by the surjectivity witness); for `n` large
the residual class `θⁿ·(𝒪(F))⁻ᵐ⁰` has degree `≥ 1 − χ(𝒪)`, giving an **effective** witness `E`
of that class (`exists_effective_of_picClass`); `D₀ + m₀·F + E` is in class `l·θⁿ`, and peeling
`E` (`peel_effective`) transports the vanishing; witness-independence (W6-lite
`subsingleton_hModule_one_of_picClass_eq`) upgrades it to every `D` of the class. -/
theorem exists_subsingleton_hModule_one_of_one_le_classDeg_of_isFinite_toP1
    [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
    (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K))
    (l θ : Y.CechPic) (hθ : 1 ≤ classDeg K θ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ D : Y.CurveDivisor,
      CurveDivisor.picClass K D = l * θ ^ n →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K D) 1) := by
  obtain ⟨D₀, hD₀⟩ := CurveDivisor.exists_picClass_eq K l
  obtain ⟨m₀, hm₀⟩ := subsingleton_hModule_divisorSheaf_one_of_isFinite_toP1 π hπ D₀
  set F : Y.CurveDivisor := fiberWeilDivisor π with hF
  set d' : ℤ := CurveDivisor.deg K F with hd'
  have hd'pos : 0 < d' := by rw [hd', hF]; exact zero_lt_deg_fiberWeilDivisor π
  set φ : Y.CechPic := CurveDivisor.picClass K F with hφ
  have hφdeg : classDeg K φ = d' := by rw [hφ, hd', classDeg_picClass]
  set gtld : ℤ := 1 - Sheaf.chi (Y.moduleKSheaf K) with hgtld
  refine ⟨(m₀ * d' + gtld).toNat, fun n hn D hD => ?_⟩
  -- the residual class and its degree
  set c : Y.CechPic := θ ^ n * (φ ^ m₀)⁻¹ with hc
  have hcdeg : classDeg K c = n * classDeg K θ - m₀ * d' := by
    rw [hc, classDeg_mul, classDeg_inv, classDeg_pow, classDeg_pow, hφdeg]; ring
  have hlarge : gtld ≤ classDeg K c := by
    rw [hcdeg]
    have h1 : (m₀ * d' + gtld : ℤ) ≤ (n : ℤ) :=
      le_trans (Int.self_le_toNat _) (by exact_mod_cast hn)
    have h2 : (n : ℤ) ≤ (n : ℤ) * classDeg K θ :=
      le_mul_of_one_le_right (Int.natCast_nonneg n) hθ
    linarith
  -- an effective witness of the residual class
  obtain ⟨W, hWc⟩ := CurveDivisor.exists_picClass_eq K c
  have hWdeg : 1 ≤ CurveDivisor.deg K W + Sheaf.chi (Y.moduleKSheaf K) := by
    have hWc' : classDeg K c = CurveDivisor.deg K W := by rw [← hWc, classDeg_picClass]
    rw [hWc', hgtld] at hlarge; linarith
  obtain ⟨E, hEnonneg, hEc⟩ := exists_effective_of_picClass W hWdeg
  -- the class of the witness divisor `D₀ + m₀·F + E`
  have hD'class : CurveDivisor.picClass K (D₀ + m₀ • F + E) = l * θ ^ n := by
    rw [CurveDivisor.picClass_add, CurveDivisor.picClass_add, hD₀, picClass_nsmul, ← hφ,
      hEc, hWc, hc]
    rw [mul_comm (θ ^ n) ((φ ^ m₀)⁻¹), ← mul_assoc, mul_assoc l, mul_inv_cancel, mul_one]
  -- vanishing at the base, then peel `E`, then transport by witness-independence
  have hbase : Subsingleton (Sheaf.HModule (Y.divisorSheaf K (D₀ + m₀ • F)) 1) := by
    rw [hF]; exact hm₀ m₀ le_rfl
  have hpeel : Subsingleton (Sheaf.HModule (Y.divisorSheaf K (D₀ + m₀ • F + E)) 1) :=
    peel_effective (D₀ + m₀ • F) E hEnonneg hbase
  exact subsingleton_hModule_one_of_picClass_eq K (hD'class.trans hD.symm) hpeel

omit [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] in
/-- **The rank anchor** (`informal/w4-flv-worksheet.md` §1.2 corollary, the CBC-3 input). Under
the fibrewise vanishing `Subsingleton H¹(𝒪(D))`, the global-section count is exactly
`h⁰(𝒪(D)) = deg D + χ(𝒪_Y)` — the fibrewise value of Kleiman's `rank Q = χ`. One line from
`Sheaf.chi_eq_h0` and the closed χ-ledger `chi_divisorSheaf`. -/
theorem h0_eq_deg_add_chi_of_subsingleton_hModule_one
    [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
    (D : Y.CurveDivisor) (hsub : Subsingleton (Sheaf.HModule (Y.divisorSheaf K D) 1)) :
    (Sheaf.h0 (Y.divisorSheaf K D) : ℤ)
      = CurveDivisor.deg K D + Sheaf.chi (Y.moduleKSheaf K) := by
  have h1 : Sheaf.chi (Y.divisorSheaf K D) = (Sheaf.h0 (Y.divisorSheaf K D) : ℤ) :=
    Sheaf.chi_eq_h0 hsub
  have h2 := chi_divisorSheaf K D
  rw [h1] at h2
  omega

end ClassForm

end AlgebraicGeometry
