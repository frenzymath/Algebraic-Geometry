/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.MulEquiv
import AlgebraicJacobian.RiemannRoch.ChiFiniteness
import AlgebraicJacobian.Picard.PresentationDivisor

/-!
# DD-F brick 2 — global sections of `𝒪(D)` as submodules of the function field

The field-level vocabulary of the P-fib lane (`informal/dat-d-worksheet.md` §3.2–3.3,
`informal/dd-f-probe-verdict.md` inventory brick 2): on the curve bundle `X`, the space of
global sections `H⁰(𝒪(A)) = divisorSections K A ⊤` is literally a `K`-submodule of the
function field `K(X)`, so the multiplication data of the carve `(♦)` is honest
function-field multiplication. This file provides the submodule calculus the P-fib route
consumes:

* **the lattice of Weil divisors**: `Scheme.CurveDivisor.instLattice` (pointwise min/max),
  `inf_add_sup`, degree monotonicity/additivity (`deg_nonneg`, `deg_mono`,
  `deg_inf_add_deg_sup`, `deg_nsmul'`, `deg_sub'`, `eq_zero_of_deg_le_zero`);
* **membership through the principal divisor**: `mem_divisorSections_top_iff`
  (`f ∈ H⁰(𝒪(A)) ↔ 0 ≤ A + div f` for `f ≠ 0`) — the `ord`-calculus bridge every
  base-divisor computation runs through;
* **multiplication** `Scheme.mulLinear K a : K(X) →ₗ[K] K(X)` and the product rule
  `mul_mem_divisorSections_top : H⁰(𝒪(A)) · H⁰(𝒪(B)) ⊆ H⁰(𝒪(A + B))`;
* **the shift identity** `map_mulLinear_divisorSections_top`:
  `f · H⁰(𝒪(A)) = H⁰(𝒪(A - div f))` — multiplication by a nonzero rational function is an
  exact `ord`-shift (the submodule-image form of `mulEquivDivisorSheaf`);
* **the intersection identity** `divisorSections_inf`:
  `H⁰(𝒪(A)) ⊓ H⁰(𝒪(B)) = H⁰(𝒪(A ⊓ B))` — pure `ord` calculus, no cohomology;
* **the `h⁰` bridge** `finrank_divisorSections_top`:
  `dim_K H⁰(𝒪(A)) = h⁰(𝒪(A))` through `Sheaf.HModule.linearEquiv₀`, with the
  `Module.Finite` instance making every dimension count downstream fire.

Everything here is elementary; the windows/cohomology enter only in the consumers
(`SumIntersection.lean`, `BpfSpan.lean`, `PFib.lean`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.Scheme.functionFieldOverModule
  AlgebraicGeometry.Scheme.overModule

namespace AlgebraicGeometry

open Scheme

/-! ## The lattice of Weil divisors -/

section DivisorLattice

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable instance Scheme.CurveDivisor.instLattice : Lattice X.CurveDivisor :=
  inferInstanceAs (Lattice ({x : X // x ≠ genericPoint X} →₀ ℤ))

lemma Scheme.CurveDivisor.coeffAt_inf {x : X} (hx : x ≠ genericPoint X)
    (D D' : X.CurveDivisor) :
    coeffAt hx (D ⊓ D') = min (coeffAt hx D) (coeffAt hx D') :=
  rfl

lemma Scheme.CurveDivisor.coeffAt_sup {x : X} (hx : x ≠ genericPoint X)
    (D D' : X.CurveDivisor) :
    coeffAt hx (D ⊔ D') = max (coeffAt hx D) (coeffAt hx D') :=
  rfl

/-- Pointwise `min + max = +`: the divisor lattice satisfies `(D ⊓ D') + (D ⊔ D') = D + D'`. -/
lemma Scheme.CurveDivisor.inf_add_sup (D D' : X.CurveDivisor) :
    (D ⊓ D') + (D ⊔ D') = D + D' := by
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  rw [CurveDivisor.coeffAt_add,
    CurveDivisor.coeffAt_add,
    Scheme.CurveDivisor.coeffAt_inf, Scheme.CurveDivisor.coeffAt_sup]
  exact min_add_max _ _

/-- The pointwise comparison of divisors, in `coeffAt` form. -/
lemma Scheme.CurveDivisor.le_iff_coeffAt {D D' : X.CurveDivisor} :
    D ≤ D' ↔ ∀ (x : X) (hx : x ≠ genericPoint X), coeffAt hx D ≤ coeffAt hx D' := by
  constructor
  · intro h x hx
    exact Finsupp.le_def.mp h ⟨x, hx⟩
  · intro h
    exact Finsupp.le_def.mpr (fun p => h p.1 p.2)

section Degree

variable (K : Type u) [CommRing K] [X.Over (Spec (CommRingCat.of K))]

/-- Degree of a natural multiple: `deg (n • D) = n · deg D` (public form of the
`WindowLedger` helper). -/
lemma Scheme.CurveDivisor.deg_nsmul' (n : ℕ) (D : X.CurveDivisor) :
    CurveDivisor.deg K (n • D) = n * CurveDivisor.deg K D := by
  induction n with
  | zero => rw [zero_nsmul, CurveDivisor.deg_zero, Nat.cast_zero, zero_mul]
  | succ n ih => rw [succ_nsmul, CurveDivisor.deg_add, ih]; push_cast; ring

/-- Degree of a difference: `deg (A − B) = deg A − deg B` (public form of the
`WindowLedger` helper). -/
lemma Scheme.CurveDivisor.deg_sub' (A B : X.CurveDivisor) :
    CurveDivisor.deg K (A - B) = CurveDivisor.deg K A - CurveDivisor.deg K B := by
  rw [sub_eq_add_neg, CurveDivisor.deg_add, CurveDivisor.deg_neg, sub_eq_add_neg]

/-- **An effective divisor has nonnegative degree**: residue degrees are nonnegative. -/
lemma Scheme.CurveDivisor.deg_nonneg {E : X.CurveDivisor} (hE : 0 ≤ E) :
    0 ≤ CurveDivisor.deg K E := by
  refine Finsupp.sum_nonneg (fun p _ => ?_)
  exact mul_nonneg (Finsupp.le_def.mp hE p) (Int.natCast_nonneg _)

/-- **Degree is monotone** on the divisor lattice. -/
lemma Scheme.CurveDivisor.deg_mono {D D' : X.CurveDivisor} (h : D ≤ D') :
    CurveDivisor.deg K D ≤ CurveDivisor.deg K D' := by
  have hE : 0 ≤ D' - D := by
    refine Finsupp.le_def.mpr (fun p => ?_)
    have hp : toFinsupp D p ≤ toFinsupp D' p := Finsupp.le_def.mp h p
    change (0 : ℤ) ≤ toFinsupp (D' - D) p
    have hsub : toFinsupp (D' - D) p = toFinsupp D' p - toFinsupp D p :=
      Finsupp.sub_apply _ _ _
    omega
  have hnn := Scheme.CurveDivisor.deg_nonneg K hE
  rw [Scheme.CurveDivisor.deg_sub' K] at hnn
  linarith

/-- `deg (D ⊓ D') + deg (D ⊔ D') = deg D + deg D'` — the degree balance of the lattice. -/
lemma Scheme.CurveDivisor.deg_inf_add_deg_sup (D D' : X.CurveDivisor) :
    CurveDivisor.deg K (D ⊓ D') + CurveDivisor.deg K (D ⊔ D')
      = CurveDivisor.deg K D + CurveDivisor.deg K D' := by
  rw [← CurveDivisor.deg_add, Scheme.CurveDivisor.inf_add_sup, CurveDivisor.deg_add]

end Degree

section EffectiveSupport

variable (K : Type u) [Field K] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- The number of support points of an effective divisor is at most its degree. Each nonzero
coefficient and each residue degree contributes at least one to the degree sum. -/
lemma Scheme.CurveDivisor.support_card_le_deg {E : X.CurveDivisor} (hE : 0 ≤ E) :
    ((toFinsupp E).support.card : ℤ) ≤ CurveDivisor.deg K E := by
  classical
  rw [CurveDivisor.deg]
  calc
    ((toFinsupp E).support.card : ℤ)
        = ∑ p ∈ (toFinsupp E).support, (1 : ℤ) := by simp
    _ ≤ ∑ p ∈ (toFinsupp E).support,
        toFinsupp E p * (X.residueDeg K p.1 : ℤ) := by
      gcongr with p hp
      have hcoeff : (1 : ℤ) ≤ toFinsupp E p := by
        have hnonneg : (0 : ℤ) ≤ toFinsupp E p := Finsupp.le_def.mp hE p
        have hne : toFinsupp E p ≠ 0 := Finsupp.mem_support_iff.mp hp
        omega
      have hres : (1 : ℤ) ≤ (X.residueDeg K p.1 : ℤ) := by
        exact_mod_cast Scheme.residueDeg_pos (K := K) p.2
      exact one_le_mul_of_one_le_of_one_le hcoeff hres
    _ = (toFinsupp E).sum fun p n => n * (X.residueDeg K p.1 : ℤ) := rfl

end EffectiveSupport

section DegreeZero

variable (K : Type u) [Field K] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- **An effective divisor of degree `≤ 0` is zero**: each coefficient is nonnegative and
weighted by a positive residue degree, so all must vanish. -/
lemma Scheme.CurveDivisor.eq_zero_of_deg_le_zero {E : X.CurveDivisor} (hE : 0 ≤ E)
    (hdeg : CurveDivisor.deg K E ≤ 0) : E = 0 := by
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  by_contra hne
  have hpos : 0 < coeffAt hx E := by
    have hp := Finsupp.le_def.mp hE ⟨x, hx⟩
    change (0 : ℤ) ≤ coeffAt hx E at hp
    change coeffAt hx E ≠ 0 at hne
    omega
  have hmem : (⟨x, hx⟩ : {p : X // p ≠ genericPoint X}) ∈ (toFinsupp E).support :=
    Finsupp.mem_support_iff.mpr (by change coeffAt hx E ≠ 0; omega)
  have hterm : ∀ p ∈ (toFinsupp E).support,
      (0 : ℤ) ≤ toFinsupp E p * (X.residueDeg K p.1 : ℤ) := fun p _ =>
    mul_nonneg (Finsupp.le_def.mp hE p) (Int.natCast_nonneg _)
  have hxpos : (0 : ℤ) < coeffAt hx E * (X.residueDeg K x : ℤ) := by
    have hres : 0 < X.residueDeg K x := Scheme.residueDeg_pos hx
    have hres' : (0 : ℤ) < (X.residueDeg K x : ℤ) := by exact_mod_cast hres
    exact mul_pos hpos hres'
  have hsum : (0 : ℤ) < ∑ p ∈ (toFinsupp E).support,
      toFinsupp E p * (X.residueDeg K p.1 : ℤ) :=
    Finset.sum_pos' hterm ⟨⟨x, hx⟩, hmem, hxpos⟩
  have hdeg' : CurveDivisor.deg K E
      = ∑ p ∈ (toFinsupp E).support, toFinsupp E p * (X.residueDeg K p.1 : ℤ) := rfl
  omega

end DegreeZero

end DivisorLattice

/-! ## Membership through the principal divisor -/

section Membership

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]

/-- The top open of the irreducible space `X` is nonempty (it contains the generic point). -/
lemma top_opens_nonempty : ((⊤ : X.Opens) : Set X).Nonempty :=
  ⟨genericPoint X, trivial⟩

omit [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] in
/-- The divisor-bound comparison at a point in `coeffAt` form (public restatement of the
`FLVClass` bridge, kept here so the section-space files do not import the FLV lane). -/
lemma divisorBound_le_divisorBound_iff {A B : X.CurveDivisor} {x : X}
    (hx : x ≠ genericPoint X) :
    Scheme.divisorBound A hx ≤ Scheme.divisorBound B hx ↔
      coeffAt hx A ≤ coeffAt hx B := by
  simp only [Scheme.divisorBound, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  rfl

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **Membership of a nonzero rational function in `H⁰(𝒪(A))` is effectivity of `A + div f`.**
The `ord`-calculus form of the pole bound: `f ∈ 𝒪(A)(⊤) ↔ 0 ≤ A + div f`. -/
theorem mem_divisorSections_top_iff {A : X.CurveDivisor} {f : X.functionField}
    (hf : f ≠ 0) :
    f ∈ divisorSections K A ⊤ ↔
      0 ≤ A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf) := by
  rw [mem_divisorSections_of_nonempty K (top_opens_nonempty (X := X))]
  constructor
  · intro h
    refine Finsupp.le_def.mpr (fun p => ?_)
    have hb := h p.1 p.2 trivial
    have hval : (Units.mk0 f hf : X.functionField) = f := rfl
    rw [← hval, Scheme.ord_val_eq K (Units.mk0 f hf) p.2,
      divisorBound_le_divisorBound_iff p.2,
      CurveDivisor.coeffAt_neg] at hb
    change (0 : ℤ)
      ≤ coeffAt p.2 (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf))
    rw [CurveDivisor.coeffAt_add]
    omega
  · intro h x hx _
    have hp := Finsupp.le_def.mp h ⟨x, hx⟩
    change (0 : ℤ)
      ≤ coeffAt hx (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) at hp
    rw [CurveDivisor.coeffAt_add] at hp
    have hval : (Units.mk0 f hf : X.functionField) = f := rfl
    rw [← hval, Scheme.ord_val_eq K (Units.mk0 f hf) hx,
      divisorBound_le_divisorBound_iff hx,
      CurveDivisor.coeffAt_neg]
    omega

end Membership

/-! ## Multiplication -/

section MulLinear

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [IsIntegral X]

/-- **Multiplication by a fixed rational function**, as a `K`-linear endomorphism of the
function field: `s ↦ a · s`. The `μ`-map vocabulary of the carve `(♦)` (worksheet §3.1);
for `a ≠ 0` it is the underlying map of `Scheme.mulByUnit`. -/
noncomputable def Scheme.mulLinear (a : X.functionField) :
    X.functionField →ₗ[K] X.functionField where
  toFun s := a * s
  map_add' _ _ := mul_add _ _ _
  map_smul' r s := by
    simp only [RingHom.id_apply, Scheme.functionFieldOverModule_smul_def]
    exact mul_left_comm _ _ _

@[simp] lemma Scheme.mulLinear_apply (a s : X.functionField) :
    Scheme.mulLinear K a s = a * s := rfl

end MulLinear

section Multiplication

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- **The product rule for pole bounds**: `H⁰(𝒪(A)) · H⁰(𝒪(B)) ⊆ H⁰(𝒪(A + B))` — the
valuation is multiplicative and `divisorBound` turns divisor addition into multiplication. -/
theorem mul_mem_divisorSections_top {A B : X.CurveDivisor} {f h : X.functionField}
    (hfA : f ∈ divisorSections K A ⊤) (hhB : h ∈ divisorSections K B ⊤) :
    f * h ∈ divisorSections K (A + B) ⊤ := by
  rw [mem_divisorSections_of_nonempty K (top_opens_nonempty (X := X))] at hfA hhB ⊢
  intro x hx hxU
  rw [map_mul, Scheme.divisorBound_add]
  exact mul_le_mul' (hfA x hx hxU) (hhB x hx hxU)

/-- **The shift identity**: multiplication by a nonzero rational function `f` carries
`H⁰(𝒪(A))` exactly onto `H⁰(𝒪(A − div f))` — the submodule-image form of the sheaf
isomorphism `mulEquivDivisorSheaf`. -/
theorem map_mulLinear_divisorSections_top {f : X.functionField} (hf : f ≠ 0)
    (A : X.CurveDivisor) :
    Submodule.map (Scheme.mulLinear K f) (divisorSections K A ⊤)
      = divisorSections K
          (A - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) ⊤ := by
  have htop : ((⊤ : X.Opens) : Set X).Nonempty := top_opens_nonempty (X := X)
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    rw [divisorSections_of_nonempty K htop] at hs ⊢
    rw [Scheme.mulLinear_apply]
    exact (Scheme.mem_boundedSections_mul_iff K (Units.mk0 f hf) A s).mpr hs
  · intro t ht
    rw [divisorSections_of_nonempty K htop] at ht
    refine Submodule.mem_map.mpr ⟨(↑(Units.mk0 f hf)⁻¹ : X.functionField) * t, ?_, ?_⟩
    · rw [divisorSections_of_nonempty K htop,
        ← Scheme.mem_boundedSections_mul_iff K (Units.mk0 f hf) A]
      have hcancel : (Units.mk0 f hf : X.functionField)
          * ((↑(Units.mk0 f hf)⁻¹ : X.functionField) * t) = t := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
      rwa [hcancel]
    · have hcancel : (Units.mk0 f hf : X.functionField)
          * ((↑(Units.mk0 f hf)⁻¹ : X.functionField) * t) = t := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
      exact hcancel

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- **The intersection identity**: `H⁰(𝒪(A)) ⊓ H⁰(𝒪(B)) = H⁰(𝒪(A ⊓ B))` — a pole bounded
by both divisors is bounded by their pointwise minimum. Pure `ord` calculus. -/
theorem divisorSections_inf (A B : X.CurveDivisor) :
    divisorSections K A ⊤ ⊓ divisorSections K B ⊤
      = divisorSections K (A ⊓ B) ⊤ := by
  have htop : ((⊤ : X.Opens) : Set X).Nonempty := top_opens_nonempty (X := X)
  have hbound : ∀ {x : X} (hx : x ≠ genericPoint X) (z : WithZero (Multiplicative ℤ)),
      z ≤ Scheme.divisorBound (A ⊓ B) hx ↔
        z ≤ Scheme.divisorBound A hx ∧ z ≤ Scheme.divisorBound B hx := by
    intro x hx z
    have hmin : Scheme.divisorBound (A ⊓ B) hx
        = min (Scheme.divisorBound A hx) (Scheme.divisorBound B hx) := by
      rcases min_cases (coeffAt hx A) (coeffAt hx B) with ⟨heq, hle⟩ | ⟨heq, hle⟩
      · rw [min_eq_left ((divisorBound_le_divisorBound_iff hx).mpr hle)]
        rw [Scheme.divisorBound, Scheme.divisorBound]
        congr 2
      · rw [min_eq_right ((divisorBound_le_divisorBound_iff hx).mpr hle.le)]
        rw [Scheme.divisorBound, Scheme.divisorBound]
        congr 2
    rw [hmin, le_min_iff]
  apply le_antisymm
  · intro g hg
    have hgA := (Submodule.mem_inf.mp hg).1
    have hgB := (Submodule.mem_inf.mp hg).2
    rw [mem_divisorSections_of_nonempty K htop] at hgA hgB ⊢
    intro x hx hxU
    exact (hbound hx _).mpr ⟨hgA x hx hxU, hgB x hx hxU⟩
  · intro g hg
    rw [mem_divisorSections_of_nonempty K htop] at hg
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩ <;>
      · rw [mem_divisorSections_of_nonempty K htop]
        intro x hx hxU
        have hb := (hbound hx _).mp (hg x hx hxU)
        tauto

end Multiplication

/-! ## The `h⁰` bridge and finite-dimensionality -/

section Bridge

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]

/-- The degree-zero cohomology of the divisor sheaf is its module of global sections,
`K`-linearly: the specialization of `Sheaf.HModule.linearEquiv₀` to `𝒪(A)`. -/
noncomputable def divisorSectionsEquivH0 (A : X.CurveDivisor) :
    Sheaf.HModule (X.divisorSheaf K A) 0 ≃ₗ[K] ↥(divisorSections K A ⊤) :=
  Sheaf.HModule.linearEquiv₀ (Opens.grothendieckTopology (X : TopCat))
    (isTerminalTop : IsTerminal (⊤ : X.Opens)) (X.divisorSheaf K A)

/-- **The `h⁰` bridge** (★): the `K`-dimension of the global-section submodule
`H⁰(𝒪(A)) ⊆ K(X)` is `h⁰(𝒪(A))`. Every dimension count of the P-fib route reads section
spaces through this bridge. -/
theorem finrank_divisorSections_top (A : X.CurveDivisor) :
    Module.finrank K ↥(divisorSections K A ⊤) = Sheaf.h0 (X.divisorSheaf K A) :=
  ((divisorSectionsEquivH0 K A).finrank_eq).symm

variable [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-- **`H⁰(𝒪(A))` is finite-dimensional** as a submodule of the function field — transport of
`moduleFinite_hModule_divisorSheaf_zero` across the degree-zero identification. -/
instance moduleFinite_divisorSections_top (A : X.CurveDivisor) :
    Module.Finite K ↥(divisorSections K A ⊤) :=
  Module.Finite.equiv (divisorSectionsEquivH0 K A)

end Bridge

end AlgebraicGeometry
