/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.MulEquiv
import AlgebraicJacobian.RiemannRoch.Ledger.DivisorSheafZero
import AlgebraicJacobian.RiemannRoch.Ledger.Devissage
import AlgebraicJacobian.RiemannRoch.Ledger.FiberDivisor
import AlgebraicJacobian.RiemannRoch.Ledger.AffineVanishingQcoh

/-!
# Quasi-coherence packaging of the divisor sheaves `𝒪(D)`

The divisor sheaves of the curve bundle satisfy the quasi-coherence packaging `Scheme.QcohOn`
of `Ledger/QcohSections.lean` on **every** open `U`, so the twisted affine Serre vanishing
(`IsAffineOpen.subsingleton_hModule'_one_of_qcoh`, `Ledger/AffineVanishingQcoh.lean`) fires on
them over every affine open.  That is what discharges the two affine-vanishing instances the
two-cover `H¹` carrier consumes at the chart preimages `V₀`, `V₁`.

## Provenance

AJCR `RiemannRoch/FLVQcoh.lean`, bodies unchanged.  **This file is the empirical confirmation
of the port audit**: AJCR imports it against `Picard/PresentationDivisor.lean`, and that edge —
the single entry point of AJCR's fourteen-module `Picard.*` presentation cone into the vanishing
chain — turned out to be needed only for the `coeffAt` calculus, which
`Ledger/FiberDivisor.lean` now carries.  Substituting that import for the Picard one, the file
elaborates with **no other change**: no `picClass`, no `CechPic`, no meromorphic presentation.
So the cone was bundling, not dependency, and the claim is now checked rather than argued.

For the curve bundle `X` (integral, smooth of relative dimension one and quasi-compact over
a field `K`) and a Weil divisor `D`:

* **(P1) action.** An ambient section `r : Γ(X, U)` acts on `𝒪(D)(W)` for `W ≤ U` by
  multiplication with its germ at the generic point: `ord_x (germ_η r) ≤ 1` at every closed
  `x ∈ U` (`Scheme.ord_algebraMap_stalk_le_one` through the germ/stalk seam), so the pole
  bounds of `D` are preserved. Naturality under restriction is automatic: restrictions of
  `𝒪(D)`-sections are inclusions of submodules of `K(X)`.
* **(P2a) denominator clearing** is ord bookkeeping: `germ_η g` has order `0` on `D(g)`
  (`Scheme.ord_eq_one_of_mem_basicOpen`) and order `≥ 1` at the finitely many zeros of `g`
  (the divisor `div (germ_η g)` is finitely supported), so a large power of `g` clears the
  poles of any section of `𝒪(D)(V ⊓ D(g))` along `V ∖ D(g)` — the same pole-clearing
  pattern as the lattice exhaustion `iSup_fiberLattice` of `Ledger/FiberLattice.lean`.
* **(P2b) defect annihilation is degenerate** for this family: restrictions between
  nonempty opens are injective, and when `V ⊓ D(g)` is empty while `V` is not, the germ
  `germ_η g` is a non-unit of the function *field*, hence zero — so `g` itself annihilates.

The empty-open corners are absorbed by the `⊥`-guard of `Scheme.divisorSections`; when `U`
does not contain the generic point (i.e. `U = ∅`), all section modules over `W ≤ U` are
zero and the packaging is trivial.

## Main declarations

* `AlgebraicGeometry.Scheme.divisorSheaf.instQcohOn` — the instance
  `Scheme.QcohOn (X.divisorSheaf K D) U`, for every open `U`.
* `AlgebraicGeometry.IsAffineOpen.subsingleton_hModule'_divisorSheaf_one` — the discharge:
  `Subsingleton (Sheaf.HModule' (X.divisorSheaf K D) U 1)` for affine `U`. This is the pair of
  vanishing instances the two-cover H¹ carrier (`Scheme.twoCoverH1LinearEquiv`) consumes at the
  chart preimages `V₀`, `V₁` in `Ledger/FiberVanishing.lean`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

section OrderBookkeeping

/-! ## Order bookkeeping for ambient sections

Coefficient facts about `div (germ_η g)` for an ambient section `g : Γ(X, U)`: nonnegative
on `U` (regularity), zero on `D(g)` (unit germ), at least `1` off `D(g)` (genuine zero).
Everything is a statement about `coeffAt` of a principal divisor, per the D1 discipline. -/

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- The divisor bound `≤`-comparison at a point reduces to the pointwise coefficient
`≤`-comparison in `ℤ`. -/
private lemma divisorBound_le_iff {A B : X.CurveDivisor} {x : X} (hx : x ≠ genericPoint X) :
    Scheme.divisorBound A hx ≤ Scheme.divisorBound B hx ↔ coeffAt hx A ≤ coeffAt hx B := by
  simp only [Scheme.divisorBound, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  rfl

/-- The classical order of `w⁻¹` is the negative of that of `w`, coefficient-wise. -/
private lemma coeffAt_divOf_inv (w : X.functionFieldˣ) {x : X} (hx : x ≠ genericPoint X) :
    coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w⁻¹) =
      - coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w) := by
  have h : Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w⁻¹
      + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w = 0 := by
    rw [← Scheme.divOf_mul (X ↘ Spec (CommRingCat.of K)), inv_mul_cancel,
      Scheme.divOf_one (X ↘ Spec (CommRingCat.of K))]
  have hc := congrArg (coeffAt hx) h
  rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_zero] at hc
  linarith

/-- The classical order of `wⁿ` scales linearly. -/
private lemma coeffAt_divOf_pow (w : X.functionFieldˣ) (n : ℕ) {x : X}
    (hx : x ≠ genericPoint X) :
    coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (w ^ n)) =
      (n : ℤ) * coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w) := by
  induction n with
  | zero => rw [pow_zero, Scheme.divOf_one, CurveDivisor.coeffAt_zero, Nat.cast_zero, zero_mul]
  | succ m ih =>
    rw [pow_succ, Scheme.divOf_mul, CurveDivisor.coeffAt_add, ih, Nat.cast_succ]; ring

/-- The nonnegativity/regularity bridge: the classical order `div w` of a unit `w` is
nonnegative at `x` exactly when its valuation order is `≤ 1` (no pole). -/
private lemma zero_le_coeffAt_divOf_iff_ord_le_one (w : X.functionFieldˣ) {x : X}
    (hx : x ≠ genericPoint X) :
    (0 : ℤ) ≤ coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w) ↔
      Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (w : X.functionField) ≤ 1 := by
  rw [Scheme.ord_val_eq K w hx, ← Scheme.divisorBound_zero hx, divisorBound_le_iff hx,
    CurveDivisor.coeffAt_zero, CurveDivisor.coeffAt_neg, neg_nonpos]

/-- Membership of a *nonzero* rational function in a bounded lattice, read through its
principal divisor: `s ∈ 𝒪(A)(U)` iff `-div(s) ≤ A` at every closed point of `U`. -/
private lemma mem_boundedSections_unit_iff (s : X.functionFieldˣ) (A : X.CurveDivisor)
    (U : X.Opens) :
    (s : X.functionField) ∈ Scheme.boundedSections K A U ↔
      ∀ (x : X) (hx : x ≠ genericPoint X), x ∈ U →
        - coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) s) ≤ coeffAt hx A := by
  rw [Scheme.mem_boundedSections]
  refine forall_congr' (fun x => forall_congr' (fun hx => imp_congr_right (fun _ => ?_)))
  rw [Scheme.ord_val_eq K s hx, divisorBound_le_iff hx, CurveDivisor.coeffAt_neg]

/-- **Trivial order on the basic open.** If the unit `w` of the function field is the germ
at `η` of the ambient section `g` and `x ∈ D(g)`, then `w` has coefficient `0` at `x`. -/
private lemma coeffAt_divOf_eq_zero_of_mem_basicOpen {U : X.Opens}
    (hηU : genericPoint X ∈ U) (g : Γ(X, U)) {w : X.functionFieldˣ}
    (hw : (w : X.functionField) = (X.presheaf.germ U (genericPoint X) hηU).hom g)
    {x : X} (hx : x ≠ genericPoint X) (hxg : x ∈ X.basicOpen g) :
    coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w) = 0 := by
  have h1 : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (w : X.functionField) = 1 := by
    rw [hw]
    exact Scheme.ord_eq_one_of_mem_basicOpen (X ↘ Spec (CommRingCat.of K)) hx g hηU hxg
  have h2 : (0 : ℤ) ≤ coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w) :=
    (zero_le_coeffAt_divOf_iff_ord_le_one K w hx).mpr h1.le
  have h3 : (0 : ℤ) ≤ coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w⁻¹) :=
    (zero_le_coeffAt_divOf_iff_ord_le_one K w⁻¹ hx).mpr
      (by rw [Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one])
  rw [coeffAt_divOf_inv K w hx] at h3
  omega

/-- **Strict order at a zero.** If the unit `w` is the germ at `η` of the ambient section
`g` and `x ∈ U` lies *outside* `D(g)`, then `w` has a genuine zero at `x`: its coefficient
is at least `1`. The germ of `g` at `x` is a non-unit of the DVR stalk, so its valuation is
`< 1`. -/
private lemma one_le_coeffAt_divOf_of_notMem_basicOpen {U : X.Opens}
    (hηU : genericPoint X ∈ U) (g : Γ(X, U)) {w : X.functionFieldˣ}
    (hw : (w : X.functionField) = (X.presheaf.germ U (genericPoint X) hηU).hom g)
    {x : X} (hx : x ≠ genericPoint X) (hxU : x ∈ U) (hxg : x ∉ X.basicOpen g) :
    1 ≤ coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w) := by
  have hnn : (0 : ℤ) ≤ coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w) := by
    rw [zero_le_coeffAt_divOf_iff_ord_le_one K w hx, hw,
      germ_generic_eq_algebraMap_germ hηU hxU g]
    exact Scheme.ord_algebraMap_stalk_le_one K hx _
  have hnu : ¬ IsUnit ((X.presheaf.germ U x hxU).hom g) := fun hu =>
    hxg ((X.mem_basicOpen g x hxU).mpr hu)
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hx
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hx
  have hlt : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (w : X.functionField) < 1 := by
    rw [hw, germ_generic_eq_algebraMap_germ hηU hxU g, Scheme.ord_eq_valuation]
    refine (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (stalkHeightOne X x) _).mpr ?_
    by_contra h
    exact hnu (IsLocalRing.notMem_maximalIdeal.mp h)
  have hne : coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w) ≠ 0 := by
    intro h0
    apply ne_of_lt hlt
    rw [← Scheme.ordZ_eq_one_iff]
    have hc := CurveDivisor.coeffAt_divOf (X ↘ Spec (CommRingCat.of K)) w hx
    rw [h0] at hc
    exact Multiplicative.toAdd.injective (by rw [← hc, toAdd_one])
  omega

end OrderBookkeeping

section Packaging

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-! ## The two localization lemmas for `𝒪(D)`-sections -/

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- **(P1) membership.** Multiplication by the germ at the generic point of an ambient
section `r : Γ(X, U)` preserves the pole bounds of `𝒪(D)` over any `W ≤ U`: the germ is
integral at every point of `U` (order `≤ 1`), so it can only improve the bounds. -/
private lemma germ_mul_mem_divisorSections {U W : X.Opens} (hηU : genericPoint X ∈ U)
    (hWU : W ≤ U) (r : Γ(X, U)) {D : X.CurveDivisor} {a : X.functionField}
    (ha : a ∈ divisorSections K D W) :
    (X.presheaf.germ U (genericPoint X) hηU).hom r * a ∈ divisorSections K D W := by
  by_cases hW : (W : Set X).Nonempty
  · rw [divisorSections_of_nonempty K hW] at ha ⊢
    rw [Scheme.mem_boundedSections] at ha ⊢
    intro x hx hxW
    rw [map_mul]
    calc Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx
            ((X.presheaf.germ U (genericPoint X) hηU).hom r)
          * Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx a
        ≤ 1 * Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx a := by
          gcongr
          rw [germ_generic_eq_algebraMap_germ hηU (hWU hxW) r]
          exact Scheme.ord_algebraMap_stalk_le_one K hx _
      _ = Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx a := one_mul _
      _ ≤ Scheme.divisorBound D hx := ha x hx hxW
  · rw [divisorSections_of_empty K hW] at ha
    have ha0 : a = 0 := (Submodule.mem_bot K).mp ha
    rw [ha0, mul_zero]
    exact Submodule.zero_mem _

/-- **(P2a) pole clearing.** A rational function with `𝒪(D)`-bounded poles on `V ⊓ D(g)`
acquires `𝒪(D)`-bounded poles on all of `V ≤ U` after multiplication by a large power of
`germ_η g`: the power clears the finitely many poles along the zero locus of `g` in `V`,
where `germ_η g` vanishes to order `≥ 1`. -/
private lemma exists_pow_germ_mul_mem_divisorSections {U V : X.Opens}
    (hηU : genericPoint X ∈ U) (hVU : V ≤ U) (g : Γ(X, U)) (D : X.CurveDivisor)
    (hne : ((V ⊓ X.basicOpen g : X.Opens) : Set X).Nonempty) {a : X.functionField}
    (ha : a ∈ divisorSections K D (V ⊓ X.basicOpen g)) :
    ∃ N : ℕ, ((X.presheaf.germ U (genericPoint X) hηU).hom g) ^ N * a
      ∈ divisorSections K D V := by
  classical
  obtain ⟨z, hz⟩ := hne
  have hV : (V : Set X).Nonempty := ⟨z, (inf_le_left : V ⊓ X.basicOpen g ≤ V) hz⟩
  have hηg : genericPoint X ∈ X.basicOpen g :=
    (Scheme.genericPoint_mem_of_nonempty (U := V ⊓ X.basicOpen g) ⟨z, hz⟩).2
  have hγu : IsUnit ((X.presheaf.germ U (genericPoint X) hηU).hom g) :=
    (X.mem_basicOpen g (genericPoint X) hηU).mp hηg
  by_cases ha0 : a = 0
  · exact ⟨0, by rw [ha0, mul_zero]; exact Submodule.zero_mem _⟩
  set w : X.functionFieldˣ := hγu.unit with hwdef
  have hwval : (w : X.functionField) = (X.presheaf.germ U (genericPoint X) hηU).hom g :=
    hγu.unit_spec
  set s : X.functionFieldˣ := Units.mk0 a ha0 with hsdef
  have hsval : (s : X.functionField) = a := rfl
  -- read the hypothesis as coefficient bounds on the overlap
  rw [divisorSections_of_nonempty K ⟨z, hz⟩] at ha
  have haB := (mem_boundedSections_unit_iff K s D (V ⊓ X.basicOpen g)).mp (hsval ▸ ha)
  -- the pole-clearing exponent: the finite set of points to clear, and the budget
  set Z : Finset {p : X // p ≠ genericPoint X} :=
    (toFinsupp D).support
      ∪ (toFinsupp (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) s)).support with hZ
  set B : {p : X // p ≠ genericPoint X} → ℕ := fun p =>
    (- coeffAt p.2 (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) s)
      - coeffAt p.2 D).toNat with hB
  set N : ℕ := Z.sup B with hN
  refine ⟨N, ?_⟩
  have hval : ((X.presheaf.germ U (genericPoint X) hηU).hom g) ^ N * a
      = ((w ^ N * s : X.functionFieldˣ) : X.functionField) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hwval, hsval]
  rw [divisorSections_of_nonempty K hV, hval,
    mem_boundedSections_unit_iff K (w ^ N * s) D V]
  intro x hx hxV
  have hprod : coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (w ^ N * s))
      = (N : ℤ) * coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w)
        + coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) s) := by
    rw [Scheme.divOf_mul, CurveDivisor.coeffAt_add, coeffAt_divOf_pow K w N hx]
  rw [hprod]
  by_cases hxg : x ∈ X.basicOpen g
  · -- on the basic open: `w` has trivial order, use the overlap bound directly
    rw [coeffAt_divOf_eq_zero_of_mem_basicOpen K hηU g hwval hx hxg, mul_zero, zero_add]
    exact haB x hx ⟨hxV, hxg⟩
  · -- at a zero of `g`: order `≥ 1`, the power `N` clears the pole
    have h1 : 1 ≤ coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w) :=
      one_le_coeffAt_divOf_of_notMem_basicOpen K hηU g hwval hx (hVU hxV) hxg
    by_cases hxZ : (⟨x, hx⟩ : {p : X // p ≠ genericPoint X}) ∈ Z
    · have hle : B ⟨x, hx⟩ ≤ N := by rw [hN]; exact Finset.le_sup hxZ
      have hle2 : (- coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) s)
          - coeffAt hx D).toNat ≤ N := hle
      have h2 : - coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) s)
          - coeffAt hx D ≤ (N : ℤ) :=
        le_trans (Int.self_le_toNat _) (by exact_mod_cast hle2)
      have h3 : (N : ℤ) ≤ (N : ℤ)
          * coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) w) := by
        nlinarith [h1, Nat.cast_nonneg (α := ℤ) N]
      linarith
    · -- outside both supports: all coefficients vanish
      have hD0 : coeffAt hx D = 0 := by
        by_contra h
        exact hxZ (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h))
      have hs0 : coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) s) = 0 := by
        by_contra h
        exact hxZ (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr h))
      rw [hD0, hs0, add_zero, neg_nonpos]
      exact mul_nonneg (Nat.cast_nonneg N) (by linarith)

/-! ## The value calculus for sheaf-typed sections -/

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- The underlying rational function of a sum of `𝒪(D)`-sections. -/
private lemma divisorVal_add {D : X.CurveDivisor} {W : X.Opens}
    (a b : (X.divisorSheaf K D).obj.obj (op W)) :
    divisorVal K (a + b) = divisorVal K a + divisorVal K b := rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- The underlying rational function of the zero `𝒪(D)`-section. -/
private lemma divisorVal_zero {D : X.CurveDivisor} {W : X.Opens} :
    divisorVal K (0 : (X.divisorSheaf K D).obj.obj (op W)) = 0 := rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- The underlying rational function of a restricted `𝒪(D)`-section (nonempty target) is
unchanged: restriction is the submodule inclusion. -/
private lemma divisorVal_secRes {D : X.CurveDivisor} {V W : X.Opens} (hVW : V ≤ W)
    (hV : (V : Set X).Nonempty) (s : (X.divisorSheaf K D).obj.obj (op W)) :
    divisorVal K (secRes (X.divisorSheaf K D) hVW s) = divisorVal K s :=
  divisorPresheaf_map_val K (homOfLE hVW).op hV s

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- Sections of `𝒪(D)` over an empty open form a subsingleton, at the sheaf spelling. -/
private lemma divisorSheaf_obj_subsingleton {D : X.CurveDivisor} {W : X.Opens}
    (hW : ¬ (W : Set X).Nonempty) :
    Subsingleton ((X.divisorSheaf K D).obj.obj (op W)) :=
  divisorPresheaf_obj_subsingleton K hW

/-- An open below an open avoiding the generic point is empty. -/
private lemma not_nonempty_of_le_of_notMem {U W : X.Opens} (hWU : W ≤ U)
    (hη : genericPoint X ∉ U) : ¬ (W : Set X).Nonempty := fun h =>
  hη (hWU (Scheme.genericPoint_mem_of_nonempty h))

/-! ## The packaging -/

/-- The (P1) scaling operation of the packaging: an ambient section `r : Γ(X, U)` acts on
`𝒪(D)(W)`, `W ≤ U`, by multiplication with its germ at the generic point. -/
private noncomputable def divisorQsmul {U : X.Opens} (hηU : genericPoint X ∈ U)
    (D : X.CurveDivisor) {W : X.Opens} (hWU : W ≤ U) (r : Γ(X, U))
    (s : (X.divisorSheaf K D).obj.obj (op W)) : (X.divisorSheaf K D).obj.obj (op W) :=
  (⟨(X.presheaf.germ U (genericPoint X) hηU).hom r * divisorVal K s,
    germ_mul_mem_divisorSections K hηU hWU r (divisorVal_mem K s)⟩ :
    divisorSections K D W)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- The underlying rational function of the scaled section. -/
private lemma divisorVal_divisorQsmul {U : X.Opens} (hηU : genericPoint X ∈ U)
    (D : X.CurveDivisor) {W : X.Opens} (hWU : W ≤ U) (r : Γ(X, U))
    (s : (X.divisorSheaf K D).obj.obj (op W)) :
    divisorVal K (divisorQsmul K hηU D hWU r s)
      = (X.presheaf.germ U (genericPoint X) hηU).hom r * divisorVal K s := rfl

open Classical in
/-- **The divisor sheaves are quasi-coherently packaged on every open** (FLV-2(a)):
`𝒪(D)` satisfies `Scheme.QcohOn` on every `U`, with the ambient action by
germ-at-`η`-multiplication and the localization axioms discharged by ord bookkeeping.
Through the ported twisted affine vanishing this yields
`IsAffineOpen.subsingleton_hModule'_divisorSheaf_one`. -/
noncomputable instance Scheme.divisorSheaf.instQcohOn (D : X.CurveDivisor) (U : X.Opens) :
    Scheme.QcohOn (X.divisorSheaf K D) U :=
  if hηU : genericPoint X ∈ U then
    { qsmul := divisorQsmul K hηU D
      one_qsmul := fun {W} hWU m => divisorSection_ext K (by
        rw [divisorVal_divisorQsmul, map_one, one_mul])
      mul_qsmul := fun {W} hWU r s m => divisorSection_ext K (by
        rw [divisorVal_divisorQsmul, divisorVal_divisorQsmul, divisorVal_divisorQsmul,
          map_mul, mul_assoc])
      add_qsmul := fun {W} hWU r s m => divisorSection_ext K (by
        rw [divisorVal_divisorQsmul, divisorVal_add, divisorVal_divisorQsmul,
          divisorVal_divisorQsmul, map_add, add_mul])
      qsmul_add := fun {W} hWU r m n => divisorSection_ext K (by
        rw [divisorVal_divisorQsmul, divisorVal_add, divisorVal_add,
          divisorVal_divisorQsmul, divisorVal_divisorQsmul, mul_add])
      secRes_qsmul := fun {V W} hVW hWU r m => by
        by_cases hV : (V : Set X).Nonempty
        · refine divisorSection_ext K ?_
          rw [divisorVal_secRes K hVW hV, divisorVal_divisorQsmul,
            divisorVal_divisorQsmul, divisorVal_secRes K hVW hV]
        · haveI := divisorSheaf_obj_subsingleton K (D := D) (W := V) hV
          exact Subsingleton.elim _ _
      exists_secRes_eq_qsmul_pow := fun {V} hV hVU g c => by
        by_cases hne : ((V ⊓ X.basicOpen g : X.Opens) : Set X).Nonempty
        · obtain ⟨N, hN⟩ := exists_pow_germ_mul_mem_divisorSections K hηU hVU g D hne
            (divisorVal_mem K c)
          refine ⟨N,
            (⟨((X.presheaf.germ U (genericPoint X) hηU).hom g) ^ N * divisorVal K c, hN⟩ :
              divisorSections K D V), ?_⟩
          refine divisorSection_ext K ?_
          rw [divisorVal_secRes K inf_le_left hne, divisorVal_divisorQsmul, map_pow]
          rfl
        · haveI := divisorSheaf_obj_subsingleton K (D := D)
            (W := V ⊓ X.basicOpen g) hne
          exact ⟨0, 0, Subsingleton.elim _ _⟩
      exists_qsmul_pow_eq_zero := fun {V} hV hVU g t ht => by
        refine ⟨1, divisorSection_ext K ?_⟩
        rw [divisorVal_divisorQsmul, pow_one, divisorVal_zero]
        by_cases hne : ((V ⊓ X.basicOpen g : X.Opens) : Set X).Nonempty
        · -- the restriction is injective on values: `t` itself vanishes
          have hval : divisorVal K t = 0 := by
            have h1 := congrArg (divisorVal K) ht
            rwa [divisorVal_secRes K inf_le_left hne, divisorVal_zero] at h1
          rw [hval, mul_zero]
        · by_cases hVne : (V : Set X).Nonempty
          · -- `g` has empty basic open in `V ∋ η`: its germ is a non-unit of a field
            have hg0 : (X.presheaf.germ U (genericPoint X) hηU).hom g = 0 := by
              have hηV : genericPoint X ∈ V := Scheme.genericPoint_mem_of_nonempty hVne
              have hnb : genericPoint X ∉ X.basicOpen g := fun hmem =>
                hne ⟨genericPoint X, ⟨hηV, hmem⟩⟩
              by_contra h0
              exact hnb ((X.mem_basicOpen g (genericPoint X) hηU).mpr
                (isUnit_iff_ne_zero.mpr h0))
            rw [hg0, zero_mul]
          · -- `V` empty: `t` is the zero section
            have hval : divisorVal K t = 0 := by
              have hmem := divisorVal_mem K t
              rw [divisorSections_of_empty K hVne, Submodule.mem_bot] at hmem
              exact hmem
            rw [hval, mul_zero] }
  else
    { qsmul := fun {W} _ _ s => s
      one_qsmul := fun {W} _ m => rfl
      mul_qsmul := fun {W} _ _ _ m => rfl
      add_qsmul := fun {W} hWU r s m => by
        haveI := divisorSheaf_obj_subsingleton K (D := D) (W := W)
          (not_nonempty_of_le_of_notMem hWU hηU)
        exact Subsingleton.elim _ _
      qsmul_add := fun {W} _ _ m n => rfl
      secRes_qsmul := fun {V W} _ _ _ m => rfl
      exists_secRes_eq_qsmul_pow := fun {V} hV hVU g c => by
        haveI := divisorSheaf_obj_subsingleton K (D := D) (W := V ⊓ X.basicOpen g)
          (not_nonempty_of_le_of_notMem (le_trans inf_le_left hVU) hηU)
        exact ⟨0, 0, Subsingleton.elim _ _⟩
      exists_qsmul_pow_eq_zero := fun {V} hV hVU g t ht => by
        haveI := divisorSheaf_obj_subsingleton K (D := D) (W := V)
          (not_nonempty_of_le_of_notMem hVU hηU)
        exact ⟨0, Subsingleton.elim _ _⟩ }

/-- **The twisted affine vanishing for divisor sheaves** (FLV-2(a) discharge): the
degree-one cohomology of any affine open with coefficients in any divisor sheaf `𝒪(D)`
vanishes — the ported headline `IsAffineOpen.subsingleton_hModule'_one_of_qcoh` fired
through the packaging instance. Instantiated at the chart preimages `V₀`, `V₁` of the
π-two-cover, these are the two vanishing instances the H¹ carrier
`Scheme.twoCoverH1LinearEquiv` consumes. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.subsingleton_hModule'_divisorSheaf_one
    {U : X.Opens} (hU : IsAffineOpen U) (D : X.CurveDivisor) :
    Subsingleton (Sheaf.HModule' (X.divisorSheaf K D) U 1) :=
  hU.subsingleton_hModule'_one_of_qcoh (X.divisorSheaf K D)

end Packaging

end AlgebraicGeometry
