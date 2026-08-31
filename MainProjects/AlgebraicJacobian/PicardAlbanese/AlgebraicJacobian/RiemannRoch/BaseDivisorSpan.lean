/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.BaseDivisor
import AlgebraicJacobian.RiemannRoch.MulEquiv

/-!
# DDR-3 achiever purity — the base divisor of a span is achieved on the spanning set

The **pure-tensor minimality step** of the DDR-3 seed provider (I-0198 route item (ii)):
at a residue-field fibre `κ(p)`, the window `K ⊗ κ(p)` is the `κ(p)`-span of the *pure*
images `ψ ⊗ 1`, so the base multiplicity of the span at a closed point is already achieved
by a pure element — because the order of a sum is at least the minimum of the orders
(the valuation ultrametric) and `κ(p)`-scalars do not move orders (constants of the base
field have divisor zero).

* `AlgebraicGeometry.Scheme.divOf_functionFieldOverAlgebraMap` — constants have divisor
  zero: `div(c·1) = 0` for `c ≠ 0` in the base field;
* `AlgebraicGeometry.Scheme.divOf_smul` — the principal divisor is scalar-invariant:
  `div(c • f) = div(f)`;
* `AlgebraicGeometry.Scheme.min_coeffAt_divOf_le_add` — **the ultrametric**:
  `ordₓ(f + g) ≥ min (ordₓ f) (ordₓ g)` in `coeffAt`/`divOf` form;
* `AlgebraicGeometry.Scheme.exists_coeffAt_divOf_le_sum` — the finite-sum form: some
  summand has order `≤` the order of the sum;
* `AlgebraicGeometry.Scheme.exists_achiever_of_span` — **the keystone**: for
  `T := span K S` with `T ≤ H⁰(𝒪(A))`, the base multiplicity `bd(T)ₓ` is achieved by an
  element of `S` itself (`exists_coeffAt_eq_baseDivisorAt` refined to the spanning set).

Everything is `ord`/`coeffAt` calculus through the landed bridges
(`Scheme.ord_val_eq`, `divisorBound_le_iff`, `Valuation.map_add`); no cohomology.
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

/-! ## Constants have divisor zero -/

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- The `K`-structure image of a nonzero constant is nonzero in the function field. -/
lemma Scheme.functionFieldOverAlgebraMap_ne_zero {c : K} (hc : c ≠ 0) :
    Scheme.functionFieldOverAlgebraMap K X c ≠ 0 := by
  intro h0
  have h1 := congrArg (· * Scheme.functionFieldOverAlgebraMap K X c⁻¹) h0
  simp only [← map_mul, mul_inv_cancel₀ hc, map_one, zero_mul] at h1
  exact one_ne_zero h1

/-- **Constants have divisor zero**: the principal divisor of the `K`-structure image of a
nonzero constant vanishes — both `c` and `c⁻¹` have nonnegative order everywhere, and
their orders are opposite. -/
lemma Scheme.divOf_functionFieldOverAlgebraMap {c : K} (hc : c ≠ 0) :
    Scheme.divOf (X ↘ Spec (CommRingCat.of K))
      (Units.mk0 (Scheme.functionFieldOverAlgebraMap K X c)
        (Scheme.functionFieldOverAlgebraMap_ne_zero K hc)) = 0 := by
  -- the order of a structure constant is nonnegative at every closed point
  have hnn : ∀ {d : K} (hd : d ≠ 0) (x : X) (hx : x ≠ genericPoint X),
      (0 : ℤ) ≤ coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K))
        (Units.mk0 (Scheme.functionFieldOverAlgebraMap K X d)
          (Scheme.functionFieldOverAlgebraMap_ne_zero K hd))) := by
    intro d hd x hx
    have hord : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx
        ((Units.mk0 (Scheme.functionFieldOverAlgebraMap K X d)
          (Scheme.functionFieldOverAlgebraMap_ne_zero K hd) :
            X.functionFieldˣ) : X.functionField) ≤ 1 :=
      Scheme.ord_functionFieldOverAlgebraMap_le_one K hx d
    rw [Scheme.ord_val_eq K (Units.mk0 _ (Scheme.functionFieldOverAlgebraMap_ne_zero K hd))
        hx, ← Scheme.divisorBound_zero hx] at hord
    have hcoeff := (divisorBound_le_divisorBound_iff hx).mp hord
    rw [CurveDivisor.coeffAt_zero, CurveDivisor.coeffAt_neg] at hcoeff
    omega
  -- the two constants multiply to `1`, so their divisors are opposite
  have hmul : Units.mk0 (Scheme.functionFieldOverAlgebraMap K X c)
        (Scheme.functionFieldOverAlgebraMap_ne_zero K hc)
      * Units.mk0 (Scheme.functionFieldOverAlgebraMap K X c⁻¹)
        (Scheme.functionFieldOverAlgebraMap_ne_zero K (inv_ne_zero hc)) = 1 := by
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_one, Units.val_mk0, ← map_mul,
      mul_inv_cancel₀ hc, map_one]
  have hsum := congrArg (Scheme.divOf (X ↘ Spec (CommRingCat.of K))) hmul
  rw [Scheme.divOf_mul, Scheme.divOf_one] at hsum
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  have h1 := hnn hc x hx
  have h2 := hnn (inv_ne_zero hc) x hx
  have h3 := congrArg (coeffAt hx) hsum
  rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_zero] at h3
  rw [CurveDivisor.coeffAt_zero]
  omega

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- The `K`-scalar action does not move a nonzero rational function to zero. -/
lemma Scheme.smul_ne_zero_of_ne_zero {c : K} (hc : c ≠ 0) {f : X.functionField}
    (hf : f ≠ 0) : c • f ≠ 0 := by
  rw [functionFieldOverModule_smul_def]
  exact mul_ne_zero (Scheme.functionFieldOverAlgebraMap_ne_zero K hc) hf

/-- **Scalar invariance of the principal divisor**: `div(c • f) = div(f)` for a nonzero
constant `c` of the base field. -/
lemma Scheme.divOf_smul {c : K} (hc : c ≠ 0) {f : X.functionField} (hf : f ≠ 0) :
    Scheme.divOf (X ↘ Spec (CommRingCat.of K))
        (Units.mk0 (c • f) (Scheme.smul_ne_zero_of_ne_zero K hc hf))
      = Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf) := by
  have hfactor : Units.mk0 (c • f) (Scheme.smul_ne_zero_of_ne_zero K hc hf)
      = Units.mk0 (Scheme.functionFieldOverAlgebraMap K X c)
          (Scheme.functionFieldOverAlgebraMap_ne_zero K hc)
        * Units.mk0 f hf := by
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_mk0]
    exact functionFieldOverModule_smul_def K c f
  rw [hfactor, Scheme.divOf_mul, Scheme.divOf_functionFieldOverAlgebraMap K hc, zero_add]

/-! ## The ultrametric inequality -/

/-- **The ultrametric in `coeffAt`/`divOf` form**: the order of a sum is at least the
minimum of the orders — `Valuation.map_add` read through the sign-reversing bridge
`Scheme.ord_val_eq`. -/
lemma Scheme.min_coeffAt_divOf_le_add {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) {x : X} (hx : x ≠ genericPoint X) :
    min (coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)))
        (coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 g hg)))
      ≤ coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 (f + g) hfg)) := by
  have hval : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (f + g)
      ≤ max (Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx f)
          (Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g) :=
    Valuation.map_add _ f g
  rcases max_cases (Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx f)
      (Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx g) with ⟨hmax, _⟩ | ⟨hmax, _⟩
  · -- the max is the order of `f`
    rw [hmax] at hval
    have h1 : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx ((Units.mk0 (f + g) hfg :
          X.functionFieldˣ) : X.functionField)
        ≤ Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx ((Units.mk0 f hf :
          X.functionFieldˣ) : X.functionField) := hval
    rw [Scheme.ord_val_eq K _ hx, Scheme.ord_val_eq K _ hx] at h1
    have h2 := (divisorBound_le_divisorBound_iff hx).mp h1
    rw [CurveDivisor.coeffAt_neg, CurveDivisor.coeffAt_neg] at h2
    omega
  · -- the max is the order of `g`
    rw [hmax] at hval
    have h1 : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx ((Units.mk0 (f + g) hfg :
          X.functionFieldˣ) : X.functionField)
        ≤ Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx ((Units.mk0 g hg :
          X.functionFieldˣ) : X.functionField) := hval
    rw [Scheme.ord_val_eq K _ hx, Scheme.ord_val_eq K _ hx] at h1
    have h2 := (divisorBound_le_divisorBound_iff hx).mp h1
    rw [CurveDivisor.coeffAt_neg, CurveDivisor.coeffAt_neg] at h2
    omega

/-- **The finite-sum ultrametric**: a nonzero finite sum has some nonzero summand of
order `≤` the order of the sum. -/
lemma Scheme.exists_coeffAt_divOf_le_sum {ι : Type*} (s : Finset ι)
    (F : ι → X.functionField) (hsum : ∑ i ∈ s, F i ≠ 0) {x : X}
    (hx : x ≠ genericPoint X) :
    ∃ i ∈ s, ∃ (hFi : F i ≠ 0),
      coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 (F i) hFi))
        ≤ coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K))
            (Units.mk0 (∑ i ∈ s, F i) hsum)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd (Finset.sum_empty (f := F)) hsum
  | insert a s ha ih =>
    have hsum' : F a + ∑ i ∈ s, F i ≠ 0 := by rwa [Finset.sum_insert ha] at hsum
    have hU : Units.mk0 (∑ i ∈ Insert.insert a s, F i) hsum
        = Units.mk0 (F a + ∑ i ∈ s, F i) hsum' := by
      refine Units.ext ?_
      simp only [Units.val_mk0]
      exact Finset.sum_insert ha
    rw [hU]
    by_cases hFa : F a = 0
    · -- the head vanishes: recurse into the tail
      have hrest : ∑ i ∈ s, F i ≠ 0 := by rwa [hFa, zero_add] at hsum'
      have hU₂ : Units.mk0 (F a + ∑ i ∈ s, F i) hsum'
          = Units.mk0 (∑ i ∈ s, F i) hrest := by
        refine Units.ext ?_
        simp only [Units.val_mk0]
        rw [hFa, zero_add]
      rw [hU₂]
      obtain ⟨i, his, hFi, hle⟩ := ih hrest
      exact ⟨i, Finset.mem_insert_of_mem his, hFi, hle⟩
    · by_cases hrest : ∑ i ∈ s, F i = 0
      · -- the tail vanishes: the head is the sum
        have hU₃ : Units.mk0 (F a + ∑ i ∈ s, F i) hsum' = Units.mk0 (F a) hFa := by
          refine Units.ext ?_
          simp only [Units.val_mk0]
          rw [hrest, add_zero]
        rw [hU₃]
        exact ⟨a, Finset.mem_insert_self a s, hFa, le_rfl⟩
      · -- both halves are nonzero: the two-term ultrametric splits the minimum
        have hmin := Scheme.min_coeffAt_divOf_le_add K hFa hrest hsum' hx
        rcases min_cases
            (coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K))
              (Units.mk0 (F a) hFa)))
            (coeffAt hx (Scheme.divOf (X ↘ Spec (CommRingCat.of K))
              (Units.mk0 (∑ i ∈ s, F i) hrest))) with ⟨hcase, _⟩ | ⟨hcase, _⟩
        · exact ⟨a, Finset.mem_insert_self a s, hFa, by omega⟩
        · obtain ⟨i, his, hFi, hle⟩ := ih hrest
          exact ⟨i, Finset.mem_insert_of_mem his, hFi, by omega⟩

/-! ## The keystone: the achiever of a span lies in the spanning set -/

/-- **Achiever purity** (the DDR-3 pure-tensor minimality step): for a subspace
`T = span K S` of `H⁰(𝒪(A))`, the base multiplicity of `T` relative to `A` at any closed
point is achieved by an element of the spanning set `S` itself.  Any achiever of `T` is a
finite `K`-combination of elements of `S`; the ultrametric bounds the order of the sum
from below by the order of some summand, scalars do not move orders, and the spanning
elements cannot undercut the infimum. -/
theorem Scheme.exists_achiever_of_span {S : Set X.functionField} {A : X.CurveDivisor}
    (hSA : Submodule.span K S ≤ divisorSections K A ⊤)
    (hT : ∃ f ∈ Submodule.span K S, f ≠ 0) {x : X} (hx : x ≠ genericPoint X) :
    ∃ f ∈ S, ∃ (hf : f ≠ 0),
      coeffAt hx (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf))
        = (Scheme.baseDivisorAt K (Submodule.span K S) A ⟨x, hx⟩ : ℤ) := by
  classical
  -- the achiever of the span
  obtain ⟨t, htT, ht0, hach⟩ := Scheme.exists_coeffAt_eq_baseDivisorAt K hSA hT hx
  -- write it as a finite combination of spanning elements
  obtain ⟨n, c, gg, hcomb⟩ := Submodule.mem_span_set'.mp htT
  set F : Fin n → X.functionField := fun i => c i • (gg i : X.functionField) with hF
  have hsum : ∑ i ∈ Finset.univ, F i ≠ 0 := by
    rw [hF]
    simp only []
    rw [show ∑ i ∈ Finset.univ, c i • (gg i : X.functionField) = t from hcomb]
    exact ht0
  -- the ultrametric picks a summand
  obtain ⟨i, -, hFi, hle⟩ := Scheme.exists_coeffAt_divOf_le_sum K Finset.univ F hsum hx
  -- unpack the summand: a nonzero scalar times a spanning element
  have hci : c i ≠ 0 := by
    intro h0
    apply hFi
    rw [hF]
    simp only []
    rw [h0, zero_smul]
  have hgi : (gg i : X.functionField) ≠ 0 := by
    intro h0
    apply hFi
    rw [hF]
    simp only []
    rw [h0, smul_zero]
  -- scalars do not move the divisor
  have hdiv : Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 (F i) hFi)
      = Scheme.divOf (X ↘ Spec (CommRingCat.of K)) (Units.mk0 (gg i : X.functionField) hgi) := by
    have hFi' : F i = c i • (gg i : X.functionField) := rfl
    have hcast : Units.mk0 (F i) hFi
        = Units.mk0 (c i • (gg i : X.functionField))
            (Scheme.smul_ne_zero_of_ne_zero K hci hgi) :=
      Units.ext hFi'
    rw [hcast]
    exact Scheme.divOf_smul K hci hgi
  -- the sum is the achiever
  have hsum_eq : Units.mk0 (∑ i ∈ Finset.univ, F i) hsum = Units.mk0 t ht0 := by
    refine Units.ext ?_
    simp only [Units.val_mk0]
    rw [hF]
    simp only []
    exact hcomb
  rw [hdiv, hsum_eq] at hle
  -- squeeze: the spanning element cannot undercut the infimum
  have hlow := Scheme.baseDivisorAt_le_coeffAt K hSA
    (Submodule.subset_span (gg i).2) hgi hx
  refine ⟨(gg i : X.functionField), (gg i).2, hgi, ?_⟩
  rw [CurveDivisor.coeffAt_add] at hlow ⊢
  rw [CurveDivisor.coeffAt_add] at hach
  omega

end AlgebraicGeometry
