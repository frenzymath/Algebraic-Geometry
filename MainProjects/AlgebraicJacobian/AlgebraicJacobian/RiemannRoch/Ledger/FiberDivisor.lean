/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.FiberChart
import AlgebraicJacobian.RiemannRoch.Ledger.MulEquiv
import AlgebraicJacobian.RiemannRoch.Ledger.ResidueDegree
import AlgebraicJacobian.RiemannRoch.Ledger.ChiFiniteness

/-!
# The fiber Weil divisor `F` of a dominant map to the projective line

For a curve bundle `Y` over `K` with a dominant `π : Y ⟶ ℙ¹`, the pulled-back chart-0
coordinate `t₀` has a germ at the generic point which is a **unit** `u ∈ K(Y)ˣ` (its
overlap-inverse is the chart-1 coordinate `t₁`).  Its principal divisor `div u` is nonnegative on
`V₀`, nonpositive on `V₁`, and at least `1` at every point of `V₀ ∖ V₁` — the fiber of `π` over
`[1 : 0]`.  The **fiber Weil divisor** is its positive part

`F = (div u)⁺ = Finsupp.mapRange (max · 0) (div u)`,

an effective divisor supported on that fiber.  `F` is the direction in which the twist
`D + n·F` grows in the fibrewise large-twist vanishing (`Ledger/FiberVanishing.lean`): the order
table below is exactly what makes the section lattice over `V₀` grow with `n` while the one over
`V₁` stays fixed.

## The `coeffAt` calculus

The first section ports the small transport calculus for the coefficient function
`AlgebraicGeometry.coeffAt` of `Ledger/Devissage.lean` — values on `0`, `+`, `-`, `-·-`,
one-point divisors, and principal divisors.  AJC had `coeffAt` but none of these lemmas: in AJCR
they live in `Picard/PresentationDivisor.lean`, whose *other* half is the meromorphic-presentation
bridge and whose import edge is what pulls the `Picard.*` cone into the FLV closure.  The calculus
half is pure `Finsupp` bookkeeping with no Picard content, so it is ported here instead of taking
that edge.  Bodies are AJCR's unchanged.

## Provenance

Everything after the calculus section is AJCR `RiemannRoch/FLVFiberToolkit.lean`, bodies
unchanged, with the chart-1 coordinate and the overlap identity from its `section Cover` and the
order table and `fiberWeilDivisor` from its `section Main`.  The only omissions are AJCR's
`fiberWeilDivisor_deg_nonneg`-adjacent class statements that mention `picClass`; the degree
statements kept here (`fiberWeilDivisor_deg_nonneg`,
`fiberWeilDivisor_deg_pos_of_notMem_chart₁`) are stated with `CurveDivisor.deg` and are
Picard-free.

## Main declarations

* `AlgebraicGeometry.fiberCoord₁` — the pulled-back chart-1 coordinate `t₁`.
* `AlgebraicGeometry.fiberCoord_mul_fiberCoord₁_res` — `t₀ · t₁ = 1` on the overlap.
* `AlgebraicGeometry.fiberCoordUnit` — the fiber unit `u = germ_η t₀ ∈ K(Y)ˣ`.
* the order table: `fiberCoordUnit_coeffAt_divOf_nonneg_of_mem_chart₀`,
  `fiberCoordUnit_coeffAt_divOf_nonpos_of_mem_chart₁`,
  `one_le_fiberCoordUnit_coeffAt_divOf_of_notMem_chart₁`.
* `AlgebraicGeometry.fiberWeilDivisor` — the effective fiber divisor `F`, with
  `fiberWeilDivisor_nonneg`, its vanishing on `V₁`, its agreement with `div u` on `V₀`, and
  positivity of its degree given a fiber witness.
-/

set_option autoImplicit false
/- Scheme-theoretic unification (mixing `P1 K` with `Proj 𝒜`, `Γ(Y, U)` with functor
applications) needs defeq checks through semireducible definitions, as in mathlib's own
algebraic-geometry files. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme

/-! ## The `coeffAt` calculus for Weil divisors

`CurveDivisor` is a sealed `Finsupp`; these lemmas keep raw `Finsupp` projections out of
downstream proofs.  Ported from AJCR `Picard/PresentationDivisor.lean` (its calculus half only —
see the module docstring). -/

namespace Scheme.CurveDivisor

variable {X : Scheme.{u}} [IsIntegral X]

/-- Two Weil divisors with the same coefficient at every closed point are equal. -/
lemma ext_coeffAt {D D' : X.CurveDivisor}
    (h : ∀ (x : X) (hx : x ≠ genericPoint X), coeffAt hx D = coeffAt hx D') : D = D' :=
  Finsupp.ext fun p => h p.1 p.2

variable {x : X} (hx : x ≠ genericPoint X)

@[simp]
lemma coeffAt_zero : coeffAt hx (0 : X.CurveDivisor) = 0 :=
  rfl

@[simp]
lemma coeffAt_add (D D' : X.CurveDivisor) :
    coeffAt hx (D + D') = coeffAt hx D + coeffAt hx D' :=
  Finsupp.add_apply _ _ _

@[simp]
lemma coeffAt_neg (D : X.CurveDivisor) : coeffAt hx (-D) = -coeffAt hx D :=
  Finsupp.neg_apply _ _

@[simp]
lemma coeffAt_sub (D D' : X.CurveDivisor) :
    coeffAt hx (D - D') = coeffAt hx D - coeffAt hx D' :=
  Finsupp.sub_apply _ _ _

/-- The coefficient of the one-point divisor `n · x` at `x` is `n`. -/
@[simp]
lemma coeffAt_single_self (n : ℤ) : coeffAt hx (CurveDivisor.single hx n) = n :=
  Finsupp.single_eq_same

/-- The coefficient of the one-point divisor `n · x` at a closed point `z ≠ x` is `0`. -/
lemma coeffAt_single_of_ne {z : X} (hz : z ≠ genericPoint X) (hzx : z ≠ x) (n : ℤ) :
    coeffAt hz (CurveDivisor.single hx n) = 0 :=
  Finsupp.single_eq_of_ne fun h => hzx (Subtype.mk_eq_mk.mp h)

/-- One-point divisors negate their multiplicities. -/
lemma single_neg (n : ℤ) :
    CurveDivisor.single hx (-n) = -CurveDivisor.single hx n :=
  Finsupp.single_neg _ _

/-- The coefficient of a principal divisor at a closed point is the order of vanishing
there. -/
lemma coeffAt_divOf {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 f] [IsIntegral X]
    [LocallyOfFiniteType f] [QuasiCompact f] (g : X.functionFieldˣ) {x : X}
    (hx : x ≠ genericPoint X) :
    coeffAt hx (Scheme.divOf f g) = Multiplicative.toAdd (Scheme.ordZ f hx g) :=
  rfl

end Scheme.CurveDivisor

/-! ## The chart-1 coordinate and the overlap identity -/

section Cover

variable {K : Type u} [Field K] {Y : Scheme.{u}} (π : Y ⟶ P1 K)

/-- The standard grading of `K[X₀, X₁]`, the graded ring underlying `P1 K`. -/
local notation "𝒜" => homogeneousSubmodule (Fin 2) K

/-- The two-cover overlap `V₀ ⊓ V₁`, abbreviated for the order table. -/
local notation "ov" => fiberChart₀ π ⊓ fiberChart₁ π

/-- **The pulled-back chart-1 coordinate** `t₁ = π* (X₀/X₁) ∈ Γ(Y, V₁)`: the image under `π`'s
section map of the chart-1 coordinate of `ℙ¹`. Regular on all of `V₁ = π⁻¹ D₊(X₁)`, and the
overlap-inverse of the chart-0 coordinate `fiberCoord π = t₀`
(`fiberCoord_mul_fiberCoord₁_res`). -/
noncomputable def fiberCoord₁ : Γ(Y, fiberChart₁ π) :=
  (π.app (P1.chartOpen K 1)).hom ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord K 1 0))

/-- `V₀ ⊓ V₁ = π⁻¹ D₊(X₀X₁)`: the overlap is the preimage of the `ℙ¹`-chart overlap. -/
private lemma preimage_overlap_eq :
    ov = π ⁻¹ᵁ Proj.basicOpen 𝒜 (X 0 * X 1) := by
  rw [← Scheme.Hom.preimage_inf, P1.chartOpen_inf K]

private lemma preimage_overlap_le : ov ≤ π ⁻¹ᵁ Proj.basicOpen 𝒜 (X 0 * X 1) :=
  (preimage_overlap_eq π).le

/-- **The two coordinates multiply to `1` on the overlap.** The restrictions of `t₀` and of `t₁`
to `V₀ ⊓ V₁` are inverse sections: the `ℙ¹`-side identity `awayToOverlap_mul_eq_one` pulled back
along `π`'s section map on the chart overlap. -/
theorem fiberCoord_mul_fiberCoord₁_res :
    (Y.presheaf.map (homOfLE (inf_le_left : ov ≤ fiberChart₀ π)).op).hom (fiberCoord π)
        * (Y.presheaf.map (homOfLE (inf_le_right : ov ≤ fiberChart₁ π)).op).hom (fiberCoord₁ π)
      = 1 := by
  set ρ := (π.appLE (Proj.basicOpen 𝒜 (X 0 * X 1)) ov (preimage_overlap_le π)).hom with hρ
  have hleft : (Y.presheaf.map (homOfLE (inf_le_left : ov ≤ fiberChart₀ π)).op).hom (fiberCoord π)
      = ρ ((Proj.awayToSection 𝒜 (X 0 * X 1)).hom
          (P1.awayToOverlapLeft K (P1.chartCoord K 0 1))) := by
    rw [← P1.res_awayToSection_left K]
    symm
    calc ρ (((P1 K).presheaf.map (homOfLE (P1.overlap_le_left K)).op).hom
            ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord K 0 1)))
        = ((P1 K).presheaf.map (homOfLE (P1.overlap_le_left K)).op ≫
            π.appLE (Proj.basicOpen 𝒜 (X 0 * X 1)) ov (preimage_overlap_le π)).hom
            ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord K 0 1)) := rfl
      _ = (π.appLE (P1.chartOpen K 0) ov ((preimage_overlap_le π).trans
            ((Opens.map π.base).map (homOfLE (P1.overlap_le_left K))).le)).hom
            ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord K 0 1)) := by
          rw [Scheme.Hom.map_appLE]
      _ = (π.app (P1.chartOpen K 0) ≫
            Y.presheaf.map (homOfLE (inf_le_left : ov ≤ fiberChart₀ π)).op).hom
            ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord K 0 1)) := by
          rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
      _ = _ := rfl
  have hright : (Y.presheaf.map (homOfLE (inf_le_right : ov ≤ fiberChart₁ π)).op).hom
        (fiberCoord₁ π)
      = ρ ((Proj.awayToSection 𝒜 (X 0 * X 1)).hom
          (P1.awayToOverlapRight K (P1.chartCoord K 1 0))) := by
    rw [← P1.res_awayToSection_right K]
    symm
    calc ρ (((P1 K).presheaf.map (homOfLE (P1.overlap_le_right K)).op).hom
            ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord K 1 0)))
        = ((P1 K).presheaf.map (homOfLE (P1.overlap_le_right K)).op ≫
            π.appLE (Proj.basicOpen 𝒜 (X 0 * X 1)) ov (preimage_overlap_le π)).hom
            ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord K 1 0)) := rfl
      _ = (π.appLE (P1.chartOpen K 1) ov ((preimage_overlap_le π).trans
            ((Opens.map π.base).map (homOfLE (P1.overlap_le_right K))).le)).hom
            ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord K 1 0)) := by
          rw [Scheme.Hom.map_appLE]
      _ = (π.app (P1.chartOpen K 1) ≫
            Y.presheaf.map (homOfLE (inf_le_right : ov ≤ fiberChart₁ π)).op).hom
            ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord K 1 0)) := by
          rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
      _ = _ := rfl
  have hP1 : (Proj.awayToSection 𝒜 (X 0 * X 1)).hom (P1.awayToOverlapLeft K (P1.chartCoord K 0 1))
        * (Proj.awayToSection 𝒜 (X 0 * X 1)).hom (P1.awayToOverlapRight K (P1.chartCoord K 1 0))
      = 1 := by
    rw [← map_mul, P1.awayToOverlap_mul_eq_one K, map_one]
  rw [hleft, hright, ← map_mul, hP1, map_one]

end Cover

/-! ## The fiber unit and its order table -/

section Main

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  (π : Y ⟶ P1 K) [IsDominant π]

/-- The divisor bound `≤`-comparison at a point reduces to the pointwise coefficient
`≤`-comparison in `ℤ`: `divisorBound A ≤ divisorBound B ↔ coeffAt A ≤ coeffAt B`. -/
private lemma divisorBound_le_iff {A B : Y.CurveDivisor} {x : Y} (hx : x ≠ genericPoint Y) :
    Scheme.divisorBound A hx ≤ Scheme.divisorBound B hx ↔
      coeffAt hx A ≤ coeffAt hx B := by
  simp only [Scheme.divisorBound, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  rfl

/-- **The nonnegativity/regularity bridge.** The classical order `div w` of a unit `w` is
nonnegative at `x` exactly when its valuation order `ord_x w ≤ 1` (no pole). -/
private lemma zero_le_coeffAt_divOf_iff_ord_le_one (w : Y.functionFieldˣ) {x : Y}
    (hx : x ≠ genericPoint Y) :
    (0 : ℤ) ≤ coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) w) ↔
      Scheme.ord (Y ↘ Spec (CommRingCat.of K)) hx (w : Y.functionField) ≤ 1 := by
  rw [Scheme.ord_val_eq K w hx, ← Scheme.divisorBound_zero hx, divisorBound_le_iff hx,
    CurveDivisor.coeffAt_zero, CurveDivisor.coeffAt_neg, neg_nonpos]

/-- **The core regularity lemma.** If a unit `w` of the function field is the germ at `η` of a
*regular* section `s` on an open `W ∋ x`, then its order at `x` is nonnegative (`w` has no pole
at `x`). This is `ord_x (algebraMap (germ_x s)) ≤ 1` read off from integrality. -/
private lemma zero_le_coeffAt_divOf_of_val_eq_germ {w : Y.functionFieldˣ} {W : Y.Opens}
    (hηW : genericPoint Y ∈ W) {x : Y} (hx : x ≠ genericPoint Y) (hxW : x ∈ W) (s : Γ(Y, W))
    (hws : (w : Y.functionField) = (Y.presheaf.germ W (genericPoint Y) hηW).hom s) :
    (0 : ℤ) ≤ coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) w) := by
  rw [zero_le_coeffAt_divOf_iff_ord_le_one w hx, hws, germ_generic_eq_algebraMap_germ hηW hxW s]
  exact Scheme.ord_algebraMap_stalk_le_one K hx _

omit [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] in
/-- The two coordinate germs at `η` multiply to `1` in `K(Y)`: the germ image of the overlap
identity `fiberCoord_mul_fiberCoord₁_res`. -/
private theorem germ_fiberCoord_mul_germ_fiberCoord₁ :
    (Y.presheaf.germ (fiberChart₀ π) (genericPoint Y)
        (genericPoint_mem_preimage_inf π).1).hom (fiberCoord π)
      * (Y.presheaf.germ (fiberChart₁ π) (genericPoint Y)
        (genericPoint_mem_preimage_inf π).2).hom (fiberCoord₁ π) = 1 := by
  have hη : genericPoint Y ∈ fiberChart₀ π ⊓ fiberChart₁ π := genericPoint_mem_preimage_inf π
  rw [← Y.presheaf.germ_res_apply (homOfLE inf_le_left) (genericPoint Y) hη (fiberCoord π),
    ← Y.presheaf.germ_res_apply (homOfLE inf_le_right) (genericPoint Y) hη (fiberCoord₁ π),
    ← map_mul, fiberCoord_mul_fiberCoord₁_res π, map_one]

/-- **The fiber unit `u = germ_η t₀ ∈ K(Y)ˣ`.** The pulled-back chart-0 coordinate, read as a
unit of the function field: its value is `germ_η t₀` and its inverse is `germ_η t₁`, the two
coordinates being mutually inverse on the overlap. This is the `K(Y)ˣ` datum on which the fiber
Weil divisor and the twist lattices rest. -/
noncomputable def fiberCoordUnit : Y.functionFieldˣ where
  val := (Y.presheaf.germ (fiberChart₀ π) (genericPoint Y)
    (genericPoint_mem_preimage_inf π).1).hom (fiberCoord π)
  inv := (Y.presheaf.germ (fiberChart₁ π) (genericPoint Y)
    (genericPoint_mem_preimage_inf π).2).hom (fiberCoord₁ π)
  val_inv := germ_fiberCoord_mul_germ_fiberCoord₁ π
  inv_val := by rw [mul_comm]; exact germ_fiberCoord_mul_germ_fiberCoord₁ π

omit [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] in
lemma fiberCoordUnit_val : (fiberCoordUnit π : Y.functionField)
    = (Y.presheaf.germ (fiberChart₀ π) (genericPoint Y)
        (genericPoint_mem_preimage_inf π).1).hom (fiberCoord π) := rfl

omit [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] in
lemma fiberCoordUnit_inv_val : ((fiberCoordUnit π)⁻¹).val
    = (Y.presheaf.germ (fiberChart₁ π) (genericPoint Y)
        (genericPoint_mem_preimage_inf π).2).hom (fiberCoord₁ π) := rfl

/-- **Order table, chart 0.** The fiber unit `u` is regular on `V₀ = π⁻¹ D₊(X₀)`: its classical
order `div u` is nonnegative at every point of `V₀` (`u = germ_η t₀`, and `t₀` is a regular
section on `V₀`). -/
theorem fiberCoordUnit_coeffAt_divOf_nonneg_of_mem_chart₀ {x : Y} (hx : x ≠ genericPoint Y)
    (hxV₀ : x ∈ fiberChart₀ π) :
    (0 : ℤ) ≤ coeffAt hx
      (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π)) :=
  zero_le_coeffAt_divOf_of_val_eq_germ (genericPoint_mem_preimage_inf π).1 hx hxV₀ (fiberCoord π)
    (fiberCoordUnit_val π)

/-- The classical order of `u⁻¹` is the negative of that of `u`, coefficient-wise. -/
private lemma coeffAt_divOf_inv {x : Y} (hx : x ≠ genericPoint Y) :
    coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π)⁻¹) =
      - coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π)) := by
  have h : Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π)⁻¹
      + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π) = 0 := by
    rw [← Scheme.divOf_mul (Y ↘ Spec (CommRingCat.of K)), inv_mul_cancel,
      Scheme.divOf_one (Y ↘ Spec (CommRingCat.of K))]
  have hc := congrArg (coeffAt hx) h
  rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_zero] at hc
  linarith

/-- **Order table, chart 1.** The fiber unit `u` is co-regular on `V₁ = π⁻¹ D₊(X₁)`: its
classical order `div u` is nonpositive at every point of `V₁` (`u⁻¹ = germ_η t₁`, and `t₁` is a
regular section on `V₁`, so `u` has no zero there). -/
theorem fiberCoordUnit_coeffAt_divOf_nonpos_of_mem_chart₁ {x : Y} (hx : x ≠ genericPoint Y)
    (hxV₁ : x ∈ fiberChart₁ π) :
    coeffAt hx
      (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π)) ≤ 0 := by
  have hinv := zero_le_coeffAt_divOf_of_val_eq_germ (K := K) (w := (fiberCoordUnit π)⁻¹)
    (genericPoint_mem_preimage_inf π).2 hx hxV₁ (fiberCoord₁ π) (fiberCoordUnit_inv_val π)
  rw [coeffAt_divOf_inv π hx, neg_nonneg] at hinv
  exact hinv

/-- **Strict order at a zero.** At a point of `V₀` lying *outside* `V₁` (a point of the fiber
over `[1 : 0]`), the fiber unit `u = germ_η t₀` has a genuine zero: its classical order is `≥ 1`.
The germ of `t₀` there is a nonzero non-unit of the DVR stalk, so its valuation is `< 1`. This is
the pole-clearing strength that drives the exhaustion of the twist lattices. -/
theorem one_le_fiberCoordUnit_coeffAt_divOf_of_notMem_chart₁ {x : Y} (hx : x ≠ genericPoint Y)
    (hxV₀ : x ∈ fiberChart₀ π) (hxV₁ : x ∉ fiberChart₁ π) :
    1 ≤ coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π)) := by
  have hnn := fiberCoordUnit_coeffAt_divOf_nonneg_of_mem_chart₀ π hx hxV₀
  -- the germ of `t₀` at `x` is a non-unit: `x` avoids the overlap `= basicOpen t₀`.
  have hnu : ¬ IsUnit ((Y.presheaf.germ (fiberChart₀ π) x hxV₀).hom (fiberCoord π)) := by
    intro hu
    have hmem : x ∈ Y.basicOpen (fiberCoord π) :=
      (Y.mem_basicOpen (fiberCoord π) x hxV₀).mpr hu
    rw [← preimage_inf_eq_basicOpen_fiberCoord π] at hmem
    exact hxV₁ hmem.2
  -- hence `ord_x u < 1`.
  letI := isDiscreteValuationRing_stalk (Y ↘ Spec (CommRingCat.of K)) hx
  letI := isDedekindDomain_stalk (Y ↘ Spec (CommRingCat.of K)) hx
  have hlt : Scheme.ord (Y ↘ Spec (CommRingCat.of K)) hx
      (fiberCoordUnit π : Y.functionField) < 1 := by
    rw [fiberCoordUnit_val,
      germ_generic_eq_algebraMap_germ (genericPoint_mem_preimage_inf π).1 hxV₀ (fiberCoord π),
      Scheme.ord_eq_valuation]
    refine (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (stalkHeightOne Y x) _).mpr ?_
    by_contra h
    exact hnu (IsLocalRing.notMem_maximalIdeal.mp h)
  -- translate `ord < 1` into `coeffAt ≥ 1`.
  have hne : coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π)) ≠ 0 := by
    intro h0
    apply ne_of_lt hlt
    rw [← Scheme.ordZ_eq_one_iff]
    have : Scheme.ordZ (Y ↘ Spec (CommRingCat.of K)) hx (fiberCoordUnit π) = 1 := by
      have := CurveDivisor.coeffAt_divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π) hx
      rw [h0] at this
      exact Multiplicative.toAdd.injective (this.symm.trans toAdd_one.symm ▸ rfl)
    exact this
  omega

/-- **The fiber Weil divisor `F = (div u)⁺`.** The effective divisor of the zeros of the fiber
unit `u`: `F x = max (div u x, 0)`. Supported on `V₀ ∖ V₁` (the fiber of `π` over `[1 : 0]`), it
is the direction in which the twist `D + n·F` grows. -/
noncomputable def fiberWeilDivisor : Y.CurveDivisor :=
  Finsupp.mapRange (fun n => max n 0) (max_self 0)
    (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π))

lemma fiberWeilDivisor_coeffAt {x : Y} (hx : x ≠ genericPoint Y) :
    coeffAt hx (fiberWeilDivisor π) =
      max (coeffAt hx
        (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π))) 0 := by
  simp only [coeffAt, toFinsupp, fiberWeilDivisor, Finsupp.mapRange_apply]

/-- **`F` is effective.** -/
theorem fiberWeilDivisor_nonneg : 0 ≤ fiberWeilDivisor π := by
  refine Finsupp.le_def.mpr (fun p => ?_)
  change (0 : ℤ) ≤ coeffAt p.2 (fiberWeilDivisor π)
  rw [fiberWeilDivisor_coeffAt π p.2]
  exact le_max_right _ _

/-- **Support avoids `V₁`.** At every point of `V₁` the fiber divisor vanishes: `u` has no zero
there, so its positive part is trivial. -/
theorem fiberWeilDivisor_coeffAt_of_mem_chart₁ {x : Y} (hx : x ≠ genericPoint Y)
    (hxV₁ : x ∈ fiberChart₁ π) :
    coeffAt hx (fiberWeilDivisor π) = 0 := by
  rw [fiberWeilDivisor_coeffAt π hx,
    max_eq_right (fiberCoordUnit_coeffAt_divOf_nonpos_of_mem_chart₁ π hx hxV₁)]

/-- **Agreement with `div u` on `V₀`.** At every point of `V₀` the fiber divisor equals the
classical order of `u` (which is nonnegative there). -/
theorem fiberWeilDivisor_coeffAt_of_mem_chart₀ {x : Y} (hx : x ≠ genericPoint Y)
    (hxV₀ : x ∈ fiberChart₀ π) :
    coeffAt hx (fiberWeilDivisor π) =
      coeffAt hx (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π)) := by
  rw [fiberWeilDivisor_coeffAt π hx,
    max_eq_left (fiberCoordUnit_coeffAt_divOf_nonneg_of_mem_chart₀ π hx hxV₀)]

/-- **`F` has nonnegative degree** (it is effective and residue degrees are positive). -/
theorem fiberWeilDivisor_deg_nonneg :
    0 ≤ CurveDivisor.deg K (fiberWeilDivisor π) := by
  refine Finsupp.sum_nonneg (fun p _ => ?_)
  have hp : 0 ≤ coeffAt p.2 (fiberWeilDivisor π) := by
    rw [fiberWeilDivisor_coeffAt π p.2]; exact le_max_right _ _
  exact mul_nonneg hp (Int.natCast_nonneg _)

/-- **Pole existence (from a fiber witness).** If some point of `V₀` lies outside `V₁` — a point
of the fiber of `π` over `[1 : 0]` — then the fiber divisor is nonzero: `u` has a genuine zero
there. The witness exists whenever `π` is surjective (the fiber over `[1 : 0]` is nonempty),
which holds for a finite dominant `π`. -/
theorem fiberWeilDivisor_ne_zero_of_notMem_chart₁ {x₀ : Y} (hx₀ : x₀ ≠ genericPoint Y)
    (hxV₀ : x₀ ∈ fiberChart₀ π) (hxV₁ : x₀ ∉ fiberChart₁ π) :
    fiberWeilDivisor π ≠ 0 := by
  intro h
  have h0 : coeffAt hx₀ (fiberWeilDivisor π) = 0 := by rw [h, CurveDivisor.coeffAt_zero]
  rw [fiberWeilDivisor_coeffAt_of_mem_chart₀ π hx₀ hxV₀] at h0
  have h1 := one_le_fiberCoordUnit_coeffAt_divOf_of_notMem_chart₁ π hx₀ hxV₀ hxV₁
  omega

/-- **Positive degree (from a fiber witness).** The fiber divisor has degree `≥ 1`: it is
effective with a coefficient `≥ 1` at the fiber witness (residue degrees being `≥ 1`). -/
theorem fiberWeilDivisor_deg_pos_of_notMem_chart₁ {x₀ : Y} (hx₀ : x₀ ≠ genericPoint Y)
    (hxV₀ : x₀ ∈ fiberChart₀ π) (hxV₁ : x₀ ∉ fiberChart₁ π) :
    0 < CurveDivisor.deg K (fiberWeilDivisor π) := by
  have hcoeff : 1 ≤ coeffAt hx₀ (fiberWeilDivisor π) := by
    rw [fiberWeilDivisor_coeffAt_of_mem_chart₀ π hx₀ hxV₀]
    exact one_le_fiberCoordUnit_coeffAt_divOf_of_notMem_chart₁ π hx₀ hxV₀ hxV₁
  have hsupp : (⟨x₀, hx₀⟩ : {p : Y // p ≠ genericPoint Y}) ∈
      (toFinsupp (fiberWeilDivisor π)).support := by
    rw [Finsupp.mem_support_iff]
    change coeffAt hx₀ (fiberWeilDivisor π) ≠ 0
    omega
  refine Finset.sum_pos' (fun p _ => ?_) ⟨⟨x₀, hx₀⟩, hsupp, ?_⟩
  · have hp : 0 ≤ coeffAt p.2 (fiberWeilDivisor π) := by
      rw [fiberWeilDivisor_coeffAt π p.2]; exact le_max_right _ _
    exact mul_nonneg hp (Int.natCast_nonneg _)
  · have hrd : 0 < (Y.residueDeg K x₀ : ℤ) := by exact_mod_cast Scheme.residueDeg_pos hx₀
    have hpos : (0 : ℤ) < coeffAt hx₀ (fiberWeilDivisor π) := by omega
    exact mul_pos hpos hrd

end Main

end AlgebraicGeometry
