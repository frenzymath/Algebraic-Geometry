/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.FinitenessP1
import AlgebraicJacobian.Curve.MapToP1
import AlgebraicJacobian.RiemannRoch.Degree

/-!
# The fiber twist `Θₙ` of a finite map to the projective line

For the curve bundle `Y` (integral, smooth of relative dimension one and quasi-compact over
a field `K`) equipped with a **dominant** morphism `π : Y ⟶ ℙ¹`, this file pins the
Wave-4 twist datum: the divisor class of `n · (fiber of π)` and its two-cover triviality
*by construction*.

## The fiber-divisor design decision

The overlap of the pinned affine two-cover `V₀ = π⁻¹ D₊(X₀)`, `V₁ = π⁻¹ D₊(X₁)` is the
basic open of the **pulled-back chart-0 coordinate** `t₀ = π* (X₁/X₀) ∈ Γ(Y, V₀)`
(`AlgebraicGeometry.preimage_inf_eq_basicOpen_fiberCoord`, the public re-derivation of the
`private` lemma of `Cohomology.Finiteness`). The section `t₀` is regular on all of `V₀` —
its germ at every point is a nonzero element of the domain stalk, since `t₀` is a unit at the
generic point (`π` dominant) — and is a **unit exactly on the overlap** `V₀ ⊓ V₁`. Its zero
locus on `V₀` is the fiber of `π` over the point `[1 : 0]` (where `X₁` vanishes).

We therefore pin the fiber divisor of `Θₙ` as the local-equation system **on the pinned
cover itself**: the equation `t₀ⁿ` on the chart `V₀` and the constant `1` on `V₁`. The
transition cocycle between the two charts is then the two-cover unit cocycle
`gₙ = t₀ⁿ|_{V₀ ⊓ V₁}` — trivial (a single global regular equation) on each chart by
construction. This is the fiber-twist normalization certified in
`informal/w4-datum-design.md` §2(a).

## Main declarations

* `AlgebraicGeometry.fiberCoord` — the pulled-back chart-0 coordinate `t₀ ∈ Γ(Y, V₀)`.
* `AlgebraicGeometry.preimage_inf_eq_basicOpen_fiberCoord` — the overlap is `Y.basicOpen t₀`
  (public form of the `private` `Cohomology.Finiteness` seam).
* `AlgebraicGeometry.isUnit_fiberCoord_res_inf` — `t₀` restricts to a unit on the overlap:
  the two-cover-unit-cocycle certificate.
* `AlgebraicGeometry.fiberDivisor` — the local-equation system `(t₀ⁿ on V₀, 1 on V₁)`
  for `n · (fiber of π)`, a `Y.LocalEquations`.
* `AlgebraicGeometry.fiberTwist` — the Picard class `Θₙ = 𝒪(n · fiber) = (fiberDivisor n).picClass`.
* `AlgebraicGeometry.fiberTwist_succ`, `AlgebraicGeometry.fiberTwist_pow` — the twist is the
  `n`-th power of the unit twist: `Θₙ = Θ₁ⁿ`.
* `AlgebraicGeometry.classDeg_fiberTwist` — the degree scales linearly,
  `deg Θₙ = n · deg Θ₁` (the `= n · deg π` normalization is a *frontier*; see the note there).
-/

set_option autoImplicit false
/- Scheme-theoretic unification (mixing `P1 K` with `Proj 𝒜`, `Γ(Y, U)` with functor
applications) needs defeq checks through semireducible definitions, as in mathlib's own
algebraic-geometry files. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization TopologicalSpace Opposite
  CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

open Scheme

/-! ## The pinned cover and its local equations

These constructions depend only on the morphism `π`; the integrality/smoothness hypotheses
enter with the regularity of the equations in the next section. -/

section Cover

variable {K : Type u} [Field K] {Y : Scheme.{u}} (π : Y ⟶ P1 K)

/-- The standard grading of `K[X₀, X₁]`, the graded ring underlying `P1 K`. -/
local notation "𝒜" => homogeneousSubmodule (Fin 2) K

/-- The chart-0 preimage `V₀ = π⁻¹ D₊(X₀)`. -/
@[reducible] noncomputable def fiberChart₀ : Y.Opens := π ⁻¹ᵁ P1.chartOpen K 0

/-- The chart-1 preimage `V₁ = π⁻¹ D₊(X₁)`. -/
@[reducible] noncomputable def fiberChart₁ : Y.Opens := π ⁻¹ᵁ P1.chartOpen K 1

/-- The **pulled-back chart-0 coordinate** `t₀ = π* (X₁/X₀) ∈ Γ(Y, V₀)`: the image under
`π`'s section map of the chart-0 coordinate of `ℙ¹`. The two-cover overlap is the basic
open of `t₀` (`preimage_inf_eq_basicOpen_fiberCoord`), and its `n`-th power is the twist's
transition cocycle. -/
noncomputable def fiberCoord : Γ(Y, fiberChart₀ π) :=
  (π.app (P1.chartOpen K 0)).hom ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord K 0 1))

/-- **The two-cover overlap is the basic open of `t₀`.** Public re-derivation of the
`private` lemma `Cohomology.Finiteness.preimage_inf_eq_basicOpen_left`: the overlap of the
pinned chart preimages equals `Y.basicOpen t₀`, obtained from `Scheme.preimage_basicOpen`
together with the `ℙ¹`-side identification `P1.basicOpen_awayToSection_chartCoord`. -/
theorem preimage_inf_eq_basicOpen_fiberCoord :
    fiberChart₀ π ⊓ fiberChart₁ π = Y.basicOpen (fiberCoord π) := by
  have h : π ⁻¹ᵁ ((P1 K).basicOpen
        ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord K 0 1)))
      = Y.basicOpen (fiberCoord π) :=
    Scheme.preimage_basicOpen π _
  rw [P1.basicOpen_awayToSection_chartCoord K 0 1, Scheme.Hom.preimage_inf] at h
  exact h

open Classical in
/-- The pinned two-chart pointed cover: `V₀` at every point of `V₀`, `V₁` elsewhere. -/
noncomputable def fiberCover : Y.PointedCover where
  opens z := if z ∈ fiberChart₀ π then fiberChart₀ π else fiberChart₁ π
  mem_opens z := by
    by_cases h : z ∈ fiberChart₀ π
    · rw [if_pos h]; exact h
    · rw [if_neg h]
      have hz : z ∈ fiberChart₀ π ⊔ fiberChart₁ π := by
        rw [preimage_chartOpen_sup]; trivial
      exact (TopologicalSpace.Opens.mem_sup.mp hz).resolve_left h

lemma fiberCover_opens_of_mem {z : Y} (h : z ∈ fiberChart₀ π) :
    (fiberCover π).opens z = fiberChart₀ π :=
  if_pos h

lemma fiberCover_opens_of_notMem {z : Y} (h : z ∉ fiberChart₀ π) :
    (fiberCover π).opens z = fiberChart₁ π :=
  if_neg h

open Classical in
/-- The local equation of `n · (fiber)` at a point: `t₀ⁿ` on the chart `V₀`, the constant
`1` on `V₁`. -/
noncomputable def fiberEqn (n : ℕ) (z : Y) : Γ(Y, (fiberCover π).opens z) :=
  if h : z ∈ fiberChart₀ π then
    (Y.presheaf.map (homOfLE (le_of_eq (fiberCover_opens_of_mem π h))).op).hom
      ((fiberCoord π) ^ n)
  else 1

lemma fiberEqn_of_mem (n : ℕ) {z : Y} (h : z ∈ fiberChart₀ π) :
    fiberEqn π n z
      = (Y.presheaf.map (homOfLE (le_of_eq (fiberCover_opens_of_mem π h))).op).hom
          ((fiberCoord π) ^ n) :=
  dif_pos h

lemma fiberEqn_of_notMem (n : ℕ) {z : Y} (h : z ∉ fiberChart₀ π) :
    fiberEqn π n z = 1 :=
  dif_neg h

/-- The fiber equation is multiplicative in the exponent: `t₀^(n+1) = t₀ⁿ · t₀`. This is the
section-level heart of the power law `Θₙ = Θ₁ⁿ`. -/
lemma fiberEqn_succ (n : ℕ) (z : Y) :
    fiberEqn π (n + 1) z = fiberEqn π n z * fiberEqn π 1 z := by
  by_cases h : z ∈ fiberChart₀ π
  · rw [fiberEqn_of_mem π (n + 1) h, fiberEqn_of_mem π n h, fiberEqn_of_mem π 1 h,
      ← map_mul, pow_one, ← pow_succ]
  · rw [fiberEqn_of_notMem π (n + 1) h, fiberEqn_of_notMem π n h, fiberEqn_of_notMem π 1 h,
      one_mul]

/-- The zeroth fiber equation is the constant `1`. -/
lemma fiberEqn_zero (z : Y) : fiberEqn π 0 z = 1 := by
  by_cases h : z ∈ fiberChart₀ π
  · rw [fiberEqn_of_mem π 0 h, pow_zero, map_one]
  · rw [fiberEqn_of_notMem π 0 h]

/-- Restriction of a section along `W ≤ V ≤ U` composes to restriction along `W ≤ U`. -/
private lemma res_comp {W V U : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (s : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h₁).op).hom ((Y.presheaf.map (homOfLE h₂).op).hom s)
      = (Y.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- **The two-cover-unit-cocycle certificate.** The restriction of `t₀` to the overlap
`V₀ ⊓ V₁` is a unit: every point of the overlap lies in `Y.basicOpen t₀`. Hence `t₀ⁿ` is a
genuine unit Čech cocycle on the pinned two-cover. -/
theorem isUnit_fiberCoord_res_inf :
    IsUnit ((Y.presheaf.map (homOfLE
        (inf_le_left : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₀ π)).op).hom
      (fiberCoord π)) := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ
  intro w hw
  rw [Y.presheaf.germ_res_apply]
  refine (Y.mem_basicOpen (fiberCoord π) w hw.1).mp ?_
  rw [← preimage_inf_eq_basicOpen_fiberCoord π]
  exact hw

end Cover

/-! ## Regularity and the fiber divisor -/

section Main

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  (π : Y ⟶ P1 K) [IsDominant π]

/-- The standard grading of `K[X₀, X₁]`, the graded ring underlying `P1 K`. -/
local notation "𝒜" => homogeneousSubmodule (Fin 2) K

/-- The generic point of `Y` lies in the two-cover overlap: since `π` is dominant, the
`ℙ¹`-overlap `D₊(X₀X₁)` (nonempty as the range of its affine chart) meets the range of `π`,
so its `π`-preimage is a nonempty open of the irreducible `Y`. -/
theorem genericPoint_mem_preimage_inf :
    genericPoint Y ∈ fiberChart₀ π ⊓ fiberChart₁ π := by
  have hP1 : (↑(P1.chartOpen K 0 ⊓ P1.chartOpen K 1) : Set (P1 K)).Nonempty := by
    rw [P1.chartOpen_inf]
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of
        (Away 𝒜 ((X 0 : MvPolynomial (Fin 2) K) * X 1)))) := inferInstance
    refine ⟨(Proj.awayι 𝒜 _ (P1.X_mul_X_mem K) two_pos).base z, ?_⟩
    rw [← Proj.opensRange_awayι 𝒜 _ (P1.X_mul_X_mem K) two_pos]
    exact ⟨z, rfl⟩
  have hne : (↑(π ⁻¹ᵁ (P1.chartOpen K 0 ⊓ P1.chartOpen K 1)) : Set Y).Nonempty := by
    obtain ⟨p, hp⟩ :=
      π.denseRange.inter_open_nonempty _ (P1.chartOpen K 0 ⊓ P1.chartOpen K 1).isOpen hP1
    obtain ⟨y, hy⟩ := hp.2
    refine ⟨y, ?_⟩
    change π.base y ∈ (P1.chartOpen K 0 ⊓ P1.chartOpen K 1 : (P1 K).Opens)
    rw [(hy : π.base y = p)]
    exact hp.1
  rw [← Scheme.Hom.preimage_inf]
  exact genericPoint_mem_of_nonempty hne

/-- The germ of the pulled-back coordinate at any point of `V₀` is nonzero: it maps, under
the domain stalk's embedding into the function field, to the germ at `η`, which is a **unit**
(the generic point lies in `Y.basicOpen t₀`). -/
theorem germ_fiberCoord_ne_zero {y : Y} (hy : y ∈ fiberChart₀ π) :
    (Y.presheaf.germ (fiberChart₀ π) y hy).hom (fiberCoord π) ≠ 0 := by
  have hη : genericPoint Y ∈ fiberChart₀ π := (genericPoint_mem_preimage_inf π).1
  have hunit : IsUnit ((Y.presheaf.germ (fiberChart₀ π) (genericPoint Y) hη).hom
      (fiberCoord π)) := by
    refine (Y.mem_basicOpen (fiberCoord π) (genericPoint Y) hη).mp ?_
    rw [← preimage_inf_eq_basicOpen_fiberCoord π]
    exact genericPoint_mem_preimage_inf π
  intro hzero
  have key := germ_generic_eq_algebraMap_germ (X := Y) hη hy (fiberCoord π)
  rw [hzero, map_zero] at key
  rw [key] at hunit
  exact not_isUnit_zero hunit

/-- The germ of `t₀` at a point of `V₀` is a nonzerodivisor of the domain stalk. -/
theorem germ_fiberCoord_mem_nonZeroDivisors {y : Y} (hy : y ∈ fiberChart₀ π) :
    (Y.presheaf.germ (fiberChart₀ π) y hy).hom (fiberCoord π)
      ∈ nonZeroDivisors (Y.presheaf.stalk y) :=
  mem_nonZeroDivisors_iff_ne_zero.mpr (germ_fiberCoord_ne_zero π hy)

/-- **The fiber divisor `n · (fiber of π)`.** The local-equation system on the pinned
two-cover: `t₀ⁿ` on `V₀` (regular everywhere, vanishing to order `n` on the fiber over
`[1 : 0]`) and `1` on `V₁`. The overlap ratio is the unit `t₀ⁿ`. -/
noncomputable def fiberDivisor (n : ℕ) : Y.LocalEquations where
  cover := fiberCover π
  eqn := fiberEqn π n
  regular z y hy := by
    by_cases h : z ∈ fiberChart₀ π
    · rw [fiberEqn_of_mem π n h, Y.presheaf.germ_res_apply, map_pow]
      exact pow_mem (germ_fiberCoord_mem_nonZeroDivisors π _) n
    · rw [fiberEqn_of_notMem π n h, map_one]
      exact one_mem _
  ratio_isUnit z z' := by
    by_cases h : z ∈ fiberChart₀ π <;> by_cases h' : z' ∈ fiberChart₀ π
    · refine ⟨1, ?_⟩
      rw [Units.val_one, one_mul, fiberEqn_of_mem π n h, fiberEqn_of_mem π n h',
        res_comp, res_comp]
    · have hle : (fiberCover π).opens z ⊓ (fiberCover π).opens z' ≤ fiberChart₀ π :=
        inf_le_left.trans (le_of_eq (fiberCover_opens_of_mem π h))
      have hbo : ∀ w ∈ (fiberCover π).opens z ⊓ (fiberCover π).opens z',
          w ∈ Y.basicOpen (fiberCoord π) := by
        intro w hw
        rw [← preimage_inf_eq_basicOpen_fiberCoord π]
        exact ⟨(fiberCover_opens_of_mem π h) ▸ hw.1,
          (fiberCover_opens_of_notMem π h') ▸ hw.2⟩
      have hunit : IsUnit ((Y.presheaf.map (homOfLE hle).op).hom ((fiberCoord π) ^ n)) := by
        apply Y.toRingedSpace.isUnit_of_isUnit_germ
        intro w hw
        rw [Y.presheaf.germ_res_apply, map_pow]
        exact ((Y.mem_basicOpen (fiberCoord π) w (hle hw)).mp (hbo w hw)).pow n
      refine ⟨hunit.unit, ?_⟩
      rw [fiberEqn_of_notMem π n h', map_one, mul_one, IsUnit.unit_spec,
        fiberEqn_of_mem π n h, res_comp]
    · have hle : (fiberCover π).opens z ⊓ (fiberCover π).opens z' ≤ fiberChart₀ π :=
        inf_le_right.trans (le_of_eq (fiberCover_opens_of_mem π h'))
      have hbo : ∀ w ∈ (fiberCover π).opens z ⊓ (fiberCover π).opens z',
          w ∈ Y.basicOpen (fiberCoord π) := by
        intro w hw
        rw [← preimage_inf_eq_basicOpen_fiberCoord π]
        exact ⟨(fiberCover_opens_of_mem π h') ▸ hw.2,
          (fiberCover_opens_of_notMem π h) ▸ hw.1⟩
      have hunit : IsUnit ((Y.presheaf.map (homOfLE hle).op).hom ((fiberCoord π) ^ n)) := by
        apply Y.toRingedSpace.isUnit_of_isUnit_germ
        intro w hw
        rw [Y.presheaf.germ_res_apply, map_pow]
        exact ((Y.mem_basicOpen (fiberCoord π) w (hle hw)).mp (hbo w hw)).pow n
      refine ⟨hunit.unit⁻¹, ?_⟩
      rw [fiberEqn_of_notMem π n h, map_one, fiberEqn_of_mem π n h', res_comp]
      exact (Units.inv_mul_of_eq (by rw [IsUnit.unit_spec])).symm
    · refine ⟨1, ?_⟩
      rw [Units.val_one, one_mul, fiberEqn_of_notMem π n h, fiberEqn_of_notMem π n h',
        map_one, map_one]

@[simp] lemma fiberDivisor_cover (n : ℕ) : (fiberDivisor π n).cover = fiberCover π := rfl

@[simp] lemma fiberDivisor_eqn (n : ℕ) (z : Y) : (fiberDivisor π n).eqn z = fiberEqn π n z :=
  rfl

/-! ## The fiber twist and its two-cover triviality -/

/-- **The fiber twist `Θₙ = 𝒪(n · fiber)`.** The Picard class of the fiber-divisor
local-equation system on the pinned cover, `Θₙ ∈ Y.CechPic`. Two-cover-trivial *by
construction*: on each chart its equation is a single global regular section (`t₀ⁿ` on `V₀`,
`1` on `V₁`), and the transition cocycle is the unit `t₀ⁿ` (`isUnit_fiberCoord_res_inf`). -/
noncomputable def fiberTwist (n : ℕ) : Y.CechPic :=
  (fiberDivisor π n).picClass

/-- The unit Čech cocycle of the fiber twist, retyped on the pinned cover `fiberCover π`
(shared for every `n`, which is what makes the twist arithmetic close). -/
noncomputable def fiberCocycle (n : ℕ) : Y.unitsCocycle (fiberCover π) :=
  (fiberDivisor π n).unitsCocycle

theorem fiberTwist_eq_mk (n : ℕ) :
    fiberTwist π n = CechPic.mk (fiberCover π) (fiberCocycle π n).class :=
  rfl

lemma fiberCocycle_evInf (n : ℕ) (x y : Y) :
    unitsEvInf (fiberCocycle π n) x y = (fiberDivisor π n).ratioUnit x y :=
  (fiberDivisor π n).unitsCocycle_evInf x y

/-- The defining ratio equation for the fiber cocycle, retyped on `fiberCover π`:
`t₀ⁿ|ₓ = gₙ · t₀ⁿ|ᵧ` on the overlap. -/
lemma fiberCocycle_ratio (n : ℕ) (x y : Y) :
    (Y.presheaf.map (homOfLE (inf_le_left :
        (fiberCover π).opens x ⊓ (fiberCover π).opens y ≤ (fiberCover π).opens x)).op).hom
        (fiberEqn π n x)
      = (unitsEvInf (fiberCocycle π n) x y : Γ(Y, (fiberCover π).opens x ⊓ (fiberCover π).opens y))
        * (Y.presheaf.map (homOfLE (inf_le_right :
            (fiberCover π).opens x ⊓ (fiberCover π).opens y ≤ (fiberCover π).opens y)).op).hom
            (fiberEqn π n y) := by
  rw [fiberCocycle_evInf]
  exact (fiberDivisor π n).eqn_restrict_eq x y

/-- **The twist cocycle is multiplicative in `n`:** `gₙ₊₁ = gₙ · g₁`. Proved by cancelling the
regular restriction of `t₀^(n+1)` against the defining ratio equations `fiberCocycle_ratio`. -/
lemma fiberCocycle_succ (n : ℕ) :
    fiberCocycle π (n + 1) = fiberCocycle π n * fiberCocycle π 1 := by
  refine unitsCocycle_ext fun x y => ?_
  rw [mul_unitsEvInf]
  refine Units.ext ?_
  rw [Units.val_mul]
  have hc : (Y.presheaf.map (homOfLE (inf_le_right :
      (fiberCover π).opens x ⊓ (fiberCover π).opens y ≤ (fiberCover π).opens y)).op).hom
        (fiberEqn π (n + 1) y) ∈ nonZeroDivisors _ :=
    (fiberDivisor π (n + 1)).eqn_restrict_mem_nonZeroDivisors y inf_le_right
  refine (mul_cancel_right_mem_nonZeroDivisors hc).mp ?_
  rw [← fiberCocycle_ratio π (n + 1) x y, fiberEqn_succ π n y, map_mul, mul_mul_mul_comm,
    ← fiberCocycle_ratio π n x y, ← fiberCocycle_ratio π 1 x y, ← map_mul, ← fiberEqn_succ π n x]

/-- The zeroth twist cocycle is trivial: `g₀ = 1`. -/
lemma fiberCocycle_zero : fiberCocycle π 0 = 1 := by
  refine unitsCocycle_ext fun x y => ?_
  rw [one_unitsEvInf]
  refine Units.ext ?_
  have h := fiberCocycle_ratio π 0 x y
  rw [fiberEqn_zero, fiberEqn_zero, map_one, map_one, mul_one] at h
  rw [Units.val_one, ← h]

/-- **The twist is the `n`-th power of the unit twist (successor form):** `Θₙ₊₁ = Θₙ · Θ₁`. -/
theorem fiberTwist_succ (n : ℕ) :
    fiberTwist π (n + 1) = fiberTwist π n * fiberTwist π 1 := by
  rw [fiberTwist_eq_mk, fiberTwist_eq_mk, fiberTwist_eq_mk, fiberCocycle_succ,
    OneCocycle.class_mul, CechPic.mk_mul_mk]

/-- The zeroth twist is trivial: `Θ₀ = 1`. -/
@[simp]
theorem fiberTwist_zero : fiberTwist π 0 = 1 := by
  rw [fiberTwist_eq_mk, fiberCocycle_zero, OneCocycle.class_one, CechPic.mk_one]

/-- **The twist is the `n`-th power of the unit twist: `Θₙ = Θ₁ⁿ`.** The fiber-twist scaling
law consumed by the Wave-4 datum: the pinned twist is `n` copies of the single fiber, glued
by the transition cocycle `t₀ⁿ`. -/
theorem fiberTwist_pow (n : ℕ) : fiberTwist π n = fiberTwist π 1 ^ n := by
  induction n with
  | zero => rw [fiberTwist_zero, pow_zero]
  | succ n ih => rw [fiberTwist_succ, ih, pow_succ]

/-! ## The degree of the twist -/

section Degree

variable [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]

/-- **The degree of the fiber twist scales linearly**: `deg Θₙ = n · deg Θ₁`, from the
multiplicativity `Θₙ = Θ₁ⁿ` and the homomorphism property of `classDeg`.

*Frontier* (deliberately not built here, per `informal/w4-datum-design.md` §2(a) and §4.1
w4-5): the normalization `deg Θ₁ = deg π` requires the **pushforward-rank reading** of the
degree — `classDeg 𝒪(D) = dim_K Γ(𝒪_D)` for effective `D`, identifying the fiber divisor's
degree with the module rank of `π` (`finite_app_chartOpen`) — which `RiemannRoch.Degree`
explicitly defers to a later node. Wiring `deg Θ₁ = deg π` is future work once that reading
lands. -/
theorem classDeg_fiberTwist (n : ℕ) :
    classDeg K (fiberTwist π n) = n • classDeg K (fiberTwist π 1) := by
  induction n with
  | zero => rw [fiberTwist_zero, classDeg_one, zero_smul]
  | succ n ih => rw [fiberTwist_succ, classDeg_mul, ih, succ_nsmul]

end Degree

end Main

end AlgebraicGeometry
