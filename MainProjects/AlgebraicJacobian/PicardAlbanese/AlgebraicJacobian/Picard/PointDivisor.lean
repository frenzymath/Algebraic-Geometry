/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorClass
import AlgebraicJacobian.RiemannRoch.ChiFiniteness

/-!
# The point-divisor local equations and the Picard class of a Weil divisor

For the curve bundle `X` (integral, smooth of relative dimension one and quasi-compact over
a field `K`) this file turns a Weil divisor into a Čech Picard class, building on the
local-equation constructor of `AlgebraicJacobian.Picard.DivisorClass`.

* `AlgebraicGeometry.Scheme.pointDivisor`: the local equations of the effective divisor
  `1 · x` at a closed point `x` — a uniformizer of the discrete valuation ring `𝒪_{X,x}`
  spread to a section on an open neighbourhood on which it vanishes only at `x`, and the
  constant `1` on the complement of `{x}`.
* `AlgebraicGeometry.Scheme.divisorClass`: the Picard class `𝒪(D)` of a Weil divisor `D`,
  the finitely-supported product of the point-divisor classes to their multiplicities
  (a `ℤ`-power in the commutative group `X.CechPic`). This is total on `X.CurveDivisor`.
* `AlgebraicGeometry.Scheme.divisorClass_add`: additivity of the divisor `↦` class map.
* `AlgebraicGeometry.Scheme.divisorClass_single_eq_pointDivisor`: the normalization anchor,
  identifying the class of a one-point divisor with the point-divisor class.

## Construction of `pointDivisor`

A uniformizer at `x` is a rational function `t` with `ord_x t = ofAdd (−1)`; it is integral
at `x` (`exists_stalk_of_ord_le_one`) so it is the germ at `η` of a section `s₀` over a
neighbourhood `W₀` of `x`. The section `s₀` vanishes at `x` (its germ there is a non-unit)
and at finitely many other closed points (those where the rational function `t` has a zero
or a pole, `ordZ_support_finite`); removing that finite closed set of other zeros gives an
open `V ∋ x` on which `s₀` is a unit away from `x`. The pointed cover `{V, {x}ᶜ}` with the
equations `s₀` on `V` and `1` elsewhere is then a `LocalEquations` system whose overlap
ratio is the unit `s₀` on `V \ {x}`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry

namespace Scheme

variable {K : Type u} [instFld : Field K] {X : Scheme.{u}}
  [instOver : X.Over (Spec (CommRingCat.of K))]
  [instSmooth : SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [instInt : IsIntegral X]
  [instQC : QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-! ## The point section: a uniformizer vanishing only at `x` -/

omit instQC in
/-- **Order `≠ 1` at a zero of a section.** If a section `s` over an open containing `η` and a
closed point `z` is *not* a unit at `z` (i.e. `z ∉ 𝒟(s)`), then its germ at `η`, viewed as a
rational function, does not have trivial order at `z`: `z` is a zero (or pole). Contrapositive
of `Scheme.ord_eq_one_of_mem_basicOpen`. -/
private lemma ord_ne_one_of_notMem_basicOpen {z : X} (hz : z ≠ genericPoint X) {U : X.Opens}
    (s : Γ(X, U)) (hη : genericPoint X ∈ U) (hzU : z ∈ U) (hzs : z ∉ X.basicOpen s) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
        ((X.presheaf.germ U (genericPoint X) hη).hom s) ≠ 1 := by
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hz
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hz
  have hnu : ¬ IsUnit ((X.presheaf.germ U z hzU).hom s) :=
    fun h => hzs ((X.mem_basicOpen s z hzU).mpr h)
  have hgs : (X.presheaf.germ U (genericPoint X) hη).hom s
      = algebraMap (X.presheaf.stalk z) X.functionField ((X.presheaf.germ U z hzU).hom s) :=
    germ_generic_eq_algebraMap_germ hη hzU s
  have hord : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
      = (stalkHeightOne X z).valuation X.functionField := rfl
  rw [hgs, ne_eq, hord, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro h
  exact hnu (IsLocalRing.notMem_maximalIdeal.mp h)

/-- **Existence of a point local equation.** For a closed point `x`, there is an open
neighbourhood `V ∋ x` and a section `s` over `V` whose germ at the generic point is the
chosen uniformizer `uniformizer K hx` (the tracked germ), whose germ is a nonzerodivisor
at every point of `V` (regularity), and a unit at every point of `V` other than `x`
(a uniformizer of `𝒪_{X,x}` whose only zero on `V` is `x`). The germ-at-`η` conjunct is
what pins the divisor the point equations cut out; it is latent in the geometry (the
section is spread out *from* the uniformizer) and here recorded in the specification. -/
private lemma exists_pointLocalEquation (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] {x : X} (hx : x ≠ genericPoint X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ (s : Γ(X, V)),
      (∀ (hη : genericPoint X ∈ V),
          (X.presheaf.germ V (genericPoint X) hη).hom s = uniformizer K hx) ∧
      ∀ (y : X) (hy : y ∈ V),
        (X.presheaf.germ V y hy).hom s ∈ nonZeroDivisors (X.presheaf.stalk y) ∧
          (y ≠ x → IsUnit ((X.presheaf.germ V y hy).hom s)) := by
  set f := X ↘ Spec (CommRingCat.of K) with hf
  -- a uniformizer at `x`, as a nonzero rational function
  have ht0 : uniformizer K hx ≠ 0 := uniformizer_ne_zero K hx
  set tu : X.functionFieldˣ := Units.mk0 (uniformizer K hx) ht0 with htu
  have htuv : (tu : X.functionField) = uniformizer K hx := rfl
  -- `t` is integral at `x`
  have hord_le : Scheme.ord f hx (uniformizer K hx) ≤ 1 := by
    rw [ord_uniformizer K hx]
    rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num
  obtain ⟨y_st, hy_st⟩ := exists_stalk_of_ord_le_one K hx hord_le
  obtain ⟨W₀, hxW₀, s₀, hs₀⟩ := X.presheaf.exists_germ_eq (x := x) y_st
  have hηW₀ : genericPoint X ∈ W₀ := genericPoint_mem_of_nonempty ⟨x, hxW₀⟩
  -- the germ of `s₀` at `η` is the uniformizer
  have hgη : (X.presheaf.germ W₀ (genericPoint X) hηW₀).hom s₀ = uniformizer K hx := by
    rw [germ_generic_eq_algebraMap_germ hηW₀ hxW₀ s₀, hs₀, hy_st]
  -- the finite set of closed points where `t` has a zero or pole, other than `x`
  have hSfin : {p : {q : X // q ≠ genericPoint X} | Scheme.ordZ f p.2 tu ≠ 1}.Finite :=
    Scheme.ordZ_support_finite f tu
  set bad : Set X :=
    (Subtype.val '' {p : {q : X // q ≠ genericPoint X} | Scheme.ordZ f p.2 tu ≠ 1}) \ {x}
    with hbad
  have hbad_fin : bad.Finite := (hSfin.image Subtype.val).sdiff
  have hbad_ne : ∀ p ∈ bad, p ≠ genericPoint X := by
    rintro p ⟨⟨q, _, rfl⟩, _⟩
    exact q.2
  have hbad_closed : IsClosed bad := by
    rw [← Set.biUnion_of_singleton bad]
    exact hbad_fin.isClosed_biUnion
      (fun p hp => isClosed_singleton_of_ne_genericPoint f (hbad_ne p hp))
  -- the neighbourhood with the other zeros removed
  set V : X.Opens := ⟨(W₀ : Set X) \ bad, W₀.2.sdiff hbad_closed⟩ with hV
  have hVW₀ : V ≤ W₀ := Set.sdiff_subset
  have hxV : x ∈ V := ⟨hxW₀, fun h => h.2 rfl⟩
  refine ⟨V, hxV, (X.presheaf.map (homOfLE hVW₀).op).hom s₀, fun hη => ?_, fun y hy => ?_⟩
  · -- the germ at `η` is the tracked uniformizer
    exact (X.presheaf.germ_res_apply (homOfLE hVW₀) (genericPoint X) hη s₀).trans hgη
  -- the germ of the restricted section at `y`
  have hgy : (X.presheaf.germ V y hy).hom ((X.presheaf.map (homOfLE hVW₀).op).hom s₀)
      = (X.presheaf.germ W₀ y (hVW₀ hy)).hom s₀ :=
    X.presheaf.germ_res_apply (homOfLE hVW₀) y hy s₀
  -- the germ, as a rational function via the structure map to the function field
  have hgalg : algebraMap (X.presheaf.stalk y) X.functionField
      ((X.presheaf.germ W₀ y (hVW₀ hy)).hom s₀) = uniformizer K hx :=
    (germ_generic_eq_algebraMap_germ hηW₀ (hVW₀ hy) s₀).symm.trans hgη
  refine ⟨?_, fun hyx => ?_⟩
  · -- regularity: the germ is a nonzerodivisor (it is nonzero in the domain stalk)
    rw [hgy, mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    rw [hzero, map_zero] at hgalg
    exact ht0 hgalg.symm
  · -- unit away from `x`
    rw [hgy]
    by_cases hyη : y = genericPoint X
    · subst hyη
      rw [show (X.presheaf.germ W₀ (genericPoint X) (hVW₀ hy)).hom s₀ = uniformizer K hx
        from hgη]
      exact isUnit_iff_ne_zero.mpr ht0
    · by_contra hnu
      have hybad : y ∈ bad := by
        refine ⟨⟨⟨y, hyη⟩, ?_, rfl⟩, ?_⟩
        · change Scheme.ordZ f hyη tu ≠ 1
          rw [ne_eq, Scheme.ordZ_eq_one_iff f hyη tu, htuv]
          intro hord1
          have hne := ord_ne_one_of_notMem_basicOpen (K := K) (z := y) hyη s₀ hηW₀ (hVW₀ hy)
            (fun h => hnu ((X.mem_basicOpen s₀ y (hVW₀ hy)).mp h))
          rw [hgη] at hne
          exact hne hord1
        · exact hyx
      exact hy.2 hybad

/-! ## The point divisor and the Picard class of a Weil divisor

The point divisor `1 · x` is packaged from the *tracked* data of `exists_pointLocalEquation`
through top-level named pieces (`pointOpen`, `pointSec`, `pointDivisorCover`,
`pointDivisorEqn`), so that its defining equations — and in particular the germ at `η` of the
equation at `x` — are publicly accessible (`germGeneric_pointDivisorEqn_self`). This is what
lets the compatibility bridge read off the divisor `pointDivisor` cuts out. -/

section PointDivisorConstruction

variable (K : Type u) [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] {x : X} (hx : x ≠ genericPoint X)

/-- The chosen open neighbourhood `V ∋ x` carrying the tracked point-uniformizer section
(`exists_pointLocalEquation`). -/
noncomputable def pointOpen : X.Opens := (exists_pointLocalEquation K hx).choose

/-- The point `x` lies in the chosen neighbourhood. -/
lemma mem_pointOpen : x ∈ pointOpen K hx := (exists_pointLocalEquation K hx).choose_spec.1

/-- The chosen spread-out uniformizer section on `pointOpen K hx`. -/
noncomputable def pointSec : Γ(X, pointOpen K hx) :=
  ((exists_pointLocalEquation K hx).choose_spec).2.choose

/-- **The tracked germ.** The germ at the generic point of the chosen section is the chosen
uniformizer `uniformizer K hx`. -/
lemma germGeneric_pointSec (hη : genericPoint X ∈ pointOpen K hx) :
    (X.presheaf.germ (pointOpen K hx) (genericPoint X) hη).hom (pointSec K hx)
      = uniformizer K hx :=
  ((exists_pointLocalEquation K hx).choose_spec).2.choose_spec.1 hη

/-- The chosen section is regular: its germs are nonzerodivisors. -/
lemma pointSec_regular (y : X) (hy : y ∈ pointOpen K hx) :
    (X.presheaf.germ (pointOpen K hx) y hy).hom (pointSec K hx)
      ∈ nonZeroDivisors (X.presheaf.stalk y) :=
  (((exists_pointLocalEquation K hx).choose_spec).2.choose_spec.2 y hy).1

/-- Away from `x`, the chosen section is a unit. -/
lemma isUnit_germ_pointSec (y : X) (hy : y ∈ pointOpen K hx) (hyx : y ≠ x) :
    IsUnit ((X.presheaf.germ (pointOpen K hx) y hy).hom (pointSec K hx)) :=
  (((exists_pointLocalEquation K hx).choose_spec).2.choose_spec.2 y hy).2 hyx

/-- The complement of the closed point `x`, as an open of `X`. -/
def pointDivisorCompl : X.Opens :=
  ⟨({x} : Set X)ᶜ,
    (isClosed_singleton_of_ne_genericPoint (X ↘ Spec (CommRingCat.of K)) hx).isOpen_compl⟩

open Classical in
/-- The pointed cover `{V, {x}ᶜ}` of the point divisor at `x`: the piece at `x` is the
neighbourhood of the chosen uniformizer, every other piece is the complement of `x`. -/
noncomputable def pointDivisorCover : X.PointedCover where
  opens y := if y = x then pointOpen K hx else pointDivisorCompl K hx
  mem_opens y := by
    by_cases h : y = x
    · rw [if_pos h]; subst h; exact mem_pointOpen K hx
    · rw [if_neg h]; exact h

@[simp]
lemma pointDivisorCover_opens_self :
    (pointDivisorCover K hx).opens x = pointOpen K hx :=
  if_pos rfl

lemma pointDivisorCover_opens_of_ne {z : X} (hz : z ≠ x) :
    (pointDivisorCover K hx).opens z = pointDivisorCompl K hx :=
  if_neg hz

open Classical in
/-- The equations of the point divisor at `x`: the chosen uniformizer section on the piece at
`x`, the constant `1` on every other piece. -/
noncomputable def pointDivisorEqn (z : X) : Γ(X, (pointDivisorCover K hx).opens z) :=
  if h : z = x then
    (X.presheaf.map
        (homOfLE (le_of_eq (by rw [h, pointDivisorCover_opens_self]))).op).hom (pointSec K hx)
  else 1

lemma pointDivisorEqn_self :
    pointDivisorEqn K hx x
      = (X.presheaf.map
          (homOfLE (pointDivisorCover_opens_self K hx).le).op).hom (pointSec K hx) :=
  dif_pos rfl

lemma pointDivisorEqn_of_ne {z : X} (hz : z ≠ x) : pointDivisorEqn K hx z = 1 :=
  dif_neg hz

/-- **The tracked germ of the point equation** (the exported consequence of the strengthened
`exists_pointLocalEquation`): the germ at the generic point of the equation at `x` is the
chosen uniformizer. This pins the divisor `pointDivisor` cuts out. -/
theorem germGeneric_pointDivisorEqn_self
    (hη : genericPoint X ∈ (pointDivisorCover K hx).opens x) :
    (X.presheaf.germ ((pointDivisorCover K hx).opens x) (genericPoint X) hη).hom
        (pointDivisorEqn K hx x)
      = uniformizer K hx := by
  rw [pointDivisorEqn_self, X.presheaf.germ_res_apply]
  exact germGeneric_pointSec K hx _

omit [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X] hx in
/-- Restriction of sections composes (a local copy of the `DivisorClass` helper). -/
private lemma pointDivisor_map_map_sec {W V U : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s)
      = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- **The point divisor `1 · x`.** The local equations of the effective divisor `1 · x` at a
closed point `x`: on the neighbourhood `pointOpen K hx` the equation is the tracked
uniformizer section, and on the complement `{x}ᶜ` it is `1`. The overlap ratio on `V \ {x}` is
the uniformizer, a unit there. Unlike an existential, all defining data is publicly accessible
(`pointDivisorEqn_self`, `pointDivisorEqn_of_ne`, `germGeneric_pointDivisorEqn_self`). -/
noncomputable def pointDivisor : X.LocalEquations where
  cover := pointDivisorCover K hx
  eqn := pointDivisorEqn K hx
  regular := by
    intro x' y hy
    by_cases h : x' = x
    · subst h
      rw [pointDivisorEqn_self, X.presheaf.germ_res_apply]
      exact pointSec_regular K hx y _
    · rw [pointDivisorEqn_of_ne K hx h, map_one]
      exact one_mem _
  ratio_isUnit := by
    intro x' y'
    by_cases h : x' = x <;> by_cases h' : y' = x
    · -- both pieces at `x`: the ratio is `1`
      subst h; subst h'
      refine ⟨1, ?_⟩
      rw [Units.val_one, one_mul]
    · -- piece at `x` against a piece away from `x`: the ratio is the unit section
      subst h
      have hle : (pointDivisorCover K hx).opens x' ⊓ (pointDivisorCover K hx).opens y'
          ≤ pointOpen K hx :=
        le_trans inf_le_left (pointDivisorCover_opens_self K hx).le
      have hne : ∀ z ∈ (pointDivisorCover K hx).opens x' ⊓ (pointDivisorCover K hx).opens y',
          z ≠ x' := by
        intro z hz
        have h2 : z ∈ (pointDivisorCover K hx).opens y' := hz.2
        rw [pointDivisorCover_opens_of_ne K hx h'] at h2
        exact h2
      have hunit : IsUnit ((X.presheaf.map (homOfLE hle).op).hom (pointSec K hx)) := by
        apply X.toRingedSpace.isUnit_of_isUnit_germ
        intro z hz
        rw [X.presheaf.germ_res_apply]
        exact isUnit_germ_pointSec K hx z (hle hz) (hne z hz)
      refine ⟨hunit.unit, ?_⟩
      rw [pointDivisorEqn_of_ne K hx h', map_one, mul_one, IsUnit.unit_spec,
        pointDivisorEqn_self, pointDivisor_map_map_sec]
    · -- piece away from `x` against the piece at `x`: the inverse unit
      subst h'
      have hle : (pointDivisorCover K hx).opens x' ⊓ (pointDivisorCover K hx).opens y'
          ≤ pointOpen K hx :=
        le_trans inf_le_right (pointDivisorCover_opens_self K hx).le
      have hne : ∀ z ∈ (pointDivisorCover K hx).opens x' ⊓ (pointDivisorCover K hx).opens y',
          z ≠ y' := by
        intro z hz
        have h1 : z ∈ (pointDivisorCover K hx).opens x' := hz.1
        rw [pointDivisorCover_opens_of_ne K hx h] at h1
        exact h1
      have hunit : IsUnit ((X.presheaf.map (homOfLE hle).op).hom (pointSec K hx)) := by
        apply X.toRingedSpace.isUnit_of_isUnit_germ
        intro z hz
        rw [X.presheaf.germ_res_apply]
        exact isUnit_germ_pointSec K hx z (hle hz) (hne z hz)
      refine ⟨hunit.unit⁻¹, ?_⟩
      rw [pointDivisorEqn_of_ne K hx h, map_one, pointDivisorEqn_self,
        pointDivisor_map_map_sec]
      exact (Units.inv_mul_of_eq hunit.unit_spec).symm
    · -- both pieces away from `x`: the ratio is `1`
      refine ⟨1, ?_⟩
      rw [pointDivisorEqn_of_ne K hx h, pointDivisorEqn_of_ne K hx h', map_one, map_one,
        Units.val_one, mul_one]

@[simp]
lemma pointDivisor_cover (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] {x : X} (hx : x ≠ genericPoint X) :
    (pointDivisor K hx).cover = pointDivisorCover K hx :=
  rfl

@[simp]
lemma pointDivisor_eqn (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] {x : X} (hx : x ≠ genericPoint X) (z : X) :
    (pointDivisor K hx).eqn z = pointDivisorEqn K hx z :=
  rfl

end PointDivisorConstruction

/-- **The Picard class of a Weil divisor.** The finitely supported product of the point-divisor
classes to their multiplicities (an integer power in the commutative group `X.CechPic`). This
is total on `X.CurveDivisor`: negative multiplicities contribute inverse classes. -/
noncomputable def divisorClass (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] (D : X.CurveDivisor) : X.CechPic :=
  (toFinsupp D).prod fun p n => (pointDivisor K p.2).picClass ^ n

/-- **Additivity of the divisor class.** `𝒪(D + D') = 𝒪(D) · 𝒪(D')`. -/
theorem divisorClass_add (D D' : X.CurveDivisor) :
    divisorClass K (D + D') = divisorClass K D * divisorClass K D' := by
  simp only [divisorClass]
  exact Finsupp.prod_add_index' (fun p => zpow_zero _) (fun p m n => zpow_add _ m n)

/-- **Normalization anchor.** The class of the one-point divisor `1 · x` is the point-divisor
class. -/
theorem divisorClass_single_eq_pointDivisor {x : X} (hx : x ≠ genericPoint X) :
    divisorClass K (CurveDivisor.single hx 1) = (pointDivisor K hx).picClass := by
  rw [divisorClass, CurveDivisor.toFinsupp_single,
    Finsupp.prod_single_index (zpow_zero _), zpow_one]

end Scheme

end AlgebraicGeometry
