/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.WindowFieldTransport
import AlgebraicJacobian.Picard.ThetaChartClassNaturality
import AlgebraicJacobian.RiemannRoch.GluedDivisorSheaf
import AlgebraicJacobian.RiemannRoch.SectionSpaces

/-!
# G-3 (core) — the theta presentation at a field test and the function-field reading

The substrate of the field window→functionField dictionary `Φ`
(`informal/spec-w4-gates.md` §G-3; the keystones `divFamPhi`/`divFamPhi_injective`/
`map_divFamPhi_eps_fst` live in `AlgebraicJacobian.Picard.DivisorFamilyFieldDictionary`):
over a field extension `K/k`, the relative theta twist `𝒪(Θᵃ)` on the fibre curve `C_K`
is trivialized meromorphically, and its global sections are read into `K(C_K)` with
image exactly the section space of the presentation divisor.

* `AlgebraicGeometry.Scheme.dvd_iff_ord_le` /
  `Scheme.LocalEquations.germ_mem_stalkIdeal_iff_ord_le` — **the stalk-ideal ↔ order
  dictionary**: membership in the stalk ideal of a divisor family at a closed point is
  the order bound against the family's local equation (DVR divisibility is valuation
  comparison).
* `AlgebraicGeometry.thetaFieldChartIndex` / `thetaFieldPointedCover` — a
  **deterministic** chart selector (`inl` on `V₀ᴷ`, `inr` off it) and the pointed cover
  by whole pinned charts it indexes.
* `AlgebraicGeometry.thetaFieldPresentation` / `thetaFieldDivisor` — the meromorphic
  presentation of the `K`-level whole-chart theta datum on that cover
  (`MeromorphicPresentation.ofCocycle` of the subordinated cocycle); its divisor `N₀(a)`.
* `AlgebraicGeometry.picClass_thetaFieldDivisor` /
  `picClass_windowTransportDivisor_eq_thetaFieldDivisor` — the class laws: `N₀(a)` lies
  in the `K`-level theta class, which is also the class of the **transported** window
  divisor `windowTransportDivisor C K π a` (the abstract `N` of the DDR-2 `N`-pack) —
  `cechPicClass_baseChange_thetaChartDatum` closes the base-change seam; the **shift
  unit** `thetaFieldShiftUnit` realizes the difference as a principal divisor.
* `AlgebraicGeometry.thetaFieldGluedEquiv` — global theta sections (twisted-pair form)
  are glued sections on the pointed cover (`gluedTwistEquiv`, then `gluedSubordEquiv`),
  with the germ readings `germ_thetaFieldGluedEquiv_fst`/`_snd`.
* `AlgebraicGeometry.thetaFieldRead` — **the reading** `H⁰(𝒪(Θᵃ)) →ₗ[K] K(C_K)`: the
  glued value against the trivialization (`gluedToDivisorApp`); injective
  (`thetaFieldRead_injective`) with image exactly `H⁰(𝒪(N₀(a)))`
  (`thetaFieldRead_mem`, `exists_thetaFieldRead_eq`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.functionFieldOverModule

/-! ## The stalk-ideal ↔ order dictionary at a closed point -/

section StalkOrder

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]

/-- **Divisibility in a DVR stalk is valuation comparison** (the engine of the
stalk-ideal ↔ order dictionary): for elements `y, e` of the stalk at a closed point with
`e ≠ 0`, `e ∣ y` exactly when the order of `y` in the function field is at most that of
`e`.  Total divisibility of the valuation ring, with the unit case read off
`valuation_eq_one_iff_notMem`. -/
theorem Scheme.dvd_iff_ord_le {z : X} (hz : z ≠ genericPoint X)
    {y e : X.presheaf.stalk z} :
    e ∣ y ↔
      Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
          (algebraMap (X.presheaf.stalk z) X.functionField y)
        ≤ Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
            (algebraMap (X.presheaf.stalk z) X.functionField e) := by
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hz
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hz
  have hord : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
      = (stalkHeightOne X z).valuation X.functionField := rfl
  rw [hord]
  constructor
  · rintro ⟨c, rfl⟩
    rw [map_mul, Valuation.map_mul]
    exact mul_le_of_le_one_right' ((stalkHeightOne X z).valuation_le_one c)
  · intro hle
    rcases eq_or_ne y 0 with rfl | hy
    · exact dvd_zero e
    rcases ValuationRing.dvd_total e y with hdvd | hdvd
    · exact hdvd
    · -- `y ∣ e`: the cofactor has valuation `1`, hence is a unit
      obtain ⟨c, hc⟩ := hdvd
      have hyne : (stalkHeightOne X z).valuation X.functionField
          (algebraMap (X.presheaf.stalk z) X.functionField y) ≠ 0 := by
        simp only [ne_eq, Valuation.zero_iff]
        exact fun h0 =>
          hy ((map_eq_zero_iff _
            (IsFractionRing.injective (X.presheaf.stalk z) X.functionField)).mp h0)
      have hcge : (1 : WithZero (Multiplicative ℤ))
          ≤ (stalkHeightOne X z).valuation X.functionField
              (algebraMap (X.presheaf.stalk z) X.functionField c) := by
        have he' : (stalkHeightOne X z).valuation X.functionField
            (algebraMap (X.presheaf.stalk z) X.functionField e)
            = (stalkHeightOne X z).valuation X.functionField
                (algebraMap (X.presheaf.stalk z) X.functionField y)
              * (stalkHeightOne X z).valuation X.functionField
                (algebraMap (X.presheaf.stalk z) X.functionField c) := by
          rw [← Valuation.map_mul, ← map_mul, ← hc]
        rw [he'] at hle
        exact (mul_le_mul_iff_right₀ (zero_lt_iff.mpr hyne)).mp (by rwa [mul_one])
      have hcunit : IsUnit c := by
        have h1 : (stalkHeightOne X z).valuation X.functionField
            (algebraMap (X.presheaf.stalk z) X.functionField c) = 1 :=
          le_antisymm ((stalkHeightOne X z).valuation_le_one c) hcge
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem] at h1
        exact IsLocalRing.notMem_maximalIdeal.mp h1
      obtain ⟨u, rfl⟩ := hcunit
      exact ⟨(u⁻¹ : (X.presheaf.stalk z)ˣ), by
        rw [hc, mul_assoc, Units.mul_inv_eq_one.mpr rfl, mul_one]⟩

/-- **The stalk-ideal ↔ order dictionary** (the pole-bound bridge of the DD-4 field
dictionary): the germ at a closed point `z` of a section `β` lies in the stalk ideal of
the divisor family `d` exactly when the order at `z` of its rational-function reading
`germ_η β` is bounded by the order of `d`'s local equation — i.e. of the trivializing
element `d.presentation.elem z`. -/
theorem Scheme.LocalEquations.germ_mem_stalkIdeal_iff_ord_le (d : X.LocalEquations)
    {U : X.Opens} (hηU : genericPoint X ∈ U) {z : X} (hzU : z ∈ U)
    (hz : z ≠ genericPoint X) (β : Γ(X, U)) :
    (X.presheaf.germ U z hzU).hom β ∈ d.stalkIdeal z ↔
      Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
          ((X.presheaf.germ U (genericPoint X) hηU).hom β)
        ≤ Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
            ((d.presentation.elem z : X.functionField)) := by
  have hβ := Scheme.germ_generic_eq_algebraMap_germ hηU hzU β
  have helem : (d.presentation.elem z : X.functionField)
      = algebraMap (X.presheaf.stalk z) X.functionField
          ((X.presheaf.germ (d.cover.opens z) z (d.cover.mem_opens z)).hom (d.eqn z)) := by
    rw [Scheme.LocalEquations.presentation_elem_val]
    exact Scheme.germ_generic_eq_algebraMap_germ (d.cover.genericPoint_mem_opens z)
      (d.cover.mem_opens z) (d.eqn z)
  rw [Scheme.LocalEquations.stalkIdeal, Ideal.mem_span_singleton, hβ, helem]
  exact Scheme.dvd_iff_ord_le K hz

/-- **The stalk ideal at the generic point is everything**: the local equation is
regular, so its germ at `η` is a nonzero element of the function *field* — the
generic-point clauses of the vanishing submodule are vacuous. -/
theorem Scheme.LocalEquations.stalkIdeal_genericPoint (d : X.LocalEquations) :
    d.stalkIdeal (genericPoint X) = ⊤ := by
  rw [Scheme.LocalEquations.stalkIdeal, Ideal.span_singleton_eq_top]
  have hne : (X.presheaf.germ (d.cover.opens (genericPoint X)) (genericPoint X)
      (d.cover.mem_opens (genericPoint X))).hom (d.eqn (genericPoint X)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp
      (d.regular (genericPoint X) (genericPoint X)
        (d.cover.mem_opens (genericPoint X)))
  exact isUnit_iff_ne_zero.mpr hne

/-- The order of the trivializing element of the presentation of a divisor family is
the divisor bound of the **negated** presentation divisor: `ord_z (elem z)` prescribes
exactly the zero the divisor demands. -/
theorem Scheme.LocalEquations.ord_presentation_elem
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] (d : X.LocalEquations) {z : X}
    (hz : z ≠ genericPoint X) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz ((d.presentation.elem z : X.functionField))
      = Scheme.divisorBound (-Scheme.presentationDivisor K d.presentation) hz := by
  rw [← Scheme.coe_inv_ordZ K (d.presentation.elem z) hz]
  have hbound : Scheme.divisorBound (-Scheme.presentationDivisor K d.presentation) hz
      = ((Multiplicative.ofAdd
            (coeffAt hz (-Scheme.presentationDivisor K d.presentation)) :
          Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    rfl
  have hcoeff : coeffAt hz (-Scheme.presentationDivisor K d.presentation)
      = Multiplicative.toAdd
          ((Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (d.presentation.elem z))⁻¹) := by
    rw [Scheme.CurveDivisor.coeffAt_neg hz,
      Scheme.coeffAt_presentationDivisor K d.presentation hz, toAdd_inv]
  rw [hbound, hcoeff, ofAdd_toAdd]

end StalkOrder

/-! ## The deterministic pointed cover by the pinned charts -/

section Cover

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]

open Classical in
/-- **The deterministic chart selector**: `inl` on the first pinned chart `V₀ᴷ`, `inr`
off it.  Unlike the datum's `pieceIndex` (a `Classical.choose`), the branch is
*provable*: `x ∈ V₀ → thetaFieldChartIndex x = inl`. -/
noncomputable def thetaFieldChartIndex (x : relCurve C K) : (thetaChartCover C K π).index :=
  if x ∈ (relCover C K (fiberTwoCover π)).V₀ then Sum.inl PUnit.unit
  else Sum.inr PUnit.unit

lemma thetaFieldChartIndex_of_mem {x : relCurve C K}
    (hx : x ∈ (relCover C K (fiberTwoCover π)).V₀) :
    thetaFieldChartIndex C K π x = Sum.inl PUnit.unit :=
  if_pos hx

lemma thetaFieldChartIndex_of_notMem {x : relCurve C K}
    (hx : x ∉ (relCover C K (fiberTwoCover π)).V₀) :
    thetaFieldChartIndex C K π x = Sum.inr PUnit.unit :=
  if_neg hx

/-- A point off the first pinned chart lies in the second: the pinned charts cover. -/
lemma mem_V₁_of_notMem_V₀ {x : relCurve C K}
    (hx : x ∉ (relCover C K (fiberTwoCover π)).V₀) :
    x ∈ (relCover C K (fiberTwoCover π)).V₁ := by
  have hx' : x ∈ (relCover C K (fiberTwoCover π)).V₀
      ⊔ (relCover C K (fiberTwoCover π)).V₁ := by rw [relCover_sup]; trivial
  rcases (TopologicalSpace.Opens.mem_sup).mp hx' with h0 | h1
  exacts [absurd h0 hx, h1]

/-- Every point lies in the whole-chart piece its selector picks. -/
lemma mem_pieces_thetaFieldChartIndex (x : relCurve C K) :
    x ∈ (thetaChartCover C K π).pieces (thetaFieldChartIndex C K π x) := by
  by_cases hx : x ∈ (relCover C K (fiberTwoCover π)).V₀
  · rw [thetaFieldChartIndex_of_mem C K π hx, thetaChartCover_pieces_inl]
    exact hx
  · rw [thetaFieldChartIndex_of_notMem C K π hx, thetaChartCover_pieces_inr]
    exact mem_V₁_of_notMem_V₀ C K π hx

/-- **The deterministic pointed cover by the pinned charts**: the member through `x` is
the whole chart selected by `thetaFieldChartIndex`. -/
noncomputable def thetaFieldPointedCover : (relCurve C K).PointedCover where
  opens x := (thetaChartCover C K π).pieces (thetaFieldChartIndex C K π x)
  mem_opens x := mem_pieces_thetaFieldChartIndex C K π x

@[simp]
lemma thetaFieldPointedCover_opens (x : relCurve C K) :
    (thetaFieldPointedCover C K π).opens x
      = (thetaChartCover C K π).pieces (thetaFieldChartIndex C K π x) :=
  rfl

end Cover

/-! ## The theta presentation at the field test and its divisor -/

section Presentation

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]
variable (a : ℕ)

/-- **The subordinated theta cocycle at the field test**: the whole-chart theta datum's
transition units, restricted onto the deterministic pointed cover — a unit Čech
1-cocycle presenting the `K`-level theta class. -/
noncomputable def thetaFieldCocycle :
    (relCurve C K).unitsCocycle (thetaFieldPointedCover C K π) :=
  gluedSubordCocycle (thetaChartDatum C K π a).isGluingCocycle
    (thetaFieldPointedCover C K π) (thetaFieldChartIndex C K π) (fun _ => le_rfl)

variable [IsIntegral (relCurve C K)]

/-- **The theta presentation at the field test**: the meromorphic presentation of the
subordinated theta cocycle on the deterministic pointed cover (base-index construction
at the generic point). -/
noncomputable def thetaFieldPresentation : (relCurve C K).MeromorphicPresentation :=
  Scheme.MeromorphicPresentation.ofCocycle (thetaFieldPointedCover C K π)
    (thetaFieldCocycle C K π a)

@[simp]
lemma thetaFieldPresentation_cover :
    (thetaFieldPresentation C K π a).cover = thetaFieldPointedCover C K π :=
  rfl

@[simp]
lemma thetaFieldPresentation_cocycle :
    (thetaFieldPresentation C K π a).cocycle = thetaFieldCocycle C K π a :=
  rfl

variable [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **The theta divisor at the field test** `N₀(a)`: the presentation divisor of the
theta presentation — an honest Weil divisor on the fibre curve in the `K`-level theta
class `Θᵃ`. -/
noncomputable def thetaFieldDivisor : (relCurve C K).CurveDivisor :=
  Scheme.presentationDivisor K (thetaFieldPresentation C K π a)

/-- The theta divisor lies in the class of the `K`-level whole-chart theta datum. -/
theorem picClass_thetaFieldDivisor :
    Scheme.CurveDivisor.picClass K (thetaFieldDivisor C K π a)
      = (thetaChartDatum C K π a).cechPicClass := by
  rw [thetaFieldDivisor, Scheme.CurveDivisor.picClass_presentationDivisor]
  exact (thetaChartDatum C K π a).cechPicClass_eq_mk (thetaFieldPointedCover C K π)
    (thetaFieldChartIndex C K π) (fun _ => le_rfl)

/-- **The transported window divisor and the theta divisor share their class** (the
base-change seam, closed by `cechPicClass_baseChange_thetaChartDatum`): the abstract `N`
of the DDR-2 `N`-pack and the concrete `N₀(a)` of the reading are linearly
equivalent. -/
theorem picClass_windowTransportDivisor_eq_thetaFieldDivisor :
    Scheme.CurveDivisor.picClass K (windowTransportDivisor C K π a)
      = Scheme.CurveDivisor.picClass K (thetaFieldDivisor C K π a) := by
  rw [picClass_windowTransportDivisor, picClass_thetaFieldDivisor]
  exact cechPicClass_baseChange_thetaChartDatum C K π a

variable [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **The shift unit**: a rational function with
`div w = thetaFieldDivisor − windowTransportDivisor`, extracted from the class equality
(extraction (X), `exists_divOf_of_picClass_eq`).  Multiplication by `w` transports the
reading from the concrete `N₀(a)` to the abstract transported window divisor. -/
noncomputable def thetaFieldShiftUnit : (relCurve C K).functionFieldˣ :=
  (Scheme.CurveDivisor.exists_divOf_of_picClass_eq K
    (picClass_windowTransportDivisor_eq_thetaFieldDivisor C K π a).symm).choose

lemma divOf_thetaFieldShiftUnit :
    thetaFieldDivisor C K π a - windowTransportDivisor C K π a
      = Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
          (thetaFieldShiftUnit C K π a) :=
  (Scheme.CurveDivisor.exists_divOf_of_picClass_eq K
    (picClass_windowTransportDivisor_eq_thetaFieldDivisor C K π a).symm).choose_spec

end Presentation

/-! ## The reading of global theta sections into the function field -/

section Read

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]
variable (a : ℕ)
variable [IsIntegral (relCurve C K)]

/-- **Global theta sections are glued sections on the deterministic pointed cover**: the
collapse to the whole-chart datum (`gluedTwistEquiv`) followed by the subordination onto
the pointed cover (`gluedSubordEquiv`). -/
noncomputable def thetaFieldGluedEquiv :
    relThetaSections C K π a ≃ₗ[K]
      ↥(gluedSubmodule K (thetaFieldPointedCover C K π).opens
        (fun x y => Scheme.unitsEvInf (thetaFieldCocycle C K π a) x y) ⊤) :=
  (gluedTwistEquiv C K π a ⊤).symm.trans
    (gluedSubordEquiv K (U := (thetaChartDatum C K π a).pieces)
      (g := (thetaChartDatum C K π a).unit) (σ := thetaFieldChartIndex C K π)
      (fun _ => le_rfl)
      (fun x y => congrArg Units.val
        (gluedSubordCocycle_evInf (thetaChartDatum C K π a).isGluingCocycle
          (thetaFieldPointedCover C K π) (thetaFieldChartIndex C K π) (fun _ => le_rfl) x y))
      (thetaChartDatum C K π a).isGluingCocycle
      (fun z => ⟨z, (thetaFieldPointedCover C K π).mem_opens z⟩) ⊤)

omit [IsIntegral (relCurve C K)] in
/-- **The germ reading of the glued components on the first chart**: at a point `x` of
`V₀`, the component of the glued image is (a restriction of) the chart-0 component of
the pair — their germs agree at every point of the member. -/
lemma germ_thetaFieldGluedEquiv_fst (s : relThetaSections C K π a) {x : relCurve C K}
    (hx : x ∈ (relCover C K (fiberTwoCover π)).V₀) {w : relCurve C K}
    (hw : w ∈ ⊤ ⊓ (thetaFieldPointedCover C K π).opens x)
    (hw₀ : w ∈ ⊤ ⊓ (relCover C K (fiberTwoCover π)).V₀) :
    ((relCurve C K).presheaf.germ (⊤ ⊓ (thetaFieldPointedCover C K π).opens x) w hw).hom
        ((thetaFieldGluedEquiv C K π a s).val x)
      = ((relCurve C K).presheaf.germ
          (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₀) w hw₀).hom s.val.1 := by
  have hw' : w ∈ ⊤ ⊓ (thetaChartCover C K π).pieces (thetaFieldChartIndex C K π x) := hw
  -- the outer subordination restriction is germ-invariant
  have hA : ((relCurve C K).presheaf.germ
        (⊤ ⊓ (thetaFieldPointedCover C K π).opens x) w hw).hom
        ((thetaFieldGluedEquiv C K π a s).val x)
      = ((relCurve C K).presheaf.germ
          (⊤ ⊓ (thetaChartCover C K π).pieces (thetaFieldChartIndex C K π x)) w hw').hom
        ((twistToGluedApp C K π a ⊤ s).val (thetaFieldChartIndex C K π x)) :=
    (relCurve C K).presheaf.germ_res_apply (homOfLE (inf_le_inf_left ⊤ le_rfl)) w hw
      ((twistToGluedApp C K π a ⊤ s).val (thetaFieldChartIndex C K π x))
  -- move the component to the provable index
  have key : ∀ (j : (thetaChartCover C K π).index)
      (hj : thetaFieldChartIndex C K π x = j)
      (hwj : w ∈ ⊤ ⊓ (thetaChartCover C K π).pieces j),
      ((relCurve C K).presheaf.germ
          (⊤ ⊓ (thetaChartCover C K π).pieces (thetaFieldChartIndex C K π x)) w hw').hom
        ((twistToGluedApp C K π a ⊤ s).val (thetaFieldChartIndex C K π x))
        = ((relCurve C K).presheaf.germ (⊤ ⊓ (thetaChartCover C K π).pieces j) w hwj).hom
            ((twistToGluedApp C K π a ⊤ s).val j) := by
    intro j hj hwj
    cases hj
    rfl
  have hwj : w ∈ ⊤ ⊓ (thetaChartCover C K π).pieces (Sum.inl PUnit.unit) :=
    ⟨trivial, by rw [thetaChartCover_pieces_inl]; exact hw₀.2⟩
  -- the chart-0 component of the datum-glued family is the restricted pair component
  have hB : ((relCurve C K).presheaf.germ
        (⊤ ⊓ (thetaChartCover C K π).pieces (Sum.inl PUnit.unit)) w hwj).hom
        ((twistToGluedApp C K π a ⊤ s).val (Sum.inl PUnit.unit))
      = ((relCurve C K).presheaf.germ
          (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₀) w hw₀).hom s.val.1 :=
    (relCurve C K).presheaf.germ_res_apply
      (homOfLE (inf_le_inf_left ⊤ (thetaChartCover_pieces_le_inl C K π PUnit.unit)))
      w hwj s.val.1
  exact hA.trans
    ((key (Sum.inl PUnit.unit) (thetaFieldChartIndex_of_mem C K π hx) hwj).trans hB)

omit [IsIntegral (relCurve C K)] in
/-- **The germ reading of the glued components off the first chart**: at a point `x`
outside `V₀` (hence in `V₁`), the component of the glued image is (a restriction of)
the chart-1 component of the pair. -/
lemma germ_thetaFieldGluedEquiv_snd (s : relThetaSections C K π a) {x : relCurve C K}
    (hx : x ∉ (relCover C K (fiberTwoCover π)).V₀) {w : relCurve C K}
    (hw : w ∈ ⊤ ⊓ (thetaFieldPointedCover C K π).opens x)
    (hw₁ : w ∈ ⊤ ⊓ (relCover C K (fiberTwoCover π)).V₁) :
    ((relCurve C K).presheaf.germ (⊤ ⊓ (thetaFieldPointedCover C K π).opens x) w hw).hom
        ((thetaFieldGluedEquiv C K π a s).val x)
      = ((relCurve C K).presheaf.germ
          (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₁) w hw₁).hom s.val.2 := by
  have hw' : w ∈ ⊤ ⊓ (thetaChartCover C K π).pieces (thetaFieldChartIndex C K π x) := hw
  have hA : ((relCurve C K).presheaf.germ
        (⊤ ⊓ (thetaFieldPointedCover C K π).opens x) w hw).hom
        ((thetaFieldGluedEquiv C K π a s).val x)
      = ((relCurve C K).presheaf.germ
          (⊤ ⊓ (thetaChartCover C K π).pieces (thetaFieldChartIndex C K π x)) w hw').hom
        ((twistToGluedApp C K π a ⊤ s).val (thetaFieldChartIndex C K π x)) :=
    (relCurve C K).presheaf.germ_res_apply (homOfLE (inf_le_inf_left ⊤ le_rfl)) w hw
      ((twistToGluedApp C K π a ⊤ s).val (thetaFieldChartIndex C K π x))
  have key : ∀ (j : (thetaChartCover C K π).index)
      (hj : thetaFieldChartIndex C K π x = j)
      (hwj : w ∈ ⊤ ⊓ (thetaChartCover C K π).pieces j),
      ((relCurve C K).presheaf.germ
          (⊤ ⊓ (thetaChartCover C K π).pieces (thetaFieldChartIndex C K π x)) w hw').hom
        ((twistToGluedApp C K π a ⊤ s).val (thetaFieldChartIndex C K π x))
        = ((relCurve C K).presheaf.germ (⊤ ⊓ (thetaChartCover C K π).pieces j) w hwj).hom
            ((twistToGluedApp C K π a ⊤ s).val j) := by
    intro j hj hwj
    cases hj
    rfl
  have hwj : w ∈ ⊤ ⊓ (thetaChartCover C K π).pieces (Sum.inr PUnit.unit) :=
    ⟨trivial, by rw [thetaChartCover_pieces_inr]; exact hw₁.2⟩
  have hB : ((relCurve C K).presheaf.germ
        (⊤ ⊓ (thetaChartCover C K π).pieces (Sum.inr PUnit.unit)) w hwj).hom
        ((twistToGluedApp C K π a ⊤ s).val (Sum.inr PUnit.unit))
      = ((relCurve C K).presheaf.germ
          (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₁) w hw₁).hom s.val.2 :=
    (relCurve C K).presheaf.germ_res_apply
      (homOfLE (inf_le_inf_left ⊤ (thetaChartCover_pieces_le_inr C K π PUnit.unit)))
      w hwj s.val.2
  exact hA.trans
    ((key (Sum.inr PUnit.unit) (thetaFieldChartIndex_of_notMem C K π hx) hwj).trans hB)

variable [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **The reading of global theta sections into the function field** (the twist
trivialization at the generic point, §G-3's missing leg): the value of the glued image
against the meromorphic trivialization of the theta presentation. -/
noncomputable def thetaFieldRead :
    relThetaSections C K π a →ₗ[K] (relCurve C K).functionField :=
  (Scheme.divisorSections K
      (Scheme.presentationDivisor K (thetaFieldPresentation C K π a)) ⊤).subtype.comp
    ((Scheme.MeromorphicPresentation.gluedToDivisorApp K
        (thetaFieldPresentation C K π a) (W := ⊤) trivial).comp
      (thetaFieldGluedEquiv C K π a).toLinearMap)

/-- The reading is the glued value against the trivialization. -/
lemma thetaFieldRead_apply (s : relThetaSections C K π a) :
    thetaFieldRead C K π a s
      = Scheme.MeromorphicPresentation.gluedVal K (thetaFieldPresentation C K π a)
          (W := ⊤) trivial (thetaFieldGluedEquiv C K π a s) :=
  rfl

/-- **The pole bound of the reading**: the reading of a global theta section lies in
the section space of the theta divisor, `H⁰(𝒪(N₀(a)))`. -/
lemma thetaFieldRead_mem (s : relThetaSections C K π a) :
    thetaFieldRead C K π a s
      ∈ Scheme.divisorSections K (thetaFieldDivisor C K π a) ⊤ :=
  (Scheme.MeromorphicPresentation.gluedToDivisorApp K (thetaFieldPresentation C K π a)
    (W := ⊤) trivial (thetaFieldGluedEquiv C K π a s)).property

/-- **Injectivity of the reading**: the value determines the glued section
(`gluedToDivisorApp_injective`), which determines the pair. -/
theorem thetaFieldRead_injective : Function.Injective (thetaFieldRead C K π a) := by
  intro s₁ s₂ h
  refine (thetaFieldGluedEquiv C K π a).injective
    (Scheme.MeromorphicPresentation.gluedToDivisorApp_injective K
      (thetaFieldPresentation C K π a) (W := ⊤) trivial ?_)
  exact Subtype.ext h

/-- **Surjectivity of the reading onto the section space of the theta divisor**: every
rational function with poles bounded by `N₀(a)` is the reading of a global theta
section (`gluedToDivisorApp_surjective` through the glued equivalence). -/
theorem exists_thetaFieldRead_eq {f : (relCurve C K).functionField}
    (hf : f ∈ Scheme.divisorSections K (thetaFieldDivisor C K π a) ⊤) :
    ∃ s : relThetaSections C K π a, thetaFieldRead C K π a s = f := by
  obtain ⟨t, ht⟩ := Scheme.MeromorphicPresentation.gluedToDivisorApp_surjective K
    (thetaFieldPresentation C K π a) (W := ⊤) trivial ⟨f, hf⟩
  refine ⟨(thetaFieldGluedEquiv C K π a).symm t, ?_⟩
  have h0 : thetaFieldRead C K π a ((thetaFieldGluedEquiv C K π a).symm t)
      = ((Scheme.MeromorphicPresentation.gluedToDivisorApp K
            (thetaFieldPresentation C K π a) (W := ⊤) trivial
            (thetaFieldGluedEquiv C K π a
              ((thetaFieldGluedEquiv C K π a).symm t)) :
          ↥(Scheme.divisorSections K (thetaFieldDivisor C K π a) ⊤)) :
        (relCurve C K).functionField) :=
    rfl
  rw [h0, (thetaFieldGluedEquiv C K π a).apply_symm_apply t, ht]

end Read

end AlgebraicGeometry
