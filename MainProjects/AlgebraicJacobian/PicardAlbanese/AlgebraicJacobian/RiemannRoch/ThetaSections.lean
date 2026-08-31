/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.TwistedSheaf
import AlgebraicJacobian.RiemannRoch.FLVFiberToolkit
import AlgebraicJacobian.RiemannRoch.SectionSpaces

/-!
# DD-4 (field level) — the twisted sheaf of `Θⁿ` is the divisor sheaf `𝒪(n·F)`

The W6-lite transport seam of the DAT-D campaign (`informal/dat-d-worksheet.md` §2.1,
§5 DD-4): the `H_A` spaces are *stated* on the divisor sheaf `𝒪(A·F)`
(`F = fiberWeilDivisor π`, the DD-F/P-fib vocabulary), while the relative engine works
on the two-chart twist cocycle `t₀ᴬ` (`RigidEngine4*`, `TwistedSheaf`). This file owns
the bridge, on the curve bundle `Y` over a field `K` with a dominant `π : Y ⟶ ℙ¹`:

* `AlgebraicGeometry.thetaUnit` — the transition unit `t₀|_{V₀ ⊓ V₁} ∈ Γ(Y, V₀ ⊓ V₁)ˣ`
  of the fiber twist, with inverse `t₁|_{V₀ ⊓ V₁}` (`fiberCoord_mul_fiberCoord₁_res`);
  its `n`-th power is the two-cover cocycle of `Θⁿ = fiberTwist π n`.
* `AlgebraicGeometry.thetaTwistSheaf π n := twistSheaf K V₀ V₁ (thetaUnit π ^ n)` —
  the engine-side spelling of `𝒪(Θⁿ)`.
* `AlgebraicGeometry.thetaTwistDivisorSheafIso` —
  **`thetaTwistSheaf π n ≅ Y.divisorSheaf K (n • fiberWeilDivisor π)`**: over a
  nonempty open a matching pair `(s₀, s₁)` corresponds to the rational function
  `u⁻ⁿ · germ_η s₀ = germ_η s₁` (`u = fiberCoordUnit π`), the mirror of
  `MeromorphicPresentation.gluedDivisorSheafIso` on the two-chart carrier.
* `AlgebraicGeometry.thetaTwistH0Equiv` — the `H⁰` reading:
  `H⁰(thetaTwistSheaf π n) ≃ₗ[K] divisorSections K (n • F) ⊤` — the `H_A` spaces in
  DD-F's `divisorSections` spelling.
* `AlgebraicGeometry.subsingleton_hModule_thetaTwistSheaf_one_iff` — the `H¹` vanishing
  transport that lets the DD-0 window ledger fire on the twist sheaf.

The pole-bound bookkeeping runs through the FLV fiber order table
(`fiberWeilDivisor_coeffAt_of_mem_chart₀/₁`) and `Scheme.ord_val_eq`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

/-- Germs at a point commute with `resHom`: the germ of a restricted section is the germ
of the section (the two-cover mirror of the `GluedDivisorSheaf` helper). -/
private lemma germ_resHom {Y : Scheme.{u}} {V W : Y.Opens} (h : W ≤ V) (x : Y) (hx : x ∈ W)
    (t : Γ(Y, V)) :
    (Y.presheaf.germ W x hx).hom (Y.resHom h t) =
      (Y.presheaf.germ V x (h hx)).hom t :=
  Y.presheaf.germ_res_apply (homOfLE h) x hx t

/-! ## The theta transition unit -/

section Unit

variable {K : Type u} [Field K] {Y : Scheme.{u}} (π : Y ⟶ P1 K)

/-- **The theta transition unit** `t₀|_{V₀ ⊓ V₁} ∈ Γ(Y, V₀ ⊓ V₁)ˣ`: the restriction of
the pulled-back chart-0 coordinate to the two-cover overlap, a unit with explicit
inverse the restricted chart-1 coordinate (`fiberCoord_mul_fiberCoord₁_res`). Its `n`-th
power is the transition cocycle of the fiber twist `Θⁿ` (`fiberDivisor`/`fiberCocycle`
normalization, `RiemannRoch/FiberTwist.lean`). -/
noncomputable def thetaUnit : Γ(Y, fiberChart₀ π ⊓ fiberChart₁ π)ˣ where
  val := (Y.presheaf.map (homOfLE
    (inf_le_left : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₀ π)).op).hom (fiberCoord π)
  inv := (Y.presheaf.map (homOfLE
    (inf_le_right : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₁ π)).op).hom (fiberCoord₁ π)
  val_inv := fiberCoord_mul_fiberCoord₁_res π
  inv_val := by rw [mul_comm]; exact fiberCoord_mul_fiberCoord₁_res π

lemma thetaUnit_val : (thetaUnit π : Γ(Y, fiberChart₀ π ⊓ fiberChart₁ π))
    = (Y.presheaf.map (homOfLE
        (inf_le_left : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₀ π)).op).hom
        (fiberCoord π) := rfl

/-- **The engine-side spelling of `𝒪(Θⁿ)`**: the cocycle-glued twisted sheaf of the
`n`-th power of the theta transition unit on the pinned two-cover. -/
noncomputable def thetaTwistSheaf [Y.Over (Spec (CommRingCat.of K))] (n : ℕ) :
    Sheaf (Opens.grothendieckTopology (Y : TopCat)) (ModuleCat.{u} K) :=
  twistSheaf K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)

end Unit

/-! ## The value of a twisted section -/

section Value

variable (K : Type u) [Field K] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))] [IsIntegral Y]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  (π : Y ⟶ P1 K) [IsDominant π] (n : ℕ)

omit [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] in
/-- The germ at `η` of the theta unit is the fiber unit `u`. -/
lemma germ_thetaUnit_val :
    (Y.presheaf.germ (fiberChart₀ π ⊓ fiberChart₁ π) (genericPoint Y)
        (genericPoint_mem_preimage_inf π)).hom (thetaUnit π : Γ(Y, _)) =
      (fiberCoordUnit π : Y.functionField) := by
  rw [thetaUnit_val, Y.presheaf.germ_res_apply]
  rfl

omit [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] in
/-- The germ at `η` of the `n`-th power of the theta unit is `uⁿ`. -/
lemma germ_thetaUnit_pow_val :
    (Y.presheaf.germ (fiberChart₀ π ⊓ fiberChart₁ π) (genericPoint Y)
        (genericPoint_mem_preimage_inf π)).hom
        ((thetaUnit π ^ n : Γ(Y, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) : Γ(Y, _)) =
      ((fiberCoordUnit π ^ n : Y.functionFieldˣ) : Y.functionField) := by
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    germ_thetaUnit_val K π]

/-- **The value of a twisted section** over a nonempty open: the germ at `η` of the
chart-0 component, divided by `uⁿ`. This is the mirror of
`MeromorphicPresentation.gluedVal` on the two-chart carrier. -/
noncomputable def thetaVal {W : Y.Opens} (hηW : genericPoint Y ∈ W)
    (p : ↥(twistSubmodule K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) W)) :
    Y.functionField :=
  (((fiberCoordUnit π ^ n)⁻¹ : Y.functionFieldˣ) : Y.functionField) *
    (Y.presheaf.germ (W ⊓ fiberChart₀ π) (genericPoint Y)
      ⟨hηW, (genericPoint_mem_preimage_inf π).1⟩).hom p.val.1

omit [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] in
/-- **The value read on the second chart**: the matching relation pushed to `η` cancels
the `uⁿ` factor, so `thetaVal p = germ_η p.2`. -/
lemma thetaVal_eq_germ_snd {W : Y.Opens} (hηW : genericPoint Y ∈ W)
    (p : ↥(twistSubmodule K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) W)) :
    thetaVal K π n hηW p =
      (Y.presheaf.germ (W ⊓ fiberChart₁ π) (genericPoint Y)
        ⟨hηW, (genericPoint_mem_preimage_inf π).2⟩).hom p.val.2 := by
  have hηT : genericPoint Y ∈ W ⊓ fiberChart₀ π ⊓ fiberChart₁ π :=
    ⟨⟨hηW, (genericPoint_mem_preimage_inf π).1⟩, (genericPoint_mem_preimage_inf π).2⟩
  have hmatch := (mem_twistSubmodule_iff K (fiberChart₀ π) (fiberChart₁ π)
    (thetaUnit π ^ n) p.val).mp p.property
  have hg := congrArg
    (Y.presheaf.germ (W ⊓ fiberChart₀ π ⊓ fiberChart₁ π) (genericPoint Y) hηT).hom hmatch
  -- identify the three germs: `s₀`, `g^n ↦ uⁿ`, and `s₁`, all through `germ_resHom`
  rw [map_mul, germ_resHom, germ_resHom, germ_resHom, germ_thetaUnit_pow_val K π n] at hg
  -- `thetaVal = u⁻ⁿ · germ_η s₀`; substitute `germ_η s₀ = uⁿ · germ_η s₁` and cancel
  change (((fiberCoordUnit π ^ n)⁻¹ : Y.functionFieldˣ) : Y.functionField) *
      (Y.presheaf.germ (W ⊓ fiberChart₀ π) (genericPoint Y)
        ⟨hηW, (genericPoint_mem_preimage_inf π).1⟩).hom p.val.1 =
      (Y.presheaf.germ (W ⊓ fiberChart₁ π) (genericPoint Y) _).hom p.val.2
  rw [hg, ← mul_assoc, Units.inv_mul, one_mul]

/-! ## The pole bound of a twisted value -/

private lemma divOf_pow (w : Y.functionFieldˣ) (m : ℕ) :
    Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (w ^ m)
      = m • Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) w := by
  induction m with
  | zero => rw [pow_zero, Scheme.divOf_one, zero_smul]
  | succ m ih => rw [pow_succ, Scheme.divOf_mul, ih, succ_nsmul]

private lemma coeffAt_nsmul (m : ℕ) (D : Y.CurveDivisor) {z : Y} (hz : z ≠ genericPoint Y) :
    coeffAt hz (m • D) = m • coeffAt hz D := by
  induction m with
  | zero => rw [zero_smul, zero_smul, CurveDivisor.coeffAt_zero]
  | succ m ih => rw [succ_nsmul, succ_nsmul, CurveDivisor.coeffAt_add, ih]

/-- **On the chart `V₀` the order of `u⁻ⁿ` is exactly the pole bound of `n·F`**: the fiber
divisor agrees with `div u` there (`fiberWeilDivisor_coeffAt_of_mem_chart₀`) and
`divOf(uⁿ) = n • div u`. This is the two-chart mirror of `ord_elem_inv`. -/
private lemma ord_thetaCoeff_eq_divisorBound {z : Y} (hz : z ≠ genericPoint Y)
    (hzV₀ : z ∈ fiberChart₀ π) :
    Scheme.ord (Y ↘ Spec (CommRingCat.of K)) hz
        (((fiberCoordUnit π ^ n)⁻¹ : Y.functionFieldˣ) : Y.functionField)
      = divisorBound (n • fiberWeilDivisor π) hz := by
  have hinv : Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π ^ n)⁻¹
      = - Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π ^ n) := by
    rw [eq_neg_iff_add_eq_zero, ← Scheme.divOf_mul, inv_mul_cancel, Scheme.divOf_one]
  have hcoeff : coeffAt hz (- Scheme.divOf (Y ↘ Spec (CommRingCat.of K))
        (fiberCoordUnit π ^ n)⁻¹) = coeffAt hz (n • fiberWeilDivisor π) := by
    rw [CurveDivisor.coeffAt_neg, hinv, CurveDivisor.coeffAt_neg, neg_neg, divOf_pow,
      coeffAt_nsmul, coeffAt_nsmul, fiberWeilDivisor_coeffAt_of_mem_chart₀ π hz hzV₀]
  rw [ord_val_eq K ((fiberCoordUnit π ^ n)⁻¹) hz, divisorBound_eq_coeffAt,
    divisorBound_eq_coeffAt, hcoeff]

/-- **The pole bound of the twisted value**: the value of a twisted section lies in
`𝒪(n·F)(W)`. Read on the chart containing the point: on `V₁` the fiber divisor vanishes
and the value is integral (`thetaVal = germ_η s₁`); on `V₀` the `u⁻ⁿ` factor realizes the
allowed pole `n·F` exactly. -/
lemma thetaVal_mem {W : Y.Opens} (hηW : genericPoint Y ∈ W)
    (p : ↥(twistSubmodule K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) W)) :
    thetaVal K π n hηW p ∈ divisorSections K (n • fiberWeilDivisor π) W := by
  rw [mem_divisorSections_of_nonempty K ⟨genericPoint Y, hηW⟩]
  intro z hz hzW
  have hsup : fiberChart₀ π ⊔ fiberChart₁ π = ⊤ := preimage_chartOpen_sup π
  have hmem : (z : Y) ∈ (fiberChart₀ π : Set Y) ∪ (fiberChart₁ π : Set Y) := by
    rw [← Opens.coe_sup, hsup, Opens.coe_top]; exact Set.mem_univ z
  rcases hmem with hzV₀ | hzV₁
  · -- chart 0: `thetaVal = u⁻ⁿ · germ_η s₀`, pole exactly `n·F`
    have hval : thetaVal K π n hηW p =
        (((fiberCoordUnit π ^ n)⁻¹ : Y.functionFieldˣ) : Y.functionField) *
          (Y.presheaf.germ (W ⊓ fiberChart₀ π) (genericPoint Y)
            ⟨hηW, (genericPoint_mem_preimage_inf π).1⟩).hom p.val.1 := rfl
    have hgerm : Scheme.ord (Y ↘ Spec (CommRingCat.of K)) hz
        ((Y.presheaf.germ (W ⊓ fiberChart₀ π) (genericPoint Y)
          ⟨hηW, (genericPoint_mem_preimage_inf π).1⟩).hom p.val.1) ≤ 1 := by
      rw [germ_generic_eq_algebraMap_germ
        (show genericPoint Y ∈ W ⊓ fiberChart₀ π from
          ⟨hηW, (genericPoint_mem_preimage_inf π).1⟩)
        (show z ∈ W ⊓ fiberChart₀ π from ⟨hzW, hzV₀⟩) p.val.1]
      exact ord_algebraMap_stalk_le_one K hz _
    calc Scheme.ord (Y ↘ Spec (CommRingCat.of K)) hz (thetaVal K π n hηW p)
        = Scheme.ord (Y ↘ Spec (CommRingCat.of K)) hz
            (((fiberCoordUnit π ^ n)⁻¹ : Y.functionFieldˣ) : Y.functionField) *
          Scheme.ord (Y ↘ Spec (CommRingCat.of K)) hz
            ((Y.presheaf.germ (W ⊓ fiberChart₀ π) (genericPoint Y)
              ⟨hηW, (genericPoint_mem_preimage_inf π).1⟩).hom p.val.1) := by
          rw [hval, map_mul]
      _ ≤ Scheme.ord (Y ↘ Spec (CommRingCat.of K)) hz
            (((fiberCoordUnit π ^ n)⁻¹ : Y.functionFieldˣ) : Y.functionField) * 1 :=
          mul_le_mul_right hgerm _
      _ = divisorBound (n • fiberWeilDivisor π) hz := by
          rw [mul_one, ord_thetaCoeff_eq_divisorBound K π n hz hzV₀]
  · -- chart 1: `thetaVal = germ_η s₁`; `F` vanishes on `V₁`, so `n·F` imposes no pole
    have hb : divisorBound (n • fiberWeilDivisor π) hz = 1 := by
      rw [divisorBound_eq_coeffAt, coeffAt_nsmul,
        fiberWeilDivisor_coeffAt_of_mem_chart₁ π hz hzV₁, smul_zero, ofAdd_zero,
        WithZero.coe_one]
    rw [thetaVal_eq_germ_snd K π n hηW p,
      germ_generic_eq_algebraMap_germ
        (show genericPoint Y ∈ W ⊓ fiberChart₁ π from
          ⟨hηW, (genericPoint_mem_preimage_inf π).2⟩)
        (show z ∈ W ⊓ fiberChart₁ π from ⟨hzW, hzV₁⟩) p.val.2, hb]
    exact ord_algebraMap_stalk_le_one K hz _

/-! ## The section-wise map and its injectivity -/

/-- **The section-wise `K`-linear map `Θⁿ(W) → 𝒪(n·F)(W)`** for a nonempty open:
`p ↦ (uⁿ)⁻¹ · germ_η p₀` (the chart-0 reading of the twisted value). -/
noncomputable def thetaToDivisorApp {W : Y.Opens} (hηW : genericPoint Y ∈ W) :
    ↥(twistSubmodule K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) W) →ₗ[K]
      ↥(divisorSections K (n • fiberWeilDivisor π) W) :=
  LinearMap.codRestrict (divisorSections K (n • fiberWeilDivisor π) W)
    ((Scheme.mulLinear K
        (((fiberCoordUnit π ^ n)⁻¹ : Y.functionFieldˣ) : Y.functionField)).comp
      ((germGenericLinear K (show genericPoint Y ∈ W ⊓ fiberChart₀ π from
          ⟨hηW, (genericPoint_mem_preimage_inf π).1⟩)).comp
        ((LinearMap.fst K _ _).comp
          (twistSubmodule K (fiberChart₀ π) (fiberChart₁ π)
            (thetaUnit π ^ n) W).subtype)))
    (fun p => thetaVal_mem K π n hηW p)

lemma thetaToDivisorApp_coe {W : Y.Opens} (hηW : genericPoint Y ∈ W)
    (p : ↥(twistSubmodule K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) W)) :
    ((thetaToDivisorApp K π n hηW p :
      divisorSections K (n • fiberWeilDivisor π) W) : Y.functionField) =
      thetaVal K π n hηW p :=
  rfl

/-- The section-wise map is injective: the value determines both component germs at `η`
(chart-0 through the definition, chart-1 through `thetaVal_eq_germ_snd`), and germs at `η`
determine sections on the integral `Y`. -/
lemma thetaToDivisorApp_injective {W : Y.Opens} (hηW : genericPoint Y ∈ W) :
    Function.Injective (thetaToDivisorApp K π n hηW) := by
  intro a b hab
  have hval : thetaVal K π n hηW a = thetaVal K π n hηW b := by
    have := congrArg
      (fun t : ↥(divisorSections K (n • fiberWeilDivisor π) W) => (t : Y.functionField)) hab
    rwa [thetaToDivisorApp_coe, thetaToDivisorApp_coe] at this
  refine Subtype.ext (Prod.ext ?_ ?_)
  · have ha : (((fiberCoordUnit π ^ n)⁻¹ : Y.functionFieldˣ) : Y.functionField) *
          (Y.presheaf.germ (W ⊓ fiberChart₀ π) (genericPoint Y)
            ⟨hηW, (genericPoint_mem_preimage_inf π).1⟩).hom a.val.1 =
        (((fiberCoordUnit π ^ n)⁻¹ : Y.functionFieldˣ) : Y.functionField) *
          (Y.presheaf.germ (W ⊓ fiberChart₀ π) (genericPoint Y)
            ⟨hηW, (genericPoint_mem_preimage_inf π).1⟩).hom b.val.1 := hval
    exact germ_injective_of_isIntegral Y (genericPoint Y)
      (show genericPoint Y ∈ W ⊓ fiberChart₀ π from
        ⟨hηW, (genericPoint_mem_preimage_inf π).1⟩)
      (mul_left_cancel₀ (Units.ne_zero ((fiberCoordUnit π ^ n)⁻¹)) ha)
  · have hgerm : (Y.presheaf.germ (W ⊓ fiberChart₁ π) (genericPoint Y)
        ⟨hηW, (genericPoint_mem_preimage_inf π).2⟩).hom a.val.2 =
      (Y.presheaf.germ (W ⊓ fiberChart₁ π) (genericPoint Y)
        ⟨hηW, (genericPoint_mem_preimage_inf π).2⟩).hom b.val.2 :=
      (thetaVal_eq_germ_snd K π n hηW a).symm.trans
        (hval.trans (thetaVal_eq_germ_snd K π n hηW b))
    exact germ_injective_of_isIntegral Y (genericPoint Y)
      (show genericPoint Y ∈ W ⊓ fiberChart₁ π from
        ⟨hηW, (genericPoint_mem_preimage_inf π).2⟩) hgerm

/-! ## The section-wise map is surjective -/

/-- On the chart `V₀` the pole bound of `n·F` coincides with that of `div(uⁿ)`. -/
private lemma divisorBound_nsmul_eq_divOf_pow {z : Y} (hz : z ≠ genericPoint Y)
    (hzV₀ : z ∈ fiberChart₀ π) :
    divisorBound (n • fiberWeilDivisor π) hz =
      divisorBound (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π ^ n)) hz := by
  rw [divisorBound_eq_coeffAt, divisorBound_eq_coeffAt, divOf_pow, coeffAt_nsmul,
    coeffAt_nsmul, fiberWeilDivisor_coeffAt_of_mem_chart₀ π hz hzV₀]

/-- **Chart-0 trivialization**: for `h ∈ 𝒪(n·F)(W)`, the product `uⁿ · h` is integral on
`W ⊓ V₀` — the pole of `h` is cancelled by the zero of `uⁿ` (the `mem_boundedSections_mul_iff`
mechanism, on `V₀` where `n·F = div(uⁿ)`). -/
lemma thetaElem_mul_mem_zero₀ {W : Y.Opens} (hηW : genericPoint Y ∈ W)
    {h : Y.functionField} (hh : h ∈ divisorSections K (n • fiberWeilDivisor π) W) :
    ((fiberCoordUnit π ^ n : Y.functionFieldˣ) : Y.functionField) * h ∈
      divisorSections K (0 : Y.CurveDivisor) (W ⊓ fiberChart₀ π) := by
  have hne : ((W ⊓ fiberChart₀ π : Y.Opens) : Set Y).Nonempty :=
    ⟨genericPoint Y, hηW, (genericPoint_mem_preimage_inf π).1⟩
  rw [divisorSections_of_nonempty K hne]
  have hmem : h ∈ boundedSections K
      (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π ^ n))
      (W ⊓ fiberChart₀ π) := by
    rw [mem_boundedSections]
    intro z hz hzWx
    rw [← divisorBound_nsmul_eq_divOf_pow K π n hz hzWx.2]
    exact (mem_divisorSections_of_nonempty K ⟨genericPoint Y, hηW⟩).mp hh z hz hzWx.1
  have hkey := (mem_boundedSections_mul_iff K (fiberCoordUnit π ^ n)
    (Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (fiberCoordUnit π ^ n)) h).mpr hmem
  rwa [sub_self] at hkey

/-- **Chart-1 trivialization**: `h ∈ 𝒪(n·F)(W)` is already integral on `W ⊓ V₁`, since the
fiber divisor vanishes there. -/
lemma thetaElem_mul_mem_zero₁ {W : Y.Opens} (hηW : genericPoint Y ∈ W)
    {h : Y.functionField} (hh : h ∈ divisorSections K (n • fiberWeilDivisor π) W) :
    h ∈ divisorSections K (0 : Y.CurveDivisor) (W ⊓ fiberChart₁ π) := by
  have hne : ((W ⊓ fiberChart₁ π : Y.Opens) : Set Y).Nonempty :=
    ⟨genericPoint Y, hηW, (genericPoint_mem_preimage_inf π).2⟩
  rw [mem_divisorSections_of_nonempty K hne]
  intro z hz hzWx
  rw [divisorBound_zero]
  have hb : divisorBound (n • fiberWeilDivisor π) hz = 1 := by
    rw [divisorBound_eq_coeffAt, coeffAt_nsmul,
      fiberWeilDivisor_coeffAt_of_mem_chart₁ π hz hzWx.2, smul_zero, ofAdd_zero, WithZero.coe_one]
  rw [← hb]
  exact (mem_divisorSections_of_nonempty K ⟨genericPoint Y, hηW⟩).mp hh z hz hzWx.1

/-- The section-wise map is surjective: a bounded rational function `h` is trivialized on
each chart (`uⁿ·h` on `V₀`, `h` on `V₁`, both integral, hence genuine sections by the
`𝒪(0) ≅ 𝒪_Y` engine), and the resulting pair matches through the cocycle `uⁿ`. -/
lemma thetaToDivisorApp_surjective {W : Y.Opens} (hηW : genericPoint Y ∈ W) :
    Function.Surjective (thetaToDivisorApp K π n hηW) := by
  intro t
  obtain ⟨s₀, hs₀⟩ := exists_section_germ_eq K
    (show genericPoint Y ∈ W ⊓ fiberChart₀ π from ⟨hηW, (genericPoint_mem_preimage_inf π).1⟩)
    (thetaElem_mul_mem_zero₀ K π n hηW t.property)
  obtain ⟨s₁, hs₁⟩ := exists_section_germ_eq K
    (show genericPoint Y ∈ W ⊓ fiberChart₁ π from ⟨hηW, (genericPoint_mem_preimage_inf π).2⟩)
    (thetaElem_mul_mem_zero₁ K π n hηW t.property)
  have hmatch : ((s₀, s₁) : Γ(Y, W ⊓ fiberChart₀ π) × Γ(Y, W ⊓ fiberChart₁ π)) ∈
      twistSubmodule K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) W := by
    rw [mem_twistSubmodule_iff]
    apply germ_injective_of_isIntegral Y (genericPoint Y)
      (show genericPoint Y ∈ W ⊓ fiberChart₀ π ⊓ fiberChart₁ π from
        ⟨⟨hηW, (genericPoint_mem_preimage_inf π).1⟩, (genericPoint_mem_preimage_inf π).2⟩)
    rw [map_mul, germ_resHom, germ_resHom, germ_resHom, germ_thetaUnit_pow_val K π n, hs₀, hs₁]
  refine ⟨⟨(s₀, s₁), hmatch⟩, ?_⟩
  apply Subtype.ext
  rw [thetaToDivisorApp_coe]
  change (((fiberCoordUnit π ^ n)⁻¹ : Y.functionFieldˣ) : Y.functionField) *
      (Y.presheaf.germ (W ⊓ fiberChart₀ π) (genericPoint Y)
        ⟨hηW, (genericPoint_mem_preimage_inf π).1⟩).hom s₀ = (t : Y.functionField)
  rw [hs₀, ← mul_assoc, Units.inv_mul, one_mul]

/-- The section-wise map is bijective on every nonempty open. -/
lemma thetaToDivisorApp_bijective {W : Y.Opens} (hηW : genericPoint Y ∈ W) :
    Function.Bijective (thetaToDivisorApp K π n hηW) :=
  ⟨thetaToDivisorApp_injective K π n hηW, thetaToDivisorApp_surjective K π n hηW⟩

omit [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] in
/-- Restriction does not move the value of a twisted section. -/
lemma thetaVal_res {W' W : Y.Opens} (h : W' ≤ W) (hηW' : genericPoint Y ∈ W')
    (p : ↥(twistSubmodule K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) W)) :
    thetaVal K π n hηW'
        (twistRes K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) h p) =
      thetaVal K π n (h hηW') p := by
  unfold thetaVal
  rw [twistRes_coe_fst, germ_resHom]

end Value

end AlgebraicGeometry
