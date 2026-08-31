/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZarFunctor
import AlgebraicJacobian.Picard.AbelElement
import AlgebraicJacobian.Picard.ThetaShift
import AlgebraicJacobian.Picard.DivisorFamilyFieldCRT

/-!
# DAT-C C5 — the Abel layer: `abelDiv`, the degree ledger, `sigmaFamily`, `chartValue`
(`informal/w4-datc-worksheet.md` §4 + §3.2 chart-value data)

The Abel transformation from the locally certified divisor functor into the étale
Picard functor, its degree ledger into the degree-`n` layer, and the Σ-shifted chart
values:

* `AlgebraicGeometry.DivFam.exists_toZar_eq` — **over a field, `toZar` is surjective**:
  a locally certified class collapses to a globally certified family (some member of
  the span-⊤ family is a unit; the away localization is `K` itself).
* `AlgebraicGeometry.DivFamZar.classDeg_picClass` — **the field-level degree law**:
  `classDeg K F₀.picClass = n` for every locally certified class of degree `n` over a
  field — E-i (`classDeg_picClass`) + the CRT degree identity (`deg_divFamDivisor`).
* `AlgebraicGeometry.abelDivPlus` / `abelDivAff` — the Abel transformation at an
  affine test: `F₀ ↦ unit (relPicMk 𝒪(F₀))`, natural in the test algebra
  (`abelDivPlus_mapAlgHom`).
* `AlgebraicGeometry.abelDiv` — **the Abel transformation at an arbitrary test**,
  componentwise over the affine opens; natural in the test object
  (`picEtMap_abelDiv`), collapsing on affine tests to the affine form
  (`picEtAffineEquiv_abelDiv`, `abelDiv_overSpec`).
* `AlgebraicGeometry.degAt_abelDiv` — **the degree ledger**: `degAt (abelDiv s) t = n`
  at every field point, so `abelDiv` factors through the degree-`n` layer:
  `abelDivTrans : divFunctor C π n ⟶ picDegLayerFunctor C n` (the sharpened dat-d
  Addendum row; no Type-valued `picEt` functor exists in-tree, so the ledgered
  natural transformation is stated directly into `picDegLayerFunctor` — recorded
  deviation from the worksheet's `picEtTypeFunctor` name).
* `AlgebraicGeometry.sigmaFamily` — the DAT-5 base-class pullback mechanism reused at
  `L₀ := 𝒪(Z)` for a divisor `Z` on the base-changed curve, with degree law
  `degAt_sigmaFamily` and naturality `sigmaFamily_natural`.
* `AlgebraicGeometry.chartValue` — the §3.2 chart value
  `abelDiv s · sigmaFamily Z · (θ_T^m)⁻¹`, natural in the test
  (`picEtMap_chartValue`), of degree `n + deg Z − m·d₁` (`degAt_chartValue`); under
  the chart-index degree constraint it lands in `pic0Subgroup`
  (`chartValue_mem_pic0Subgroup`).
-/

set_option autoImplicit false
/- Statements mix `relCurve C K` with the product spelling `(C ⊗ overSpec k K).left`;
see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}

noncomputable section

/-! ## The field collapse: `toZar` is surjective over a field -/

section Field

variable {K : Type u} [Field K] [Algebra k K]

/-- **Over a field, every locally certified class is globally certified**: some member
of the span-⊤ family is nonzero, hence a unit, so the corresponding away localization
is `K` itself and the local certified family transports back along the localization
isomorphism. -/
theorem DivFam.exists_toZar_eq (F₀ : DivFamZar C K π n) :
    ∃ G : DivFam C K π n, G.toZar = F₀ := by
  induction F₀ using Quotient.inductionOn with
  | h dp =>
    obtain ⟨m, g, hspan, hG⟩ := dp.2
    -- some member of the span-⊤ family is nonzero
    have hex : ∃ i, g i ≠ 0 := by
      by_contra hall
      have hall' : ∀ i, g i = 0 := fun i => by
        by_contra hi
        exact hall ⟨i, hi⟩
      have hle : Ideal.span (Set.range g) ≤ ⊥ := Ideal.span_le.mpr (by
        rintro x ⟨i, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_bot]
        exact hall' i)
      rw [hspan, top_le_iff] at hle
      exact one_ne_zero (Ideal.mem_bot.mp (hle ▸ Submodule.mem_top (x := (1 : K))))
    obtain ⟨i, hgi⟩ := hex
    haveI : IsOpenImmersion (relCurveMap C K (Localization.Away (g i))) :=
      isOpenImmersion_relCurveMap_away C K (Localization.Away (g i)) (g i)
    obtain ⟨Gᵢ, hGdiv⟩ := hG i
    -- the away localization at a unit is `K` itself
    have hunits : Submonoid.powers (g i) ≤ IsUnit.submonoid K := by
      rintro x ⟨e, rfl⟩
      exact (isUnit_iff_ne_zero.mpr hgi).pow e
    haveI : IsLocalization (Submonoid.powers (g i)) K :=
      IsLocalization.of_le_isUnit hunits
    let e₀ : K ≃ₐ[K] Localization.Away (g i) :=
      IsLocalization.atUnits K (Submonoid.powers (g i)) hunits
    let e : Localization.Away (g i) ≃ₐ[k] K := e₀.symm.restrictScalars k
    refine ⟨DivFam.mapAlgHom e.toAlgHom (DivFam.mk Gᵢ), ?_⟩
    -- the local family restricts the class
    have htoZar : (DivFam.mk Gᵢ).toZar
        = DivFamZar.mapAlg (Localization.Away (g i)) n (DivFamZar.mk dp.1 dp.2) := by
      rw [DivFam.toZar_mk, DivFamZar.mapAlg_mk]
      exact DivFamZar.mk_eq_mk_iff.mpr hGdiv
    -- transport back along the isomorphism
    have hcomp : e.toAlgHom.comp (IsScalarTower.toAlgHom k K (Localization.Away (g i)))
        = AlgHom.id k K := by
      ext a
      change e₀.symm (algebraMap K (Localization.Away (g i)) a) = a
      rw [← e₀.commutes a]
      exact e₀.symm_apply_apply _
    calc (DivFam.mapAlgHom e.toAlgHom (DivFam.mk Gᵢ)).toZar
        = DivFamZar.mapAlgHom e.toAlgHom (DivFam.mk Gᵢ).toZar :=
          DivFam.toZar_mapAlgHom e.toAlgHom (DivFam.mk Gᵢ)
      _ = DivFamZar.mapAlgHom e.toAlgHom
            (DivFamZar.mapAlgHom (IsScalarTower.toAlgHom k K (Localization.Away (g i)))
              (DivFamZar.mk dp.1 dp.2)) := by
          rw [htoZar, DivFamZar.mapAlgHom_eq_mapAlg
            (IsScalarTower.toAlgHom k K (Localization.Away (g i))) (fun _ => rfl)]
      _ = DivFamZar.mapAlgHom (AlgHom.id k K) (DivFamZar.mk dp.1 dp.2) := by
          rw [← DivFamZar.mapAlgHom_comp, hcomp]
      _ = ⟦dp⟧ := DivFamZar.mapAlgHom_id _

/-- **The field-level degree law of the Abel ledger** (worksheet §4.2, bottom rows):
the Čech Picard class of a locally certified divisor class of degree `n` over a field
has `classDeg = n` — E-i (`classDeg_picClass`) composed with the CRT degree identity
(`deg_divFamDivisor`) on a globally certified representative. -/
theorem DivFamZar.classDeg_picClass
    [IsIntegral (relCurve C K)]
    [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]
    (F₀ : DivFamZar C K π n) :
    classDeg K F₀.picClass = (n : ℤ) := by
  obtain ⟨G, rfl⟩ := DivFam.exists_toZar_eq F₀
  rw [DivFamZar.picClass_toZar]
  induction G using Quotient.inductionOn with
  | h F =>
    calc classDeg K (DivFam.picClass (DivFam.mk F))
        = classDeg K F.eqns.presentation.picClass := by
          rw [DivFam.picClass_mk, Scheme.LocalEquations.presentation_picClass]
      _ = classDeg K (Scheme.CurveDivisor.picClass K
            (Scheme.presentationDivisor K F.eqns.presentation)) := by
          rw [Scheme.CurveDivisor.picClass_presentationDivisor]
      _ = Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K F.eqns.presentation) :=
          _root_.AlgebraicGeometry.classDeg_picClass K _
      _ = (n : ℤ) := by
          rw [show Scheme.presentationDivisor K F.eqns.presentation
              = divFamDivisor (DivFam.mk F) from (divFamDivisor_mk F).symm]
          exact deg_divFamDivisor (DivFam.mk F)

end Field

/-! ## The Abel transformation at an affine test -/

section AbelAff

variable (C π) in
/-- The Abel transformation at an affine test, plus-construction form: the étale-unit
image of the relative Picard class of `𝒪(F₀)`. -/
def abelDivPlus (A : Type u) [CommRing A] [Algebra k A] (F₀ : DivFamZar C A π n) :
    PicEtAff C A :=
  PicEtAff.unit C A (relPicMk C (overSpec k A) F₀.picClass)

variable (C π) in
/-- **The Abel transformation at an affine test** (worksheet §4.1): the `picEt`-valued
form, through the unit of the étale sheafification. -/
def abelDivAff (A : Type u) [CommRing A] [Algebra k A] (F₀ : DivFamZar C A π n) :
    picEt C (overSpec k A) :=
  relPicToPicEt C (overSpec k A) (relPicMk C (overSpec k A) F₀.picClass)

/-- The affine collapse of the `picEt`-valued Abel value is the plus-construction
form. -/
theorem picEtAffineEquiv_abelDivAff (A : Type u) [CommRing A] [Algebra k A]
    (F₀ : DivFamZar C A π n) :
    picEtAffineEquiv C A (abelDivAff C π A F₀) = abelDivPlus C π A F₀ :=
  picEtAffineEquiv_relPicToPicEt C A _

/-- **Naturality of the affine Abel transformation in the test algebra** (worksheet
§4.1: `picClass_mapAlg` + `PicEtAff.mapAlg_unit`): base change of the Abel value is
the Abel value of the base-changed class. -/
theorem abelDivPlus_mapAlgHom {A B : Type u} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (φ : A →ₐ[k] B) (F₀ : DivFamZar C A π n) :
    PicEtAff.mapAlg C φ (abelDivPlus C π A F₀)
      = abelDivPlus C π B (DivFamZar.mapAlgHom φ F₀) := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A B := .of_algebraMap_eq fun a => (φ.commutes a).symm
  have hclass : (DivFamZar.mapAlgHom φ F₀).picClass
      = Scheme.CechPic.map (C ◁ Over.overSpecMap φ).left F₀.picClass := by
    have hcurve : relCurveMap C A B = (C ◁ Over.overSpecMap φ).left := by
      refine congrArg (fun ψ : overSpec k B ⟶ overSpec k A => (C ◁ ψ).left) ?_
      exact Over.OverMorphism.ext rfl
    rw [← hcurve]
    exact DivFamZar.picClass_mapAlg B n F₀
  calc PicEtAff.mapAlg C φ (abelDivPlus C π A F₀)
      = PicEtAff.unit C B (relPicAlgMap C φ
          (relPicMk C (overSpec k A) F₀.picClass)) := PicEtAff.mapAlg_unit C φ _
    _ = PicEtAff.unit C B (relPicMk C (overSpec k B)
          (Scheme.CechPic.map (C ◁ Over.overSpecMap φ).left F₀.picClass)) :=
        congrArg (PicEtAff.unit C B)
          (relPicMap_mk C (Over.overSpecMap φ) F₀.picClass)
    _ = abelDivPlus C π B (DivFamZar.mapAlgHom φ F₀) := by
        rw [abelDivPlus, hclass]

end AbelAff

/-! ## The Abel transformation at an arbitrary test -/

section AbelVehicle

variable (C π n) in
/-- **The Abel transformation at an arbitrary test object** (worksheet §4.1, the
vehicle lift): componentwise over the affine opens, compatible by the affine
naturality. -/
def abelDiv (T : Over (Spec (.of k))) (s : divFamZar C π n T) : picEt C T :=
  ⟨fun U => abelDivPlus C π Γ(T.left, U.1) (s.1 U), fun U V h => by
    rw [abelDivPlus_mapAlgHom (Over.resAlgHom T h) (s.1 V), s.compat U V h]⟩

@[simp]
lemma abelDiv_val (T : Over (Spec (.of k))) (s : divFamZar C π n T)
    (U : T.left.affineOpens) :
    (abelDiv C π n T s).1 U = abelDivPlus C π Γ(T.left, U.1) (s.1 U) :=
  rfl

/-- The affine collapse of the vehicle-level Abel transformation: definitionally the
affine naturality law at the `ΓSpecIso` identification. -/
theorem picEtAffineEquiv_abelDiv (A : Type u) [CommRing A] [Algebra k A]
    (s : divFamZar C π n (overSpec k A)) :
    picEtAffineEquiv C A (abelDiv C π n (overSpec k A) s)
      = abelDivPlus C π A (divFamZarAffineEquiv C π n A s) :=
  abelDivPlus_mapAlgHom (Over.overSpecΓTopAlgEquiv k A).toAlgHom
    (s.1 (overSpecTopAffine A))

/-- On an affine test the vehicle-level Abel transformation is the affine one, through
the comparison equivalences. -/
theorem abelDiv_overSpec (A : Type u) [CommRing A] [Algebra k A]
    (s : divFamZar C π n (overSpec k A)) :
    abelDiv C π n (overSpec k A) s
      = abelDivAff C π A (divFamZarAffineEquiv C π n A s) :=
  (picEtAffineEquiv C A).injective
    ((picEtAffineEquiv_abelDiv A s).trans
      (picEtAffineEquiv_abelDivAff A (divFamZarAffineEquiv C π n A s)).symm)

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- **Naturality of the Abel transformation in the test object**: restriction of the
Abel value along an arbitrary test morphism is the Abel value of the restricted
family — through the `∃!`-characterizations of both glued restrictions. -/
theorem picEtMap_abelDiv {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (s : divFamZar C π n T) :
    picEtMap C f (abelDiv C π n T s) = abelDiv C π n T' (divFamZar.map C π n f s) := by
  refine picEt.ext fun W => ?_
  rw [picEtMap_val]
  refine picEtMapVal_eq_of C f (abelDiv C π n T s) ?_
  intro W₀ hW₀ V hV
  rw [abelDiv_val, abelDiv_val, divFamZar.map_val,
    abelDivPlus_mapAlgHom (Over.resAlgHom T' hW₀) (divFamZar.mapVal C π n f s W),
    abelDivPlus_mapAlgHom (Over.appLEAlgHom f V.1 W₀.1 hV) (s.1 V),
    divFamZar.mapVal_spec C π n f s W W₀ hW₀ V hV]

/-! ## The degree ledger -/

/-- **The degree ledger** (worksheet §4.2): the Abel value of a degree-`n` family has
degree `n` at every field point — naturality reduces to the affine collapse at the
field, `degAff_unit` + `relPicDeg_relPicMk` read the class degree, and the field-level
degree law finishes. -/
theorem degAt_abelDiv {T : Over (Spec (.of k))} (s : divFamZar C π n T) {K : Type u}
    [Field K] [Algebra k K] (t : overSpec k K ⟶ T) :
    degAt (abelDiv C π n T s) t = (n : ℤ) := by
  haveI : IsIntegral (relCurve C K) := instIsIntegralBaseChange C K
  haveI : SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    instSmoothOfRelativeDimensionBaseChange C K
  haveI : QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    instQuasiCompactBaseChange C K
  haveI : Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
    instModuleFiniteHModuleZeroBaseChange C K
  haveI : Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
    instModuleFiniteHModuleOneBaseChange C K
  change PicEtAff.degAff K (picEtAffineEquiv C K
      (picEtMap C t (abelDiv C π n T s))) = (n : ℤ)
  rw [picEtMap_abelDiv, picEtAffineEquiv_abelDiv]
  change PicEtAff.degAff K (PicEtAff.unit C K (relPicMk C (overSpec k K)
      (divFamZarAffineEquiv C π n K (divFamZar.map C π n t s)).picClass)) = (n : ℤ)
  rw [PicEtAff.degAff_unit, relPicDeg_relPicMk]
  exact DivFamZar.classDeg_picClass _

variable (C π n) in
/-- **The Abel natural transformation into the degree-`n` layer** (the sharpened
dat-d Addendum row, worksheet §4.2): the Abel transformation, ledgered by
`degAt_abelDiv`, as a natural transformation
`divFunctor C π n ⟶ picDegLayerFunctor C n`. -/
def abelDivTrans : divFunctor C π n ⟶ picDegLayerFunctor C (n : ℤ) where
  app T := ↾fun s => ⟨abelDiv C π n T.unop s, fun K _ _ t => degAt_abelDiv s t⟩
  naturality T T' g := by
    ext s
    refine Subtype.ext ?_
    exact (picEtMap_abelDiv g.unop s).symm

@[simp]
lemma abelDivTrans_app_coe (T : (Over (Spec (.of k)))ᵒᵖ) (s : divFamZar C π n T.unop) :
    ((abelDivTrans C π n).app T s).1 = abelDiv C π n T.unop s :=
  rfl

end AbelVehicle

/-! ## The Σ-family and the chart value -/

section Sigma

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

variable (C) in
/-- **The Σ-family** (worksheet §3.2): the DAT-5 base-class pullback mechanism reused
at the class `𝒪(Z)` of a Weil divisor `Z` on the base-changed curve `C_k`. -/
def sigmaFamily (Z : (C ⊗ overSpec k k).left.CurveDivisor) (T : Over (Spec (.of k))) :
    picEt C T :=
  thetaFamily C (Scheme.CurveDivisor.picClass k Z) T

variable (C) in
/-- Naturality of the Σ-family: it pulls back to itself under every test map. -/
theorem sigmaFamily_natural (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) :
    picEtMap C f (sigmaFamily C Z T) = sigmaFamily C Z T' :=
  thetaFamily_natural C _ f

variable (C) in
/-- **The degree of the Σ-family at every field point is `deg k Z`** (E-iv-alg under
the DAT-5 degree law + E-i). -/
theorem degAt_sigmaFamily (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {T : Over (Spec (.of k))} {K : Type u} [Field K] [Algebra k K]
    (t : overSpec k K ⟶ T) :
    degAt (sigmaFamily C Z T) t = Scheme.CurveDivisor.deg k Z := by
  change degAt (thetaFamily C (Scheme.CurveDivisor.picClass k Z) T) t = _
  rw [degAt_thetaFamily, classDeg_picClass]

variable (C π n) in
/-- **The chart value** (worksheet §3.2): the Abel value shifted by the Σ-family and
`m` inverse powers of the pinned θ-family,
`abelDiv s · sigmaFamily Z · (θ_T^m)⁻¹`. -/
def chartValue (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (s : divFamZar C π n T) : picEt C T :=
  abelDiv C π n T s * sigmaFamily C Z T
    * (thetaFamily C (thetaCechClass C) T ^ m)⁻¹

variable (C π n) in
/-- Naturality of the chart value in the test object. -/
theorem picEtMap_chartValue (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (s : divFamZar C π n T) :
    picEtMap C f (chartValue C π n m Z T s)
      = chartValue C π n m Z T' (divFamZar.map C π n f s) := by
  rw [chartValue, chartValue, map_mul, map_mul, map_inv, map_pow, picEtMap_abelDiv,
    sigmaFamily_natural, thetaFamily_natural]

variable (C π n) in
/-- **The degree of the chart value at every field point**:
`n + deg k Z − m·d₁` — the §4.2 ledger summed across the three factors. -/
theorem degAt_chartValue (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {T : Over (Spec (.of k))} (s : divFamZar C π n T) {K : Type u} [Field K]
    [Algebra k K] (t : overSpec k K ⟶ T) :
    degAt (chartValue C π n m Z T s) t
      = (n : ℤ) + Scheme.CurveDivisor.deg k Z
        - (m : ℤ) * classDeg k (thetaCechClass C) := by
  rw [chartValue, degAt_mul, degAt_mul, degAt_inv, degAt_thetaFamily_pow,
    degAt_abelDiv, degAt_sigmaFamily]
  ring

variable (C π n) in
/-- **The chart value lands in `pic0`** (worksheet §3.2/§4.2, the chart-index degree
ledger): under the chart-index constraint `deg k Z = m·d₁ − n` the three degrees sum
to zero at every field point. -/
theorem chartValue_mem_pic0Subgroup (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (T : Over (Spec (.of k))) (s : divFamZar C π n T) :
    chartValue C π n m Z T s ∈ pic0Subgroup C T := by
  rw [mem_pic0Subgroup_iff]
  intro K _ _ t
  rw [degAt_chartValue, hdeg]
  ring

end Sigma

end

end AlgebraicGeometry
