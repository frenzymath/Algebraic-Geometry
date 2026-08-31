/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RelCurveCollapse
import AlgebraicJacobian.Cohomology.GluedSheafH0BaseChange
import AlgebraicJacobian.Cohomology.GluedSheafDatumFibre
import AlgebraicJacobian.RiemannRoch.DegreeBaseFieldInvariance
import AlgebraicJacobian.RiemannRoch.WindowLedgerF3
import AlgebraicJacobian.Picard.DivisorFamilyWindow

/-!
# The base-field window transport pack — DDR-2's `N`-pack (DAT-D `dd4`/`ddr`)

The abstract fibre window divisor `N` of DDR-2's certified-degree pinch
(`RiemannRoch/CarveDegree.lean`), built for any field extension `K/k`: an honest Weil
divisor on `relCurve C K` carrying the **transported** DD-0 window facts of the `k`-level
embedding window `M·F`.  Per I-0204's binding architectural finding, the per-field ledger
constants do *not* transport (`windowM_choice` is a per-field `Classical.choose`), so `N`
is produced by transporting window **facts**, not by re-running the `K`-level ledger:

* the `k`-level `H¹` inputs enter through the landed twist-pair collapse
  (`relThetaPairH1_windowM`, `subsingleton_relThetaPairH1`) and cross into the datum
  world by the whole-chart theta datum (`Cohomology/RelCurveCollapse.lean`);
* the datum base-changes to `K` (`datum_subsingleton_h1_baseChange`), where the
  presentation bridge (`presentationSheafIso` + `subsingleton_hModule_gluedSheaf_one_iff`)
  extracts an honest divisor `windowTransportDivisor C K π a` with vanishing `H¹`;
* its class is the transported theta class (`cechPicClass_baseChange` + the collapse
  class law), so its degree is `a·δ` by E-iv-alg
  (`classDeg_cechPicMap_baseFieldTransition`) and W7-B3 (`classDeg_cechPicMap_of_isIso`);
* the `K`-level normalization windows come from the π-free peeling
  (`subsingleton_hModule_one_of_witness`, the abstract-witness form of DAT-0a's
  `exists_bound_subsingleton_hModule_one_of_isFinite_toP1`) at the transported
  multiplier window `s·F`, licensed by ledger arithmetic.

## The `N`-pack (DDR-2's threaded hypotheses, exact spellings)

At `N := windowN C K π hπ g = windowTransportDivisor C K π (windowM_choice π hπ g)`:

* `hNwin` — `subsingleton_h1_windowN` : `Subsingleton H¹(𝒪(N))`;
* `hNdeg` — `two_mul_genus_le_deg_windowN` : `2g ≤ deg K N`;
* `hNnorm` — `subsingleton_h1_windowN_sub` : `∀ D', deg D' ≤ 2g → Subsingleton
  H¹(𝒪(N − D'))`;
* `hNrank` — `h0_windowN` : `h⁰_K(𝒪(N)) = h⁰_k(𝒪(M·F))`.

The remaining threaded hypothesis of `deg_divFamDivisor_of_carve` supplied elsewhere is
`hdict` (the sections dictionary at the field point, DD-4 Task 5 field content — still
open), besides the sibling seams `hsurj`/`hpair`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule
attribute [local instance 10000] relCurve.instOver

open Scheme

/-! ## The π-free peeling: uniform `H¹`-vanishing from an abstract witness -/

section Peeling

variable (K : Type u) [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]

omit [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] in
/-- **The π-free peeling** (the abstract-witness form of DAT-0a): a single witness
divisor `W₀` with vanishing `H¹` makes `H¹(𝒪(D))` vanish for **every** divisor `D` of
degree `≥ deg W₀ + 1 − χ(𝒪_Y)` — the residual class `[D]·[W₀]⁻¹` has an effective
representative (`exists_effective_of_picClass`), peeling (`peel_effective`) transports
the vanishing to `W₀ + E`, and witness-independence
(`subsingleton_hModule_one_of_picClass_eq`) reaches `D`. -/
theorem subsingleton_hModule_one_of_witness (W₀ D : Y.CurveDivisor)
    (hW₀ : Subsingleton (Sheaf.HModule (Y.divisorSheaf K W₀) 1))
    (hdeg : CurveDivisor.deg K W₀ + 1 - Sheaf.chi (Y.moduleKSheaf K)
      ≤ CurveDivisor.deg K D) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K D) 1) := by
  set c : Y.CechPic :=
    CurveDivisor.picClass K D * (CurveDivisor.picClass K W₀)⁻¹ with hc
  obtain ⟨Wc, hWc⟩ := CurveDivisor.exists_picClass_eq K c
  have hWcdeg : CurveDivisor.deg K Wc
      = CurveDivisor.deg K D - CurveDivisor.deg K W₀ := by
    rw [← classDeg_picClass K Wc, hWc, hc, classDeg_mul, classDeg_inv,
      classDeg_picClass, classDeg_picClass]
    ring
  have hWdeg : 1 ≤ CurveDivisor.deg K Wc + Sheaf.chi (Y.moduleKSheaf K) := by
    rw [hWcdeg]; linarith
  obtain ⟨E, hE0, hEc⟩ := exists_effective_of_picClass Wc hWdeg
  have hclass : CurveDivisor.picClass K (W₀ + E) = CurveDivisor.picClass K D := by
    rw [CurveDivisor.picClass_add, hEc, hWc, hc,
      mul_comm (CurveDivisor.picClass K D), ← mul_assoc, mul_inv_cancel, one_mul]
  exact subsingleton_hModule_one_of_picClass_eq K hclass
    (peel_effective W₀ E hE0 hW₀)

end Peeling

/-! ## The transported window divisor at a field extension -/

section Transport

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
variable (a : ℕ)

/-- **The transported theta datum**: the whole-chart theta datum of the base field,
base-changed to `K`. -/
noncomputable def windowTransportDatum : BasicOpenCocycleDatum C K π :=
  (thetaChartDatum C k π a).baseChange K

/-- **The `K`-fibre presentation of the transported theta class**: the meromorphic
presentation of the subordinated cocycle of the transported datum on its canonical
pointed cover (the target of `presentationSheafIso`). -/
noncomputable def windowTransportPresentation : (relCurve C K).MeromorphicPresentation :=
  Scheme.MeromorphicPresentation.ofCocycle (windowTransportDatum C K π a).pointedCover
    (gluedSubordCocycle (windowTransportDatum C K π a).isGluingCocycle
      (windowTransportDatum C K π a).pointedCover
      (windowTransportDatum C K π a).pieceIndex fun _ => le_rfl)

/-- **The transported window divisor** `N(a)` on the `K`-fibre: the presentation divisor
of the transported theta presentation — an honest Weil divisor in the transported class
`Θᵃ`. -/
noncomputable def windowTransportDivisor : (relCurve C K).CurveDivisor :=
  Scheme.presentationDivisor K (windowTransportPresentation C K π a)

/-- **`H¹` of the transported window divisor vanishes** whenever the `k`-level theta
pair `H¹` does (the ledger input, e.g. `relThetaPairH1_windowM`): the `H¹` seam of the
collapse brick pushed through the datum base change and the presentation bridge. -/
theorem subsingleton_h1_windowTransportDivisor
    (h : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    Subsingleton (Sheaf.HModule
      ((relCurve C K).divisorSheaf K (windowTransportDivisor C K π a)) 1) := by
  have h1 : Subsingleton (datumPair (thetaChartDatum C k π a)).H1 :=
    subsingleton_datumPair_h1_thetaChartDatum C π a h
  have h2 : Subsingleton (Sheaf.HModule (windowTransportDatum C K π a).sheaf 1) :=
    BasicOpenCocycleDatum.datum_subsingleton_h1_baseChange K (thetaChartDatum C k π a) h1
  have h3 : Subsingleton (Sheaf.HModule
      ((windowTransportPresentation C K π a).gluedSheaf K) 1) :=
    (Sheaf.HModule.mapEquiv
      (BasicOpenCocycleDatum.presentationSheafIso (windowTransportDatum C K π a))
      1).toEquiv.subsingleton_congr.mp h2
  exact (subsingleton_hModule_gluedSheaf_one_iff K _).mp h3

/-- The transported window divisor lies in the transported datum class. -/
theorem picClass_windowTransportDivisor :
    CurveDivisor.picClass K (windowTransportDivisor C K π a)
      = (windowTransportDatum C K π a).cechPicClass := by
  rw [windowTransportDivisor, CurveDivisor.picClass_presentationDivisor]
  rfl

end Transport

/-! ## The degree of the transported window divisor -/

section Degree

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π] [IsDominant π]
variable [IsIntegral C.left]

noncomputable local instance instOverCleftDeg : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]
variable (a : ℕ)

set_option linter.unusedSectionVars false in
/-- The relative-curve comparison at the base-field transition `k → K` is the E-iv-alg
transition morphism. -/
lemma relCurveMap_eq_overSpecMap_ofId :
    relCurveMap C k K = (C ◁ Over.overSpecMap (Algebra.ofId k K)).left := by
  refine congrArg (fun φ : C ⊗ overSpec k K ⟶ C ⊗ overSpec k k => φ.left)
    (congrArg (fun ψ : overSpec k K ⟶ overSpec k k => C ◁ ψ) ?_)
  exact Over.OverMorphism.ext rfl

set_option linter.unusedSectionVars false in
/-- The structure morphism of the self test `overSpec k k` is the identity. -/
lemma overSpec_self_hom : (overSpec k k).hom = 𝟙 (Spec (CommRingCat.of k)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

set_option linter.unusedSectionVars false in
/-- The base-field collapse is a morphism of curve bundles over `Spec k`: composing with
the structure morphism of `C.left` gives the structure morphism of the relative curve. -/
lemma fst_left_self_over :
    letI : C.left.Over (Spec (.of k)) := ⟨C.hom⟩
    (fst C (overSpec k k)).left ≫ (C.left ↘ Spec (CommRingCat.of k))
      = relCurve C k ↘ Spec (CommRingCat.of k) := by
  letI : C.left.Over (Spec (.of k)) := ⟨C.hom⟩
  change (fst C (overSpec k k)).left ≫ C.hom = (snd C (overSpec k k)).left
  rw [Over.w (fst C (overSpec k k)), ← Over.w (snd C (overSpec k k)),
    overSpec_self_hom (k := k)]
  exact Category.comp_id _

set_option maxSynthPendingDepth 8 in
set_option synthInstance.maxHeartbeats 800000 in
-- (The two-field instance towers of the degree stack at `k` and `K` exceed the default
-- synthesis limits; the I-0198 escape hatch.)
/-- **The degree of the transported window divisor is `a·δ`**: E-i reads the degree off
the class, `cechPicClass_baseChange` and E-iv-alg carry it to the base field, the
collapse class law identifies it with the pulled fiber twist, and W7-B3 computes it as
`a · classDeg (Θ¹) = a · δ`. -/
theorem deg_windowTransportDivisor :
    CurveDivisor.deg K (windowTransportDivisor C K π a) = (a : ℤ) * windowδ π := by
  haveI : IsIntegral (relCurve C k) := instIsIntegralBaseChange C k
  haveI : SmoothOfRelativeDimension 1 (relCurve C k ↘ Spec (CommRingCat.of k)) :=
    instSmoothOfRelativeDimensionBaseChange C k
  haveI : QuasiCompact (relCurve C k ↘ Spec (CommRingCat.of k)) :=
    instQuasiCompactBaseChange C k
  haveI : Module.Finite k (Sheaf.HModule ((relCurve C k).moduleKSheaf k) 0) :=
    instModuleFiniteHModuleZeroBaseChange C k
  haveI : Module.Finite k (Sheaf.HModule ((relCurve C k).moduleKSheaf k) 1) :=
    instModuleFiniteHModuleOneBaseChange C k
  haveI : SmoothOfRelativeDimension 1
      ((C ⊗ overSpec k k).left ↘ Spec (CommRingCat.of k)) :=
    instSmoothOfRelativeDimensionBaseChange C k
  haveI : QuasiCompact ((C ⊗ overSpec k k).left ↘ Spec (CommRingCat.of k)) :=
    instQuasiCompactBaseChange C k
  have hbc : (windowTransportDatum C K π a).cechPicClass
      = Scheme.CechPic.map (relCurveMap C k K)
          (thetaChartDatum C k π a).cechPicClass :=
    BasicOpenCocycleDatum.cechPicClass_baseChange K (thetaChartDatum C k π a)
  -- E-iv-alg at the transition `k → K`, bridged across the `relCurveMap` spelling
  have htr : classDeg K (Scheme.CechPic.map (relCurveMap C k K)
        (thetaChartDatum C k π a).cechPicClass)
      = classDeg k (thetaChartDatum C k π a).cechPicClass := by
    rw [relCurveMap_eq_overSpecMap_ofId C K]
    exact classDeg_cechPicMap_baseFieldTransition C (Algebra.ofId k K) _
  -- the collapse class law and W7-B3 at the base field
  have hcol : classDeg k (Scheme.CechPic.map (fst C (overSpec k k)).left
        (fiberTwist π a))
      = (a : ℤ) * windowδ π := by
    have h := classDeg_cechPicMap_of_isIso k (fst C (overSpec k k)).left
      (fst_left_self_over C) (fiberTwist π a)
    rw [h, fiberTwist_pow, classDeg_pow]
    rfl
  rw [← classDeg_picClass K (windowTransportDivisor C K π a),
    picClass_windowTransportDivisor, hbc, htr, cechPicClass_thetaChartDatum C π a]
  exact hcol

end Degree

/-! ## The `N`-pack: DDR-2's transported window facts -/

section Pack

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable (K : Type u) [Field K] [Algebra k K]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
variable [IsIntegral C.left]

noncomputable local instance instOverCleftWFT : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]
variable [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]

set_option linter.unusedSectionVars false in
/-- **The `H¹` input at the multiplier window `s`** (`window_embedding_mult`, DAT-0a),
transported onto the relative theta pair — the `s`-companion of
`relThetaPairH1_windowM`. -/
theorem relThetaPairH1_windowS (g : ℕ) :
    Subsingleton
      (relTwistPair C k π (relThetaCocycle C k π (windowS_choice π hπ g))).H1 :=
  subsingleton_relThetaPairH1 C π _
    ((subsingleton_hModule_thetaTwistSheaf_one_iff k π _).mpr
      (window_embedding_mult π hπ g))

/-- **The abstract fibre window divisor `N`** of DDR-2's pinch: the transported window
divisor at the `k`-ledger embedding exponent `M = windowM_choice π hπ g`. -/
noncomputable def windowN (g : ℕ) : (relCurve C K).CurveDivisor :=
  windowTransportDivisor C K π (windowM_choice π hπ g)

set_option linter.unusedSectionVars false in
/-- **`hNwin`**: `H¹(𝒪(N)) = 0` — the transported embedding window
(`window_embedding` at `k`, pushed across the collapse and the base change). -/
theorem subsingleton_h1_windowN (g : ℕ) :
    Subsingleton (Sheaf.HModule
      ((relCurve C K).divisorSheaf K (windowN C K hπ g)) 1) :=
  subsingleton_h1_windowTransportDivisor C K π _ (relThetaPairH1_windowM C π hπ g)

/-- The degree of `N` is the `k`-ledger embedding degree `M·δ`. -/
theorem deg_windowN (g : ℕ) :
    CurveDivisor.deg K (windowN C K hπ g)
      = (windowM_choice π hπ g : ℤ) * windowδ π :=
  deg_windowTransportDivisor C K π _

/-- **`hNdeg`**: `2g ≤ deg K N` — the transported embedding budget
(`two_mul_genus_le_M_mul_windowδ`). -/
theorem two_mul_genus_le_deg_windowN (g : ℕ)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    2 * (g : ℤ) ≤ CurveDivisor.deg K (windowN C K hπ g) := by
  rw [deg_windowN]
  exact two_mul_genus_le_M_mul_windowδ π hπ g hO hχ

/-- **The degree-keyed embedding budget**: the transported `N`-window has degree at
least twice the divisor-family degree.  Unlike the diagonal genus spelling above, this
uses only the positively normalized ledger bound. -/
theorem two_mul_degree_le_deg_windowN (g : ℕ) :
    2 * (g : ℤ) ≤ CurveDivisor.deg K (windowN C K hπ g) := by
  rw [deg_windowN]
  exact two_mul_degree_le_M_mul_windowδ π hπ g

/-- **`hNrank`**: the window-size transport `h⁰_K(𝒪(N)) = h⁰_k(𝒪(M·F))` — both sides
are computed by the rank anchor at their own field (`deg + χ`), the degree is the
transported `M·δ`, and `χ` matches through the genus normalizations. -/
theorem h0_windowN (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ)) :
    Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hπ g))
      = Sheaf.h0 (C.left.divisorSheaf k
          (windowM_choice π hπ g • fiberWeilDivisor π)) := by
  have hK : (Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hπ g)) : ℤ)
      = CurveDivisor.deg K (windowN C K hπ g)
        + Sheaf.chi ((relCurve C K).moduleKSheaf K) :=
    h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (subsingleton_h1_windowN C K hπ g)
  have hk : (Sheaf.h0 (C.left.divisorSheaf k
        (windowM_choice π hπ g • fiberWeilDivisor π)) : ℤ)
      = (windowM_choice π hπ g : ℤ) * windowδ π + 1 - (g : ℤ) :=
    rank_embedding_of_genus π hπ g hχ
  have hdeg := deg_windowN C K hπ g
  have hcast : (Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hπ g)) : ℤ)
      = (Sheaf.h0 (C.left.divisorSheaf k
          (windowM_choice π hπ g • fiberWeilDivisor π)) : ℤ) := by
    rw [hK, hdeg, hχK, hk]
    ring
  exact_mod_cast hcast

/-- **The decoupled window-size transport**: the window exponent is keyed by the
divisor degree `g`, while both Euler-characteristic formulas use the independent curve
parameter `gamma`. -/
theorem h0_windowN_at (g : ℕ) {gamma : ℕ}
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (gamma : ℤ)) :
    Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hπ g))
      = Sheaf.h0 (C.left.divisorSheaf k
          (windowM_choice π hπ g • fiberWeilDivisor π)) := by
  have hK : (Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hπ g)) : ℤ)
      = CurveDivisor.deg K (windowN C K hπ g)
        + Sheaf.chi ((relCurve C K).moduleKSheaf K) :=
    h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (subsingleton_h1_windowN C K hπ g)
  have hk := rank_embedding π hπ g
  rw [hχ] at hk
  have hdeg := deg_windowN C K hπ g
  have hcast : (Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hπ g)) : ℤ)
      = (Sheaf.h0 (C.left.divisorSheaf k
          (windowM_choice π hπ g • fiberWeilDivisor π)) : ℤ) := by
    rw [hK, hdeg, hχK, hk]
  exact_mod_cast hcast

/-- **`hNnorm`**: the transported normalization windows — for every `K`-divisor `D'` of
degree `≤ 2g`, `H¹(𝒪(N − D')) = 0`.  The π-free peeling at the transported multiplier
window `s·F` (or at `N` itself in the degenerate `windowBound ≤ 0` branch, where
`g = 0`), licensed by the ledger budgets. -/
theorem subsingleton_h1_windowN_sub (g : ℕ)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ))
    (D' : (relCurve C K).CurveDivisor)
    (hD' : CurveDivisor.deg K D' ≤ 2 * (g : ℤ)) :
    Subsingleton (Sheaf.HModule
      ((relCurve C K).divisorSheaf K (windowN C K hπ g - D')) 1) := by
  have hsub : CurveDivisor.deg K (windowN C K hπ g - D')
      = CurveDivisor.deg K (windowN C K hπ g) - CurveDivisor.deg K D' := by
    rw [sub_eq_add_neg, CurveDivisor.deg_add, CurveDivisor.deg_neg, sub_eq_add_neg]
  by_cases hb : windowBound π hπ ≤ 0
  · -- degenerate branch: `g = 0`, peel from `N` itself
    have hg0 : g = 0 := genus_eq_zero_of_windowBound_nonpos π hπ g hb hO hχ
    refine subsingleton_hModule_one_of_witness K (windowN C K hπ g) _
      (subsingleton_h1_windowN C K hπ g) ?_
    rw [hsub, hχK, hg0]
    simp only [Nat.cast_zero] at hD' ⊢
    linarith
  · -- main branch: peel from the transported multiplier window `s·F`
    refine subsingleton_hModule_one_of_witness K
      (windowTransportDivisor C K π (windowS_choice π hπ g)) _
      (subsingleton_h1_windowTransportDivisor C K π _ (relThetaPairH1_windowS C hπ g))
      ?_
    rw [hsub, hχK, deg_windowN, deg_windowTransportDivisor]
    have hb1 : 0 < windowBound π hπ := not_le.mp hb
    have hM := windowM_spec π hπ g
    have hδ := one_le_windowδ π
    have hs : (0 : ℤ) ≤ (windowS_choice π hπ g : ℤ) := Int.natCast_nonneg _
    have hg : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg _
    have hkey : (windowS_choice π hπ g : ℤ) * windowδ π + ((g : ℤ) + 2)
        ≤ ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) * windowδ π := by
      nlinarith [hs, hg, hδ, mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ (g:ℤ) + 1) hs)
        (by linarith : (0:ℤ) ≤ windowδ π)]
    linarith [hM, hkey, hb1, hD']

/-- **The decoupled transported normalization family**: for a degree-`g` divisor
family, every subtraction of degree at most `2g` from the `N(g)` window has vanishing
`H¹`.  The curve normalization may use any Euler parameter `gamma`; it cancels from
the witness comparison. -/
theorem subsingleton_h1_windowN_sub_at (g : ℕ) {gamma : ℕ}
    (hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (gamma : ℤ))
    (D' : (relCurve C K).CurveDivisor)
    (hD' : CurveDivisor.deg K D' ≤ 2 * (g : ℤ))
    (hgamma : gamma ≤ g) :
    Subsingleton (Sheaf.HModule
      ((relCurve C K).divisorSheaf K (windowN C K hπ g - D')) 1) := by
  have hsub : CurveDivisor.deg K (windowN C K hπ g - D')
      = CurveDivisor.deg K (windowN C K hπ g) - CurveDivisor.deg K D' := by
    rw [sub_eq_add_neg, CurveDivisor.deg_add, CurveDivisor.deg_neg, sub_eq_add_neg]
  refine subsingleton_hModule_one_of_witness K
    (windowTransportDivisor C K π (windowS_choice π hπ g)) _
    (subsingleton_h1_windowTransportDivisor C K π _ (relThetaPairH1_windowS C hπ g))
    ?_
  rw [hsub, hχK, deg_windowN, deg_windowTransportDivisor]
  have hb := windowBound_pos π hπ
  have hM := windowM_spec π hπ g
  have hδ := one_le_windowδ π
  have hs : (0 : ℤ) ≤ (windowS_choice π hπ g : ℤ) := Int.natCast_nonneg _
  have hg : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg _
  have hgamma' : (gamma : ℤ) ≤ (g : ℤ) := by exact_mod_cast hgamma
  have hkey : (windowS_choice π hπ g : ℤ) * windowδ π + ((g : ℤ) + 2)
      ≤ ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) * windowδ π := by
    nlinarith [hs, hg, hδ, mul_nonneg (mul_nonneg (by linarith : (0 : ℤ) ≤ (g : ℤ) + 1) hs)
      (by linarith : (0 : ℤ) ≤ windowδ π)]
  linarith [hM, hkey, hb, hD', hgamma']

end Pack

end AlgebraicGeometry
