/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.ModulesBaseSheaf
import AlgebraicJacobian.Cohomology.ModulesPushforwardBaseChange
import AlgebraicJacobian.Cohomology.GluedSheafH0BaseChange
import AlgebraicJacobian.Picard.LocalGenerators
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveH0BaseChange
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveSite
import AlgebraicJacobian.Picard.Pic0RingDatumEngine
import AlgebraicJacobian.Picard.SectionsToDivisorsClass
import AlgebraicJacobian.Picard.ThetaShift

/-!
# The local-presentation contract for the rank-one Picard locus

An element of `picDegLayerFunctor` is an etale-plus class, not a chosen line bundle.  The
rank-one route therefore needs an explicit local presentation before it can use the evaluation
map of a line bundle.  `PicRankOneLocalPresentation` records that presentation on an affine
test and ties every piece of data to the input class:

* a descent-class representative whose plus class is the affine collapse of the input;
* a cocycle datum presenting that same relative Picard class;
* a locally free rank-one `Scheme.Modules` object whose base-ring sheaf is the datum's sheaf;
* invertibility of the canonical native pushforward base-change mate on every cartesian square;
* the cohomological rank-one outputs used by the evaluation construction.

No existence, openness, or representability assertion is made here.  The first canonical
consumer is `PicRankOneLocalPresentation.evaluation`, the pullback-pushforward counit.
The method `PicRankOneLocalPresentation.h0BaseChange` derives arbitrary affine base change
from the same presentation's `H^1`-vanishing field.  The section bridge at the end identifies
datum `H^0` with native global sections and proves, by the adjunction triangle identity, that
the evaluation counit sends the canonical unit-lift back to that same section.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
  CartesianMonoidalCategory

open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {A : Type u} [CommRing A] [Algebra k A]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

/-- A rank-one presentation of a genus-degree plus class on an affine test.

The two equality fields prevent an unrelated cocycle datum or line bundle from serving as a
witness: `representative` presents the input plus class, `datum_class` presents that same
relative Picard class, and `module_iso` identifies the resulting cocycle sheaf with the
underlying base-ring sheaf of `module`. -/
structure PicRankOneLocalPresentation
    (lam : picDegLayer C (genus C : ℤ) (overSpec k A)) : Type (u + 1) where
  cover : Algebra.EtaleCover A
  representative : descentClasses C cover
  represents :
    PicEtAff.mk C cover representative = picEtAffineEquiv C A lam.1
  datum : BasicOpenCocycleDatum C cover.Carrier pi
  datum_class :
    (representative : relPic C (overSpec k cover.Carrier)) =
      relPicMk C (overSpec k cover.Carrier) datum.cechPicClass
  module : (relCurve C cover.Carrier).Modules
  module_iso :
    Scheme.toModuleKSheafOfModules
      (Over.mk (relCurve C cover.Carrier ↘ Spec (.of cover.Carrier))) module ≅ datum.sheaf
  line_bundle : Scheme.Modules.IsLineBundle module
  native_pushforward_base_change :
    ∀ {T' X' : Scheme.{u}}
      (g : T' ⟶ Spec (.of cover.Carrier)) (f' : X' ⟶ T')
      (g' : X' ⟶ relCurve C cover.Carrier)
      (sq : IsPullback g' f'
        (relCurve C cover.Carrier ↘ Spec (.of cover.Carrier)) g),
      IsIso ((canonicalBaseChangeMap sq).app module)
  h1_vanishing : Subsingleton (Sheaf.HModule datum.sheaf 1)
  h0_finite : Module.Finite cover.Carrier (Sheaf.HModule datum.sheaf 0)
  h0_projective : Module.Projective cover.Carrier (Sheaf.HModule datum.sheaf 0)
  h0_rank_one :
    ∀ p : PrimeSpectrum cover.Carrier,
      Module.rankAtStalk (Sheaf.HModule datum.sheaf 0) p = 1

namespace PicRankOneLocalPresentation

variable {pi} {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

noncomputable local instance presentationModuleSections
    (P : PicRankOneLocalPresentation pi lam) (U : (relCurve C P.cover.Carrier).Opens) :
    Module P.cover.Carrier Γ(P.module, U) :=
  Scheme.moduleKSections
    (Over.mk (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))) P.module U

/-- The canonical `H^0` base-change equivalence attached to a rank-one presentation.

This is derived from `P.h1_vanishing`; it is not an independently chosen witness. -/
noncomputable def h0BaseChange (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B] :
    B ⊗[P.cover.Carrier] (Sheaf.HModule P.datum.sheaf 0) ≃ₗ[B]
      Sheaf.HModule (P.datum.baseChange B).sheaf 0 :=
  P.datum.datumH0BaseChange B
    ((subsingleton_datumPair_h1_iff P.datum).mpr P.h1_vanishing)

/-- The canonical evaluation map attached to a tied local rank-one presentation. -/
noncomputable def evaluation (P : PicRankOneLocalPresentation pi lam) :
    (Scheme.Modules.pullback
      (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj
        ((Scheme.Modules.pushforward
          (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj P.module) ⟶
      P.module :=
  (Scheme.Modules.pullbackPushforwardAdjunction
    (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).counit.app P.module

/-! ## Native pushforward base change and evaluation coherence -/

/-- The canonical native pushforward base-change isomorphism supplied by the presentation.

The isomorphism is not chosen independently: its hom is definitionally
`(canonicalBaseChangeMap sq).app P.module`. -/
noncomputable def nativeBaseChangeIso (P : PicRankOneLocalPresentation pi lam)
    {T' X' : Scheme.{u}}
    (g : T' ⟶ Spec (.of P.cover.Carrier)) (f' : X' ⟶ T')
    (g' : X' ⟶ relCurve C P.cover.Carrier)
    (sq : IsPullback g' f'
      (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) g) :
    (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward
          (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj P.module) ≅
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj P.module) := by
  exact @asIso _ _ _ _ ((canonicalBaseChangeMap sq).app P.module)
    (P.native_pushforward_base_change g f' g' sq)

/-- The native pushforward base-change isomorphism for an affine coefficient extension. -/
noncomputable def nativeBaseChangeIsoAffine (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B] :
    (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap P.cover.Carrier B)))).obj
        ((Scheme.Modules.pushforward
          (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj P.module) ≅
      (Scheme.Modules.pushforward
        (relCurve C B ↘ Spec (.of B))).obj
          ((Scheme.Modules.pullback (relCurveMap C P.cover.Carrier B)).obj P.module) :=
  P.nativeBaseChangeIso
    (overSpecMap (k := k) P.cover.Carrier B).left
    (snd C (overSpec k B)).left
    (relCurveMap C P.cover.Carrier B)
    (Over.isPullback_whiskerLeft C (overSpecMap (k := k) P.cover.Carrier B))

/-- The source of evaluation identifies canonically with the source of evaluation after any
cartesian base change. -/
noncomputable def evaluationSourceBaseChangeIso (P : PicRankOneLocalPresentation pi lam)
    {T' X' : Scheme.{u}}
    (g : T' ⟶ Spec (.of P.cover.Carrier)) (f' : X' ⟶ T')
    (g' : X' ⟶ relCurve C P.cover.Carrier)
    (sq : IsPullback g' f'
      (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) g) :
    (Scheme.Modules.pullback
        (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⋙
      Scheme.Modules.pullback g').obj
        ((Scheme.Modules.pushforward
          (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj P.module) ≅
      (Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pullback f').obj
        ((Scheme.Modules.pullback g').obj P.module) :=
  ((((Scheme.Modules.pullbackComp f' g) ≪≫
    Scheme.Modules.pullbackCongr sq.w.symm ≪≫
    (Scheme.Modules.pullbackComp g'
      (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).symm).app
        ((Scheme.Modules.pushforward
          (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj P.module)).symm) ≪≫
    (Scheme.Modules.pullback f').mapIso (P.nativeBaseChangeIso g f' g' sq)

/-- Under the source identification, evaluation after base change is the pullback of the
presentation's original evaluation counit. -/
theorem evaluationSourceBaseChangeIso_hom_evaluation
    (P : PicRankOneLocalPresentation pi lam)
    {T' X' : Scheme.{u}}
    (g : T' ⟶ Spec (.of P.cover.Carrier)) (f' : X' ⟶ T')
    (g' : X' ⟶ relCurve C P.cover.Carrier)
    (sq : IsPullback g' f'
      (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) g) :
    (P.evaluationSourceBaseChangeIso g f' g' sq).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f').counit.app
          ((Scheme.Modules.pullback g').obj P.module) =
      (Scheme.Modules.pullback g').map P.evaluation := by
  change ((((Scheme.Modules.pullbackComp f' g) ≪≫
      Scheme.Modules.pullbackCongr sq.w.symm ≪≫
      (Scheme.Modules.pullbackComp g'
        (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).symm).inv).app
          ((Scheme.Modules.pushforward
            (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj P.module)) ≫
    ((Scheme.Modules.pullback f').map ((canonicalBaseChangeMap sq).app P.module) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction f').counit.app
        ((Scheme.Modules.pullback g').obj P.module)) =
    (Scheme.Modules.pullback g').map
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).counit.app P.module)
  exact canonicalBaseChangeMap_counit_cancel sq P.module

/-! The affine coefficient-extension spelling of the evaluation/base-change contract.

This is the consumer-facing specialization for the future zero-locus construction: it keeps
the coefficient ring `B` and `relCurveMap` explicit while retaining the canonical cartesian
square, rather than introducing a second base-change witness. -/
theorem evaluationSourceBaseChangeIsoAffine_hom_evaluation
    (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B] :
    (P.evaluationSourceBaseChangeIso
      (overSpecMap (k := k) P.cover.Carrier B).left
      (snd C (overSpec k B)).left
      (relCurveMap C P.cover.Carrier B)
      (Over.isPullback_whiskerLeft C
        (overSpecMap (k := k) P.cover.Carrier B))).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction
          (snd C (overSpec k B)).left).counit.app
          ((Scheme.Modules.pullback (relCurveMap C P.cover.Carrier B)).obj P.module) =
      (Scheme.Modules.pullback (relCurveMap C P.cover.Carrier B)).map P.evaluation := by
  exact P.evaluationSourceBaseChangeIso_hom_evaluation
    (overSpecMap (k := k) P.cover.Carrier B).left
    (snd C (overSpec k B)).left
    (relCurveMap C P.cover.Carrier B)
    (Over.isPullback_whiskerLeft C (overSpecMap (k := k) P.cover.Carrier B))

/-! ## The datum/native-section/evaluation bridge -/

/-- The global datum section represented by a degree-zero cohomology class. -/
noncomputable def datumSection (P : PicRankOneLocalPresentation pi lam)
    (y : Sheaf.HModule P.datum.sheaf 0) :
    P.datum.sheaf.obj.obj (op (⊤ : (relCurve C P.cover.Carrier).Opens)) :=
  Sheaf.HModule.linearEquiv₀
    (Opens.grothendieckTopology ((relCurve C P.cover.Carrier : Scheme.{u}) : TopCat))
    isTerminalTop P.datum.sheaf y

/-! The datum-side section after coefficient extension.  This deliberately stops at the
glued cocycle sheaf; identifying it with native `Scheme.Modules` global sections is a
separate contract and is not smuggled in here. -/
noncomputable def datumSectionBaseChange (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B]
    (y : Sheaf.HModule P.datum.sheaf 0) :
    (P.datum.baseChange B).sheaf.obj.obj
      (op (⊤ : (relCurve C B).Opens)) :=
  Sheaf.HModule.linearEquiv₀
    (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
    isTerminalTop (P.datum.baseChange B).sheaf
    (P.h0BaseChange B ((1 : B) ⊗ₜ[P.cover.Carrier] y))

/-- H⁰ base change transports the tied datum section to the canonical glued-section map. -/
theorem datumSectionBaseChange_one_tmul (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B]
    (y : Sheaf.HModule P.datum.sheaf 0) :
    P.datumSectionBaseChange B y =
      P.datum.sectionsMapTop B (P.datumSection y) := by
  exact P.datum.linearEquiv₀_datumH0BaseChange_one_tmul B
    ((subsingleton_datumPair_h1_iff P.datum).mpr P.h1_vanishing) y

/-- The linear map underlying the canonical base-changed datum-section construction. -/
noncomputable def datumSectionBaseChangeLinearMap
    (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B] :
    (B ⊗[P.cover.Carrier] Sheaf.HModule P.datum.sheaf 0) →ₗ[B]
      (P.datum.baseChange B).sheaf.obj.obj
        (op (⊤ : (relCurve C B).Opens)) :=
  ((P.h0BaseChange B).trans
    (Sheaf.HModule.linearEquiv₀
      (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
      isTerminalTop (P.datum.baseChange B).sheaf)).toLinearMap

@[simp]
theorem datumSectionBaseChangeLinearMap_one_tmul
    (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B]
    (y : Sheaf.HModule P.datum.sheaf 0) :
    P.datumSectionBaseChangeLinearMap B ((1 : B) ⊗ₜ[P.cover.Carrier] y) =
      P.datumSectionBaseChange B y := by
  rfl

set_option maxHeartbeats 800000 in
-- The composed H⁰ equivalences create a large dependent linear-map elaboration.
/-- Equality of localized H⁰ generators transports canonically to the associated datum
sections.  This exposes the linearity used by fixed-open divisor canonicality without choosing
a second section comparison. -/
theorem datumSectionBaseChange_eq_smul_of_tensor_eq
    (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B]
    (y y' : Sheaf.HModule P.datum.sheaf 0) (v : B)
    (h : (1 : B) ⊗ₜ[P.cover.Carrier] y' =
      v • ((1 : B) ⊗ₜ[P.cover.Carrier] y)) :
    P.datumSectionBaseChange B y' =
      v • P.datumSectionBaseChange B y := by
  rw [← P.datumSectionBaseChangeLinearMap_one_tmul B y',
    ← P.datumSectionBaseChangeLinearMap_one_tmul B y,
    ← map_smul, h]

/-- The conditional divisor datum cut by a base-changed presentation section.

The explicit `hsec` hypothesis is the non-vacuous fibrewise nonvanishing input.  It is
converted componentwise to the injectivity required by the fibrewise-regular section
construction; the integral fibre instance is installed from the standing geometrically
irreducible curve hypotheses.
-/
noncomputable def sectionLocalEquationsOfDatumSectionBaseChange
    (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B] [IsNoetherianRing B]
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hsec : ∀ q : PrimeSpectrum B,
      (P.datum.baseChange B).sectionsMapTop q.asIdeal.ResidueField
        (P.datumSectionBaseChange B y) ≠ 0) :
    (relCurve C B).LocalEquations :=
  let D := P.datum.baseChange B
  let s : ↥(gluedSubmodule B D.pieces D.unit ⊤) :=
    P.datumSectionBaseChange B y
  D.sectionLocalEquationsOfFibrewiseRegular s
    (fun j q => by
      letI : IsIntegral (relCurve C q.asIdeal.ResidueField) :=
        instIsIntegralBaseChange C q.asIdeal.ResidueField
      exact D.injective_rTensor_component_of_sectionsMapTop_ne_zero s q (hsec q) j)

/-- The conditional section construction preserves the base-changed datum's Picard class. -/
theorem sectionLocalEquationsOfDatumSectionBaseChange_picClass
    (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B] [IsNoetherianRing B]
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hsec : ∀ q : PrimeSpectrum B,
      (P.datum.baseChange B).sectionsMapTop q.asIdeal.ResidueField
        (P.datumSectionBaseChange B y) ≠ 0) :
    (P.sectionLocalEquationsOfDatumSectionBaseChange B y hsec).picClass =
      (P.datum.baseChange B).cechPicClass := by
  let D := P.datum.baseChange B
  let s : ↥(gluedSubmodule B D.pieces D.unit ⊤) :=
    P.datumSectionBaseChange B y
  unfold sectionLocalEquationsOfDatumSectionBaseChange
  exact D.sectionLocalEquationsOfFibrewiseRegular_picClass s
    (fun j q => by
      letI : IsIntegral (relCurve C q.asIdeal.ResidueField) :=
        instIsIntegralBaseChange C q.asIdeal.ResidueField
      exact D.injective_rTensor_component_of_sectionsMapTop_ne_zero s q (hsec q) j)

/-- The presentation identifies datum `H^0` with native global sections of its line bundle. -/
noncomputable def moduleSectionsEquiv (P : PicRankOneLocalPresentation pi lam) :
    Sheaf.HModule P.datum.sheaf 0 ≃ₗ[P.cover.Carrier] Γ(P.module, ⊤) :=
  (Sheaf.HModule.mapEquiv P.module_iso.symm 0).trans
    (Sheaf.HModule.linearEquiv₀
      (Opens.grothendieckTopology ((relCurve C P.cover.Carrier : Scheme.{u}) : TopCat))
      isTerminalTop
      (Scheme.toModuleKSheafOfModules
        (Over.mk (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))) P.module))

/-- The native section is exactly the datum section transported through `module_iso`. -/
theorem module_iso_inv_datumSection (P : PicRankOneLocalPresentation pi lam)
    (y : Sheaf.HModule P.datum.sheaf 0) :
    (P.module_iso.inv.hom.app (op (⊤ : (relCurve C P.cover.Carrier).Opens))).hom
      (P.datumSection y) = P.moduleSectionsEquiv y := by
  exact Sheaf.HModule.linearEquiv₀_naturality
    (hT := isTerminalTop) (f := P.module_iso.inv) y

/-- A datum `H^0` class, read as a global section of the native pushforward. -/
noncomputable def pushforwardSectionOfH0 (P : PicRankOneLocalPresentation pi lam)
    (y : Sheaf.HModule P.datum.sheaf 0) :
    Γ((Scheme.Modules.pushforward
      (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj P.module, ⊤) := by
  change Γ(P.module,
    (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
      (⊤ : (Spec (.of P.cover.Carrier)).Opens))
  simpa using P.moduleSectionsEquiv y

/-- The canonical unit-lift of a datum `H^0` class to the source of evaluation. -/
noncomputable def evaluationLiftOfH0 (P : PicRankOneLocalPresentation pi lam)
    (y : Sheaf.HModule P.datum.sheaf 0) :
    Γ((Scheme.Modules.pullback
      (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj
        ((Scheme.Modules.pushforward
          (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj P.module),
      (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
        (⊤ : (Spec (.of P.cover.Carrier)).Opens)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction
    (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).unit.app
      ((Scheme.Modules.pushforward
        (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj P.module)).app
          (⊤ : (Spec (.of P.cover.Carrier)).Opens) (P.pushforwardSectionOfH0 y)

/-- Evaluation of the canonical unit-lift returns the original native global section.

This is the right triangle identity of pullback-pushforward.  It is the counit compatibility
needed before the section can be used to define a divisor; no zero-locus claim is made here. -/
theorem evaluation_evaluationLiftOfH0 (P : PicRankOneLocalPresentation pi lam)
    (y : Sheaf.HModule P.datum.sheaf 0) :
    (Scheme.Modules.Hom.app P.evaluation
      ((relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
        (⊤ : (Spec (.of P.cover.Carrier)).Opens))).hom
      (P.evaluationLiftOfH0 y) = P.pushforwardSectionOfH0 y := by
  have h := congrArg
    (fun (f : (Scheme.Modules.pushforward
        (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj P.module ⟶
      (Scheme.Modules.pushforward
        (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).obj P.module) =>
      (Scheme.Modules.Hom.app f (⊤ : (Spec (.of P.cover.Carrier)).Opens)).hom
        (P.pushforwardSectionOfH0 y))
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier))).right_triangle_components
        P.module)
  exact h

/-! ## Local-away generators for the canonical evaluation -/

/-- Nonvanishing on every residue-field fibre of `D(f)` survives passage from the
corresponding prime of the original ring to the residue field of a prime of `A_f`.

The residue-field comparison is an isomorphism because localization induces bijective
residue-field maps.  Keeping this as a module-level lemma prevents the rank-one
construction from depending on a false definitional transitivity of datum base change. -/
theorem fibre_tmul_ne_zero_of_away
    {A Q : Type u} [CommRing A] [AddCommGroup Q] [Module A Q]
    (f : A) (y : Q)
    (hy : ∀ p : PrimeSpectrum A, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Q ⊗[A] p.asIdeal.ResidueField) ≠ 0)
    (q : PrimeSpectrum (Localization.Away f)) :
    ((1 : q.asIdeal.ResidueField) ⊗ₜ[A] y :
      q.asIdeal.ResidueField ⊗[A] Q) ≠ 0 := by
  let p : PrimeSpectrum A :=
    PrimeSpectrum.comap (algebraMap A (Localization.Away f)) q
  have hfp : f ∉ p.asIdeal := by
    intro hf
    refine q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem q.asIdeal
      (Ideal.mem_comap.mp hf) ?_)
    exact IsLocalization.Away.algebraMap_isUnit f
  have hp : ((1 : p.asIdeal.ResidueField) ⊗ₜ[A] y :
      p.asIdeal.ResidueField ⊗[A] Q) ≠ 0 := by
    have h := (TensorProduct.comm A Q p.asIdeal.ResidueField).map_ne_zero_iff.mpr
      (hy p hfp)
    simpa only [TensorProduct.comm_tmul] using h
  have hcom : p.asIdeal =
      q.asIdeal.comap (algebraMap A (Localization.Away f)) := rfl
  let rho : p.asIdeal.ResidueField →ₐ[A] q.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal
      (Algebra.ofId A (Localization.Away f)) hcom
  have hrho : Function.Bijective rho :=
    (RingHom.surjectiveOnStalks_of_isLocalization (Submonoid.powers f)
      (Localization.Away f)).residueFieldMap_bijective
        p.asIdeal q.asIdeal hcom
  let e : p.asIdeal.ResidueField ≃ₗ[A] q.asIdeal.ResidueField :=
    LinearEquiv.ofBijective rho.toLinearMap hrho
  have he := (e.rTensor Q).map_ne_zero_iff.mpr hp
  simpa only [LinearEquiv.rTensor_tmul, e, LinearEquiv.ofBijective_apply,
    AlgHom.toLinearMap_apply, map_one] using he

/-- Cancelling an iterated scalar extension preserves a nonzero pure tensor. -/
theorem one_tmul_one_tmul_ne_zero
    {R S K Q : Type u} [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [AddCommGroup Q] [Module R Q]
    (y : Q) (hy : ((1 : K) ⊗ₜ[R] y : K ⊗[R] Q) ≠ 0) :
    ((1 : K) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] y) :
      K ⊗[S] (S ⊗[R] Q)) ≠ 0 := by
  let e : K ⊗[S] (S ⊗[R] Q) ≃ₗ[K] K ⊗[R] Q :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S K K Q
  rw [← e.map_ne_zero_iff]
  simpa only [e, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    one_smul] using hy

/-- Base change of a linear equivalence preserves nonvanishing of a pure tensor. -/
theorem one_tmul_linearEquiv_ne_zero
    {R K M N : Type u} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (x : M)
    (hx : ((1 : K) ⊗ₜ[R] x : K ⊗[R] M) ≠ 0) :
    ((1 : K) ⊗ₜ[R] e x : K ⊗[R] N) ≠ 0 := by
  let eK := LinearEquiv.baseChange R K M N e
  have h := eK.map_ne_zero_iff.mpr hx
  simpa only [eK, LinearEquiv.baseChange_tmul] using h

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] in
/-- A nonzero cohomology class on a field fibre gives a nonzero glued section. -/
theorem sectionsMapTop_ne_zero_of_one_tmul_ne_zero
    {B K : Type u} [CommRing B] [Algebra k B] [Field K]
    [Algebra k K] [Algebra B K] [IsScalarTower k B K]
    (D : BasicOpenCocycleDatum C B pi)
    (hH1 : Subsingleton (datumPair D).H1)
    (y : Sheaf.HModule D.sheaf 0)
    (hy : ((1 : K) ⊗ₜ[B] y : K ⊗[B] Sheaf.HModule D.sheaf 0) ≠ 0) :
    D.sectionsMapTop K
      (Sheaf.HModule.linearEquiv₀
        (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
        isTerminalTop D.sheaf y) ≠ 0 := by
  let eDatum := D.datumH0BaseChange K hH1
  have hDatum : eDatum ((1 : K) ⊗ₜ[B] y) ≠ 0 :=
    eDatum.map_ne_zero_iff.mpr hy
  let eSection := Sheaf.HModule.linearEquiv₀
    (Opens.grothendieckTopology ((relCurve C K : Scheme.{u}) : TopCat))
    isTerminalTop (D.baseChange K).sheaf
  have hSection : eSection (eDatum ((1 : K) ⊗ₜ[B] y)) ≠ 0 :=
    eSection.map_ne_zero_iff.mpr hDatum
  rw [← D.linearEquiv₀_datumH0BaseChange_one_tmul K hH1 y]
  exact hSection

/-- A fibrewise-nonzero section remains nonzero after localizing and extending once more
to a residue field of the localized ring. -/
theorem away_one_tmul_one_tmul_ne_zero
    {R Q : Type u} [CommRing R] [AddCommGroup Q] [Module R Q]
    (f : R) (y : Q)
    (hy : ∀ p : PrimeSpectrum R, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Q ⊗[R] p.asIdeal.ResidueField) ≠ 0)
    (q : PrimeSpectrum (Localization.Away f)) :
    ((1 : q.asIdeal.ResidueField) ⊗ₜ[Localization.Away f]
      ((1 : Localization.Away f) ⊗ₜ[R] y) :
      q.asIdeal.ResidueField ⊗[Localization.Away f]
        (Localization.Away f ⊗[R] Q)) ≠ 0 := by
  let B := Localization.Away f
  let K := q.asIdeal.ResidueField
  have hdirect : ((1 : K) ⊗ₜ[R] y : K ⊗[R] Q) ≠ 0 :=
    fibre_tmul_ne_zero_of_away f y hy q
  exact one_tmul_one_tmul_ne_zero y hdirect

/-- A generator which is nonzero on every fibre of `D(f)` remains nonzero in every
residue fibre after extending the whole module to `Localization.Away f`.  This is the
orientation consumed by the rank-one local-basis theorem. -/
theorem tensorAwayGenerator_fibre_ne_zero
    {R Q : Type u} [CommRing R] [AddCommGroup Q] [Module R Q]
    (f : R) (y : Q)
    (hy : ∀ p : PrimeSpectrum R, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Q ⊗[R] p.asIdeal.ResidueField) ≠ 0)
    (q : PrimeSpectrum (Localization.Away f)) :
    (((1 : Localization.Away f) ⊗ₜ[R] y) ⊗ₜ[Localization.Away f]
      (1 : q.asIdeal.ResidueField) :
      (Localization.Away f ⊗[R] Q) ⊗[Localization.Away f]
        q.asIdeal.ResidueField) ≠ 0 := by
  have h := TensorProduct.comm (Localization.Away f)
    q.asIdeal.ResidueField (Localization.Away f ⊗[R] Q) |>.map_ne_zero_iff.mpr
      (away_one_tmul_one_tmul_ne_zero f y hy q)
  simpa only [TensorProduct.comm_tmul] using h

/-- Canonical `H⁰` base change preserves the localized pure tensor's nonvanishing. -/
theorem h0BaseChange_one_tmul_ne_zero
    (P : PicRankOneLocalPresentation pi lam)
    (B K : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B] [Field K] [Algebra k K]
    [Algebra B K] [IsScalarTower k B K]
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ((1 : K) ⊗ₜ[B] ((1 : B) ⊗ₜ[P.cover.Carrier] y) :
      K ⊗[B] (B ⊗[P.cover.Carrier]
        Sheaf.HModule P.datum.sheaf 0)) ≠ 0) :
    ((1 : K) ⊗ₜ[B]
      (P.h0BaseChange B ((1 : B) ⊗ₜ[P.cover.Carrier] y)) :
      K ⊗[B] Sheaf.HModule (P.datum.baseChange B).sheaf 0) ≠ 0 := by
  let eH0 : B ⊗[P.cover.Carrier] Sheaf.HModule P.datum.sheaf 0 ≃ₗ[B]
      Sheaf.HModule (P.datum.baseChange B).sheaf 0 :=
    P.h0BaseChange B
  exact one_tmul_linearEquiv_ne_zero eH0
    ((1 : B) ⊗ₜ[P.cover.Carrier] y) hy

/-- The canonical scalar-extension certificate package attached to a tied presentation.

The presentation's own `H¹`-vanishing, finite/projective `H⁰`, and stalk-rank-one fields are
transported along its canonical `h0BaseChange` equivalence.  In particular, the target module
is not replaced by an unrelated witness: it is exactly the datum module of `P.datum.baseChange`.
This is a coefficient-extension feeder for the family producer; it does not assert the missing
native pushforward base-change isomorphism or construct a presentation over a new affine test.
-/
theorem baseChangeRankOneCertificates
    (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B] :
    Subsingleton (Sheaf.HModule (P.datum.baseChange B).sheaf 1) ∧
      Module.Finite B (Sheaf.HModule (P.datum.baseChange B).sheaf 0) ∧
      Module.Projective B (Sheaf.HModule (P.datum.baseChange B).sheaf 0) ∧
      ∀ p : PrimeSpectrum B,
        Module.rankAtStalk (Sheaf.HModule (P.datum.baseChange B).sheaf 0) p = 1 := by
  let Q := Sheaf.HModule P.datum.sheaf 0
  letI : Module.Finite P.cover.Carrier Q := P.h0_finite
  letI : Module.Projective P.cover.Carrier Q := P.h0_projective
  have hH1 : Subsingleton (datumPair P.datum).H1 :=
    (subsingleton_datumPair_h1_iff P.datum).mpr P.h1_vanishing
  have hh1 : Subsingleton (Sheaf.HModule (P.datum.baseChange B).sheaf 1) :=
    P.datum.datum_subsingleton_h1_baseChange B hH1
  let e : B ⊗[P.cover.Carrier] Q ≃ₗ[B]
      Sheaf.HModule (P.datum.baseChange B).sheaf 0 := P.h0BaseChange B
  letI : Module.Finite B (B ⊗[P.cover.Carrier] Q) := by
    infer_instance
  letI : Module.Projective B (B ⊗[P.cover.Carrier] Q) := by
    infer_instance
  have hfin : Module.Finite B (Sheaf.HModule (P.datum.baseChange B).sheaf 0) :=
    Module.Finite.equiv e
  have hproj : Module.Projective B (Sheaf.HModule (P.datum.baseChange B).sheaf 0) :=
    Module.Projective.of_equiv e
  have hrank : ∀ p : PrimeSpectrum B,
      Module.rankAtStalk (Sheaf.HModule (P.datum.baseChange B).sheaf 0) p = 1 := by
    intro p
    rw [← Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_baseChange]
    exact P.h0_rank_one (p.comap (algebraMap P.cover.Carrier B))
  exact ⟨hh1, hfin, hproj, hrank⟩

/-- `H¹`-vanishing in a presentation propagates to every coefficient extension. -/
private theorem datumPair_h1_baseChange
    (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B] :
    Subsingleton (datumPair (P.datum.baseChange B)).H1 :=
  (subsingleton_datumPair_h1_iff (P.datum.baseChange B)).mpr
    (P.baseChangeRankOneCertificates B).1

/-- The local-away generator supplied over the presentation ring gives the exact
fibrewise-nonvanishing hypothesis required by the divisor construction after localizing.

This is the missing consumer bridge between the finite-projective generator theorem and
`sectionLocalEquationsOfDatumSectionBaseChange`.  It compares residue fields across the
localization, cancels the iterated tensor product, and then uses the presentation's
canonical `H⁰` base-change equivalence. -/
theorem sectionsMapTop_datumSectionBaseChange_away_ne_zero
    (P : PicRankOneLocalPresentation pi lam)
    (f : P.cover.Carrier)
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0)
    (q : PrimeSpectrum (Localization.Away f)) :
    (P.datum.baseChange (Localization.Away f)).sectionsMapTop
      q.asIdeal.ResidueField
      (P.datumSectionBaseChange (Localization.Away f) y) ≠ 0 := by
  let B := Localization.Away f
  let K := q.asIdeal.ResidueField
  have hiter : ((1 : K) ⊗ₜ[B]
      ((1 : B) ⊗ₜ[P.cover.Carrier] y) :
      K ⊗[B] (B ⊗[P.cover.Carrier]
        Sheaf.HModule P.datum.sheaf 0)) ≠ 0 :=
    away_one_tmul_one_tmul_ne_zero f y hy q
  have hyB : ((1 : K) ⊗ₜ[B]
      (P.h0BaseChange B ((1 : B) ⊗ₜ[P.cover.Carrier] y)) :
      K ⊗[B] Sheaf.HModule (P.datum.baseChange B).sheaf 0) ≠ 0 :=
    P.h0BaseChange_one_tmul_ne_zero B K y hiter
  have hH1 : Subsingleton (datumPair (P.datum.baseChange B)).H1 :=
    P.datumPair_h1_baseChange B
  let yB : Sheaf.HModule (P.datum.baseChange B).sheaf 0 :=
    P.h0BaseChange B ((1 : B) ⊗ₜ[P.cover.Carrier] y)
  change (P.datum.baseChange B).sectionsMapTop K
    (Sheaf.HModule.linearEquiv₀
      (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
      isTerminalTop (P.datum.baseChange B).sheaf yB) ≠ 0
  exact sectionsMapTop_ne_zero_of_one_tmul_ne_zero
    (P.datum.baseChange B) hH1 yB hyB

/-- A rank-one presentation has a tied local-away evaluation generator.

The rank-one field of `P` makes every residue-field fibre of its `H⁰` module nontrivial.
The projective-module generator lemma therefore supplies a single basic open `D(f)` and
one datum section `y` which stays nonzero on every residue fibre over that open.  The same
`y` is transported to a native global section and its unit-lift through the evaluation
counit; the final conjunct records that counit identity explicitly so the future
`divisorOfRankOne` construction consumes this witness rather than an unrelated section.
-/
theorem exists_baseOpen_evaluation_generator
    (P : PicRankOneLocalPresentation pi lam)
    (p : PrimeSpectrum P.cover.Carrier) :
    ∃ f : P.cover.Carrier, f ∉ p.asIdeal ∧
      ∃ y : Sheaf.HModule P.datum.sheaf 0,
        (∀ q : PrimeSpectrum P.cover.Carrier, f ∉ q.asIdeal →
          (y ⊗ₜ (1 : q.asIdeal.ResidueField) :
            Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
              q.asIdeal.ResidueField) ≠ 0) ∧
        (Scheme.Modules.Hom.app P.evaluation
          ((relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
            (⊤ : (Spec (.of P.cover.Carrier)).Opens))).hom
          (P.evaluationLiftOfH0 y) = P.pushforwardSectionOfH0 y := by
  let Q := Sheaf.HModule P.datum.sheaf 0
  letI : Module.Finite P.cover.Carrier Q := P.h0_finite
  letI : Module.Projective P.cover.Carrier Q := P.h0_projective
  have hfr : Module.finrank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[P.cover.Carrier] Q) = 1 := by
    rw [← Module.rankAtStalk_eq]
    exact P.h0_rank_one p
  haveI : Nontrivial (p.asIdeal.ResidueField ⊗[P.cover.Carrier] Q) :=
    Module.nontrivial_of_finrank_pos (by rw [hfr]; norm_num)
  haveI : Nontrivial (Q ⊗[P.cover.Carrier] p.asIdeal.ResidueField) :=
    (TensorProduct.comm P.cover.Carrier _ _).toEquiv.symm.nontrivial
  obtain ⟨f, hf, y, hy⟩ :=
    Module.exists_fibrewise_tmul_ne_zero_of_projective p (Q := Q)
      (by infer_instance)
  refine ⟨f, hf, y, ?_, ?_⟩
  · simpa only [Q] using hy
  · exact P.evaluation_evaluationLiftOfH0 y

/-- The fibrewise-regular local equations cut by a tied local-away datum section.

The nonvanishing proof is derived by
`sectionsMapTop_datumSectionBaseChange_away_ne_zero`; it is not additional witness data.
Together with `exists_baseOpen_evaluation_generator`, this is the immediate local divisor
consumer on the datum side.  Identifying it with the native evaluation zero locus remains
a separate `O`-module base-change contract. -/
noncomputable def baseOpenDatumSectionLocalEquations
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f : P.cover.Carrier)
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    (relCurve C (Localization.Away f)).LocalEquations :=
  P.sectionLocalEquationsOfDatumSectionBaseChange
    (Localization.Away f) y
    (fun q => P.sectionsMapTop_datumSectionBaseChange_away_ne_zero f y hy q)

/-- The local equations cut by the tied datum section represent its base-changed
cocycle datum. -/
theorem baseOpenDatumSectionLocalEquations_picClass
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f : P.cover.Carrier)
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    (P.baseOpenDatumSectionLocalEquations f y hy).picClass =
      (P.datum.baseChange (Localization.Away f)).cechPicClass := by
  unfold baseOpenDatumSectionLocalEquations
  exact P.sectionLocalEquationsOfDatumSectionBaseChange_picClass
    (Localization.Away f) y
    (fun q => P.sectionsMapTop_datumSectionBaseChange_away_ne_zero f y hy q)

/-! ## Degree of the tied datum -/

/- The high-priority `relCurve.instOver` used by the section bridge and the degree stack's
base-change `Over` instance have the same structure morphism but different instance keys.
Re-key the standard base-change bundle locally before stating the degree theorem. -/
noncomputable local instance (priority := 20000) rankOneDegreeOver
    (L : Type u) [Field L] [Algebra k L] :
    (relCurve C L).Over (Spec (.of L)) :=
  instOverBaseChange C L

noncomputable local instance rankOneDegreeSmooth
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance rankOneDegreeIntegral
    (L : Type u) [Field L] [Algebra k L] :
    IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance rankOneDegreeQuasiCompact
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance rankOneDegreeFiniteH0
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance rankOneDegreeFiniteH1
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

/-- A datum presenting an affine representative of a genus-degree class has degree `genus C`
after every field-valued coefficient extension.

These are exactly the first five, canonical inputs of `PicRankOneLocalPresentation`.  Stating
the calculation before the remaining native and cohomological fields lets the family producer
use it when proving rank one, without assuming the completed presentation it is constructing. -/
theorem datum_classDeg_baseChange_of_representation
    (E : Algebra.EtaleCover A)
    (x : descentClasses C E)
    (hrep : PicEtAff.mk C E x = picEtAffineEquiv C A lam.1)
    (D : BasicOpenCocycleDatum C E.Carrier pi)
    (hclass :
      (x : relPic C (overSpec k E.Carrier)) =
        relPicMk C (overSpec k E.Carrier) D.cechPicClass)
    (L : Type u) [Field L] [Algebra k L] [Algebra E.Carrier L]
    [IsScalarTower k E.Carrier L] :
    classDeg L
      (Scheme.CechPic.map (relCurveMap C E.Carrier L)
        D.cechPicClass) = genus C := by
  let iota : A →ₐ[k] E.Carrier :=
    (Algebra.ofId A E.Carrier).restrictScalars k
  let psi : E.Carrier →ₐ[k] L :=
    (Algebra.ofId E.Carrier L).restrictScalars k
  have hcurve :
      relCurveMap C E.Carrier L =
        (C ◁ Over.overSpecMap psi).left := by
    refine congrArg
      (fun f : overSpec k L ⟶ overSpec k E.Carrier => (C ◁ f).left) ?_
    exact Over.OverMorphism.ext rfl
  have hpresentation :
      picEtMap C (Over.overSpecMap iota) lam.1 =
        relPicToPicEt C (overSpec k E.Carrier)
          (x : relPic C (overSpec k E.Carrier)) := by
    exact picEtMap_eq_relPicToPicEt_of_affineRepresentative
      C lam.1 E x hrep.symm
  calc
    classDeg L
        (Scheme.CechPic.map (relCurveMap C E.Carrier L)
          D.cechPicClass) =
      relPicDeg L
        (relPicMk C (overSpec k L)
          (Scheme.CechPic.map (relCurveMap C E.Carrier L)
            D.cechPicClass)) :=
      (relPicDeg_relPicMk L _).symm
    _ = relPicDeg L
        (relPicMap C (Over.overSpecMap psi)
          (relPicMk C (overSpec k E.Carrier)
            D.cechPicClass)) := by
      rw [relPicMap_mk, ← hcurve]
      rfl
    _ = relPicDeg L
        (relPicMap C (Over.overSpecMap psi)
          (x : relPic C (overSpec k E.Carrier))) := by
      rw [hclass]
    _ = degAt
        (relPicToPicEt C (overSpec k E.Carrier)
          (x : relPic C (overSpec k E.Carrier)))
        (Over.overSpecMap psi) :=
      (degAt_relPicToPicEt
        (x : relPic C (overSpec k E.Carrier))
        (Over.overSpecMap psi)).symm
    _ = degAt (picEtMap C (Over.overSpecMap iota) lam.1)
        (Over.overSpecMap psi) := by rw [hpresentation]
    _ = degAt lam.1 (Over.overSpecMap psi ≫ Over.overSpecMap iota) :=
      degAt_picEtMap (Over.overSpecMap iota) lam.1 (Over.overSpecMap psi)
    _ = genus C := lam.2 L (Over.overSpecMap psi ≫ Over.overSpecMap iota)

/-- The cocycle datum tied to a completed presentation has class degree `genus C`
after every field-valued coefficient extension. -/
theorem datum_classDeg_baseChange
    (P : PicRankOneLocalPresentation pi lam)
    (L : Type u) [Field L] [Algebra k L] [Algebra P.cover.Carrier L]
    [IsScalarTower k P.cover.Carrier L] :
    classDeg L
      (Scheme.CechPic.map (relCurveMap C P.cover.Carrier L)
        P.datum.cechPicClass) = genus C :=
  datum_classDeg_baseChange_of_representation
    P.cover P.representative P.represents P.datum P.datum_class L

end PicRankOneLocalPresentation

end AlgebraicGeometry
