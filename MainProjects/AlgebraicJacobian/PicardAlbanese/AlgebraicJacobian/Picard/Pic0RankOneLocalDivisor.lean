/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOnePresentation
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveEffectivity
import AlgebraicJacobian.Picard.DivisorFamilyMonoH1
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The consumed local divisor package for the rank-one route

This module is the first divisor consumer of PicRankOneLocalPresentation.  The projective
rank-one H0 module supplies a basic open and a section which is nonzero on every residue fibre
there.  The datum-side section construction then gives regular local equations, and the widened
effectivity engine packages those equations as a DivFamZarAff of degree genus C.

The package is deliberately local and presentation-tied.  It does not define the canonical
family-level divisorOfRankOne, identify the equations with the native zero locus, or assert
that the rank-one locus is represented by an open subscheme.  Those remain the next contracts.
-/

set_option autoImplicit false

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
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

namespace PicRankOneLocalPresentation

/- The degree theorem needs the base-change geometric package under the local relCurve instance,
   which has lower priority in the general curve API. -/
noncomputable local instance (priority := 20000) rankOneLocalDivisorOver
    (L : Type u) [Field L] [Algebra k L] :
    (relCurve C L).Over (Spec (.of L)) :=
  instOverBaseChange C L

noncomputable local instance rankOneLocalDivisorSmooth
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance rankOneLocalDivisorIntegral
    (L : Type u) [Field L] [Algebra k L] :
    IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance rankOneLocalDivisorQuasiCompact
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance rankOneLocalDivisorFiniteH0
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance rankOneLocalDivisorFiniteH1
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

/-! ## Regularity and degree of the local equations -/

/-- The local equations cut from the tied datum section remain regular after every field-valued
coefficient extension.  This is the regularity input consumed by the widened effectivity
engine, derived from the same fibrewise nonvanishing hypothesis used in the construction. -/
theorem baseOpenDatumSectionLocalEquations_fibrewiseRegular
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f : P.cover.Carrier)
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0)
    (L : Type u) [Field L] [Algebra k L]
    [Algebra (Localization.Away f) L]
    [IsScalarTower k (Localization.Away f) L]
    (z : relCurve C L) :
    ((relCurve C L).presheaf.germ
      (((P.baseOpenDatumSectionLocalEquations f y hy).cover.pullback
        (relCurveMap C (Localization.Away f) L)).opens z) z
      (((P.baseOpenDatumSectionLocalEquations f y hy).cover.pullback
        (relCurveMap C (Localization.Away f) L)).mem_opens z)).hom
      (Scheme.LocalEquations.pullbackEqn
        (relCurveMap C (Localization.Away f) L)
        (P.baseOpenDatumSectionLocalEquations f y hy) z) ∈
      nonZeroDivisors ((relCurve C L).presheaf.stalk z) := by
  let B := Localization.Away f
  let D := P.datum.baseChange B
  let s : ↥(gluedSubmodule B D.pieces D.unit ⊤) :=
    P.datumSectionBaseChange B y
  have hsec : ∀ q : PrimeSpectrum B,
      D.sectionsMapTop q.asIdeal.ResidueField
        (P.datumSectionBaseChange B y) ≠ 0 :=
    fun q => P.sectionsMapTop_datumSectionBaseChange_away_ne_zero f y hy q
  have hfib : ∀ (j : D.index) (q : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor q.asIdeal.ResidueField) :=
    fun j q => D.injective_rTensor_component_of_sectionsMapTop_ne_zero
      s q (hsec q) j
  unfold baseOpenDatumSectionLocalEquations sectionLocalEquationsOfDatumSectionBaseChange
  exact D.germ_self_pullbackEqn_sectionLocalEquationsOfFibrewiseRegular
    s hfib L z

/-- The local equations have the genus class degree after every field-valued extension.  The
calculation uses the datum class law and datum_classDeg_baseChange, so the degree is tied to
the presentation rather than supplied as an unrelated witness. -/
theorem baseOpenDatumSectionLocalEquations_classDeg
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f : P.cover.Carrier)
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0)
    (L : Type u) [Field L] [Algebra k L]
    [Algebra (Localization.Away f) L]
    [IsScalarTower k (Localization.Away f) L] :
    classDeg L
      (Scheme.CechPic.map (relCurveMap C (Localization.Away f) L)
        (P.baseOpenDatumSectionLocalEquations f y hy).picClass) = genus C := by
  letI : Algebra P.cover.Carrier L :=
    ((algebraMap (Localization.Away f) L).comp
      (algebraMap P.cover.Carrier (Localization.Away f))).toAlgebra
  haveI : IsScalarTower P.cover.Carrier (Localization.Away f) L :=
    ⟨fun r s x => by
      rw [← IsScalarTower.algebraMap_smul (Localization.Away f) r s]
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        RingHom.id_apply, map_mul, mul_assoc]⟩
  haveI : IsScalarTower k P.cover.Carrier L :=
    IsScalarTower.of_algebraMap_eq' (R := k) (S := P.cover.Carrier) (A := L) (by
      ext a
      simp only [RingHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply k (Localization.Away f) L,
        IsScalarTower.algebraMap_apply k P.cover.Carrier (Localization.Away f)] <;>
        rfl)
  rw [P.baseOpenDatumSectionLocalEquations_picClass f y hy,
    P.datum.cechPicClass_baseChange (Localization.Away f),
    ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
    relCurveMap_comp]
  exact P.datum_classDeg_baseChange L

/-! ## The local widened divisor and its immediate consumer -/

/- The next canonicality edge is expressed first in the localized H⁰ module.  The datum
   section/native comparison needed to transport this unit to local equations is deliberately
   a separate contract. -/
theorem existsUnique_unit_tensorAway_rankOne_generators
    (P : PicRankOneLocalPresentation pi lam)
    (f : P.cover.Carrier)
    (y y' : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0)
    (hy' : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y' ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    ∃! v : (Localization.Away f)ˣ,
      ((1 : Localization.Away f) ⊗ₜ[P.cover.Carrier] y') =
        (v : Localization.Away f) •
          ((1 : Localization.Away f) ⊗ₜ[P.cover.Carrier] y) := by
  let B := Localization.Away f
  let Q := Sheaf.HModule P.datum.sheaf 0
  letI : Module.Finite P.cover.Carrier Q := P.h0_finite
  letI : Module.Projective P.cover.Carrier Q := P.h0_projective
  have hrankB : ∀ q : PrimeSpectrum B,
      Module.rankAtStalk (B ⊗[P.cover.Carrier] Q) q = 1 := by
    intro q
    rw [Module.rankAtStalk_baseChange]
    exact P.h0_rank_one (PrimeSpectrum.comap
      (algebraMap P.cover.Carrier B) q)
  exact Module.existsUnique_unit_smul_of_forall_tmul_ne_zero
    hrankB ((1 : B) ⊗ₜ[P.cover.Carrier] y) ((1 : B) ⊗ₜ[P.cover.Carrier] y')
    (AlgebraicGeometry.PicRankOneLocalPresentation.tensorAwayGenerator_fibre_ne_zero
      f y hy)
    (AlgebraicGeometry.PicRankOneLocalPresentation.tensorAwayGenerator_fibre_ne_zero
      f y' hy')

private theorem baseChange_component_smul
    {B : Type u} [CommRing B] [Algebra k B]
    (D : BasicOpenCocycleDatum C B pi)
    (v : B)
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤)) (j : D.index) :
    D.component (v • s) j = v • D.component s j := by
  unfold BasicOpenCocycleDatum.component
  change (relCurve C B).resHom (le_inf le_top le_rfl) (v • s.val j) =
    v • (relCurve C B).resHom (le_inf le_top le_rfl) (s.val j)
  rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
  congr 1
  exact (relCurve C B).overAlgebraMap_apply_res B
    (homOfLE (le_inf le_top le_rfl)).op v

set_option maxHeartbeats 800000 in
-- The dependent local-equation constructors and restriction maps need a larger elaboration budget.
/-- A unit relating two tied datum sections transports the resulting local equations by pointwise
rescaling on the canonical pointed cover over an arbitrary noetherian coefficient ring. -/
theorem sectionLocalEquationsOfDatumSectionBaseChange_divEq_of_unit
    (P : PicRankOneLocalPresentation pi lam)
    (B : Type u) [CommRing B] [Algebra k B] [Algebra P.cover.Carrier B]
    [IsScalarTower k P.cover.Carrier B] [IsNoetherianRing B]
    (y y' : Sheaf.HModule P.datum.sheaf 0)
    (hsec : ∀ q : PrimeSpectrum B,
      (P.datum.baseChange B).sectionsMapTop q.asIdeal.ResidueField
        (P.datumSectionBaseChange B y) ≠ 0)
    (hsec' : ∀ q : PrimeSpectrum B,
      (P.datum.baseChange B).sectionsMapTop q.asIdeal.ResidueField
        (P.datumSectionBaseChange B y') ≠ 0)
    (v : Bˣ)
    (hsec_smul : P.datumSectionBaseChange B y' =
      (v : B) • P.datumSectionBaseChange B y) :
    Scheme.LocalEquations.DivEq
      (P.sectionLocalEquationsOfDatumSectionBaseChange B y hsec)
      (P.sectionLocalEquationsOfDatumSectionBaseChange B y' hsec') := by
  let D := P.datum.baseChange B
  let s : ↥(gluedSubmodule B D.pieces D.unit ⊤) := P.datumSectionBaseChange B y
  let s' : ↥(gluedSubmodule B D.pieces D.unit ⊤) := P.datumSectionBaseChange B y'
  have hs : s' = (v : B) • s := hsec_smul
  have hcomp : ∀ j : D.index, D.component s' j = (v : B) • D.component s j := by
    intro j
    calc
      D.component s' j = D.component ((v : B) • s) j := by
        exact congrArg (fun t => D.component t j) hs
      _ = (v : B) • D.component s j :=
        baseChange_component_smul (C := C) (pi := pi) D (v : B) s j
  simp only [sectionLocalEquationsOfDatumSectionBaseChange]
  apply Scheme.LocalEquations.DivEq.symm
  dsimp [BasicOpenCocycleDatum.sectionLocalEquationsOfFibrewiseRegular,
    BasicOpenCocycleDatum.sectionLocalEquations]
  refine ⟨D.pointedCover, le_rfl, le_rfl, ?_⟩
  intro x
  let a : B →+* Γ(relCurve C B, D.pointedCover.opens x) :=
    (relCurve C B).overAlgebraMap B (D.pointedCover.opens x)
  refine ⟨Units.map a.toMonoidHom v, ?_⟩
  simp only []
  rw [hcomp]
  simp only [Scheme.overModule_smul_def]
  change (relCurve C B).resHom _ ((relCurve C B).resHom _ _) =
    (Units.map a.toMonoidHom v : Γ(relCurve C B, D.pointedCover.opens x)) *
      (relCurve C B).resHom _ ((relCurve C B).resHom _ _)
  simp only [map_mul, Scheme.resHom_resHom]
  congr 1
  change (relCurve C B).resHom _ ((relCurve C B).overAlgebraMap B _ (v : B)) =
    a (v : B)
  exact (relCurve C B).overAlgebraMap_apply_res B
    (homOfLE (le_of_eq (D.pointedCover_opens x))).op (v : B)

set_option maxHeartbeats 800000 in
-- The localized wrapper supplies the fibrewise nonvanishing hypotheses from the same generator
-- certificate used by the existing fixed-open divisor construction.
/-- The arbitrary-coefficient unit-rescaling bridge specialized to a basic open. -/
theorem baseOpenDatumSectionLocalEquations_divEq_of_unit
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f : P.cover.Carrier)
    (y y' : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0)
    (hy' : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y' ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0)
    (v : (Localization.Away f)ˣ)
    (hsec : P.datumSectionBaseChange (Localization.Away f) y' =
      (v : Localization.Away f) • P.datumSectionBaseChange (Localization.Away f) y) :
    Scheme.LocalEquations.DivEq
      (P.baseOpenDatumSectionLocalEquations f y hy)
      (P.baseOpenDatumSectionLocalEquations f y' hy') := by
  have hsec_y : ∀ q : PrimeSpectrum (Localization.Away f),
      (P.datum.baseChange (Localization.Away f)).sectionsMapTop q.asIdeal.ResidueField
        (P.datumSectionBaseChange (Localization.Away f) y) ≠ 0 :=
    fun q => P.sectionsMapTop_datumSectionBaseChange_away_ne_zero f y hy q
  have hsec_y' : ∀ q : PrimeSpectrum (Localization.Away f),
      (P.datum.baseChange (Localization.Away f)).sectionsMapTop q.asIdeal.ResidueField
        (P.datumSectionBaseChange (Localization.Away f) y') ≠ 0 :=
    fun q => P.sectionsMapTop_datumSectionBaseChange_away_ne_zero f y' hy' q
  simpa only [baseOpenDatumSectionLocalEquations] using
    (P.sectionLocalEquationsOfDatumSectionBaseChange_divEq_of_unit
      (Localization.Away f) y y' hsec_y hsec_y' v hsec)

set_option maxHeartbeats 800000 in
-- The unique-unit wrapper reuses the preceding non-vacuous generator and section bridges.
/-- The local equations are independent of the choice of nonvanishing rank-one generator on the
fixed basic open. -/
theorem baseOpenDatumSectionLocalEquations_divEq
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f : P.cover.Carrier)
    (y y' : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0)
    (hy' : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y' ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    Scheme.LocalEquations.DivEq
      (P.baseOpenDatumSectionLocalEquations f y hy)
      (P.baseOpenDatumSectionLocalEquations f y' hy') := by
  obtain ⟨v, hv, _⟩ :=
    P.existsUnique_unit_tensorAway_rankOne_generators f y y' hy hy'
  exact P.baseOpenDatumSectionLocalEquations_divEq_of_unit f y y' hy hy' v
    (P.datumSectionBaseChange_eq_smul_of_tensor_eq
      (Localization.Away f) y y' (v : Localization.Away f) hv)

/-- The widened divisor cut by a tied rank-one section on its basic open. -/
noncomputable def baseOpenRankOneDivisor
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f : P.cover.Carrier)
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    DivFamZarAff C (Localization.Away f) (genus C) :=
  divFamZarAffOfFibrewiseRegularLocalEquations C (genus C)
    (P.baseOpenDatumSectionLocalEquations f y hy) pi
    (P.baseOpenDatumSectionLocalEquations_fibrewiseRegular f y hy)
    (P.baseOpenDatumSectionLocalEquations_classDeg f y hy)

theorem baseOpenRankOneDivisor_eq
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f : P.cover.Carrier)
    (y y' : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0)
    (hy' : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y' ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    P.baseOpenRankOneDivisor f y hy = P.baseOpenRankOneDivisor f y' hy' := by
  unfold baseOpenRankOneDivisor
  apply DivFamZarAff.mk_eq_mk_iff.mpr
  exact P.baseOpenDatumSectionLocalEquations_divEq f y y' hy hy'

@[simp]
theorem baseOpenRankOneDivisor_picClass
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f : P.cover.Carrier)
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    (P.baseOpenRankOneDivisor f y hy).picClass =
      (P.datum.baseChange (Localization.Away f)).cechPicClass := by
  unfold baseOpenRankOneDivisor
  rw [picClass_divFamZarAffOfFibrewiseRegularLocalEquations]
  exact P.baseOpenDatumSectionLocalEquations_picClass f y hy

/-- The Abel value of the local divisor is the restriction of the input Picard datum.  This is
the immediate consumer which keeps the widened divisor tied to the chosen presentation. -/
theorem baseOpenRankOneDivisor_abelAff
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f : P.cover.Carrier)
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    abelDivAffPlus C (Localization.Away f) (P.baseOpenRankOneDivisor f y hy) =
      PicEtAff.mapAlg C ((Algebra.ofId P.cover.Carrier (Localization.Away f)).restrictScalars k)
        (PicEtAff.mapAlg C ((Algebra.ofId A P.cover.Carrier).restrictScalars k)
          (picEtAffineEquiv C A lam.1)) := by
  let B := Localization.Away f
  let iota : A →ₐ[k] P.cover.Carrier :=
    (Algebra.ofId A P.cover.Carrier).restrictScalars k
  let psi : P.cover.Carrier →ₐ[k] B :=
    (Algebra.ofId P.cover.Carrier B).restrictScalars k
  let F := P.baseOpenRankOneDivisor f y hy
  have hFclass : F.picClass = (P.datum.baseChange B).cechPicClass :=
    P.baseOpenRankOneDivisor_picClass f y hy
  have hrel : (relPicMk C (overSpec k B)) F.picClass =
      relPicAlgMap C psi (P.representative : relPic C (overSpec k P.cover.Carrier)) := by
    rw [hFclass, P.datum_class, relPicAlgMap_mk]
    have hcurve : Over.Hom.left (C ◁ Over.overSpecMap psi) =
        relCurveMap C P.cover.Carrier B := by
      refine congrArg (fun f : overSpec k B ⟶ overSpec k P.cover.Carrier => (C ◁ f).left) ?_
      exact Over.OverMorphism.ext rfl
    rw [P.datum.cechPicClass_baseChange B, hcurve]
    rfl
  calc
    abelDivAffPlus C B F = PicEtAff.unit C B ((relPicMk C (overSpec k B)) F.picClass) := rfl
    _ = PicEtAff.unit C B (relPicAlgMap C psi
      (P.representative : relPic C (overSpec k P.cover.Carrier))) := by rw [hrel]
    _ = PicEtAff.mapAlg C psi
      (PicEtAff.unit C P.cover.Carrier
        (P.representative : relPic C (overSpec k P.cover.Carrier))) := by
      rw [PicEtAff.mapAlg_unit]
    _ = PicEtAff.mapAlg C psi (PicEtAff.mapAlg C iota (picEtAffineEquiv C A lam.1)) := by
      congr 1
      rw [← P.represents, PicEtAff.mapAlg_mk_eq_unit_self]

/-- Every base point of a rank-one presentation has a tied local widened divisor.  The final
conjunct retains the native counit identity for the very same section. -/
theorem exists_baseOpen_rankOne_divisor_with_evaluation
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (p : PrimeSpectrum P.cover.Carrier) :
    ∃ f : P.cover.Carrier, f ∉ p.asIdeal ∧
      ∃ (y : Sheaf.HModule P.datum.sheaf 0)
        (hy : ∀ q : PrimeSpectrum P.cover.Carrier, f ∉ q.asIdeal →
          (y ⊗ₜ (1 : q.asIdeal.ResidueField) :
            Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
              q.asIdeal.ResidueField) ≠ 0),
        (P.baseOpenRankOneDivisor f y hy).picClass =
            (P.datum.baseChange (Localization.Away f)).cechPicClass ∧
          (Scheme.Modules.Hom.app P.evaluation
            ((relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
              (⊤ : (Spec (.of P.cover.Carrier)).Opens))).hom
            (P.evaluationLiftOfH0 y) = P.pushforwardSectionOfH0 y := by
  obtain ⟨f, hf, y, hy, heval⟩ := P.exists_baseOpen_evaluation_generator p
  exact ⟨f, hf, y, hy, P.baseOpenRankOneDivisor_picClass f y hy, heval⟩

/-- Every base point has one tied local divisor whose Abel value is the restriction of the
input class and whose defining section satisfies the native evaluation identity. -/
theorem exists_baseOpen_rankOne_divisor_with_abel_evaluation
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (p : PrimeSpectrum P.cover.Carrier) :
    ∃ f : P.cover.Carrier, f ∉ p.asIdeal ∧
      ∃ (y : Sheaf.HModule P.datum.sheaf 0)
        (hy : ∀ q : PrimeSpectrum P.cover.Carrier, f ∉ q.asIdeal →
          (y ⊗ₜ (1 : q.asIdeal.ResidueField) :
            Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
              q.asIdeal.ResidueField) ≠ 0),
        abelDivAffPlus C (Localization.Away f) (P.baseOpenRankOneDivisor f y hy) =
            PicEtAff.mapAlg C
              ((Algebra.ofId P.cover.Carrier (Localization.Away f)).restrictScalars k)
              (PicEtAff.mapAlg C ((Algebra.ofId A P.cover.Carrier).restrictScalars k)
                (picEtAffineEquiv C A lam.1)) ∧
          (P.baseOpenRankOneDivisor f y hy).picClass =
              (P.datum.baseChange (Localization.Away f)).cechPicClass ∧
            (Scheme.Modules.Hom.app P.evaluation
              ((relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
                (⊤ : (Spec (.of P.cover.Carrier)).Opens))).hom
              (P.evaluationLiftOfH0 y) = P.pushforwardSectionOfH0 y := by
  obtain ⟨f, hf, y, hy, hclass, heval⟩ :=
    P.exists_baseOpen_rankOne_divisor_with_evaluation p
  exact ⟨f, hf, y, hy, P.baseOpenRankOneDivisor_abelAff f y hy, hclass, heval⟩

/-! ## Finite away extraction -/

set_option maxHeartbeats 800000 in
-- The dependent finite-cover predicate repeats the localized divisor construction in full.
/-- A tied rank-one presentation carries local divisor/evaluation data on one finite basic-open
cover of its affine base.  The selected carriers span the unit ideal, and every member retains
the Abel restriction, datum Picard-class identity, and native evaluation identity of the
pointwise endpoint above.  This is only a finite extraction of presentation-local witnesses; it
does not glue the divisors or identify them with a global native zero locus. -/
theorem exists_fin_rankOne_away_divisor_with_abel_evaluation
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier] :
    ∃ (m : ℕ) (f : Fin m → P.cover.Carrier),
      Ideal.span (Set.range f) = ⊤ ∧
        ∀ i : Fin m,
          ∃ (y : Sheaf.HModule P.datum.sheaf 0)
            (hy : ∀ q : PrimeSpectrum P.cover.Carrier, f i ∉ q.asIdeal →
              (y ⊗ₜ (1 : q.asIdeal.ResidueField) :
                Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
                  q.asIdeal.ResidueField) ≠ 0),
            abelDivAffPlus C (Localization.Away (f i))
                (P.baseOpenRankOneDivisor (f i) y hy) =
                PicEtAff.mapAlg C
                  ((Algebra.ofId P.cover.Carrier (Localization.Away (f i))).restrictScalars k)
                  (PicEtAff.mapAlg C
                    ((Algebra.ofId A P.cover.Carrier).restrictScalars k)
                    (picEtAffineEquiv C A lam.1)) ∧
              (P.baseOpenRankOneDivisor (f i) y hy).picClass =
                (P.datum.baseChange (Localization.Away (f i))).cechPicClass ∧
              (Scheme.Modules.Hom.app P.evaluation
                ((relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
                  (⊤ : (Spec (.of P.cover.Carrier)).Opens))).hom
                (P.evaluationLiftOfH0 y) = P.pushforwardSectionOfH0 y := by
  obtain ⟨m, f, hspan, hgood⟩ :=
    exists_fin_span_eq_top_of_forall_prime (R := P.cover.Carrier)
      (fun f =>
        ∃ (y : Sheaf.HModule P.datum.sheaf 0)
          (hy : ∀ q : PrimeSpectrum P.cover.Carrier, f ∉ q.asIdeal →
            (y ⊗ₜ (1 : q.asIdeal.ResidueField) :
              Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
                q.asIdeal.ResidueField) ≠ 0),
          abelDivAffPlus C (Localization.Away f)
              (P.baseOpenRankOneDivisor f y hy) =
              PicEtAff.mapAlg C
                ((Algebra.ofId P.cover.Carrier (Localization.Away f)).restrictScalars k)
                (PicEtAff.mapAlg C
                  ((Algebra.ofId A P.cover.Carrier).restrictScalars k)
                  (picEtAffineEquiv C A lam.1)) ∧
            (P.baseOpenRankOneDivisor f y hy).picClass =
              (P.datum.baseChange (Localization.Away f)).cechPicClass ∧
            (Scheme.Modules.Hom.app P.evaluation
              ((relCurve C P.cover.Carrier ↘ Spec (.of P.cover.Carrier)) ⁻¹ᵁ
                (⊤ : (Spec (.of P.cover.Carrier)).Opens))).hom
              (P.evaluationLiftOfH0 y) = P.pushforwardSectionOfH0 y)
      (by
        intro p
        obtain ⟨f, hf, y, hy, habel, hclass, heval⟩ :=
          P.exists_baseOpen_rankOne_divisor_with_abel_evaluation p
        exact ⟨f, hf, y, hy, habel, hclass, heval⟩)
  exact ⟨m, f, hspan, hgood⟩

end PicRankOneLocalPresentation

end AlgebraicGeometry
