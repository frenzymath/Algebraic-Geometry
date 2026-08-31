/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveEffectivity
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveH0BaseChange
import AlgebraicJacobian.Picard.Pic0ChartLocusFibreField
import AlgebraicJacobian.Picard.DivSchemeFrameKit

/-!
# Away-local spreading of an admissible effective divisor

An H1-vanishing witness at one prime first spreads to a basic open.  On that open the
datum engine makes H0 finite projective.  A second basic open makes H0 free, and a basis
section stays nonzero on every field fibre.  The intrinsic equations cut by that section
therefore feed the arbitrary-affine widened effectivity constructor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

namespace BasicOpenCocycleDatum

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {B : Type u} [CommRing B] [Algebra k B]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

/-- A witness at one prime is contained in a basic open on which the datum-pair H1
fibre vanishes at every prime. -/
theorem exists_basicOpen_h1_vanishing
    (D : BasicOpenCocycleDatum C B pi)
    (hpi : pi ≫ P1.structureMap k = C.hom) (p : PrimeSpectrum B)
    (hp : D.HasWitnessH1Vanishing p.asIdeal.ResidueField) :
    ∃ h : B, h ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum B, h ∉ q.asIdeal →
      Subsingleton ((datumPair D).H1 ⊗[B] q.asIdeal.ResidueField) := by
  have hp' : Subsingleton ((datumPair D).H1 ⊗[B] p.asIdeal.ResidueField) :=
    (D.hasWitnessH1Vanishing_iff_subsingleton p.asIdeal.ResidueField).mp hp
  obtain ⟨U, ⟨h, rfl⟩, hpU, hU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp'
      (datumRigidEngine_isOpen_vanishing D hpi)
  refine ⟨h, (PrimeSpectrum.mem_basicOpen h p).mp hpU, fun q hq => ?_⟩
  exact hU ((PrimeSpectrum.mem_basicOpen h q).mpr hq)

/-- Fibrewise H1 vanishing on a basic open is the rigid-engine hypothesis for the
datum pulled to its away localization. -/
theorem hfib_baseChange_away
    (D : BasicOpenCocycleDatum C B pi) (h : B)
    (hvan : ∀ q : PrimeSpectrum B, h ∉ q.asIdeal →
      Subsingleton ((datumPair D).H1 ⊗[B] q.asIdeal.ResidueField))
    (q : PrimeSpectrum (Localization.Away h)) :
    Subsingleton ((datumPair (D.baseChange (Localization.Away h))).H1
      ⊗[Localization.Away h] q.asIdeal.ResidueField) := by
  let p : PrimeSpectrum B :=
    PrimeSpectrum.comap (algebraMap B (Localization.Away h)) q
  have hhp : h ∉ p.asIdeal := by
    intro hh
    refine q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem q.asIdeal
      (Ideal.mem_comap.mp hh) ?_)
    exact IsLocalization.Away.algebraMap_isUnit h
  have hp : Subsingleton ((datumPair D).H1 ⊗[B] p.asIdeal.ResidueField) :=
    hvan p hhp
  have hpw : D.HasWitnessH1Vanishing p.asIdeal.ResidueField :=
    (D.hasWitnessH1Vanishing_iff_subsingleton p.asIdeal.ResidueField).mpr hp
  have hunit : IsUnit (algebraMap B p.asIdeal.ResidueField h) :=
    isUnit_iff_ne_zero.mpr fun h0 =>
      hhp (Ideal.algebraMap_residueField_eq_zero.mp h0)
  letI : Algebra (Localization.Away h) p.asIdeal.ResidueField :=
    (IsLocalization.Away.lift (S := Localization.Away h) h hunit).toAlgebra
  haveI : IsScalarTower B (Localization.Away h) p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp])
  haveI : IsScalarTower k (Localization.Away h) p.asIdeal.ResidueField :=
    isScalarTower_left_of_isScalarTower (R₀ := B)
  have hcom : p.asIdeal = q.asIdeal.comap (algebraMap B (Localization.Away h)) := rfl
  let psi : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q.asIdeal
      (algebraMap B (Localization.Away h)) hcom
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := psi.toAlgebra
  haveI : IsScalarTower B p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra]
      ext b
      rw [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap,
        IsScalarTower.algebraMap_apply B (Localization.Away h)])
  have hDq : D.HasWitnessH1Vanishing q.asIdeal.ResidueField :=
    (D.hasWitnessH1Vanishing_iff_of_fieldExtension
      p.asIdeal.ResidueField q.asIdeal.ResidueField).mp hpw
  have hcl :
      Scheme.CechPic.map (relCurveMap C B q.asIdeal.ResidueField) D.cechPicClass =
        Scheme.CechPic.map
          (relCurveMap C (Localization.Away h) q.asIdeal.ResidueField)
          (D.baseChange (Localization.Away h)).cechPicClass := by
    rw [D.cechPicClass_baseChange (Localization.Away h),
      ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
      relCurveMap_comp]
  have hDq' : (D.baseChange (Localization.Away h)).HasWitnessH1Vanishing
      q.asIdeal.ResidueField :=
    (D.hasWitnessH1Vanishing_congr_of_cechPicClass_eq
      (D.baseChange (Localization.Away h)) q.asIdeal.ResidueField hcl).mp hDq
  exact ((D.baseChange (Localization.Away h)).hasWitnessH1Vanishing_iff_subsingleton
    q.asIdeal.ResidueField).mp hDq'

/-- If a module has a nontrivial fibre at `p`, its base change to any away
neighbourhood of `p` is nontrivial. -/
theorem nontrivial_away_tensor_of_nontrivial_fibre
    {Q : Type u} [AddCommGroup Q] [Module B Q]
    (p : PrimeSpectrum B) (h : B) (hh : h ∉ p.asIdeal)
    (hp : Nontrivial (p.asIdeal.ResidueField ⊗[B] Q)) :
    Nontrivial (Localization.Away h ⊗[B] Q) := by
  have hunit : IsUnit (algebraMap B p.asIdeal.ResidueField h) :=
    isUnit_iff_ne_zero.mpr fun h0 =>
      hh (Ideal.algebraMap_residueField_eq_zero.mp h0)
  letI : Algebra (Localization.Away h) p.asIdeal.ResidueField :=
    (IsLocalization.Away.lift (S := Localization.Away h) h hunit).toAlgebra
  haveI : IsScalarTower B (Localization.Away h) p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp])
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have hleft : Subsingleton (p.asIdeal.ResidueField ⊗[Localization.Away h]
      (Localization.Away h ⊗[B] Q)) := inferInstance
  have hright : Subsingleton (p.asIdeal.ResidueField ⊗[B] Q) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B (Localization.Away h)
      p.asIdeal.ResidueField p.asIdeal.ResidueField Q).toEquiv.subsingleton_congr.mp hleft
  exact (not_subsingleton (p.asIdeal.ResidueField ⊗[B] Q)) hright

noncomputable local instance instIsIntegralRelCurveSpread
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveSpread
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQuasiCompactRelCurveSpread
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instFiniteH0RelCurveSpread
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFiniteH1RelCurveSpread
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

/-- A pulled datum class has unchanged degree at a prime lying over the base prime. -/
theorem classDeg_map_residueField_of_comap
    (D : BasicOpenCocycleDatum C B pi)
    {S : Type u} [CommRing S] [Algebra k S] [Algebra B S]
    [IsScalarTower k B S] (p : PrimeSpectrum B) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap B S) q = p) (n : ℕ)
    (hdegp : classDeg p.asIdeal.ResidueField
      (Scheme.CechPic.map (relCurveMap C B p.asIdeal.ResidueField)
        D.cechPicClass) = (n : ℤ)) :
    classDeg q.asIdeal.ResidueField
      (Scheme.CechPic.map (relCurveMap C B q.asIdeal.ResidueField)
        D.cechPicClass) = (n : ℤ) := by
  have hcom : p.asIdeal = q.asIdeal.comap (algebraMap B S) := by
    simpa using congrArg PrimeSpectrum.asIdeal hq.symm
  let rho : p.asIdeal.ResidueField →ₐ[k] q.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal
      (IsScalarTower.toAlgHom k B S) hcom
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    rho.toRingHom.toAlgebra
  haveI : IsScalarTower k p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x => (rho.commutes x).symm
  haveI : IsScalarTower B p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap B q.asIdeal.ResidueField x =
        rho (algebraMap B p.asIdeal.ResidueField x)
      rw [Ideal.ResidueField.mapₐ_apply, Ideal.ResidueField.map_algebraMap]
      exact IsScalarTower.algebraMap_apply B S q.asIdeal.ResidueField x
  have hcurve : (C ◁ Over.overSpecMap rho).left =
      relCurveMap C p.asIdeal.ResidueField q.asIdeal.ResidueField := by
    refine congrArg
      (fun t : overSpec k q.asIdeal.ResidueField ⟶
        overSpec k p.asIdeal.ResidueField => (C ◁ t).left) ?_
    exact Over.OverMorphism.ext rfl
  have hinv := classDeg_cechPicMap_baseFieldTransition C rho
    (Scheme.CechPic.map (relCurveMap C B p.asIdeal.ResidueField)
      D.cechPicClass)
  rw [hcurve] at hinv
  have hpic : Scheme.CechPic.map
      (relCurveMap C p.asIdeal.ResidueField q.asIdeal.ResidueField)
      (Scheme.CechPic.map (relCurveMap C B p.asIdeal.ResidueField)
        D.cechPicClass) =
      Scheme.CechPic.map (relCurveMap C B q.asIdeal.ResidueField)
        D.cechPicClass := by
    rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, relCurveMap_comp]
  exact (congrArg (classDeg q.asIdeal.ResidueField) hpic.symm).trans
    (hinv.trans hdegp)

/-- At degree at least the genus, H1 vanishing makes datum H0 nontrivial. -/
theorem nontrivial_hModule_zero_of_degree_of_h1
    (D : BasicOpenCocycleDatum C B pi)
    (L : Type u) [Field L] [Algebra k L] [Algebra B L]
    [IsScalarTower k B L] (n g : ℕ)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hdeg : classDeg L (D.baseChange L).cechPicClass = (n : ℤ))
    (hgn : g ≤ n)
    (hsub : Subsingleton (Sheaf.HModule (D.baseChange L).sheaf 1)) :
    Nontrivial (Sheaf.HModule (D.baseChange L).sheaf 0) := by
  set P : (relCurve C L).MeromorphicPresentation :=
    Scheme.MeromorphicPresentation.ofCocycle (D.baseChange L).pointedCover
      (gluedSubordCocycle (D.baseChange L).isGluingCocycle
        (D.baseChange L).pointedCover (D.baseChange L).pieceIndex
        fun _ => le_rfl) with hP
  have hsubP : Subsingleton (Sheaf.HModule (P.gluedSheaf L) 1) :=
    (Sheaf.HModule.mapEquiv
      (BasicOpenCocycleDatum.presentationSheafIso (D.baseChange L))
      1).toEquiv.subsingleton_congr.mp hsub
  have h0eq : Sheaf.h0 (D.baseChange L).sheaf = Sheaf.h0 (P.gluedSheaf L) :=
    Sheaf.h0_congr
      (BasicOpenCocycleDatum.presentationSheafIso (D.baseChange L))
  have hformula := h0_gluedSheaf_eq_classDeg_add_chi L P hsubP
  have hPclass : P.picClass = (D.baseChange L).cechPicClass := rfl
  have hint : (Sheaf.h0 (D.baseChange L).sheaf : ℤ) =
      (n : ℤ) + 1 - (g : ℤ) := by
    rw [h0eq, hformula, hPclass, hdeg,
      chi_relCurve_baseField C L g hchi]
    ring
  have hposZ : (0 : ℤ) < (Sheaf.h0 (D.baseChange L).sheaf : ℤ) := by
    rw [hint]
    omega
  have hpos : 0 < Sheaf.h0 (D.baseChange L).sheaf := by
    exact_mod_cast hposZ
  exact Module.nontrivial_of_finrank_pos hpos

/-- With H1 zero, Riemann--Roch recovers degree from the H0 dimension. -/
theorem classDeg_baseChange_eq_h0_sub_chi
    (D : BasicOpenCocycleDatum C B pi)
    (L : Type u) [Field L] [Algebra k L] [Algebra B L]
    [IsScalarTower k B L] (g : ℕ)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hsub : Subsingleton (Sheaf.HModule (D.baseChange L).sheaf 1)) :
    classDeg L (D.baseChange L).cechPicClass =
      (Sheaf.h0 (D.baseChange L).sheaf : ℤ) - (1 - (g : ℤ)) := by
  set P : (relCurve C L).MeromorphicPresentation :=
    Scheme.MeromorphicPresentation.ofCocycle (D.baseChange L).pointedCover
      (gluedSubordCocycle (D.baseChange L).isGluingCocycle
        (D.baseChange L).pointedCover (D.baseChange L).pieceIndex
        fun _ => le_rfl) with hP
  have hsubP : Subsingleton (Sheaf.HModule (P.gluedSheaf L) 1) :=
    (Sheaf.HModule.mapEquiv
      (BasicOpenCocycleDatum.presentationSheafIso (D.baseChange L))
      1).toEquiv.subsingleton_congr.mp hsub
  have h0eq : Sheaf.h0 (D.baseChange L).sheaf = Sheaf.h0 (P.gluedSheaf L) :=
    Sheaf.h0_congr
      (BasicOpenCocycleDatum.presentationSheafIso (D.baseChange L))
  have hformula := h0_gluedSheaf_eq_classDeg_add_chi L P hsubP
  have hPclass : P.picClass = (D.baseChange L).cechPicClass := rfl
  rw [h0eq, hformula, hPclass, chi_relCurve_baseField C L g hchi]
  ring

/-- Free H0 and vanishing H1 make one field-fibre degree valid on every fibre. -/
theorem classDeg_baseChange_eq_of_freeH0_of_one
    (D : BasicOpenCocycleDatum C B pi)
    [Module.Free B (Sheaf.HModule D.sheaf 0)] (g n : ℕ)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hH1 : Subsingleton (datumPair D).H1)
    (K : Type u) [Field K] [Algebra k K] [Algebra B K]
    [IsScalarTower k B K]
    (hdegK : classDeg K (D.baseChange K).cechPicClass = (n : ℤ)) :
    ∀ (L : Type u) [Field L] [Algebra k L] [Algebra B L]
      [IsScalarTower k B L],
      classDeg L (D.baseChange L).cechPicClass = (n : ℤ) := by
  letI : Nontrivial B := RingHom.domain_nontrivial (algebraMap B K)
  intro L _ _ _ _
  have hsubL : Subsingleton (Sheaf.HModule (D.baseChange L).sheaf 1) :=
    D.datum_subsingleton_h1_baseChange L hH1
  have hsubK : Subsingleton (Sheaf.HModule (D.baseChange K).sheaf 1) :=
    D.datum_subsingleton_h1_baseChange K hH1
  have h0eq : Sheaf.h0 (D.baseChange L).sheaf =
      Sheaf.h0 (D.baseChange K).sheaf := by
    change Module.finrank L (Sheaf.HModule (D.baseChange L).sheaf 0) =
      Module.finrank K (Sheaf.HModule (D.baseChange K).sheaf 0)
    calc
      _ = Module.finrank L (L ⊗[B] Sheaf.HModule D.sheaf 0) :=
        (D.datumH0BaseChange L hH1).finrank_eq.symm
      _ = Module.finrank B (Sheaf.HModule D.sheaf 0) := Module.finrank_baseChange
      _ = Module.finrank K (K ⊗[B] Sheaf.HModule D.sheaf 0) :=
        Module.finrank_baseChange.symm
      _ = _ := (D.datumH0BaseChange K hH1).finrank_eq
  calc
    _ = (Sheaf.h0 (D.baseChange L).sheaf : ℤ) - (1 - (g : ℤ)) :=
      D.classDeg_baseChange_eq_h0_sub_chi L g hchi hsubL
    _ = (Sheaf.h0 (D.baseChange K).sheaf : ℤ) - (1 - (g : ℤ)) := by
      rw [h0eq]
    _ = classDeg K (D.baseChange K).cechPicClass :=
      (D.classDeg_baseChange_eq_h0_sub_chi K g hchi hsubK).symm
    _ = (n : ℤ) := hdegK
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 800000 in
-- The two localization stages synthesize large sheaf and scalar-tower terms.
/-- An admissible H1-vanishing fibre spreads across two away localizations to a
widened divisor family whose class is the pullback of the original datum class.
The returned prime of the final base lies over the chosen input prime. -/
theorem exists_away_away_divFamZarAff_of_admissible_fibre
    (D : BasicOpenCocycleDatum C B pi) [IsNoetherianRing B]
    (hpi : pi ≫ P1.structureMap k = C.hom) (n g : ℕ)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hgn : g ≤ n)
    (p : PrimeSpectrum B) (hp : D.HasWitnessH1Vanishing p.asIdeal.ResidueField)
    (hdegp : classDeg p.asIdeal.ResidueField
      (Scheme.CechPic.map (relCurveMap C B p.asIdeal.ResidueField)
        D.cechPicClass) = (n : ℤ)) :
    ∃ h : B, h ∉ p.asIdeal ∧
      ∃ q₁ : PrimeSpectrum (Localization.Away h),
        PrimeSpectrum.comap (algebraMap B (Localization.Away h)) q₁ = p ∧
        ∃ f : Localization.Away h, f ∉ q₁.asIdeal ∧
          ∃ q₂ : PrimeSpectrum (Localization.Away f),
            PrimeSpectrum.comap (algebraMap B (Localization.Away f)) q₂ = p ∧
            ∃ F : DivFamZarAff C (Localization.Away f) n,
              F.picClass = Scheme.CechPic.map
                (relCurveMap C B (Localization.Away f)) D.cechPicClass := by
  obtain ⟨h, hh, hvan⟩ := D.exists_basicOpen_h1_vanishing hpi p hp
  obtain ⟨q₁, hq₁⟩ : p ∈ Set.range
      (PrimeSpectrum.comap (algebraMap B (Localization.Away h))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away h) h]
    exact hh
  let D₁ : BasicOpenCocycleDatum C (Localization.Away h) pi :=
    D.baseChange (Localization.Away h)
  have hfib₁ : ∀ q : PrimeSpectrum (Localization.Away h),
      Subsingleton ((datumPair D₁).H1 ⊗[Localization.Away h]
        q.asIdeal.ResidueField) := by
    intro q
    exact D.hfib_baseChange_away h hvan q
  obtain ⟨-, hfin₁, hproj₁⟩ := datumRigidEngine D₁ hpi hfib₁
  letI : Module.Finite (Localization.Away h) (Sheaf.HModule D₁.sheaf 0) := hfin₁
  letI : Module.Projective (Localization.Away h) (Sheaf.HModule D₁.sheaf 0) := hproj₁
  have hH1₁ : Subsingleton (datumPair D₁).H1 :=
    datum_subsingleton_pairH1 D₁ hpi hfib₁
  have hdeg₁ : classDeg q₁.asIdeal.ResidueField
      (D₁.baseChange q₁.asIdeal.ResidueField).cechPicClass = (n : ℤ) := by
    rw [D₁.cechPicClass_baseChange q₁.asIdeal.ResidueField]
    rw [show D₁.cechPicClass = Scheme.CechPic.map
        (relCurveMap C B (Localization.Away h)) D.cechPicClass from
          D.cechPicClass_baseChange (Localization.Away h),
      ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, relCurveMap_comp]
    exact D.classDeg_map_residueField_of_comap p q₁ hq₁ n hdegp
  have hsub₁ : Subsingleton
      (Sheaf.HModule (D₁.baseChange q₁.asIdeal.ResidueField).sheaf 1) :=
    D₁.datum_subsingleton_h1_baseChange q₁.asIdeal.ResidueField hH1₁
  have hnonzero₁ : Nontrivial
      (Sheaf.HModule (D₁.baseChange q₁.asIdeal.ResidueField).sheaf 0) :=
    D₁.nontrivial_hModule_zero_of_degree_of_h1 q₁.asIdeal.ResidueField
      n g hchi hdeg₁ hgn hsub₁
  have hnontrivialFibre : Nontrivial
      (q₁.asIdeal.ResidueField ⊗[Localization.Away h]
        Sheaf.HModule D₁.sheaf 0) :=
    (D₁.datumH0BaseChange q₁.asIdeal.ResidueField hH1₁).toEquiv.nontrivial_congr.mpr
      hnonzero₁
  obtain ⟨f, hf, hfree⟩ := Grassmannian.exists_away_free
    (Q := Sheaf.HModule D₁.sheaf 0) q₁
  obtain ⟨q₂, hq₂'⟩ : q₁ ∈ Set.range
      (PrimeSpectrum.comap
        (algebraMap (Localization.Away h) (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact hf
  have hq₂ : PrimeSpectrum.comap (algebraMap B (Localization.Away f)) q₂ = p := by
    rw [IsScalarTower.algebraMap_eq B (Localization.Away h) (Localization.Away f),
      PrimeSpectrum.comap_comp]
    change PrimeSpectrum.comap (algebraMap B (Localization.Away h))
      (PrimeSpectrum.comap
        (algebraMap (Localization.Away h) (Localization.Away f)) q₂) = p
    rw [hq₂', hq₁]
  let D₂ : BasicOpenCocycleDatum C (Localization.Away f) pi :=
    D₁.baseChange (Localization.Away f)
  have hH1sheaf₂ : Subsingleton (Sheaf.HModule D₂.sheaf 1) :=
    D₁.datum_subsingleton_h1_baseChange (Localization.Away f) hH1₁
  have hH1₂ : Subsingleton (datumPair D₂).H1 :=
    (subsingleton_datumPair_h1_iff D₂).mpr hH1sheaf₂
  let Q₂ := Localization.Away f ⊗[Localization.Away h]
    Sheaf.HModule D₁.sheaf 0
  letI : Module.Free (Localization.Away f) Q₂ := hfree
  letI : Nontrivial Q₂ :=
    nontrivial_away_tensor_of_nontrivial_fibre q₁ f hf hnontrivialFibre
  let b := Module.Free.chooseBasis (Localization.Away f) Q₂
  let i₀ := b.index_nonempty.some
  let t : Q₂ := b i₀
  let e₂ : Q₂ ≃ₗ[Localization.Away f] Sheaf.HModule D₂.sheaf 0 :=
    D₁.datumH0BaseChange (Localization.Away f) hH1₁
  let y₂ : Sheaf.HModule D₂.sheaf 0 := e₂ t
  have hy₂ : ∀ (L : Type u) [Field L] [Algebra k L]
      [Algebra (Localization.Away f) L]
      [IsScalarTower k (Localization.Away f) L],
      (1 : L) ⊗ₜ[Localization.Away f] y₂ ≠ 0 := by
    intro L _ _ _ _
    have ht : ((1 : L) ⊗ₜ[Localization.Away f] t : L ⊗[Localization.Away f] Q₂)
        ≠ 0 := by
      rw [← Module.Basis.baseChange_apply L b i₀]
      exact (b.baseChange L).ne_zero i₀
    let eL := LinearEquiv.baseChange (Localization.Away f) L Q₂
      (Sheaf.HModule D₂.sheaf 0) e₂
    intro hy
    apply ht
    apply eL.injective
    rw [LinearEquiv.baseChange_tmul, map_zero, hy]
  let s₂ : ↥(gluedSubmodule (Localization.Away f) D₂.pieces D₂.unit ⊤) :=
    Sheaf.HModule.linearEquiv₀
      (Opens.grothendieckTopology ((relCurve C (Localization.Away f) : Scheme.{u}) : TopCat))
      isTerminalTop D₂.sheaf y₂
  have hs₂ : ∀ (L : Type u) [Field L] [Algebra k L]
      [Algebra (Localization.Away f) L]
      [IsScalarTower k (Localization.Away f) L],
      D₂.sectionsMapTop L s₂ ≠ 0 := by
    intro L _ _ _ _
    have hbc : D₂.datumH0BaseChange L hH1₂
        ((1 : L) ⊗ₜ[Localization.Away f] y₂) ≠ 0 :=
      fun hzero => (hy₂ L) ((D₂.datumH0BaseChange L hH1₂).injective (by
        rw [hzero, map_zero]))
    have htop : Sheaf.HModule.linearEquiv₀
        (Opens.grothendieckTopology ((relCurve C L : Scheme.{u}) : TopCat))
        isTerminalTop (D₂.baseChange L).sheaf
        (D₂.datumH0BaseChange L hH1₂
          ((1 : L) ⊗ₜ[Localization.Away f] y₂)) ≠ 0 :=
      fun hzero => hbc ((Sheaf.HModule.linearEquiv₀
        (Opens.grothendieckTopology ((relCurve C L : Scheme.{u}) : TopCat))
        isTerminalTop (D₂.baseChange L).sheaf).injective (by
          rw [hzero, map_zero]))
    rw [D₂.linearEquiv₀_datumH0BaseChange_one_tmul L hH1₂ y₂] at htop
    exact htop
  have hcomponent : ∀ (j : D₂.index) (q : PrimeSpectrum (Localization.Away f)),
      Function.Injective
        ((Scheme.mulSectionEnd (Localization.Away f) (D₂.component s₂ j)).rTensor
          q.asIdeal.ResidueField) := by
    intro j q
    exact D₂.injective_rTensor_component_of_sectionsMapTop_ne_zero
      s₂ q (hs₂ q.asIdeal.ResidueField) j
  let d : (relCurve C (Localization.Away f)).LocalEquations :=
    D₂.sectionLocalEquationsOfFibrewiseRegular s₂ hcomponent
  have hreg : ∀ (L : Type u) [Field L] [Algebra k L]
      [Algebra (Localization.Away f) L]
      [IsScalarTower k (Localization.Away f) L], ∀ z : relCurve C L,
      ((relCurve C L).presheaf.germ
        ((d.cover.pullback (relCurveMap C (Localization.Away f) L)).opens z) z
        ((d.cover.pullback
          (relCurveMap C (Localization.Away f) L)).mem_opens z)).hom
        (Scheme.LocalEquations.pullbackEqn
          (relCurveMap C (Localization.Away f) L) d z) ∈
          nonZeroDivisors ((relCurve C L).presheaf.stalk z) := by
    intro L _ _ _ _ z
    exact D₂.germ_self_pullbackEqn_sectionLocalEquationsOfFibrewiseRegular
      s₂ hcomponent L z
  have hclassD₂ : D₂.cechPicClass = Scheme.CechPic.map
      (relCurveMap C B (Localization.Away f)) D.cechPicClass := by
    rw [show D₂.cechPicClass = Scheme.CechPic.map
        (relCurveMap C (Localization.Away h) (Localization.Away f))
        D₁.cechPicClass from D₁.cechPicClass_baseChange (Localization.Away f),
      show D₁.cechPicClass = Scheme.CechPic.map
        (relCurveMap C B (Localization.Away h)) D.cechPicClass from
          D.cechPicClass_baseChange (Localization.Away h),
      ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
      relCurveMap_comp]
  have hdegq₂ : classDeg q₂.asIdeal.ResidueField
      (D₂.baseChange q₂.asIdeal.ResidueField).cechPicClass = (n : ℤ) := by
    rw [D₂.cechPicClass_baseChange q₂.asIdeal.ResidueField, hclassD₂,
      ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, relCurveMap_comp]
    exact D.classDeg_map_residueField_of_comap p q₂ hq₂ n hdegp
  letI : Module.Free (Localization.Away f) (Sheaf.HModule D₂.sheaf 0) :=
    Module.Free.of_equiv e₂
  have hdeg₂ : ∀ (L : Type u) [Field L] [Algebra k L]
      [Algebra (Localization.Away f) L]
      [IsScalarTower k (Localization.Away f) L],
      classDeg L
        (Scheme.CechPic.map (relCurveMap C (Localization.Away f) L) d.picClass) =
          (n : ℤ) := by
    intro L _ _ _ _
    rw [show d.picClass = D₂.cechPicClass from
        D₂.sectionLocalEquationsOfFibrewiseRegular_picClass s₂ hcomponent,
      ← D₂.cechPicClass_baseChange L]
    exact D₂.classDeg_baseChange_eq_of_freeH0_of_one
      g n hchi hH1₂ q₂.asIdeal.ResidueField hdegq₂ L
  let F : DivFamZarAff C (Localization.Away f) n :=
    divFamZarAffOfFibrewiseRegularLocalEquations C n d pi hreg hdeg₂
  refine ⟨h, hh, q₁, hq₁, f, hf, q₂, hq₂, F, ?_⟩
  rw [show F.picClass = d.picClass from
      picClass_divFamZarAffOfFibrewiseRegularLocalEquations C n d pi hreg hdeg₂,
    show d.picClass = D₂.cechPicClass from
      D₂.sectionLocalEquationsOfFibrewiseRegular_picClass s₂ hcomponent,
    hclassD₂]

end BasicOpenCocycleDatum

end AlgebraicGeometry
