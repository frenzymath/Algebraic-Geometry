/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveSpread
import AlgebraicJacobian.Picard.DivRepAwayPush
import AlgebraicJacobian.Cohomology.DatumDescent

/-!
# Descent of the admissible away-local divisor family

The Noetherian spreading theorem applies after descending a cocycle datum to a finitely
generated subalgebra.  Its two principal localizations are pushed back to the original base,
where they form an etale algebra carrying the same widened divisor family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  TopologicalSpace Opposite

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

noncomputable local instance instIsIntegralRelCurveSpreadDescent
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveSpreadDescent
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQuasiCompactRelCurveSpreadDescent
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instFiniteH0RelCurveSpreadDescent
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFiniteH1RelCurveSpreadDescent
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option maxHeartbeats 4000000 in
-- Residue-field descent and the two localization towers elaborate large sheaf terms.
set_option synthInstance.maxHeartbeats 800000 in
/-- An admissible fibre of a cocycle datum over an arbitrary affine base lifts to a widened
divisor family after an etale base change, with a chosen prime above the input prime. -/
theorem exists_etale_divFamZarAff_of_admissible_fibre
    (D : BasicOpenCocycleDatum C B pi)
    (hpi : pi ≫ P1.structureMap k = C.hom) (n g : ℕ)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hgn : g ≤ n)
    (hdeg : ∀ (K : Type u) [Field K] [Algebra k K] [Algebra B K]
      [IsScalarTower k B K],
      classDeg K (Scheme.CechPic.map (relCurveMap C B K) D.cechPicClass) =
        (n : ℤ))
    (p : PrimeSpectrum B)
    (hp : D.HasWitnessH1Vanishing p.asIdeal.ResidueField) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra B S)
      (_ : IsScalarTower k B S) (_ : Algebra.Etale B S)
      (q : PrimeSpectrum S),
      PrimeSpectrum.comap (algebraMap B S) q = p ∧
        ∃ F : DivFamZarAff C S n,
          F.picClass = Scheme.CechPic.map (relCurveMap C B S) D.cechPicClass := by
  obtain ⟨B₀, -, hnoeth, D₀, hbc⟩ := D.exists_fg_isNoetherianRing_baseChange_eq
  letI : IsNoetherianRing (↑B₀) := hnoeth
  let phi : (↑B₀) →ₐ[k] B := IsScalarTower.toAlgHom k (↑B₀) B
  let p₀ : PrimeSpectrum (↑B₀) :=
    PrimeSpectrum.comap (algebraMap (↑B₀) B) p
  have hcom : p₀.asIdeal = p.asIdeal.comap (algebraMap (↑B₀) B) := rfl
  let rho : p₀.asIdeal.ResidueField →ₐ[k] p.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ p₀.asIdeal p.asIdeal phi hcom
  letI : Algebra p₀.asIdeal.ResidueField p.asIdeal.ResidueField :=
    rho.toRingHom.toAlgebra
  haveI : IsScalarTower k p₀.asIdeal.ResidueField p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x => (rho.commutes x).symm
  haveI : IsScalarTower (↑B₀) p₀.asIdeal.ResidueField
      p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap (↑B₀) p.asIdeal.ResidueField x =
        rho (algebraMap (↑B₀) p₀.asIdeal.ResidueField x)
      rw [Ideal.ResidueField.mapₐ_apply, Ideal.ResidueField.map_algebraMap]
      exact IsScalarTower.algebraMap_apply (↑B₀) B p.asIdeal.ResidueField x
  have hclp : Scheme.CechPic.map
      (relCurveMap C (↑B₀) p.asIdeal.ResidueField) D₀.cechPicClass =
      Scheme.CechPic.map
        (relCurveMap C B p.asIdeal.ResidueField) D.cechPicClass := by
    rw [descent_cechPicClass (C := C) (B := B) hbc,
      ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, relCurveMap_comp]
  have hpD₀ : D₀.HasWitnessH1Vanishing p.asIdeal.ResidueField :=
    (D₀.hasWitnessH1Vanishing_congr_of_cechPicClass_eq
      D p.asIdeal.ResidueField hclp).mpr hp
  have hp₀ : D₀.HasWitnessH1Vanishing p₀.asIdeal.ResidueField :=
    (D₀.hasWitnessH1Vanishing_iff_of_fieldExtension
      p₀.asIdeal.ResidueField p.asIdeal.ResidueField).mpr hpD₀
  have hcurve : (C ◁ Over.overSpecMap rho).left =
      relCurveMap C p₀.asIdeal.ResidueField p.asIdeal.ResidueField := by
    refine congrArg
      (fun t : overSpec k p.asIdeal.ResidueField ⟶
        overSpec k p₀.asIdeal.ResidueField => (C ◁ t).left) ?_
    exact Over.OverMorphism.ext rfl
  have hclass : Scheme.CechPic.map
      (relCurveMap C p₀.asIdeal.ResidueField p.asIdeal.ResidueField)
        (Scheme.CechPic.map
          (relCurveMap C (↑B₀) p₀.asIdeal.ResidueField)
          D₀.cechPicClass) =
      Scheme.CechPic.map
        (relCurveMap C B p.asIdeal.ResidueField) D.cechPicClass := by
    rw [descent_cechPicClass (C := C) (B := B) hbc,
      ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, relCurveMap_comp,
      ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, relCurveMap_comp]
  have hinv := classDeg_cechPicMap_baseFieldTransition C rho
    (Scheme.CechPic.map
      (relCurveMap C (↑B₀) p₀.asIdeal.ResidueField) D₀.cechPicClass)
  rw [hcurve] at hinv
  have hdeg₀ : classDeg p₀.asIdeal.ResidueField
      (Scheme.CechPic.map
        (relCurveMap C (↑B₀) p₀.asIdeal.ResidueField)
        D₀.cechPicClass) = (n : ℤ) := by
    calc
      _ = classDeg p.asIdeal.ResidueField
          (Scheme.CechPic.map
            (relCurveMap C p₀.asIdeal.ResidueField p.asIdeal.ResidueField)
            (Scheme.CechPic.map
              (relCurveMap C (↑B₀) p₀.asIdeal.ResidueField)
              D₀.cechPicClass)) := hinv.symm
      _ = classDeg p.asIdeal.ResidueField
          (Scheme.CechPic.map
            (relCurveMap C B p.asIdeal.ResidueField) D.cechPicClass) := by
        rw [hclass]
      _ = (n : ℤ) := hdeg p.asIdeal.ResidueField
  obtain ⟨h, hh, q₁, hq₁, f, hf, q₂, hq₂, F₀, hF₀⟩ :=
    D₀.exists_away_away_divFamZarAff_of_admissible_fibre
      hpi n g hchi hgn p₀ hp₀ hdeg₀
  let B₁ := Localization.Away (phi h)
  let phi₁ : Localization.Away h →ₐ[k] B₁ := Localization.awayMapₐ phi h
  let S := Localization.Away (phi₁ f)
  let phi₂ : Localization.Away f →ₐ[k] S := Localization.awayMapₐ phi₁ f
  let algBS : Algebra B S :=
    ((algebraMap B₁ S).comp (algebraMap B B₁)).toAlgebra
  letI : Algebra B S := algBS
  letI : SMul B S := algBS.toSMul
  haveI towerBB₁S : IsScalarTower B B₁ S :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI towerkBS : IsScalarTower k B S :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_assoc,
        ← IsScalarTower.algebraMap_eq k B B₁,
        ← IsScalarTower.algebraMap_eq k B₁ S])
  letI : Algebra.Etale B B₁ := Algebra.Etale.of_isLocalizationAway (phi h)
  letI : Algebra.Etale B₁ S := Algebra.Etale.of_isLocalizationAway (phi₁ f)
  letI : Algebra.Etale B S := Algebra.Etale.comp B B₁ S
  have hph : phi h ∉ p.asIdeal := by
    intro hmem
    apply hh
    exact hmem
  obtain ⟨q₁B, hq₁B⟩ : p ∈ Set.range
      (PrimeSpectrum.comap (algebraMap B B₁)) := by
    rw [PrimeSpectrum.localization_away_comap_range B₁ (phi h)]
    exact hph
  have hq₁push : PrimeSpectrum.comap phi₁.toRingHom q₁B = q₁ := by
    apply PrimeSpectrum.localization_comap_injective
      (Localization.Away h) (Submonoid.powers h)
    have hsquare : phi₁.toRingHom.comp
        (algebraMap (↑B₀) (Localization.Away h)) =
        (algebraMap B B₁).comp (algebraMap (↑B₀) B) := by
      ext x
      exact DivFamZar.awayMapₐ_algebraMap phi h x
    calc
      PrimeSpectrum.comap (algebraMap (↑B₀) (Localization.Away h))
          (PrimeSpectrum.comap phi₁.toRingHom q₁B) =
          PrimeSpectrum.comap
            (phi₁.toRingHom.comp
              (algebraMap (↑B₀) (Localization.Away h))) q₁B :=
        (congrFun (PrimeSpectrum.comap_comp
          (algebraMap (↑B₀) (Localization.Away h)) phi₁.toRingHom) q₁B).symm
      _ = PrimeSpectrum.comap
          ((algebraMap B B₁).comp (algebraMap (↑B₀) B)) q₁B := by
        rw [hsquare]
      _ = PrimeSpectrum.comap (algebraMap (↑B₀) B)
          (PrimeSpectrum.comap (algebraMap B B₁) q₁B) :=
        congrFun (PrimeSpectrum.comap_comp
          (algebraMap (↑B₀) B) (algebraMap B B₁)) q₁B
      _ = p₀ := by rw [hq₁B]
      _ = PrimeSpectrum.comap
          (algebraMap (↑B₀) (Localization.Away h)) q₁ := hq₁.symm
  have hfB : phi₁ f ∉ q₁B.asIdeal := by
    intro hmem
    apply hf
    have : f ∈ (PrimeSpectrum.comap phi₁.toRingHom q₁B).asIdeal := hmem
    rwa [hq₁push] at this
  obtain ⟨q, hq⟩ : q₁B ∈ Set.range
      (PrimeSpectrum.comap (algebraMap B₁ S)) := by
    rw [PrimeSpectrum.localization_away_comap_range S (phi₁ f)]
    exact hfB
  have hqB : PrimeSpectrum.comap (algebraMap B S) q = p := by
    rw [IsScalarTower.algebraMap_eq B B₁ S, PrimeSpectrum.comap_comp]
    change PrimeSpectrum.comap (algebraMap B B₁)
      (PrimeSpectrum.comap (algebraMap B₁ S) q) = p
    rw [hq, hq₁B]
  let algA₂S : Algebra (Localization.Away f) S := phi₂.toRingHom.toAlgebra
  letI : Algebra (Localization.Away f) S := algA₂S
  letI : SMul (Localization.Away f) S := algA₂S.toSMul
  haveI towerKA₂S : IsScalarTower k (Localization.Away f) S :=
    IsScalarTower.of_algebraMap_eq fun x => (phi₂.commutes x).symm
  let psi₀ : (↑B₀) →ₐ[k] S :=
    phi₂.comp (IsScalarTower.toAlgHom k (↑B₀) (Localization.Away f))
  let algB₀S : Algebra (↑B₀) S := psi₀.toRingHom.toAlgebra
  letI : Algebra (↑B₀) S := algB₀S
  letI : SMul (↑B₀) S := algB₀S.toSMul
  haveI towerKB₀S : IsScalarTower k (↑B₀) S :=
    IsScalarTower.of_algebraMap_eq fun x => (psi₀.commutes x).symm
  haveI towerB₀A₂S : IsScalarTower (↑B₀) (Localization.Away f) S :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hpsi : psi₀ = (IsScalarTower.toAlgHom k B S).comp phi := by
    apply AlgHom.ext
    intro x
    change phi₂ (algebraMap (↑B₀) (Localization.Away f) x) =
      ((algebraMap B₁ S).comp (algebraMap B B₁)) (phi x)
    rw [IsScalarTower.algebraMap_apply (↑B₀) (Localization.Away h)
        (Localization.Away f),
      DivFamZar.awayMapₐ_algebraMap phi₁ f,
      DivFamZar.awayMapₐ_algebraMap phi h]
    rfl
  haveI towerB₀BS : IsScalarTower (↑B₀) B S :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change psi₀ x = (IsScalarTower.toAlgHom k B S) (phi x)
      rw [hpsi]
      rfl
  let F : DivFamZarAff C S n := DivFamZarAff.mapAlgHom phi₂ F₀
  refine ⟨S, inferInstance, inferInstance, algBS, towerkBS, inferInstance,
    q, hqB, F, ?_⟩
  rw [show F.picClass = Scheme.CechPic.map
      (relCurveMap C (Localization.Away f) S) F₀.picClass from
        DivFamZarAff.picClass_mapAlgHom phi₂ F₀,
    hF₀, descent_cechPicClass (C := C) (B := B) hbc,
    ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, relCurveMap_comp,
    ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, relCurveMap_comp]

end BasicOpenCocycleDatum

end AlgebraicGeometry
