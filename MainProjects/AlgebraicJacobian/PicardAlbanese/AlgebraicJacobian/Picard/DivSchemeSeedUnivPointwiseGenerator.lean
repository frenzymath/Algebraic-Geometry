/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivPointwise
import AlgebraicJacobian.Picard.DivSchemeRedesignSeedUnivProduct

/-!
# The pointwise RD-N generator

RD-N gives an annihilator cutter for the redesigned pointwise section.  This file
restores the independent base-locus factor: a coordinate of the pointwise window vector
survives on a base basic open containing the chosen point.  Multiplying that factor by
the RD-N cutter gives both the fibre-nonvanishing and chart-divisibility properties
required by `ThetaGeneratorSeed.isGenerator_of_ann_cutter`.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

namespace PointwiseAchiever

section PointwiseGenerator

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftPointwiseGenerator :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k
    (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k
    ((windowS_choice pi hpi g • fiberWeilDivisor pi) +
      (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j

noncomputable local instance instIsIntegralRelCurvePointwiseGenerator
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePointwiseGenerator
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePointwiseGenerator
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

variable {R : Type u} [CommRing R] [Algebra k R]

/-- The contraction of the maximal ideal of a pinned-chart germ is the image of the
point under the relative curve's structure morphism. -/
theorem basePrime_germ_relPinnedChart_eq_relCurveBasePoint
    (side : Bool) (z : relCurve C R)
    (hz : z ∈ relPinnedChart C R pi side) :
    basePrime (R := R) ((relCurve C R).presheaf.germ
      (relPinnedChart C R pi side) z hz).hom = relCurveBasePoint C R z := by
  rw [show basePrime (R := R)
      ((relCurve C R).presheaf.germ (relPinnedChart C R pi side) z hz).hom =
      ((isAffineOpen_relPinnedChart C R pi side).primeIdealOf ⟨z, hz⟩).comap
        (algebraMap R Γ(relCurve C R, relPinnedChart C R pi side)) by
    rw [(isAffineOpen_relPinnedChart C R pi side).primeIdealOf_eq_map_closedPoint]
    rfl]
  change ((isAffineOpen_relPinnedChart C R pi side).primeIdealOf ⟨z, hz⟩).comap
      (algebraMap R Γ(relCurve C R, relPinnedChart C R pi side)) =
    (relCurve C R ↘ Spec (.of R)) z
  have hle : relPinnedChart C R pi side ≤
      (relCurve C R ↘ Spec (.of R)) ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens) := by simp
  have hmap := IsAffineOpen.comap_primeIdealOf_appLE
    (f := relCurve C R ↘ Spec (.of R)) (x := z)
    (⊤ : (Spec (.of R)).Opens) (isAffineOpen_top (Spec (.of R)))
    (relPinnedChart C R pi side) (isAffineOpen_relPinnedChart C R pi side) hle hz
  have hcomp := congrArg (fun q : PrimeSpectrum Γ(Spec (.of R), ⊤) =>
      q.comap (Scheme.ΓSpecIso (.of R)).inv.hom) hmap
  have hbase :
      ((isAffineOpen_top (Spec (.of R))).primeIdealOf
        ⟨(relCurve C R ↘ Spec (.of R)) z, hle hz⟩).comap
          (Scheme.ΓSpecIso (.of R)).inv.hom =
        (relCurve C R ↘ Spec (.of R)) z := by
    have h := (isAffineOpen_top (Spec (.of R))).fromSpec_primeIdealOf
      ⟨(relCurve C R ↘ Spec (.of R)) z, hle hz⟩
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    exact h
  rw [hbase] at hcomp
  rw [Scheme.algebraMap_overSectionsAlgebra]
  rw [← hcomp]
  rfl

set_option maxHeartbeats 2400000 in
-- The side split unfolds the pinned-chart comparison through the residue-field tower.
set_option synthInstance.maxHeartbeats 800000 in
/-- The pointwise section comparison carries a pulled-back base element to its residue
image on either pinned chart. -/
theorem relPinnedSectionsMap_algebraMap_pointwise (side : Bool)
    (p : PrimeSpectrum RZ) (f : RZ) :
    relPinnedSectionsMap C RZ p.asIdeal.ResidueField pi side
        (algebraMap RZ Γ(relCurve C RZ, relPinnedChart C RZ pi side) f) =
      algebraMap p.asIdeal.ResidueField
        Γ(relCurve C p.asIdeal.ResidueField,
          relPinnedChart C p.asIdeal.ResidueField pi side)
        (algebraMap RZ p.asIdeal.ResidueField f) := by
  rw [Scheme.algebraMap_overSectionsAlgebra, Scheme.algebraMap_overSectionsAlgebra]
  cases side with
  | false =>
    exact relSectionsMap_overAlgebraMap C RZ p.asIdeal.ResidueField (fiberChart₀ pi) f
  | true =>
    exact relSectionsMap_overAlgebraMap C RZ p.asIdeal.ResidueField (fiberChart₁ pi) f

set_option maxHeartbeats 2400000 in
-- Rewriting the residue image traverses the full carve-ring and pinned-chart types.
set_option synthInstance.maxHeartbeats 800000 in
/-- A nonempty residue-fibre basic open cut out by a pulled-back base element forces that
base element to avoid the residue prime. -/
theorem notMem_of_basicOpen_relPinnedSectionsMap_algebraMap_pointwise (side : Bool)
    (p : PrimeSpectrum RZ) (f : RZ)
    (hne : ((relCurve C p.asIdeal.ResidueField).basicOpen
        (relPinnedSectionsMap C RZ p.asIdeal.ResidueField pi side
          (algebraMap RZ Γ(relCurve C RZ, relPinnedChart C RZ pi side) f)) :
      (relCurve C p.asIdeal.ResidueField).Opens) ≠ ⊥) :
    f ∉ p.asIdeal := by
  intro hf
  apply hne
  rw [relPinnedSectionsMap_algebraMap_pointwise C hpi g r1 r2 b1 b2 i j side p f,
    (Ideal.algebraMap_residueField_eq_zero (I := p.asIdeal)).mpr hf, map_zero]
  exact (relCurve C p.asIdeal.ResidueField).toLocallyRingedSpace.basicOpen_zero _

set_option maxHeartbeats 2400000 in
-- The chosen coordinate and base-prime bridge elaborate through the dependent seed ring.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- A base coordinate of the pointwise vector cuts a basic open containing `z` and keeps
the vector nonzero at every residue prime of that base open. -/
theorem exists_pointwiseBaseCutter (z : relCurve C RZ) :
    ∃ f : RZ,
      z ∈ (relCurve C RZ).basicOpen
        (algebraMap RZ
          Γ(relCurve C RZ,
            relPinnedChart C RZ pi (pointwiseSide C hpi g r1 r2 b1 b2 i j z)) f) ∧
      ∀ q : PrimeSpectrum RZ, f ∉ q.asIdeal →
        windowCompare RZ q.asIdeal.ResidueField
          (pointwiseSectionVector C hpi g r1 r2 b1 b2 i j hO hchi z) ≠ 0 := by
  obtain ⟨f, hfp, hsurv⟩ := exists_forall_windowCompare_ne_zero
    C hpi g r1 r2 b1 b2 i j
    (pointwiseSectionVector C hpi g r1 r2 b1 b2 i j hO hchi z)
    (relCurveBasePoint C RZ z)
    (windowCompare_pointwiseSectionVector_ne_zero
      C hpi g r1 r2 b1 b2 i j hO hchi z)
  refine ⟨f, ?_, hsurv⟩
  apply mem_basicOpen_algebraMap_of_notMem_basePrime
    (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z) f
  rwa [basePrime_germ_relPinnedChart_eq_relCurveBasePoint C
    (pointwiseSide C hpi g r1 r2 b1 b2 i j z) z
    (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z)]

set_option maxHeartbeats 2400000 in
-- The dependent seed fields retain the full chart ring and selected pointwise section.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The pointwise section equipped with its base-locus cutter. -/
noncomputable def pointwiseBaseSeed :
    ThetaGeneratorSeed C RZ pi (windowM_choice pi hpi g)
      (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) where
  side := pointwiseSide C hpi g r1 r2 b1 b2 i j
  h := fun z => algebraMap RZ
    Γ(relCurve C RZ,
      relPinnedChart C RZ pi (pointwiseSide C hpi g r1 r2 b1 b2 i j z))
    (exists_pointwiseBaseCutter C hpi g r1 r2 b1 b2 i j hO hchi z).choose
  mem_basicOpen := fun z =>
    (exists_pointwiseBaseCutter C hpi g r1 r2 b1 b2 i j hO hchi z).choose_spec.1
  sec := pointwiseSection C hpi g r1 r2 b1 b2 i j hO hchi
  sec_mem := pointwiseSection_mem C hpi g r1 r2 b1 b2 i j hO hchi

set_option maxHeartbeats 2400000 in
-- Fibre nonvanishing unfolds the base seed and compares its selected window vector.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The base-locus seed has the fibre nonvanishing required by the product-cutter
generator theorem. -/
theorem pointwiseBaseSeed_hfib :
    ∀ (z : relCurve C RZ) (p : PrimeSpectrum RZ),
      ((relCurve C p.asIdeal.ResidueField).basicOpen
          (relPinnedSectionsMap C RZ p.asIdeal.ResidueField pi
            ((pointwiseBaseSeed C hpi g r1 r2 b1 b2 i j hO hchi).side z)
            ((pointwiseBaseSeed C hpi g r1 r2 b1 b2 i j hO hchi).h z)) :
        (relCurve C p.asIdeal.ResidueField).Opens) ≠ ⊥ →
      relPinnedSectionsMap C RZ p.asIdeal.ResidueField pi
          ((pointwiseBaseSeed C hpi g r1 r2 b1 b2 i j hO hchi).side z)
          (relThetaResSide (windowM_choice pi hpi g)
            ((pointwiseBaseSeed C hpi g r1 r2 b1 b2 i j hO hchi).side z) le_rfl
            ((pointwiseBaseSeed C hpi g r1 r2 b1 b2 i j hO hchi).sec z)) ≠ 0 := by
  intro z p hne
  let f := (exists_pointwiseBaseCutter
    C hpi g r1 r2 b1 b2 i j hO hchi z).choose
  have hfp : f ∉ p.asIdeal :=
    notMem_of_basicOpen_relPinnedSectionsMap_algebraMap_pointwise
      C hpi g r1 r2 b1 b2 i j
        (pointwiseSide C hpi g r1 r2 b1 b2 i j z) p f (by
          simpa only [pointwiseBaseSeed, f] using hne)
  have hsurv := (exists_pointwiseBaseCutter
    C hpi g r1 r2 b1 b2 i j hO hchi z).choose_spec.2 p hfp
  simpa only [pointwiseBaseSeed, pointwiseSection] using
    relPinnedSectionsMap_relThetaResSide_windowEquiv_ne_zero
      C hpi g r1 r2 b1 b2 i j (windowM_choice pi hpi g)
      (relThetaPairH1_windowM C pi hpi g) p
      (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
      (pointwiseSectionVector C hpi g r1 r2 b1 b2 i j hO hchi z) hsurv
      (relPinnedSectionsMap C RZ p.asIdeal.ResidueField pi
        (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
        (algebraMap RZ
          Γ(relCurve C RZ,
            relPinnedChart C RZ pi (pointwiseSide C hpi g r1 r2 b1 b2 i j z)) f))
      (by simpa only [pointwiseBaseSeed, f] using hne)

set_option maxHeartbeats 2400000 in
-- The product seed substitutes the chosen ann-cutter through dependent chart fields.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- Multiply the pointwise base-locus seed by the RD-N annihilator cutter. -/
noncomputable def pointwiseGeneratorSeed
    (hrdn : PointwiseSeedRDN C hpi g r1 r2 b1 b2 i j hO hchi) :
    ThetaGeneratorSeed C RZ pi (windowM_choice pi hpi g)
      (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) :=
  ThetaGeneratorSeed.productCutter
    (pointwiseBaseSeed C hpi g r1 r2 b1 b2 i j hO hchi)
    (fun z => (exists_pointwiseAnnCutter
      C hpi g r1 r2 b1 b2 i j hO hchi hrdn z).choose)
    (fun z => (exists_pointwiseAnnCutter
      C hpi g r1 r2 b1 b2 i j hO hchi hrdn z).choose_spec.1)

set_option maxHeartbeats 2400000 in
-- The generator theorem aligns the ann-cutter containment with base-seed nonvanishing.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- Pointwise RD-N produces an unconditional theta generator. -/
theorem isGenerator_pointwiseGeneratorSeed
    (hrdn : PointwiseSeedRDN C hpi g r1 r2 b1 b2 i j hO hchi) :
    (pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn).IsGenerator := by
  apply ThetaGeneratorSeed.isGenerator_productCutter
    (pointwiseBaseSeed C hpi g r1 r2 b1 b2 i j hO hchi)
    (fun z => (exists_pointwiseAnnCutter
      C hpi g r1 r2 b1 b2 i j hO hchi hrdn z).choose)
    (fun z => (exists_pointwiseAnnCutter
      C hpi g r1 r2 b1 b2 i j hO hchi hrdn z).choose_spec.1)
  · intro z psi hpsi
    exact (exists_pointwiseAnnCutter
      C hpi g r1 r2 b1 b2 i j hO hchi hrdn z).choose_spec.2 hpsi
  · exact pointwiseBaseSeed_hfib C hpi g r1 r2 b1 b2 i j hO hchi

/-! ## Decoupled pointwise generator -/

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- A base coordinate cutter for the pointwise vector at curve parameter `gamma ≤ g`. -/
theorem exists_pointwiseBaseCutter_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ) :
    ∃ f : RZ,
      z ∈ (relCurve C RZ).basicOpen
        (algebraMap RZ
          Γ(relCurve C RZ,
            relPinnedChart C RZ pi (pointwiseSide C hpi g r1 r2 b1 b2 i j z)) f) ∧
      ∀ q : PrimeSpectrum RZ, f ∉ q.asIdeal →
        windowCompare RZ q.asIdeal.ResidueField
          (pointwiseSectionVector_at C hpi g r1 r2 b1 b2 i j hgamma hχ z) ≠ 0 := by
  obtain ⟨f, hfp, hsurv⟩ := exists_forall_windowCompare_ne_zero
    C hpi g r1 r2 b1 b2 i j
    (pointwiseSectionVector_at C hpi g r1 r2 b1 b2 i j hgamma hχ z)
    (relCurveBasePoint C RZ z)
    (windowCompare_pointwiseSectionVector_ne_zero_at
      C hpi g r1 r2 b1 b2 i j hgamma hχ z)
  refine ⟨f, ?_, hsurv⟩
  apply mem_basicOpen_algebraMap_of_notMem_basePrime
    (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z) f
  rwa [basePrime_germ_relPinnedChart_eq_relCurveBasePoint C
    (pointwiseSide C hpi g r1 r2 b1 b2 i j z) z
    (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z)]

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The decoupled pointwise section equipped with its base-locus cutter. -/
noncomputable def pointwiseBaseSeed_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    ThetaGeneratorSeed C RZ pi (windowM_choice pi hpi g)
      (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) where
  side := pointwiseSide C hpi g r1 r2 b1 b2 i j
  h := fun z => algebraMap RZ
    Γ(relCurve C RZ,
      relPinnedChart C RZ pi (pointwiseSide C hpi g r1 r2 b1 b2 i j z))
    (exists_pointwiseBaseCutter_at
      C hpi g r1 r2 b1 b2 i j hgamma hχ z).choose
  mem_basicOpen := fun z =>
    (exists_pointwiseBaseCutter_at
      C hpi g r1 r2 b1 b2 i j hgamma hχ z).choose_spec.1
  sec := pointwiseSection_at C hpi g r1 r2 b1 b2 i j hgamma hχ
  sec_mem := pointwiseSection_mem_at C hpi g r1 r2 b1 b2 i j hgamma hχ

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The decoupled base-locus seed is nonzero on every residue fibre meeting its base open. -/
theorem pointwiseBaseSeed_hfib_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    ∀ (z : relCurve C RZ) (p : PrimeSpectrum RZ),
      ((relCurve C p.asIdeal.ResidueField).basicOpen
          (relPinnedSectionsMap C RZ p.asIdeal.ResidueField pi
            ((pointwiseBaseSeed_at C hpi g r1 r2 b1 b2 i j hgamma hχ).side z)
            ((pointwiseBaseSeed_at C hpi g r1 r2 b1 b2 i j hgamma hχ).h z)) :
        (relCurve C p.asIdeal.ResidueField).Opens) ≠ ⊥ →
      relPinnedSectionsMap C RZ p.asIdeal.ResidueField pi
          ((pointwiseBaseSeed_at C hpi g r1 r2 b1 b2 i j hgamma hχ).side z)
          (relThetaResSide (windowM_choice pi hpi g)
            ((pointwiseBaseSeed_at C hpi g r1 r2 b1 b2 i j hgamma hχ).side z) le_rfl
            ((pointwiseBaseSeed_at C hpi g r1 r2 b1 b2 i j hgamma hχ).sec z)) ≠ 0 := by
  intro z p hne
  let f := (exists_pointwiseBaseCutter_at
    C hpi g r1 r2 b1 b2 i j hgamma hχ z).choose
  have hfp : f ∉ p.asIdeal :=
    notMem_of_basicOpen_relPinnedSectionsMap_algebraMap_pointwise
      C hpi g r1 r2 b1 b2 i j
        (pointwiseSide C hpi g r1 r2 b1 b2 i j z) p f (by
          simpa only [pointwiseBaseSeed_at, f] using hne)
  have hsurv := (exists_pointwiseBaseCutter_at
    C hpi g r1 r2 b1 b2 i j hgamma hχ z).choose_spec.2 p hfp
  simpa only [pointwiseBaseSeed_at, pointwiseSection_at] using
    relPinnedSectionsMap_relThetaResSide_windowEquiv_ne_zero
      C hpi g r1 r2 b1 b2 i j (windowM_choice pi hpi g)
      (relThetaPairH1_windowM C pi hpi g) p
      (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
      (pointwiseSectionVector_at C hpi g r1 r2 b1 b2 i j hgamma hχ z) hsurv
      (relPinnedSectionsMap C RZ p.asIdeal.ResidueField pi
        (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
        (algebraMap RZ
          Γ(relCurve C RZ,
            relPinnedChart C RZ pi (pointwiseSide C hpi g r1 r2 b1 b2 i j z)) f))
      (by simpa only [pointwiseBaseSeed_at, f] using hne)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- Multiply the decoupled base-locus seed by its RD-N annihilator cutter. -/
noncomputable def pointwiseGeneratorSeed_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hrdn : PointwiseSeedRDNAt C hpi g r1 r2 b1 b2 i j hgamma hχ) :
    ThetaGeneratorSeed C RZ pi (windowM_choice pi hpi g)
      (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) :=
  ThetaGeneratorSeed.productCutter
    (pointwiseBaseSeed_at C hpi g r1 r2 b1 b2 i j hgamma hχ)
    (fun z => (exists_pointwiseAnnCutter_at
      C hpi g r1 r2 b1 b2 i j hgamma hχ hrdn z).choose)
    (fun z => (exists_pointwiseAnnCutter_at
      C hpi g r1 r2 b1 b2 i j hgamma hχ hrdn z).choose_spec.1)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- Decoupled pointwise RD-N produces a theta generator. -/
theorem isGenerator_pointwiseGeneratorSeed_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hrdn : PointwiseSeedRDNAt C hpi g r1 r2 b1 b2 i j hgamma hχ) :
    (pointwiseGeneratorSeed_at
      C hpi g r1 r2 b1 b2 i j hgamma hχ hrdn).IsGenerator := by
  apply ThetaGeneratorSeed.isGenerator_productCutter
    (pointwiseBaseSeed_at C hpi g r1 r2 b1 b2 i j hgamma hχ)
    (fun z => (exists_pointwiseAnnCutter_at
      C hpi g r1 r2 b1 b2 i j hgamma hχ hrdn z).choose)
    (fun z => (exists_pointwiseAnnCutter_at
      C hpi g r1 r2 b1 b2 i j hgamma hχ hrdn z).choose_spec.1)
  · intro z psi hpsi
    exact (exists_pointwiseAnnCutter_at
      C hpi g r1 r2 b1 b2 i j hgamma hχ hrdn z).choose_spec.2 hpsi
  · exact pointwiseBaseSeed_hfib_at C hpi g r1 r2 b1 b2 i j hgamma hχ

end PointwiseGenerator

end PointwiseAchiever

end AlgebraicGeometry
