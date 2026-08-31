/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SectionsToDivisorsClass
import AlgebraicJacobian.Picard.DivisorFamilyAffPrincipalAway
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffRank
import AlgebraicJacobian.Picard.DivisorFamilyAffAssemble

/-!
# Widened effectivity for fibrewise-regular sections

This module is the R2 bridge used by admissible Abel coverage.  A section of a cocycle datum
first cuts intrinsic local equations.  Fibrewise regularity is transported through the section
ring of an arbitrary affine open; the resulting local-equation system is then certified using
away-local arbitrary `AffCoverData` adaptations.  No widened cover piece is identified with one
of the two auxiliary charts used to present the cocycle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace BasicOpenCocycleDatum

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable {B : Type u} [CommRing B] [Algebra k B] [IsNoetherianRing B]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable (D : BasicOpenCocycleDatum C B pi)
variable (s : ↥(gluedSubmodule B D.pieces D.unit ⊤))

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [IsNoetherianRing B] in
/-- Multiplication-injectivity on a residue fibre is the pure-tensor nonzerodivisor
condition for a component of a cocycle-datum section. -/
theorem component_tmul_one_mem_nonZeroDivisors
    (hfib : ∀ (j : D.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField))
    (j : D.index) (p : PrimeSpectrum B) :
    letI : Algebra B Γ(relCurve C B, D.pieces j) :=
      ((relCurve C B).overAlgebraMap B (D.pieces j)).toAlgebra
    (D.component s j ⊗ₜ[B] (1 : p.asIdeal.ResidueField) :
      Γ(relCurve C B, D.pieces j) ⊗[B] p.asIdeal.ResidueField) ∈
        nonZeroDivisors
          (Γ(relCurve C B, D.pieces j) ⊗[B] p.asIdeal.ResidueField) := by
  letI : Algebra B Γ(relCurve C B, D.pieces j) :=
    ((relCurve C B).overAlgebraMap B (D.pieces j)).toAlgebra
  have hend : Scheme.mulSectionEnd B (D.component s j) =
      LinearMap.mulLeft B (D.component s j) := by
    ext t
    simp [Scheme.mulSectionEnd_apply]
  have hinj := hfib j p
  rw [hend, rTensor_mulLeft_eq_mulLeft_tmul p.asIdeal.ResidueField
    (D.component s j)] at hinj
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro z hz
    apply hinj
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, mul_zero]
    exact hz
  · intro z hz
    apply hinj
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, mul_zero, mul_comm]
    exact hz

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] in
/-- A fibrewise-regular component remains a nonzerodivisor after arbitrary coefficient
extension, read through the section ring of its affine open. -/
theorem component_relAffSectionsMap_mem_nonZeroDivisors
    (hfib : ∀ (j : D.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField))
    (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B']
    [IsScalarTower k B B'] (j : D.index) :
    relAffSectionsMap C B' (D.pieces j) (D.component s j) ∈
      nonZeroDivisors Γ(relCurve C B', relCurveMap C B B' ⁻¹ᵁ D.pieces j) := by
  letI : Algebra B Γ(relCurve C B, D.pieces j) :=
    ((relCurve C B).overAlgebraMap B (D.pieces j)).toAlgebra
  letI : Module.Flat B Γ(relCurve C B, D.pieces j) :=
    flat_sections_isAffineOpen C B (D.isAffineOpen_pieces j)
  have hbase :=
    Algebra.TensorProduct.includeRight_mem_nonZeroDivisors_of_forall_tmul_residueField
      (fun p => D.component_tmul_one_mem_nonZeroDivisors s hfib j p) B'
  have hpulled := map_mem_nonZeroDivisors'
    (relSectionsBaseChangeAff C B' (D.isAffineOpen_pieces j)).toRingEquiv hbase
  have hmap : (relSectionsBaseChangeAff C B' (D.isAffineOpen_pieces j)).toRingEquiv
      (Algebra.TensorProduct.includeRight (D.component s j)) =
        relAffSectionsMap C B' (D.pieces j) (D.component s j) := by
    rw [Algebra.TensorProduct.includeRight_apply]
    exact relSectionsBaseChangeAff_one_tmul C B'
      (D.isAffineOpen_pieces j) (D.component s j)
  rwa [hmap] at hpulled

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] in
/-- The pullback of the section-cut equation is the arbitrary-affine section comparison of
the selected component. -/
theorem pullbackEqn_sectionLocalEquationsOfFibrewiseRegular
    (hfib : ∀ (j : D.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField))
    (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B']
    [IsScalarTower k B B'] (z : relCurve C B') :
    Scheme.LocalEquations.pullbackEqn (relCurveMap C B B')
        (D.sectionLocalEquationsOfFibrewiseRegular s hfib) z =
      relAffSectionsMap C B'
        (D.pieces (D.pieceIndex ((relCurveMap C B B').base z)))
        (D.component s (D.pieceIndex ((relCurveMap C B B').base z))) := by
  simp [Scheme.LocalEquations.pullbackEqn,
    BasicOpenCocycleDatum.sectionLocalEquationsOfFibrewiseRegular,
    BasicOpenCocycleDatum.sectionLocalEquations,
    relAffSectionsMap, Scheme.resHom]

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] in
/-- The intrinsic local-equation system cut by a fibrewise-regular section has regular
own-member equations after every field-valued coefficient extension. -/
theorem germ_self_pullbackEqn_sectionLocalEquationsOfFibrewiseRegular
    (hfib : ∀ (j : D.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField))
    (L : Type u) [Field L] [Algebra k L] [Algebra B L]
    [IsScalarTower k B L] (z : relCurve C L) :
    ((relCurve C L).presheaf.germ
      (((D.sectionLocalEquationsOfFibrewiseRegular s hfib).cover.pullback
        (relCurveMap C B L)).opens z) z
      (((D.sectionLocalEquationsOfFibrewiseRegular s hfib).cover.pullback
        (relCurveMap C B L)).mem_opens z)).hom
      (Scheme.LocalEquations.pullbackEqn (relCurveMap C B L)
        (D.sectionLocalEquationsOfFibrewiseRegular s hfib) z) ∈
      nonZeroDivisors ((relCurve C L).presheaf.stalk z) := by
  let j := D.pieceIndex ((relCurveMap C B L).base z)
  have hsec := D.component_relAffSectionsMap_mem_nonZeroDivisors s hfib L j
  have hopen : IsAffineOpen (relCurveMap C B L ⁻¹ᵁ D.pieces j) :=
    isAffineOpen_relCurveMap_preimage C L (D.isAffineOpen_pieces j)
  have hz : z ∈ relCurveMap C B L ⁻¹ᵁ D.pieces j :=
    D.mem_pieces_pieceIndex ((relCurveMap C B L).base z)
  have hgerm := hopen.germ_mem_nonZeroDivisors hsec (y := z) hz
  rw [D.pullbackEqn_sectionLocalEquationsOfFibrewiseRegular s hfib L z]
  dsimp only [j] at hgerm
  simpa only [BasicOpenCocycleDatum.sectionLocalEquationsOfFibrewiseRegular,
    BasicOpenCocycleDatum.sectionLocalEquations,
    Scheme.PointedCover.pullback_opens,
    BasicOpenCocycleDatum.pointedCover_opens] using hgerm

end BasicOpenCocycleDatum

section WidenedEffectivity

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable (n : ℕ)
variable (d : (relCurve C R).LocalEquations)

noncomputable local instance instIsIntegralRelCurveEffectivity
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveEffectivity
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQuasiCompactRelCurveEffectivity
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instFiniteH0RelCurveEffectivity
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFiniteH1RelCurveEffectivity
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option maxHeartbeats 8000000 in
-- The certified-adaptation assembly elaborates dependent pulled equations at two field levels.
set_option synthInstance.maxHeartbeats 800000 in
/-- A fibrewise-regular local-equation system of constant fibre class degree `n` has an
away-local widened certificate at every prime of its Noetherian base. -/
theorem exists_away_certifiedAff_of_fibrewiseRegular_of_classDeg
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hreg : ∀ (L : Type u) [Field L] [Algebra k L] [Algebra R L]
      [IsScalarTower k R L], ∀ z : relCurve C L,
      ((relCurve C L).presheaf.germ
        ((d.cover.pullback (relCurveMap C R L)).opens z) z
        ((d.cover.pullback (relCurveMap C R L)).mem_opens z)).hom
        (Scheme.LocalEquations.pullbackEqn (relCurveMap C R L) d z) ∈
          nonZeroDivisors ((relCurve C L).presheaf.stalk z))
    (hdeg : ∀ (L : Type u) [Field L] [Algebra k L] [Algebra R L]
      [IsScalarTower k R L],
      classDeg L (Scheme.CechPic.map (relCurveMap C R L) d.picClass) = (n : ℤ))
    (p : PrimeSpectrum R) :
    ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ (Dr : AffCoverData C (Localization.Away r))
        (A : AffAdaptation Dr
          (d.pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) d))),
        A.IsCertified n := by
  have hfinite :=
    Scheme.LocalEquations.fibre_supportLocus_finite_of_forall_self_aff
      C R d p (fun z => hreg p.asIdeal.ResidueField z)
  obtain ⟨r, hr, Dr, A, hsw⟩ :=
    Scheme.LocalEquations.exists_away_affAdaptation_swallowedBy_of_finite_fibre
      C R pi d p hfinite
  letI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
    isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
  refine ⟨r, hr, Dr, A, ?_⟩
  obtain ⟨j0, hsub, hmiss⟩ := hsw
  have hfin : ∀ j, Module.Finite (Localization.Away r) (A.colength j) :=
    A.forall_finite_colength_of_swallowedBy ⟨j0, hsub, hmiss⟩
  have hproj : ∀ j, Module.Projective (Localization.Away r) (A.colength j) := fun j => by
    haveI := hfin j
    exact A.projective_colength_of_forall_tmul_residueField j fun q =>
      A.eqn_tmul_one_mem_nonZeroDivisors_of_self_pullbackEqn j q fun z => by
        have hcomp : relCurveMap C (Localization.Away r) q.asIdeal.ResidueField
              ≫ relCurveMap C R (Localization.Away r) =
            relCurveMap C R q.asIdeal.ResidueField :=
          relCurveMap_comp (R' := Localization.Away r)
            (R'' := q.asIdeal.ResidueField)
        have heq := Scheme.LocalEquations.germ_pullbackEqn_comp hcomp d
          (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
            (relCurveMap C R (Localization.Away r)) d) z
        exact heq ▸ hreg q.asIdeal.ResidueField z
  exact A.isCertified_of_swallowedBy_of_c1_of_rank_piece hsub hmiss hfin hproj fun q =>
    A.rankAtStalk_colength_eq_of_swallowedBy_of_pulled_degree
      j0 hsub hmiss hfin hproj q (by
        rw [← classDeg_picClass,
          Scheme.CurveDivisor.picClass_presentationDivisor,
          Scheme.LocalEquations.presentation_picClass,
          A.picClass_pulledEquations q.asIdeal.ResidueField hproj,
          Scheme.LocalEquations.picClass_pullback,
          ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
          relCurveMap_comp (R' := Localization.Away r)
            (R'' := q.asIdeal.ResidueField)]
        exact hdeg q.asIdeal.ResidueField)

set_option maxHeartbeats 8000000 in
-- The definition elaborates the full dependent certificate family produced above.
set_option synthInstance.maxHeartbeats 800000 in
/-- The widened divisor class represented by a fibrewise-regular, constant-degree intrinsic
local-equation system. -/
noncomputable def divFamZarAffOfFibrewiseRegularLocalEquations
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hreg : ∀ (L : Type u) [Field L] [Algebra k L] [Algebra R L]
      [IsScalarTower k R L], ∀ z : relCurve C L,
      ((relCurve C L).presheaf.germ
        ((d.cover.pullback (relCurveMap C R L)).opens z) z
        ((d.cover.pullback (relCurveMap C R L)).mem_opens z)).hom
        (Scheme.LocalEquations.pullbackEqn (relCurveMap C R L) d z) ∈
          nonZeroDivisors ((relCurve C L).presheaf.stalk z))
    (hdeg : ∀ (L : Type u) [Field L] [Algebra k L] [Algebra R L]
      [IsScalarTower k R L],
      classDeg L (Scheme.CechPic.map (relCurveMap C R L) d.picClass) = (n : ℤ)) :
    DivFamZarAff C R n :=
  divFamZarAff_of_forall_prime_certified_adaptation
    (exists_away_certifiedAff_of_fibrewiseRegular_of_classDeg C n d pi hreg hdeg)

@[simp]
theorem picClass_divFamZarAffOfFibrewiseRegularLocalEquations
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hreg : ∀ (L : Type u) [Field L] [Algebra k L] [Algebra R L]
      [IsScalarTower k R L], ∀ z : relCurve C L,
      ((relCurve C L).presheaf.germ
        ((d.cover.pullback (relCurveMap C R L)).opens z) z
        ((d.cover.pullback (relCurveMap C R L)).mem_opens z)).hom
        (Scheme.LocalEquations.pullbackEqn (relCurveMap C R L) d z) ∈
          nonZeroDivisors ((relCurve C L).presheaf.stalk z))
    (hdeg : ∀ (L : Type u) [Field L] [Algebra k L] [Algebra R L]
      [IsScalarTower k R L],
      classDeg L (Scheme.CechPic.map (relCurveMap C R L) d.picClass) = (n : ℤ)) :
    DivFamZarAff.picClass
      (divFamZarAffOfFibrewiseRegularLocalEquations C n d pi hreg hdeg) = d.picClass :=
  rfl

end WidenedEffectivity

end AlgebraicGeometry
