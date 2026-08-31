/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffChallenge
import AlgebraicJacobian.Picard.DivSchemeQProj

/-!
# The concrete project-local model of the admissible divisor representer

The admissible coverage parameter is strictly positive, so the chosen representer in
`DivRepAffChallenge` is definitionally the nonzero `DivScheme` branch.  This file names that
concrete branch and transports its closed immersion into the Grassmannian pair back to
`divRepAffAdmissibleScheme`.

The resulting certificate is unconditional and geometric: the target has its finite affine
product atlas, and the source is quasi-compact, locally of finite type, and separated over the
base field.  It is not yet a finite-projective-space immersion.  That stronger conclusion needs
the Plucker embeddings of both Grassmannian factors together with their Segre product; those
maps are not present in the rebuild project.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Grassmannian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section Curve

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable local instance admissibleDivisorOver :
    C.left.Over (Spec (.of k)) := .ofHom C.hom

local instance admissibleDivisorSmooth :
    SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
  inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)

local instance admissibleDivisorIntegral : IsIntegral C.left :=
  isIntegral_left_of_geometricallyReduced C

local instance admissibleDivisorLocallyOfFiniteType :
    LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
  inferInstanceAs (LocallyOfFiniteType C.hom)

local instance admissibleDivisorQuasiCompact :
    QuasiCompact (C.left ↘ Spec (.of k)) :=
  inferInstanceAs (QuasiCompact C.hom)

noncomputable local instance admissibleDivisorHModuleFiniteZero :
    Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
  moduleFinite_hModule_zero C

noncomputable local instance admissibleDivisorHModuleFiniteOne :
    Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
  moduleFinite_hModule_one C

/-- The chosen finite map is over `Spec k`, in the spelling used by the divisor-window API. -/
theorem divRepAffP1Map_comp_over :
    divRepAffP1Map C ≫ P1.structureMap k = C.left ↘ Spec (.of k) := by
  change divRepAffP1Map C ≫ P1.structureMap k = C.hom
  exact divRepAffP1Map_comp C

/-- The admissible parameter never enters the degree-zero terminal branch of the generic
representer.  Positivity follows from the positive window bound and the positive theta degree. -/
theorem divRepAffAdmissibleParameter_pos :
    0 < divRepAffAdmissibleParameter C := by
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : IsIntegral C.left := isIntegral_left_of_geometricallyReduced C
  haveI : LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  have hpi : divRepAffP1Map C ≫ P1.structureMap k = C.left ↘ Spec (.of k) :=
    divRepAffP1Map_comp C
  have hb := windowBound_pos (divRepAffP1Map C) hpi
  have hM := windowBound_le_M_mul
    (divRepAffP1Map C) hpi (genus C)
  have hd := one_le_classDeg_thetaCechClass (C := C)
  have hcast := admissibleCoverageParameter_cast
    (C := C) hpi (genus C)
  change 0 < admissibleCoverageParameter
    (C := C) hpi (genus C)
  have hpos : (0 : ℤ) <
      ((windowM_choice (divRepAffP1Map C) hpi (genus C) : ℤ) *
        windowδ (divRepAffP1Map C) + (genus C : ℤ)) *
        classDeg k (thetaCechClass C) := by
    nlinarith [Int.natCast_nonneg (genus C)]
  exact_mod_cast hcast.symm ▸ hpos

/-- Rank of the first Grassmannian window in the concrete admissible divisor model. -/
noncomputable def divRepAffAdmissibleWindowRankOne : ℕ :=
  Module.finrank k
    ↥(divisorSections k
      (windowM_choice (divRepAffP1Map C) (divRepAffP1Map_comp_over C)
        (divRepAffAdmissibleParameter C) • fiberWeilDivisor (divRepAffP1Map C)) ⊤)

/-- Rank of the second Grassmannian window in the concrete admissible divisor model. -/
noncomputable def divRepAffAdmissibleWindowRankTwo : ℕ :=
  Module.finrank k
    ↥(divisorSections k
      ((windowM_choice (divRepAffP1Map C) (divRepAffP1Map_comp_over C)
          (divRepAffAdmissibleParameter C) +
        windowS_choice (divRepAffP1Map C) (divRepAffP1Map_comp_over C)
          (divRepAffAdmissibleParameter C)) •
        fiberWeilDivisor (divRepAffP1Map C)) ⊤)

/-- The internally chosen finite basis of the first admissible window. -/
noncomputable def divRepAffAdmissibleWindowBasisOne :
    Module.Basis (Fin (divRepAffAdmissibleWindowRankOne C)) k
      ↥(divisorSections k
        (windowM_choice (divRepAffP1Map C) (divRepAffP1Map_comp_over C)
          (divRepAffAdmissibleParameter C) • fiberWeilDivisor (divRepAffP1Map C)) ⊤) :=
  Module.finBasis k _

/-- The internally chosen finite basis of the second admissible window. -/
noncomputable def divRepAffAdmissibleWindowBasisTwo :
    Module.Basis (Fin (divRepAffAdmissibleWindowRankTwo C)) k
      ↥(divisorSections k
        ((windowM_choice (divRepAffP1Map C) (divRepAffP1Map_comp_over C)
            (divRepAffAdmissibleParameter C) +
          windowS_choice (divRepAffP1Map C) (divRepAffP1Map_comp_over C)
            (divRepAffAdmissibleParameter C)) •
          fiberWeilDivisor (divRepAffP1Map C)) ⊤) :=
  Module.finBasis k _

/-- The explicit nonzero `DivScheme` branch selected by the admissible representer. -/
noncomputable def divRepAffAdmissibleConcreteScheme : Over (Spec (.of k)) := by
  letI : C.left.Over (Spec (.of k)) := admissibleDivisorOver C
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    admissibleDivisorSmooth C
  haveI : IsIntegral C.left := admissibleDivisorIntegral C
  haveI : LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
    admissibleDivisorLocallyOfFiniteType C
  haveI : QuasiCompact (C.left ↘ Spec (.of k)) := admissibleDivisorQuasiCompact C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    admissibleDivisorHModuleFiniteZero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    admissibleDivisorHModuleFiniteOne C
  exact divSchemeOver k
    (windowS_choice (divRepAffP1Map C) (divRepAffP1Map_comp_over C)
      (divRepAffAdmissibleParameter C) • fiberWeilDivisor (divRepAffP1Map C))
    (windowM_choice (divRepAffP1Map C) (divRepAffP1Map_comp_over C)
      (divRepAffAdmissibleParameter C) • fiberWeilDivisor (divRepAffP1Map C))
    (divRepAffAdmissibleParameter C)
    (divRepAffAdmissibleWindowRankOne C) (divRepAffAdmissibleWindowRankTwo C)
    (divRepAffAdmissibleWindowBasisOne C)
    ((divRepAffAdmissibleWindowBasisTwo C).map
      (windowShiftEquiv (divRepAffP1Map_comp_over C)
        (divRepAffAdmissibleParameter C)).symm)

set_option maxHeartbeats 1000000 in
-- Reducing the internally chosen bases exposes a large dependent `DivScheme` expression.
/-- The chosen admissible representer is the concrete positive-degree `DivScheme`. -/
theorem divRepAffAdmissibleScheme_eq_concrete :
    divRepAffAdmissibleScheme C = divRepAffAdmissibleConcreteScheme C := by
  classical
  unfold divRepAffAdmissibleScheme divFunctorAffAdmissibleRepresenter
    divRepAffScheme_at
    divRepAffAdmissibleConcreteScheme divRepAffAdmissibleWindowRankOne
    divRepAffAdmissibleWindowRankTwo divRepAffAdmissibleWindowBasisOne
    divRepAffAdmissibleWindowBasisTwo
  simp only [divFunctorAffRepresenter_at,
    dif_neg (divRepAffAdmissibleParameter_pos C).ne']

/-- The explicit Grassmannian-pair ambient space of the admissible divisor model. -/
noncomputable def divRepAffAdmissibleGrassmannianPair : Over (Spec (.of k)) :=
  grPairOver k
    (divRepAffAdmissibleParameter C) (divRepAffAdmissibleWindowRankOne C)
    (divRepAffAdmissibleParameter C) (divRepAffAdmissibleWindowRankTwo C)

/-- The underlying Scheme morphism of the concrete admissible divisor embedding. -/
noncomputable def divRepAffAdmissibleRawEmbedding :
    (divRepAffAdmissibleConcreteScheme C).left ⟶
      (divRepAffAdmissibleGrassmannianPair C).left := by
  letI : C.left.Over (Spec (.of k)) := admissibleDivisorOver C
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    admissibleDivisorSmooth C
  haveI : IsIntegral C.left := admissibleDivisorIntegral C
  haveI : LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
    admissibleDivisorLocallyOfFiniteType C
  haveI : QuasiCompact (C.left ↘ Spec (.of k)) := admissibleDivisorQuasiCompact C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    admissibleDivisorHModuleFiniteZero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    admissibleDivisorHModuleFiniteOne C
  exact divSchemeι k
    (windowS_choice (divRepAffP1Map C) (divRepAffP1Map_comp_over C)
      (divRepAffAdmissibleParameter C) • fiberWeilDivisor (divRepAffP1Map C))
    (windowM_choice (divRepAffP1Map C) (divRepAffP1Map_comp_over C)
      (divRepAffAdmissibleParameter C) • fiberWeilDivisor (divRepAffP1Map C))
    (divRepAffAdmissibleParameter C)
    (divRepAffAdmissibleWindowRankOne C) (divRepAffAdmissibleWindowRankTwo C)
    (divRepAffAdmissibleWindowBasisOne C)
    ((divRepAffAdmissibleWindowBasisTwo C).map
      (windowShiftEquiv (divRepAffP1Map_comp_over C)
        (divRepAffAdmissibleParameter C)).symm)

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 500000 in
-- The raw name keeps the dependent chosen bases out of downstream target types.
/-- The raw admissible divisor embedding is a closed immersion. -/
theorem isClosedImmersion_divRepAffAdmissibleRawEmbedding :
    IsClosedImmersion (divRepAffAdmissibleRawEmbedding C) := by
  letI : C.left.Over (Spec (.of k)) := admissibleDivisorOver C
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    admissibleDivisorSmooth C
  haveI : IsIntegral C.left := admissibleDivisorIntegral C
  haveI : LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
    admissibleDivisorLocallyOfFiniteType C
  haveI : QuasiCompact (C.left ↘ Spec (.of k)) := admissibleDivisorQuasiCompact C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    admissibleDivisorHModuleFiniteZero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    admissibleDivisorHModuleFiniteOne C
  change IsClosedImmersion (divSchemeι k
    (windowS_choice (divRepAffP1Map C) (divRepAffP1Map_comp_over C)
      (divRepAffAdmissibleParameter C) • fiberWeilDivisor (divRepAffP1Map C))
    (windowM_choice (divRepAffP1Map C) (divRepAffP1Map_comp_over C)
      (divRepAffAdmissibleParameter C) • fiberWeilDivisor (divRepAffP1Map C))
    (divRepAffAdmissibleParameter C)
    (divRepAffAdmissibleWindowRankOne C) (divRepAffAdmissibleWindowRankTwo C)
    (divRepAffAdmissibleWindowBasisOne C)
    ((divRepAffAdmissibleWindowBasisTwo C).map
      (windowShiftEquiv (divRepAffP1Map_comp_over C)
        (divRepAffAdmissibleParameter C)).symm))
  exact isClosedImmersion_divSchemeι k _ _ _ _ _ _ _

/-- The concrete closed immersion of the admissible divisor model into its two-window
Grassmannian pair. -/
noncomputable def divRepAffAdmissibleConcreteEmbedding :
    divRepAffAdmissibleConcreteScheme C ⟶
      divRepAffAdmissibleGrassmannianPair C := by
  letI : C.left.Over (Spec (.of k)) := admissibleDivisorOver C
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    admissibleDivisorSmooth C
  haveI : IsIntegral C.left := admissibleDivisorIntegral C
  haveI : LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
    admissibleDivisorLocallyOfFiniteType C
  haveI : QuasiCompact (C.left ↘ Spec (.of k)) := admissibleDivisorQuasiCompact C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    admissibleDivisorHModuleFiniteZero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    admissibleDivisorHModuleFiniteOne C
  refine Over.homMk (divRepAffAdmissibleRawEmbedding C) ?_
  rfl

/-- The concrete admissible divisor embedding is a closed immersion. -/
theorem isClosedImmersion_divRepAffAdmissibleConcreteEmbedding :
    IsClosedImmersion (divRepAffAdmissibleConcreteEmbedding C).left := by
  change IsClosedImmersion (divRepAffAdmissibleRawEmbedding C)
  exact isClosedImmersion_divRepAffAdmissibleRawEmbedding C

/-- The actual chosen representer, not merely its concrete spelling, embeds into the
Grassmannian pair. -/
noncomputable def divRepAffAdmissibleEmbedding :
    divRepAffAdmissibleScheme C ⟶ divRepAffAdmissibleGrassmannianPair C :=
  eqToHom (divRepAffAdmissibleScheme_eq_concrete C) ≫
    divRepAffAdmissibleConcreteEmbedding C

/-- The embedding of the actual chosen admissible representer is a closed immersion. -/
theorem isClosedImmersion_divRepAffAdmissibleEmbedding :
    IsClosedImmersion (divRepAffAdmissibleEmbedding C).left := by
  letI : IsClosedImmersion (divRepAffAdmissibleConcreteEmbedding C).left :=
    isClosedImmersion_divRepAffAdmissibleConcreteEmbedding C
  unfold divRepAffAdmissibleEmbedding
  rw [Over.comp_left]
  infer_instance

/-- The admissible Grassmannian pair has the finite product frame atlas used by the divisor
construction. -/
noncomputable def divRepAffAdmissibleGrassmannianCover :
    (divRepAffAdmissibleGrassmannianPair C).left.OpenCover :=
  grPairCover k
    (divRepAffAdmissibleParameter C) (divRepAffAdmissibleWindowRankOne C)
    (divRepAffAdmissibleParameter C) (divRepAffAdmissibleWindowRankTwo C)

instance finite_divRepAffAdmissibleGrassmannianCover :
    Finite (divRepAffAdmissibleGrassmannianCover C).I₀ :=
  finite_grPairCover_index k
    (divRepAffAdmissibleParameter C) (divRepAffAdmissibleWindowRankOne C)
    (divRepAffAdmissibleParameter C) (divRepAffAdmissibleWindowRankTwo C)

/-- Every frame patch of the admissible Grassmannian pair is affine. -/
theorem isAffine_divRepAffAdmissibleGrassmannianCover
    (ij : (divRepAffAdmissibleGrassmannianCover C).I₀) :
    IsAffine ((divRepAffAdmissibleGrassmannianCover C).X ij) :=
  isAffine_grPairCover_X k
    (divRepAffAdmissibleParameter C) (divRepAffAdmissibleWindowRankOne C)
    (divRepAffAdmissibleParameter C) (divRepAffAdmissibleWindowRankTwo C) ij

/-- The chosen admissible divisor source is quasi-compact over `k`. -/
theorem quasiCompact_divRepAffAdmissibleScheme :
    QuasiCompact (divRepAffAdmissibleScheme C).hom := by
  rw [divRepAffAdmissibleScheme_eq_concrete]
  unfold divRepAffAdmissibleConcreteScheme
  infer_instance

/-- The chosen admissible divisor source is locally of finite type over `k`. -/
theorem locallyOfFiniteType_divRepAffAdmissibleScheme :
    LocallyOfFiniteType (divRepAffAdmissibleScheme C).hom := by
  rw [divRepAffAdmissibleScheme_eq_concrete]
  unfold divRepAffAdmissibleConcreteScheme
  infer_instance

/-- The chosen admissible divisor source is separated over `k`. -/
theorem isSeparated_divRepAffAdmissibleScheme :
    IsSeparated (divRepAffAdmissibleScheme C).hom := by
  rw [divRepAffAdmissibleScheme_eq_concrete]
  unfold divRepAffAdmissibleConcreteScheme
  infer_instance

end Curve

end AlgebraicGeometry
