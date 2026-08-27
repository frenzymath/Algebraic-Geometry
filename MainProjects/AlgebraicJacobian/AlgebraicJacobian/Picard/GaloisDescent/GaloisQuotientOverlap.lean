/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GaloisDescent.GaloisQuotientRestrict
import AlgebraicJacobian.Picard.GaloisDescent.GaloisQuotientDescent
import AlgebraicJacobian.Picard.GaloisDescent.GaloisQuotientUniqueness
import AlgebraicJacobian.Picard.GaloisQuotientAffineGeneral

/-!
# Overlap charts for a finite Galois quotient

This file packages the invariant-ring quotient charts attached to stable affine
opens and their quotient-side overlaps.  Every overlap carries the full
`IsGaloisQuotient` witness for the restricted action.  The reversed overlap
comparison is then canonical by uniqueness.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicJacobian.GaloisDescent

universe u

set_option autoImplicit false

namespace SemilinearGalAction

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
variable (ρ : SemilinearGalAction K L X f)

/-- Equality of stable opens induces an equivariant isomorphism between the
corresponding restricted actions. -/
theorem restrict_isoOfEq_isEquivariant {U V : X.Opens}
    (hU : ρ.IsStableOpen U) (hV : ρ.IsStableOpen V) (e : U = V) :
    (ρ.restrict hU).IsEquivariant (ρ.restrict hV) (X.isoOfEq e).hom := by
  intro γ
  rw [restrict_act_hom, restrict_act_hom]
  rw [← cancel_mono V.ι]
  simp

end SemilinearGalAction

/-- A stable affine open for a fixed semilinear Galois action. -/
structure StableAffineOpen
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (ρ : SemilinearGalAction K L X f) where
  U : X.Opens
  affine : IsAffineOpen U
  stable : ρ.IsStableOpen U

namespace StableAffineOpen

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
variable (ρ : SemilinearGalAction K L X f)

/-- The intersection of two stable opens is stable. -/
theorem inf_stable (i j : StableAffineOpen ρ) :
    ρ.IsStableOpen (i.U ⊓ j.U) := by
  intro γ
  rw [Scheme.Hom.preimage_inf, i.stable γ, j.stable γ]

/-- The open cover of the acted scheme indexed by all stable affine opens.
The existing `HasStableAffineCover` producer supplies joint surjectivity. -/
noncomputable def sourceOpenCover [HasStableAffineCover K L ρ] :
    Scheme.OpenCover X where
  I₀ := StableAffineOpen ρ
  X i := i.U.toScheme
  f i := i.U.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨U, hUa, hx, hU⟩ :=
        HasStableAffineCover.exists_stable_affineOpen (ρ := ρ) x
      exact ⟨⟨U, hUa, hU⟩, ⟨x, hx⟩, rfl⟩
    · intro i
      infer_instance

/-- The affine invariant-ring quotient chart attached to a stable affine open. -/
noncomputable def quotientChart (i : StableAffineOpen ρ) : Scheme.{u} := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact Spec (CommRingCat.of
    (SemilinearAction.invariantsSubalgebra K L Γ(X, i.U)))

/-- The structure map of an invariant-ring quotient chart to `Spec K`. -/
noncomputable def quotientChartMap (i : StableAffineOpen ρ) :
    quotientChart ρ i ⟶ Spec (CommRingCat.of K) := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact Spec.map (CommRingCat.ofHom
    (algebraMap K (SemilinearAction.invariantsSubalgebra K L Γ(X, i.U))))

/-- The quotient-side overlap in chart `i` corresponding to `i.U ⊓ j.U`. -/
noncomputable def quotientOverlap (i j : StableAffineOpen ρ) : Scheme.{u} := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact (SemilinearGalAction.quotientOpenOfStableSubopen
    ρ i.stable (i.U ⊓ j.U)).toScheme

/-- The overlap inclusion into its quotient chart. -/
noncomputable def quotientOverlapι (i j : StableAffineOpen ρ) :
    quotientOverlap ρ i j ⟶ quotientChart ρ i := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact (SemilinearGalAction.quotientOpenOfStableSubopen
    ρ i.stable (i.U ⊓ j.U)).ι

instance quotientOverlapι_isOpenImmersion (i j : StableAffineOpen ρ) :
    IsOpenImmersion (quotientOverlapι ρ i j) := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  unfold quotientOverlapι quotientOverlap quotientChart
  infer_instance

/-- A chart overlaps itself in the whole quotient chart. -/
theorem quotientOverlapι_self_isIso [FiniteDimensional K L]
    (i : StableAffineOpen ρ) : IsIso (quotientOverlapι ρ i i) := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  have htop :
      SemilinearGalAction.quotientOpenOfStableSubopen ρ i.stable
        (i.U ⊓ i.U) = ⊤ := by
    simpa only [inf_idem] using
      (SemilinearGalAction.quotientOpenOfStableSubopen_self
        ρ i.stable i.affine)
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  unfold quotientOverlapι
  exact (Scheme.Opens.opensRange_ι
    (SemilinearGalAction.quotientOpenOfStableSubopen ρ i.stable
      (i.U ⊓ i.U))).trans htop

/-- Each quotient-side overlap represents the full Galois quotient of the
restricted action on the corresponding source overlap. -/
theorem isGaloisQuotient_overlap [FiniteDimensional K L] [IsGalois K L]
    (i j : StableAffineOpen ρ) :
    IsGaloisQuotient (ρ.restrict (inf_stable ρ i j))
      (quotientOverlapι ρ i j ≫ quotientChartMap ρ i) := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.isGaloisQuotient_quotientOpenOfStableSubopen
    ρ i.stable i.affine inf_le_left (inf_stable ρ i j)

/-- The quotient map from the source intersection to its quotient-side overlap. -/
noncomputable def overlapQuotientMap [FiniteDimensional K L]
    (i j : StableAffineOpen ρ) :
    (i.U ⊓ j.U).toScheme ⟶ quotientOverlap ρ i j := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.stableAffineQuotientMapRestrict
    ρ i.stable i.affine inf_le_left (inf_stable ρ i j)

/-- The pairwise overlap projection followed by its chart inclusion is the
ambient affine quotient map restricted from the source overlap. -/
@[reassoc]
theorem overlapQuotientMap_fac [FiniteDimensional K L]
    (i j : StableAffineOpen ρ) :
    overlapQuotientMap ρ i j ≫ quotientOverlapι ρ i j =
      X.homOfLE inf_le_left ≫
        SemilinearGalAction.stableAffineQuotientMap
          ρ i.stable i.affine := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.stableAffineQuotientMapRestrict_fac
    ρ i.stable i.affine inf_le_left (inf_stable ρ i j)

/-- The specified restricted quotient witness on a pairwise overlap. -/
noncomputable def overlapWitness [FiniteDimensional K L] [IsGalois K L]
    (i j : StableAffineOpen ρ) :
    GaloisQuotientWitnessWithProjection (ρ.restrict (inf_stable ρ i j))
      (quotientOverlap ρ i j)
      (quotientOverlapι ρ i j ≫ quotientChartMap ρ i)
      (overlapQuotientMap ρ i j) := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.galoisQuotientWitness_quotientOpenOfStableSubopen
    ρ i.stable i.affine inf_le_left (inf_stable ρ i j)

/-- The source open underlying the triple overlap in chart `i` is stable. -/
theorem triple_stable (i j k : StableAffineOpen ρ) :
    ρ.IsStableOpen ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) := by
  intro γ
  simp only [Scheme.Hom.preimage_inf, i.stable γ, j.stable γ, k.stable γ]

/-- The quotient open corresponding to the triple overlap in chart `i`. -/
noncomputable def quotientTriple (i j k : StableAffineOpen ρ) : Scheme.{u} := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact (SemilinearGalAction.quotientOpenOfStableSubopen ρ i.stable
    ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U))).toScheme

/-- The triple-overlap inclusion into its quotient chart. -/
noncomputable def quotientTripleι (i j k : StableAffineOpen ρ) :
    quotientTriple ρ i j k ⟶ quotientChart ρ i := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact (SemilinearGalAction.quotientOpenOfStableSubopen ρ i.stable
    ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U))).ι

/-- The triple quotient open has the full quotient universal property. -/
theorem isGaloisQuotient_triple [FiniteDimensional K L] [IsGalois K L]
    (i j k : StableAffineOpen ρ) :
    IsGaloisQuotient (ρ.restrict (triple_stable ρ i j k))
      (quotientTripleι ρ i j k ≫ quotientChartMap ρ i) := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.isGaloisQuotient_quotientOpenOfStableSubopen
    ρ i.stable i.affine (le_trans inf_le_left inf_le_left)
      (triple_stable ρ i j k)

/-- The quotient map from the source triple intersection to its quotient open. -/
noncomputable def tripleQuotientMap [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)).toScheme ⟶
      quotientTriple ρ i j k := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.stableAffineQuotientMapRestrict
    ρ i.stable i.affine (le_trans inf_le_left inf_le_left)
      (triple_stable ρ i j k)

/-- The triple-overlap projection followed by its chart inclusion is the
ambient affine quotient map restricted from the source triple intersection. -/
@[reassoc]
theorem tripleQuotientMap_fac [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    tripleQuotientMap ρ i j k ≫ quotientTripleι ρ i j k =
      X.homOfLE (le_trans inf_le_left inf_le_left) ≫
        SemilinearGalAction.stableAffineQuotientMap
          ρ i.stable i.affine := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.stableAffineQuotientMapRestrict_fac
    ρ i.stable i.affine (le_trans inf_le_left inf_le_left)
      (triple_stable ρ i j k)

/-- The specified restricted quotient witness on a triple overlap. -/
noncomputable def tripleWitness [FiniteDimensional K L] [IsGalois K L]
    (i j k : StableAffineOpen ρ) :
    GaloisQuotientWitnessWithProjection (ρ.restrict (triple_stable ρ i j k))
      (quotientTriple ρ i j k)
      (quotientTripleι ρ i j k ≫ quotientChartMap ρ i)
      (tripleQuotientMap ρ i j k) := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.galoisQuotientWitness_quotientOpenOfStableSubopen
    ρ i.stable i.affine (le_trans inf_le_left inf_le_left)
      (triple_stable ρ i j k)

/-- The triple quotient open in chart `i` lies in its pairwise overlap with
chart `j`. -/
theorem quotientTriple_le_overlapLeft [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    letI := ρ.sectionsMulSemiringAction i.stable
    letI := SemilinearGalAction.sectionsAlgebra f i.U
    letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
    letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
    letI := ρ.isSemilinear_sections i.stable
    SemilinearGalAction.quotientOpenOfStableSubopen ρ i.stable
        ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) ≤
      SemilinearGalAction.quotientOpenOfStableSubopen ρ i.stable
        (i.U ⊓ j.U) := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.quotientOpenOfStableSubopen_mono
    ρ i.stable i.affine
    (le_trans inf_le_left inf_le_left) inf_le_left inf_le_left
    (triple_stable ρ i j k) (inf_stable ρ i j)

/-- The canonical restriction from a triple quotient open to its left
pairwise overlap. -/
noncomputable def tripleToOverlapLeft [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    quotientTriple ρ i j k ⟶ quotientOverlap ρ i j := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  unfold quotientTriple quotientOverlap
  exact Scheme.homOfLE _ (quotientTriple_le_overlapLeft ρ i j k)

/-- Restricting a triple quotient open and then including the pairwise overlap
is its original inclusion into the quotient chart. -/
@[reassoc]
theorem tripleToOverlapLeft_fac [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    tripleToOverlapLeft ρ i j k ≫ quotientOverlapι ρ i j =
      quotientTripleι ρ i j k := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  unfold tripleToOverlapLeft quotientOverlapι quotientTripleι
    quotientOverlap quotientTriple
  exact Scheme.homOfLE_ι _ (quotientTriple_le_overlapLeft ρ i j k)

/-- The pinned triple quotient projection restricts to the pinned pairwise
quotient projection. -/
@[reassoc]
theorem tripleQuotientMap_tripleToOverlapLeft [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    tripleQuotientMap ρ i j k ≫ tripleToOverlapLeft ρ i j k =
      X.homOfLE inf_le_left ≫ overlapQuotientMap ρ i j := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  rw [← cancel_mono (quotientOverlapι ρ i j)]
  rw [Category.assoc, tripleToOverlapLeft_fac]
  rw [tripleQuotientMap_fac, Category.assoc, overlapQuotientMap_fac]
  rw [← Scheme.homOfLE_homOfLE X
    (show ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) ≤ i.U ⊓ j.U from inf_le_left)
    (show i.U ⊓ j.U ≤ i.U from inf_le_left), Category.assoc]
  rfl

/-- The triple quotient open in chart `i` also lies in its pairwise overlap
with chart `k`. -/
theorem quotientTriple_le_overlapRight [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    letI := ρ.sectionsMulSemiringAction i.stable
    letI := SemilinearGalAction.sectionsAlgebra f i.U
    letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
    letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
    letI := ρ.isSemilinear_sections i.stable
    SemilinearGalAction.quotientOpenOfStableSubopen ρ i.stable
        ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) ≤
      SemilinearGalAction.quotientOpenOfStableSubopen ρ i.stable
        (i.U ⊓ k.U) := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.quotientOpenOfStableSubopen_mono
    ρ i.stable i.affine
    (le_trans inf_le_left inf_le_left) inf_le_left inf_le_right
    (triple_stable ρ i j k) (inf_stable ρ i k)

/-- The canonical restriction from a triple quotient open to its right
pairwise overlap. -/
noncomputable def tripleToOverlapRight [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    quotientTriple ρ i j k ⟶ quotientOverlap ρ i k := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  unfold quotientTriple quotientOverlap
  exact Scheme.homOfLE _ (quotientTriple_le_overlapRight ρ i j k)

/-- Restricting a triple quotient open to the right pairwise overlap and then
including it recovers the triple inclusion. -/
@[reassoc]
theorem tripleToOverlapRight_fac [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    tripleToOverlapRight ρ i j k ≫ quotientOverlapι ρ i k =
      quotientTripleι ρ i j k := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  unfold tripleToOverlapRight quotientOverlapι quotientTripleι
    quotientOverlap quotientTriple
  exact Scheme.homOfLE_ι _ (quotientTriple_le_overlapRight ρ i j k)

/-- The pinned triple projection restricts to the pinned right pairwise
quotient projection. -/
@[reassoc]
theorem tripleQuotientMap_tripleToOverlapRight [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    tripleQuotientMap ρ i j k ≫ tripleToOverlapRight ρ i j k =
      X.homOfLE inf_le_right ≫ overlapQuotientMap ρ i k := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  rw [← cancel_mono (quotientOverlapι ρ i k)]
  rw [Category.assoc, tripleToOverlapRight_fac]
  rw [tripleQuotientMap_fac, Category.assoc, overlapQuotientMap_fac]
  rw [← Scheme.homOfLE_homOfLE X
    (show ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) ≤ i.U ⊓ k.U from inf_le_right)
    (show i.U ⊓ k.U ≤ i.U from inf_le_left), Category.assoc]
  rfl

/-- The pullback of two quotient overlaps in a chart is the quotient of their
triple source intersection. -/
noncomputable def pullbackOverlapIsoTriple [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    pullback (quotientOverlapι ρ i j) (quotientOverlapι ρ i k) ≅
      quotientTriple ρ i j k := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  unfold quotientOverlapι quotientOverlap quotientChart quotientTriple
  let A := SemilinearGalAction.quotientOpenOfStableSubopen
    ρ i.stable (i.U ⊓ j.U)
  let B := SemilinearGalAction.quotientOpenOfStableSubopen
    ρ i.stable (i.U ⊓ k.U)
  let Q := Spec (CommRingCat.of
    (SemilinearAction.invariantsSubalgebra K L Γ(X, i.U)))
  have himage : A.ι ''ᵁ (A.ι ⁻¹ᵁ B) = A ⊓ B := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
  have hinf :
      SemilinearGalAction.quotientOpenOfStableSubopen ρ i.stable
          ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) = A ⊓ B :=
    SemilinearGalAction.quotientOpenOfStableSubopen_inf
      ρ i.stable i.affine inf_le_left inf_le_left
      (inf_stable ρ i j) (inf_stable ρ i k)
  exact pullbackRestrictIsoRestrict A.ι B ≪≫
    A.ι.isoImage (A.ι ⁻¹ᵁ B) ≪≫
    Q.isoOfEq himage ≪≫
    Q.isoOfEq hinf.symm

/-- The pullback-to-triple isomorphism identifies the first pullback
projection with restriction to the left pairwise overlap. -/
@[reassoc]
theorem pullbackOverlapIsoTriple_hom_fst [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    (pullbackOverlapIsoTriple ρ i j k).hom ≫
        tripleToOverlapLeft ρ i j k =
      pullback.fst (quotientOverlapι ρ i j) (quotientOverlapι ρ i k) := by
  rw [← cancel_mono (quotientOverlapι ρ i j)]
  rw [Category.assoc, tripleToOverlapLeft_fac]
  unfold pullbackOverlapIsoTriple quotientTripleι quotientOverlapι
    quotientTriple quotientOverlap quotientChart
  simp

/-- The pullback-to-triple isomorphism identifies the second pullback
projection with restriction to the right pairwise overlap. -/
@[reassoc]
theorem pullbackOverlapIsoTriple_hom_snd [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    (pullbackOverlapIsoTriple ρ i j k).hom ≫
        tripleToOverlapRight ρ i j k =
      pullback.snd (quotientOverlapι ρ i j) (quotientOverlapι ρ i k) := by
  rw [← cancel_mono (quotientOverlapι ρ i k)]
  rw [Category.assoc, tripleToOverlapRight_fac]
  unfold pullbackOverlapIsoTriple quotientTripleι quotientOverlapι
    quotientTriple quotientOverlap quotientChart
  simpa using (pullback.condition :
    pullback.fst
        (SemilinearGalAction.quotientOpenOfStableSubopen
          ρ i.stable (i.U ⊓ j.U)).ι
        (SemilinearGalAction.quotientOpenOfStableSubopen
          ρ i.stable (i.U ⊓ k.U)).ι ≫
      (SemilinearGalAction.quotientOpenOfStableSubopen
        ρ i.stable (i.U ⊓ j.U)).ι =
    pullback.snd
        (SemilinearGalAction.quotientOpenOfStableSubopen
          ρ i.stable (i.U ⊓ j.U)).ι
        (SemilinearGalAction.quotientOpenOfStableSubopen
          ρ i.stable (i.U ⊓ k.U)).ι ≫
      (SemilinearGalAction.quotientOpenOfStableSubopen
        ρ i.stable (i.U ⊓ k.U)).ι)

/-- The inverse pullback-to-triple isomorphism followed by the second
pullback projection is restriction to the right pairwise overlap. -/
@[reassoc]
theorem pullbackOverlapIsoTriple_inv_snd [FiniteDimensional K L]
    (i j k : StableAffineOpen ρ) :
    (pullbackOverlapIsoTriple ρ i j k).inv ≫
        pullback.snd (quotientOverlapι ρ i j) (quotientOverlapι ρ i k) =
      tripleToOverlapRight ρ i j k := by
  rw [← pullbackOverlapIsoTriple_hom_snd]
  simp

/-- The next cyclic chart's triple quotient is a quotient of the same restricted
action, transported along associativity and commutativity of intersection. -/
theorem isGaloisQuotient_triple_rot [FiniteDimensional K L] [IsGalois K L]
    (i j k : StableAffineOpen ρ) :
    IsGaloisQuotient (ρ.restrict (triple_stable ρ i j k))
      (quotientTripleι ρ j k i ≫ quotientChartMap ρ j) := by
  let eOpen : ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) =
      ((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)) := by ac_rfl
  let e := X.isoOfEq eOpen
  have hef : e.hom ≫
      (((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)).ι ≫ f) =
        ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)).ι ≫ f := by
    dsimp only [e]
    rw [← Category.assoc, Scheme.isoOfEq_hom_ι]
  exact isGaloisQuotient_congr
    (ρ.restrict (triple_stable ρ i j k))
    (ρ.restrict (triple_stable ρ j k i))
    e hef (SemilinearGalAction.restrict_isoOfEq_isEquivariant ρ _ _ _)
    (isGaloisQuotient_triple ρ j k i)

/-- The next cyclic triple witness, transported to the source triple action. -/
noncomputable def tripleWitnessRot [FiniteDimensional K L] [IsGalois K L]
    (i j k : StableAffineOpen ρ) :
    GaloisQuotientWitnessWithProjection (ρ.restrict (triple_stable ρ i j k))
      (quotientTriple ρ j k i)
      (quotientTripleι ρ j k i ≫ quotientChartMap ρ j)
      ((X.isoOfEq (show ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) =
        ((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)) by ac_rfl)).hom ≫
          tripleQuotientMap ρ j k i) := by
  let eOpen : ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) =
      ((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)) := by ac_rfl
  let e := X.isoOfEq eOpen
  have hef : e.hom ≫
      (((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)).ι ≫ f) =
        ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)).ι ≫ f := by
    dsimp only [e]
    rw [← Category.assoc, Scheme.isoOfEq_hom_ι]
  exact GaloisQuotientWitnessWithProjection.transport
    (ρ.restrict (triple_stable ρ i j k))
    (ρ.restrict (triple_stable ρ j k i))
    e hef (SemilinearGalAction.restrict_isoOfEq_isEquivariant ρ _ _ _)
    (tripleWitness ρ j k i)

/-- Rotating a triple intersection and then restricting to `j ∩ i` agrees
with first restricting to `i ∩ j` and commuting the two factors. -/
@[reassoc]
theorem tripleSourceToOverlapRev (i j k : StableAffineOpen ρ) :
    X.homOfLE
        (show ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) ≤ i.U ⊓ j.U from inf_le_left) ≫
        (X.isoOfEq (inf_comm i.U j.U)).hom =
      (X.isoOfEq (show ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) =
        ((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)) by ac_rfl)).hom ≫
        X.homOfLE
          (show ((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)) ≤ j.U ⊓ i.U from inf_le_right) := by
  rw [← cancel_mono ((j.U ⊓ i.U).ι)]
  simp

/-- The canonical cyclic comparison between two presentations of a triple
quotient overlap. -/
noncomputable def tripleIso [FiniteDimensional K L] [IsGalois K L]
    (i j k : StableAffineOpen ρ) :
    quotientTriple ρ i j k ≅ quotientTriple ρ j k i :=
  GaloisQuotientWitness.uniqueIso
    (tripleWitness ρ i j k).toGaloisQuotientWitness
    (tripleWitnessRot ρ i j k).toGaloisQuotientWitness

/-- The cyclic triple comparison intertwines the two pinned quotient
projections. -/
@[reassoc]
theorem tripleIso_hom_quotientMap [FiniteDimensional K L] [IsGalois K L]
    (i j k : StableAffineOpen ρ) :
    tripleQuotientMap ρ i j k ≫ (tripleIso ρ i j k).hom =
      (X.isoOfEq (show ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) =
        ((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)) by ac_rfl)).hom ≫
          tripleQuotientMap ρ j k i := by
  simpa [tripleIso, GaloisQuotientWitness.uniqueIso] using
    GaloisQuotientWitness.comparison_quotientMap
      (tripleWitness ρ i j k) (tripleWitnessRot ρ i j k)

/-- Three cyclic reorderings of a source triple intersection compose to the
identity. -/
theorem tripleSourceRotation_cocycle (i j k : StableAffineOpen ρ) :
    (X.isoOfEq (show ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) =
      ((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)) by ac_rfl)).hom ≫
    (X.isoOfEq (show ((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)) =
      ((k.U ⊓ i.U) ⊓ (k.U ⊓ j.U)) by ac_rfl)).hom ≫
    (X.isoOfEq (show ((k.U ⊓ i.U) ⊓ (k.U ⊓ j.U)) =
      ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) by ac_rfl)).hom = 𝟙 _ := by
  rw [← cancel_mono (((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)).ι)]
  simp

/-- The canonical cyclic comparisons of the three presentations of a triple
quotient satisfy the cocycle. -/
theorem tripleIso_cocycle [FiniteDimensional K L] [IsGalois K L]
    (i j k : StableAffineOpen ρ) :
    (tripleIso ρ i j k).hom ≫ (tripleIso ρ j k i).hom ≫
      (tripleIso ρ k i j).hom = 𝟙 _ := by
  have h₁ := tripleIso_hom_quotientMap ρ i j k
  have h₂ := tripleIso_hom_quotientMap ρ j k i
  have h₃ := tripleIso_hom_quotientMap ρ k i j
  have hrot := tripleSourceRotation_cocycle (ρ := ρ) i j k
  letI : Epi (tripleQuotientMap ρ i j k) :=
    GaloisQuotientWitnessWithProjection.epi_quotientMap
      (tripleWitness ρ i j k)
  rw [← cancel_epi (tripleQuotientMap ρ i j k)]
  simp only [Category.comp_id]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃, reassoc_of% hrot]

/-- The triple-overlap transition in the shape required by
`CategoryTheory.GlueData.t'`. -/
noncomputable def overlapTransition' [FiniteDimensional K L] [IsGalois K L]
    (i j k : StableAffineOpen ρ) :
    pullback (quotientOverlapι ρ i j) (quotientOverlapι ρ i k) ⟶
      pullback (quotientOverlapι ρ j k) (quotientOverlapι ρ j i) :=
  (pullbackOverlapIsoTriple ρ i j k).hom ≫
    (tripleIso ρ i j k).hom ≫
    (pullbackOverlapIsoTriple ρ j k i).inv

/-- The quotient constructed from the reversed chart is also a quotient of the
restriction to `i.U ⊓ j.U`, transported along commutativity of intersection. -/
theorem isGaloisQuotient_overlap_rev [FiniteDimensional K L] [IsGalois K L]
    (i j : StableAffineOpen ρ) :
    IsGaloisQuotient (ρ.restrict (inf_stable ρ i j))
      (quotientOverlapι ρ j i ≫ quotientChartMap ρ j) := by
  let e := X.isoOfEq (inf_comm i.U j.U)
  have hef : e.hom ≫ ((j.U ⊓ i.U).ι ≫ f) = (i.U ⊓ j.U).ι ≫ f := by
    dsimp only [e]
    rw [← Category.assoc, Scheme.isoOfEq_hom_ι]
  exact isGaloisQuotient_congr
    (ρ.restrict (inf_stable ρ i j)) (ρ.restrict (inf_stable ρ j i))
    e hef (SemilinearGalAction.restrict_isoOfEq_isEquivariant ρ _ _ _)
    (isGaloisQuotient_overlap ρ j i)

/-- The reversed pairwise overlap witness, transported to the same restricted
action as `overlapWitness ρ i j`. -/
noncomputable def overlapWitnessRev [FiniteDimensional K L] [IsGalois K L]
    (i j : StableAffineOpen ρ) :
    GaloisQuotientWitnessWithProjection (ρ.restrict (inf_stable ρ i j))
      (quotientOverlap ρ j i)
      (quotientOverlapι ρ j i ≫ quotientChartMap ρ j)
      ((X.isoOfEq (inf_comm i.U j.U)).hom ≫ overlapQuotientMap ρ j i) := by
  let e := X.isoOfEq (inf_comm i.U j.U)
  have hef : e.hom ≫ ((j.U ⊓ i.U).ι ≫ f) = (i.U ⊓ j.U).ι ≫ f := by
    dsimp only [e]
    rw [← Category.assoc, Scheme.isoOfEq_hom_ι]
  exact GaloisQuotientWitnessWithProjection.transport
    (ρ.restrict (inf_stable ρ i j)) (ρ.restrict (inf_stable ρ j i))
    e hef (SemilinearGalAction.restrict_isoOfEq_isEquivariant ρ _ _ _)
    (overlapWitness ρ j i)

/-- The canonical transition isomorphism between the two quotient presentations
of an overlap. -/
noncomputable def overlapIso [FiniteDimensional K L] [IsGalois K L]
    (i j : StableAffineOpen ρ) :
    quotientOverlap ρ i j ≅ quotientOverlap ρ j i := by
  classical
  by_cases h : i = j
  · subst j
    exact Iso.refl _
  · exact GaloisQuotientWitness.uniqueIso
      (overlapWitness ρ i j).toGaloisQuotientWitness
      (overlapWitnessRev ρ i j).toGaloisQuotientWitness

/-- The overlap transition intertwines the two pinned quotient projections. -/
@[reassoc]
theorem overlapIso_hom_quotientMap [FiniteDimensional K L] [IsGalois K L]
    (i j : StableAffineOpen ρ) :
    overlapQuotientMap ρ i j ≫ (overlapIso ρ i j).hom =
      (X.isoOfEq (inf_comm i.U j.U)).hom ≫
        overlapQuotientMap ρ j i := by
  classical
  by_cases h : i = j
  · subst j
    simp [overlapIso]
  · simpa [overlapIso, h, GaloisQuotientWitness.uniqueIso] using
      GaloisQuotientWitness.comparison_quotientMap
        (overlapWitness ρ i j) (overlapWitnessRev ρ i j)

/-- On a triple overlap, the pairwise transition agrees with the canonical
cyclic comparison of the two triple quotient presentations. -/
@[reassoc]
theorem tripleToOverlapLeft_overlapIso [FiniteDimensional K L] [IsGalois K L]
    (i j k : StableAffineOpen ρ) :
    tripleToOverlapLeft ρ i j k ≫ (overlapIso ρ i j).hom =
      (tripleIso ρ i j k).hom ≫ tripleToOverlapRight ρ j k i := by
  letI : Epi (tripleQuotientMap ρ i j k) :=
    GaloisQuotientWitnessWithProjection.epi_quotientMap
      (tripleWitness ρ i j k)
  rw [← cancel_epi (tripleQuotientMap ρ i j k)]
  calc
    tripleQuotientMap ρ i j k ≫
          (tripleToOverlapLeft ρ i j k ≫ (overlapIso ρ i j).hom) =
        (tripleQuotientMap ρ i j k ≫ tripleToOverlapLeft ρ i j k) ≫
          (overlapIso ρ i j).hom := (Category.assoc _ _ _).symm
    _ = (X.homOfLE inf_le_left ≫ overlapQuotientMap ρ i j) ≫
          (overlapIso ρ i j).hom := by
      rw [tripleQuotientMap_tripleToOverlapLeft]
    _ = X.homOfLE inf_le_left ≫
          (overlapQuotientMap ρ i j ≫ (overlapIso ρ i j).hom) :=
      Category.assoc _ _ _
    _ = X.homOfLE inf_le_left ≫
          ((X.isoOfEq (inf_comm i.U j.U)).hom ≫
            overlapQuotientMap ρ j i) := by
      rw [overlapIso_hom_quotientMap]
    _ = (X.homOfLE inf_le_left ≫
          (X.isoOfEq (inf_comm i.U j.U)).hom) ≫
            overlapQuotientMap ρ j i := (Category.assoc _ _ _).symm
    _ = ((X.isoOfEq (show ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) =
          ((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)) by ac_rfl)).hom ≫
          X.homOfLE inf_le_right) ≫ overlapQuotientMap ρ j i := by
      rw [tripleSourceToOverlapRev]
    _ = (X.isoOfEq (show ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) =
          ((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)) by ac_rfl)).hom ≫
          (X.homOfLE inf_le_right ≫ overlapQuotientMap ρ j i) :=
      Category.assoc _ _ _
    _ = (X.isoOfEq (show ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) =
          ((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)) by ac_rfl)).hom ≫
          (tripleQuotientMap ρ j k i ≫ tripleToOverlapRight ρ j k i) := by
      rw [tripleQuotientMap_tripleToOverlapRight]
    _ = ((X.isoOfEq (show ((i.U ⊓ j.U) ⊓ (i.U ⊓ k.U)) =
          ((j.U ⊓ k.U) ⊓ (j.U ⊓ i.U)) by ac_rfl)).hom ≫
          tripleQuotientMap ρ j k i) ≫ tripleToOverlapRight ρ j k i :=
      (Category.assoc _ _ _).symm
    _ = (tripleQuotientMap ρ i j k ≫ (tripleIso ρ i j k).hom) ≫
          tripleToOverlapRight ρ j k i := by
      rw [tripleIso_hom_quotientMap]
    _ = tripleQuotientMap ρ i j k ≫
          ((tripleIso ρ i j k).hom ≫ tripleToOverlapRight ρ j k i) :=
      Category.assoc _ _ _

/-- The triple-overlap transition has the factorization required by
`CategoryTheory.GlueData.t_fac`. -/
@[reassoc]
theorem overlapTransition'_fac [FiniteDimensional K L] [IsGalois K L]
    (i j k : StableAffineOpen ρ) :
    overlapTransition' ρ i j k ≫
        pullback.snd (quotientOverlapι ρ j k) (quotientOverlapι ρ j i) =
      pullback.fst (quotientOverlapι ρ i j) (quotientOverlapι ρ i k) ≫
        (overlapIso ρ i j).hom := by
  simp only [overlapTransition', Category.assoc]
  rw [pullbackOverlapIsoTriple_inv_snd]
  rw [← tripleToOverlapLeft_overlapIso]
  rw [← Category.assoc, pullbackOverlapIsoTriple_hom_fst]

/-- The three cyclic triple-overlap transitions compose to the identity. -/
theorem overlapTransition'_cocycle [FiniteDimensional K L] [IsGalois K L]
    (i j k : StableAffineOpen ρ) :
    overlapTransition' ρ i j k ≫ overlapTransition' ρ j k i ≫
      overlapTransition' ρ k i j = 𝟙 _ := by
  simp only [overlapTransition', Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% tripleIso_cocycle ρ i j k]
  simp

/-- The overlap transition lies over `Spec K`. -/
@[reassoc]
theorem overlapIso_hom_base [FiniteDimensional K L] [IsGalois K L]
    (i j : StableAffineOpen ρ) :
    (overlapIso ρ i j).hom ≫
        (quotientOverlapι ρ j i ≫ quotientChartMap ρ j) =
      quotientOverlapι ρ i j ≫ quotientChartMap ρ i := by
  classical
  by_cases h : i = j
  · subst j
    simp [overlapIso]
  · simpa [overlapIso, h, GaloisQuotientWitness.uniqueIso] using
      (GaloisQuotientWitness.comparison
        (overlapWitness ρ i j).toGaloisQuotientWitness
        (overlapWitnessRev ρ i j).toGaloisQuotientWitness).2

/-- The self-transition is the identity. -/
@[simp]
theorem overlapIso_self [FiniteDimensional K L] [IsGalois K L]
    (i : StableAffineOpen ρ) : overlapIso ρ i i = Iso.refl _ := by
  simp [overlapIso]

/-- The gluing datum of invariant-ring quotient charts attached to all stable
affine opens of the acted scheme. -/
noncomputable def quotientGlueData [FiniteDimensional K L] [IsGalois K L] :
    Scheme.GlueData where
  J := StableAffineOpen ρ
  U i := quotientChart ρ i
  V p := quotientOverlap ρ p.1 p.2
  f i j := quotientOverlapι ρ i j
  f_id i := quotientOverlapι_self_isIso ρ i
  f_open i j := quotientOverlapι_isOpenImmersion ρ i j
  t i j := (overlapIso ρ i j).hom
  t_id i := by rw [overlapIso_self]; rfl
  t' i j k := overlapTransition' ρ i j k
  t_fac i j k := overlapTransition'_fac ρ i j k
  cocycle i j k := overlapTransition'_cocycle ρ i j k

/-- In a glued quotient chart, the inverse image of another chart is exactly
the quotient overlap used in the gluing datum. -/
theorem quotientGlueData_chart_preimage_opensRange
    [FiniteDimensional K L] [IsGalois K L]
    (i j : StableAffineOpen ρ) :
    (quotientGlueData ρ).ι j ⁻¹ᵁ
        ((quotientGlueData ρ).ι i).opensRange =
      (quotientOverlapι ρ j i).opensRange := by
  have hp := IsPullback.of_isLimit
    ((quotientGlueData ρ).vPullbackConeIsLimit j i)
  change (quotientGlueData ρ).ι j ⁻¹ᵁ
      ((quotientGlueData ρ).ι i).opensRange =
    ((quotientGlueData ρ).f j i).opensRange
  rw [← Scheme.Hom.opensRange_pullbackFst]
  have hfst := hp.isoPullback_hom_fst
  change hp.isoPullback.hom ≫
      pullback.fst ((quotientGlueData ρ).ι j) ((quotientGlueData ρ).ι i) =
    (quotientGlueData ρ).f j i at hfst
  have hrange :
      (hp.isoPullback.hom ≫
        pullback.fst ((quotientGlueData ρ).ι j) ((quotientGlueData ρ).ι i)).opensRange =
      (pullback.fst ((quotientGlueData ρ).ι j)
        ((quotientGlueData ρ).ι i)).opensRange := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_of_isIso]
    simp
  rw [← hrange]
  congr 1

/-- The scheme obtained by gluing all stable affine invariant-ring quotient
charts. -/
noncomputable def gluedQuotient [FiniteDimensional K L] [IsGalois K L] :
    Scheme := (quotientGlueData ρ).glued

/-- The quotient projection on a stable affine chart, followed by its inclusion
into the glued quotient. -/
noncomputable def quotientChartProjection [FiniteDimensional K L] [IsGalois K L]
    (i : StableAffineOpen ρ) : i.U.toScheme ⟶ gluedQuotient ρ :=
  SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine ≫
    (quotientGlueData ρ).ι i

/-- A local quotient projection pulls a glued quotient chart back to the
corresponding source-chart intersection. -/
theorem quotientChartProjection_preimage_opensRange
    [FiniteDimensional K L] [IsGalois K L]
    (i j : StableAffineOpen ρ) :
    quotientChartProjection ρ j ⁻¹ᵁ
        ((quotientGlueData ρ).ι i).opensRange =
      j.U.ι ⁻¹ᵁ i.U := by
  unfold quotientChartProjection
  rw [Scheme.Hom.comp_preimage]
  calc
    _ = SemilinearGalAction.stableAffineQuotientMap
          ρ j.stable j.affine ⁻¹ᵁ
        (quotientOverlapι ρ j i).opensRange :=
      congrArg
        (fun U ↦ SemilinearGalAction.stableAffineQuotientMap
          ρ j.stable j.affine ⁻¹ᵁ U)
        (quotientGlueData_chart_preimage_opensRange ρ i j)
    _ = _ := by
      letI := ρ.sectionsMulSemiringAction j.stable
      letI := SemilinearGalAction.sectionsAlgebra f j.U
      letI := SemilinearGalAction.sectionsAlgebraK (K := K) f j.U
      letI := SemilinearGalAction.sections_isScalarTower (K := K) f j.U
      letI := ρ.isSemilinear_sections j.stable
      unfold quotientOverlapι quotientOverlap quotientChart
      rw [Scheme.Opens.opensRange_ι]
      rw [SemilinearGalAction.stableAffineQuotientMap_preimage_quotientOpen
        ρ j.stable j.affine inf_le_left (inf_stable ρ j i)]
      simp only [Scheme.Hom.preimage_inf]
      simp

/-- The quotient projection of a stable affine chart lies over `Spec K`. -/
@[reassoc]
theorem stableAffineQuotientMap_quotientChartMap
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine ≫
        quotientChartMap ρ i =
      (i.U.ι ≫ f) ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  let w := SemilinearGalAction.galoisQuotientWitness_quotientOpenOfStableSubopen
    ρ i.stable i.affine le_rfl i.stable
  have hw := GaloisQuotientWitnessWithProjection.quotientMap_comp_base w
  have hfac := SemilinearGalAction.stableAffineQuotientMapRestrict_fac
    ρ i.stable i.affine le_rfl i.stable
  calc
    SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine ≫
          quotientChartMap ρ i =
        (X.homOfLE le_rfl ≫
          SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine) ≫
            quotientChartMap ρ i := by rw [Scheme.homOfLE_rfl, Category.id_comp]
    _ = (SemilinearGalAction.stableAffineQuotientMapRestrict
          ρ i.stable i.affine le_rfl i.stable ≫
        (SemilinearGalAction.quotientOpenOfStableSubopen ρ i.stable i.U).ι) ≫
          quotientChartMap ρ i :=
      congrArg (fun z ↦ z ≫ quotientChartMap ρ i) hfac.symm
    _ = SemilinearGalAction.stableAffineQuotientMapRestrict
          ρ i.stable i.affine le_rfl i.stable ≫
        ((SemilinearGalAction.quotientOpenOfStableSubopen ρ i.stable i.U).ι ≫
          quotientChartMap ρ i) := Category.assoc _ _ _
    _ = (i.U.ι ≫ f) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := hw

/-- The quotient-side open attached to the whole source chart. -/
noncomputable def quotientChartTopOpen (i : StableAffineOpen ρ) :
    (quotientChart ρ i).Opens := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.quotientOpenOfStableSubopen ρ i.stable i.U

/-- The quotient-side open attached to the whole source chart is the whole
quotient chart. -/
theorem quotientChartTopOpen_eq_top [FiniteDimensional K L]
    (i : StableAffineOpen ρ) : quotientChartTopOpen ρ i = ⊤ := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.quotientOpenOfStableSubopen_self
    ρ i.stable i.affine

instance quotientChartTopOpen_ι_isIso [FiniteDimensional K L]
    (i : StableAffineOpen ρ) : IsIso (quotientChartTopOpen ρ i).ι := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [Scheme.Opens.opensRange_ι, quotientChartTopOpen_eq_top]

/-- The projection-carrying quotient witness obtained by restricting a stable
affine chart to the whole chart. -/
noncomputable def quotientChartTopWitness
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    GaloisQuotientWitnessWithProjection (ρ.restrict i.stable)
      (quotientChartTopOpen ρ i).toScheme
      ((quotientChartTopOpen ρ i).ι ≫ quotientChartMap ρ i)
      (SemilinearGalAction.stableAffineQuotientMapRestrict
        ρ i.stable i.affine le_rfl i.stable) := by
  letI := ρ.sectionsMulSemiringAction i.stable
  letI := SemilinearGalAction.sectionsAlgebra f i.U
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f i.U
  letI := SemilinearGalAction.sections_isScalarTower (K := K) f i.U
  letI := ρ.isSemilinear_sections i.stable
  exact SemilinearGalAction.galoisQuotientWitness_quotientOpenOfStableSubopen
    ρ i.stable i.affine le_rfl i.stable

/-- The affine quotient map on a stable chart is invariant under the restricted
Galois action. -/
@[reassoc]
theorem restrict_act_hom_stableAffineQuotientMap
    [FiniteDimensional K L] [IsGalois K L]
    (i : StableAffineOpen ρ) (gamma : L ≃ₐ[K] L) :
    ((ρ.restrict i.stable).act gamma).hom ≫
        SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine =
      SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine := by
  let q := SemilinearGalAction.stableAffineQuotientMapRestrict
    ρ i.stable i.affine le_rfl i.stable
  let W := quotientChartTopOpen ρ i
  have hfac : q ≫ W.ι =
      SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine := by
    dsimp only [q, W, quotientChartTopOpen, quotientChart]
    simpa only [Scheme.homOfLE_rfl, Category.id_comp] using
      (SemilinearGalAction.stableAffineQuotientMapRestrict_fac
        ρ i.stable i.affine le_rfl i.stable)
  have hinv := GaloisQuotientWitnessWithProjection.act_hom_comp_quotientMap
    (quotientChartTopWitness ρ i) gamma
  change ((ρ.restrict i.stable).act gamma).hom ≫ q = q at hinv
  rw [← hfac]
  change (((ρ.restrict i.stable).act gamma).hom ≫ q) ≫ W.ι = q ≫ W.ι
  exact congrArg (fun z ↦ z ≫ W.ι) hinv

/-- The local projection into the glued quotient is Galois-invariant. -/
@[reassoc]
theorem restrict_act_hom_quotientChartProjection
    [FiniteDimensional K L] [IsGalois K L]
    (i : StableAffineOpen ρ) (gamma : L ≃ₐ[K] L) :
    ((ρ.restrict i.stable).act gamma).hom ≫
        quotientChartProjection ρ i = quotientChartProjection ρ i := by
  unfold quotientChartProjection
  rw [← Category.assoc, restrict_act_hom_stableAffineQuotientMap]

/-- Base change of the whole-chart quotient-open inclusion to `Spec L`. -/
noncomputable def quotientChartTopPullbackMap
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    pullback ((quotientChartTopOpen ρ i).ι ≫ quotientChartMap ρ i)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
      pullback (quotientChartMap ρ i)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  pullbackBaseChange K L (quotientChartMap ρ i)
    ((quotientChartTopOpen ρ i).ι ≫ quotientChartMap ρ i)
    (quotientChartTopOpen ρ i).ι rfl

instance quotientChartTopPullbackMap_isIso
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    IsIso (quotientChartTopPullbackMap ρ i) := by
  unfold quotientChartTopPullbackMap pullbackBaseChange
  infer_instance

/-- The base change of an affine quotient chart to `Spec L` is canonically its
source stable affine chart. -/
noncomputable def quotientChartBaseChangeIso
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    pullback (quotientChartMap ρ i)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅ i.U.toScheme :=
  (asIso (quotientChartTopPullbackMap ρ i)).symm ≪≫
    (quotientChartTopWitness ρ i).e

/-- The first leg of the inverse affine-chart base-change isomorphism is the
pinned local quotient projection. -/
@[reassoc]
theorem quotientChartBaseChangeIso_inv_fst
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    (quotientChartBaseChangeIso ρ i).inv ≫
        pullback.fst (quotientChartMap ρ i)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine := by
  have hfst :
      (asIso (quotientChartTopPullbackMap ρ i)).hom ≫
          pullback.fst (quotientChartMap ρ i)
            (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
        pullback.fst
            ((quotientChartTopOpen ρ i).ι ≫ quotientChartMap ρ i)
            (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
          (quotientChartTopOpen ρ i).ι := by
    change quotientChartTopPullbackMap ρ i ≫
        pullback.fst (quotientChartMap ρ i)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) = _
    exact pullbackBaseChange_fst K L (quotientChartMap ρ i)
      ((quotientChartTopOpen ρ i).ι ≫ quotientChartMap ρ i)
      (quotientChartTopOpen ρ i).ι rfl
  have hproj := (quotientChartTopWitness ρ i).projection
  have hfac := SemilinearGalAction.stableAffineQuotientMapRestrict_fac
    ρ i.stable i.affine le_rfl i.stable
  simp only [quotientChartBaseChangeIso, Iso.trans_inv, Iso.symm_inv]
  calc
    ((quotientChartTopWitness ρ i).e.inv ≫
          (asIso (quotientChartTopPullbackMap ρ i)).hom) ≫
          pullback.fst (quotientChartMap ρ i)
            (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
        (quotientChartTopWitness ρ i).e.inv ≫
          ((asIso (quotientChartTopPullbackMap ρ i)).hom ≫
            pullback.fst (quotientChartMap ρ i)
              (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :=
      Category.assoc _ _ _
    _ = (quotientChartTopWitness ρ i).e.inv ≫
          (pullback.fst
              ((quotientChartTopOpen ρ i).ι ≫ quotientChartMap ρ i)
              (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
            (quotientChartTopOpen ρ i).ι) :=
      congrArg (fun z ↦ (quotientChartTopWitness ρ i).e.inv ≫ z) hfst
    _ = ((quotientChartTopWitness ρ i).e.inv ≫
          pullback.fst
            ((quotientChartTopOpen ρ i).ι ≫ quotientChartMap ρ i)
            (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫
          (quotientChartTopOpen ρ i).ι := (Category.assoc _ _ _).symm
    _ = SemilinearGalAction.stableAffineQuotientMapRestrict
          ρ i.stable i.affine le_rfl i.stable ≫
          (quotientChartTopOpen ρ i).ι :=
      congrArg (fun z ↦ z ≫ (quotientChartTopOpen ρ i).ι) hproj
    _ = X.homOfLE le_rfl ≫
          SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine := hfac
    _ = SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine := by
      rw [Scheme.homOfLE_rfl, Category.id_comp]

/-- The second leg of the inverse affine-chart base-change isomorphism is the
source chart's structure map to `Spec L`. -/
@[reassoc]
theorem quotientChartBaseChangeIso_inv_snd
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    (quotientChartBaseChangeIso ρ i).inv ≫
        pullback.snd (quotientChartMap ρ i)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      i.U.ι ≫ f := by
  have hsnd :
      (asIso (quotientChartTopPullbackMap ρ i)).hom ≫
          pullback.snd (quotientChartMap ρ i)
            (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
        pullback.snd
          ((quotientChartTopOpen ρ i).ι ≫ quotientChartMap ρ i)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
    change quotientChartTopPullbackMap ρ i ≫
        pullback.snd (quotientChartMap ρ i)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) = _
    exact pullbackBaseChange_snd K L (quotientChartMap ρ i)
      ((quotientChartTopOpen ρ i).ι ≫ quotientChartMap ρ i)
      (quotientChartTopOpen ρ i).ι rfl
  have hinv := GaloisQuotientWitnessWithProjection.inverse_comp_snd
    (quotientChartTopWitness ρ i)
  simp only [quotientChartBaseChangeIso, Iso.trans_inv, Iso.symm_inv]
  calc
    ((quotientChartTopWitness ρ i).e.inv ≫
          (asIso (quotientChartTopPullbackMap ρ i)).hom) ≫
          pullback.snd (quotientChartMap ρ i)
            (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
        (quotientChartTopWitness ρ i).e.inv ≫
          ((asIso (quotientChartTopPullbackMap ρ i)).hom ≫
            pullback.snd (quotientChartMap ρ i)
              (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :=
      Category.assoc _ _ _
    _ = (quotientChartTopWitness ρ i).e.inv ≫
          pullback.snd
            ((quotientChartTopOpen ρ i).ι ≫ quotientChartMap ρ i)
            (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
      congrArg (fun z ↦ (quotientChartTopWitness ρ i).e.inv ≫ z) hsnd
    _ = i.U.ι ≫ f := hinv

/-- The local quotient projections agree on the intersection of two stable
affine charts. -/
theorem quotientChartProjection_inf [FiniteDimensional K L] [IsGalois K L]
    (i j : StableAffineOpen ρ) :
    X.homOfLE (show i.U ⊓ j.U ≤ i.U from inf_le_left) ≫
        quotientChartProjection ρ i =
      X.homOfLE (show i.U ⊓ j.U ≤ j.U from inf_le_right) ≫
        quotientChartProjection ρ j := by
  have hswap :
      (X.isoOfEq (inf_comm i.U j.U)).hom ≫
          X.homOfLE (show j.U ⊓ i.U ≤ j.U from inf_le_left) =
        X.homOfLE (show i.U ⊓ j.U ≤ j.U from inf_le_right) := by
    rw [← cancel_mono j.U.ι]
    simp
  have hglue := (quotientGlueData ρ).glue_condition i j
  change (overlapIso ρ i j).hom ≫ quotientOverlapι ρ j i ≫
      (quotientGlueData ρ).ι j =
    quotientOverlapι ρ i j ≫ (quotientGlueData ρ).ι i at hglue
  simp only [quotientChartProjection]
  calc
    X.homOfLE inf_le_left ≫
          (SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine ≫
            (quotientGlueData ρ).ι i) =
        (X.homOfLE inf_le_left ≫
            SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine) ≫
          (quotientGlueData ρ).ι i := (Category.assoc _ _ _).symm
    _ = (overlapQuotientMap ρ i j ≫ quotientOverlapι ρ i j) ≫
          (quotientGlueData ρ).ι i :=
      congrArg (fun z ↦ z ≫ (quotientGlueData ρ).ι i)
        (overlapQuotientMap_fac ρ i j).symm
    _ = overlapQuotientMap ρ i j ≫
          (quotientOverlapι ρ i j ≫ (quotientGlueData ρ).ι i) :=
      Category.assoc _ _ _
    _ = overlapQuotientMap ρ i j ≫
          ((overlapIso ρ i j).hom ≫ quotientOverlapι ρ j i ≫
            (quotientGlueData ρ).ι j) :=
      congrArg (fun z ↦ overlapQuotientMap ρ i j ≫ z) hglue.symm
    _ = (overlapQuotientMap ρ i j ≫ (overlapIso ρ i j).hom) ≫
          quotientOverlapι ρ j i ≫ (quotientGlueData ρ).ι j := by
      simp only [Category.assoc]
    _ = ((X.isoOfEq (inf_comm i.U j.U)).hom ≫
          overlapQuotientMap ρ j i) ≫ quotientOverlapι ρ j i ≫
          (quotientGlueData ρ).ι j := by
      rw [overlapIso_hom_quotientMap]
    _ = ((X.isoOfEq (inf_comm i.U j.U)).hom ≫
          (overlapQuotientMap ρ j i ≫ quotientOverlapι ρ j i)) ≫
          (quotientGlueData ρ).ι j := by
      simp only [Category.assoc]
    _ = ((X.isoOfEq (inf_comm i.U j.U)).hom ≫
          (X.homOfLE inf_le_left ≫
            SemilinearGalAction.stableAffineQuotientMap ρ j.stable j.affine)) ≫
          (quotientGlueData ρ).ι j :=
      congrArg
        (fun z ↦ ((X.isoOfEq (inf_comm i.U j.U)).hom ≫ z) ≫
          (quotientGlueData ρ).ι j)
        (overlapQuotientMap_fac ρ j i)
    _ = (X.homOfLE inf_le_right ≫
          SemilinearGalAction.stableAffineQuotientMap ρ j.stable j.affine) ≫
          (quotientGlueData ρ).ι j := by
      rw [← Category.assoc, hswap]
    _ = X.homOfLE inf_le_right ≫
          (SemilinearGalAction.stableAffineQuotientMap ρ j.stable j.affine ≫
            (quotientGlueData ρ).ι j) := Category.assoc _ _ _

/-- The stable-affine quotient projections satisfy the pullback compatibility
required by `Scheme.OpenCover.glueMorphisms`. -/
theorem quotientChartProjection_compatible
    [FiniteDimensional K L] [IsGalois K L]
    (i j : StableAffineOpen ρ) :
    pullback.fst i.U.ι j.U.ι ≫ quotientChartProjection ρ i =
      pullback.snd i.U.ι j.U.ι ≫ quotientChartProjection ρ j := by
  rw [← cancel_epi (isPullback_opens_inf i.U j.U).isoPullback.hom]
  simpa only [IsPullback.isoPullback_hom_fst_assoc,
    IsPullback.isoPullback_hom_snd_assoc] using
      quotientChartProjection_inf ρ i j

/-- The quotient projection from the acted scheme to the quotient obtained by
gluing its stable affine quotient charts. -/
noncomputable def gluedQuotientProjection
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    X ⟶ gluedQuotient ρ :=
  (sourceOpenCover ρ).glueMorphisms (quotientChartProjection ρ)
    (quotientChartProjection_compatible ρ)

/-- Restricting the global quotient projection to a stable affine chart recovers
the pinned local quotient projection. -/
@[reassoc]
theorem sourceOpenCover_f_gluedQuotientProjection
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ]
    (i : StableAffineOpen ρ) :
    i.U.ι ≫ gluedQuotientProjection ρ = quotientChartProjection ρ i := by
  exact (sourceOpenCover ρ).ι_glueMorphisms _ _ i

set_option backward.isDefEq.respectTransparency false in
/-- The global projection to the glued quotient is Galois-invariant. -/
@[reassoc]
theorem act_hom_gluedQuotientProjection
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ]
    (gamma : L ≃ₐ[K] L) :
    (ρ.act gamma).hom ≫ gluedQuotientProjection ρ =
      gluedQuotientProjection ρ := by
  apply (sourceOpenCover ρ).hom_ext
  intro i
  change StableAffineOpen ρ at i
  change (i.U.ι ≫ (ρ.act gamma).hom) ≫ gluedQuotientProjection ρ =
    i.U.ι ≫ gluedQuotientProjection ρ
  rw [← SemilinearGalAction.actRes_ι ρ i.stable gamma]
  rw [Category.assoc, sourceOpenCover_f_gluedQuotientProjection]
  change ((ρ.restrict i.stable).act gamma).hom ≫
    quotientChartProjection ρ i = quotientChartProjection ρ i
  exact restrict_act_hom_quotientChartProjection ρ i gamma

/-- The global quotient projection pulls a glued quotient chart back to the
stable affine source chart from which it was built. -/
theorem gluedQuotientProjection_preimage_opensRange
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ]
    (i : StableAffineOpen ρ) :
    gluedQuotientProjection ρ ⁻¹ᵁ
        ((quotientGlueData ρ).ι i).opensRange = i.U := by
  ext x
  obtain ⟨j, y, rfl⟩ := (sourceOpenCover ρ).exists_eq x
  change gluedQuotientProjection ρ (j.U.ι y) ∈
      ((quotientGlueData ρ).ι i).opensRange ↔ j.U.ι y ∈ i.U
  rw [← Scheme.Hom.comp_apply, sourceOpenCover_f_gluedQuotientProjection]
  change y ∈ quotientChartProjection ρ j ⁻¹ᵁ
      ((quotientGlueData ρ).ι i).opensRange ↔ y ∈ j.U.ι ⁻¹ᵁ i.U
  rw [quotientChartProjection_preimage_opensRange]

/-- The structure maps of the invariant-ring quotient charts glue to a map to
`Spec K`. -/
noncomputable def gluedQuotientMap [FiniteDimensional K L] [IsGalois K L] :
    gluedQuotient ρ ⟶ Spec (CommRingCat.of K) := by
  fapply Multicoequalizer.desc
  · exact quotientChartMap ρ
  · rintro ⟨i, j⟩
    change quotientOverlapι ρ i j ≫ quotientChartMap ρ i =
      ((overlapIso ρ i j).hom ≫ quotientOverlapι ρ j i) ≫
        quotientChartMap ρ j
    simpa only [Category.assoc] using
      (overlapIso_hom_base ρ i j).symm

/-- Each quotient chart inclusion lies over the chart's invariant-ring
structure map. -/
@[reassoc]
theorem quotientGlueData_ι_gluedQuotientMap
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    (quotientGlueData ρ).ι i ≫ gluedQuotientMap ρ = quotientChartMap ρ i :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- A local quotient projection followed by the glued structure map is its
source chart's structure map over `Spec K`. -/
@[reassoc]
theorem quotientChartProjection_gluedQuotientMap
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    quotientChartProjection ρ i ≫ gluedQuotientMap ρ =
      (i.U.ι ≫ f) ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  have hchart := quotientGlueData_ι_gluedQuotientMap ρ i
  calc
    quotientChartProjection ρ i ≫ gluedQuotientMap ρ =
        SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine ≫
          ((quotientGlueData ρ).ι i ≫ gluedQuotientMap ρ) := by
      unfold quotientChartProjection
      exact Category.assoc _ _ _
    _ = SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine ≫
          quotientChartMap ρ i :=
      congrArg
        (fun z ↦ SemilinearGalAction.stableAffineQuotientMap
          ρ i.stable i.affine ≫ z)
        hchart
    _ = (i.U.ι ≫ f) ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
      stableAffineQuotientMap_quotientChartMap ρ i

/-- The global quotient projection lies over `Spec K`. -/
@[reassoc]
theorem gluedQuotientProjection_gluedQuotientMap
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    gluedQuotientProjection ρ ≫ gluedQuotientMap ρ =
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  apply (sourceOpenCover ρ).hom_ext
  intro i
  change i.U.ι ≫ (gluedQuotientProjection ρ ≫ gluedQuotientMap ρ) =
    i.U.ι ≫ (f ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)))
  rw [← Category.assoc, sourceOpenCover_f_gluedQuotientProjection]
  rw [quotientChartProjection_gluedQuotientMap]
  simp only [Category.assoc]

/-- The morphism from the acted scheme to the base change of its glued quotient,
induced by the global quotient projection and the source structure map. -/
noncomputable def gluedQuotientBaseChangeLift
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    X ⟶ pullback (gluedQuotientMap ρ)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  pullback.lift (gluedQuotientProjection ρ) f
    (gluedQuotientProjection_gluedQuotientMap ρ)

@[simp, reassoc]
theorem gluedQuotientBaseChangeLift_fst
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    gluedQuotientBaseChangeLift ρ ≫ pullback.fst _ _ =
      gluedQuotientProjection ρ := by
  unfold gluedQuotientBaseChangeLift
  exact pullback.lift_fst _ _ _

@[simp, reassoc]
theorem gluedQuotientBaseChangeLift_snd
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    gluedQuotientBaseChangeLift ρ ≫ pullback.snd _ _ = f := by
  unfold gluedQuotientBaseChangeLift
  exact pullback.lift_snd _ _ _

/-- The base-changed inclusion of a quotient chart into the base change of the
glued quotient. -/
noncomputable def quotientChartBaseChangeToGlued
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    pullback (quotientChartMap ρ i)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
      pullback (gluedQuotientMap ρ)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  pullbackBaseChange K L (gluedQuotientMap ρ) (quotientChartMap ρ i)
    ((quotientGlueData ρ).ι i) (quotientGlueData_ι_gluedQuotientMap ρ i)

instance quotientChartBaseChangeToGlued_isOpenImmersion
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    IsOpenImmersion (quotientChartBaseChangeToGlued ρ i) := by
  letI : IsOpenImmersion
      (show quotientChart ρ i ⟶ gluedQuotient ρ from
        (quotientGlueData ρ).ι i) :=
    (quotientGlueData ρ).ι_isOpenImmersion i
  unfold quotientChartBaseChangeToGlued pullbackBaseChange
  infer_instance

/-- The image of a base-changed quotient chart is the inverse image of the
corresponding chart in the glued quotient. -/
theorem quotientChartBaseChangeToGlued_opensRange
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    (quotientChartBaseChangeToGlued ρ i).opensRange =
      pullback.fst (gluedQuotientMap ρ)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⁻¹ᵁ
        ((quotientGlueData ρ).ι i).opensRange := by
  unfold gluedQuotient
  apply Opens.ext
  rw [Scheme.Hom.coe_opensRange]
  change Set.range (quotientChartBaseChangeToGlued ρ i) =
    (pullback.fst (gluedQuotientMap ρ)
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).base ⁻¹'
      Set.range ((quotientGlueData ρ).ι i)
  unfold quotientChartBaseChangeToGlued pullbackBaseChange
  rw [Scheme.Pullback.range_map]
  have hid : Function.Surjective
      (𝟙 (Spec (CommRingCat.of L)) :
        Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L)) :=
    fun x ↦ ⟨x, rfl⟩
  rw [Set.range_eq_univ.mpr hid, Set.preimage_univ, Set.inter_univ]
  rfl

/-- The inverse image of a base-changed quotient chart under the global
base-change morphism is the original stable affine source chart. -/
theorem gluedQuotientBaseChangeLift_preimage_opensRange
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ]
    (i : StableAffineOpen ρ) :
    gluedQuotientBaseChangeLift ρ ⁻¹ᵁ
        (quotientChartBaseChangeToGlued ρ i).opensRange = i.U := by
  rw [quotientChartBaseChangeToGlued_opensRange]
  rw [← Scheme.Hom.comp_preimage]
  rw [gluedQuotientBaseChangeLift_fst]
  exact gluedQuotientProjection_preimage_opensRange ρ i

/-- The base change of the glued quotient is covered by the base changes of
its invariant-ring quotient charts. -/
noncomputable def gluedQuotientBaseChangeOpenCover
    [FiniteDimensional K L] [IsGalois K L] :
    Scheme.OpenCover
      (pullback (gluedQuotientMap ρ)
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) where
  I₀ := StableAffineOpen ρ
  X i := pullback (quotientChartMap ρ i)
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  f i := quotientChartBaseChangeToGlued ρ i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨i, y, hy⟩ := (quotientGlueData ρ).ι_jointly_surjective
        (pullback.fst (gluedQuotientMap ρ)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) x)
      have hx : x ∈ (quotientChartBaseChangeToGlued ρ i).opensRange := by
        rw [quotientChartBaseChangeToGlued_opensRange]
        exact ⟨y, hy⟩
      change x ∈ Set.range (quotientChartBaseChangeToGlued ρ i) at hx
      obtain ⟨z, hz⟩ := hx
      exact ⟨i, z, hz⟩
    · intro i
      infer_instance

@[simp, reassoc]
theorem quotientChartBaseChangeToGlued_fst
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    quotientChartBaseChangeToGlued ρ i ≫
        pullback.fst (gluedQuotientMap ρ)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      pullback.fst (quotientChartMap ρ i)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
        (quotientGlueData ρ).ι i := by
  exact pullbackBaseChange_fst K L (gluedQuotientMap ρ)
    (quotientChartMap ρ i) ((quotientGlueData ρ).ι i)
    (quotientGlueData_ι_gluedQuotientMap ρ i)

@[simp, reassoc]
theorem quotientChartBaseChangeToGlued_snd
    [FiniteDimensional K L] [IsGalois K L] (i : StableAffineOpen ρ) :
    quotientChartBaseChangeToGlued ρ i ≫
        pullback.snd (gluedQuotientMap ρ)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      pullback.snd (quotientChartMap ρ i)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  exact pullbackBaseChange_snd K L (gluedQuotientMap ρ)
    (quotientChartMap ρ i) ((quotientGlueData ρ).ι i)
    (quotientGlueData_ι_gluedQuotientMap ρ i)

/-- On every stable affine chart, the global base-change morphism is the inverse
affine base-change isomorphism followed by the base-changed chart inclusion. -/
@[reassoc]
theorem sourceOpenCover_f_gluedQuotientBaseChangeLift
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ]
    (i : StableAffineOpen ρ) :
    i.U.ι ≫ gluedQuotientBaseChangeLift ρ =
      (quotientChartBaseChangeIso ρ i).inv ≫
        quotientChartBaseChangeToGlued ρ i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, gluedQuotientBaseChangeLift_fst,
      sourceOpenCover_f_gluedQuotientProjection, quotientChartProjection,
      quotientChartBaseChangeToGlued_fst]
    change SemilinearGalAction.stableAffineQuotientMap ρ i.stable i.affine ≫
        (quotientGlueData ρ).ι i =
      ((quotientChartBaseChangeIso ρ i).inv ≫
        pullback.fst (quotientChartMap ρ i)
          (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫
        (quotientGlueData ρ).ι i
    exact
      congrArg (fun z ↦ z ≫ (quotientGlueData ρ).ι i)
        (quotientChartBaseChangeIso_inv_fst ρ i).symm
  · simp only [Category.assoc, gluedQuotientBaseChangeLift_snd,
      quotientChartBaseChangeToGlued_snd]
    exact (quotientChartBaseChangeIso_inv_snd ρ i).symm

/-- A source chart is the pullback of the corresponding base-changed quotient
chart along the global base-change morphism. -/
theorem quotientChartBaseChange_isPullback
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ]
    (i : StableAffineOpen ρ) :
    IsPullback (quotientChartBaseChangeIso ρ i).inv i.U.ι
      (quotientChartBaseChangeToGlued ρ i)
      (gluedQuotientBaseChangeLift ρ) := by
  apply IsOpenImmersion.isPullback
  · exact sourceOpenCover_f_gluedQuotientBaseChangeLift ρ i
  · rw [gluedQuotientBaseChangeLift_preimage_opensRange]
    exact (Scheme.Opens.opensRange_ι i.U).symm

/- The acted scheme is the base change to `Spec L` of its glued quotient. -/
set_option backward.isDefEq.respectTransparency false in
instance gluedQuotientBaseChangeLift_isIso
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    IsIso (gluedQuotientBaseChangeLift ρ) := by
  apply MorphismProperty.of_zeroHypercover_target
    (P := MorphismProperty.isomorphisms Scheme)
    (gluedQuotientBaseChangeOpenCover ρ)
  intro i
  change StableAffineOpen ρ at i
  change IsIso
    (pullback.snd (gluedQuotientBaseChangeLift ρ)
      (quotientChartBaseChangeToGlued ρ i))
  let h := (quotientChartBaseChange_isPullback ρ i).flip
  change MorphismProperty.isomorphisms Scheme
    (pullback.snd (gluedQuotientBaseChangeLift ρ)
      (quotientChartBaseChangeToGlued ρ i))
  rw [← (MorphismProperty.isomorphisms Scheme).cancel_left_of_respectsIso
    h.isoPullback.hom]
  rw [h.isoPullback_hom_snd]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The inverse global base-change isomorphism intertwines the given action
with the canonical action on the base change. -/
theorem gluedQuotientBaseChangeLift_isEquivariant
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    ρ.IsEquivariant (pullbackSemilinearGalAction K L (gluedQuotientMap ρ))
      (gluedQuotientBaseChangeLift ρ) := by
  intro gamma
  apply pullback.hom_ext
  · simp only [Category.assoc, gluedQuotientBaseChangeLift_fst,
      pullbackSemilinearGalAction_act_hom, pullbackGalMap_fst]
    exact act_hom_gluedQuotientProjection ρ gamma
  · simp only [Category.assoc, gluedQuotientBaseChangeLift_snd,
      pullbackSemilinearGalAction_act_hom, pullbackGalMap_snd]
    rw [← Category.assoc, gluedQuotientBaseChangeLift_snd]
    exact ρ.compat gamma

/-- The global base-change isomorphism, oriented from the base-changed glued
quotient to the original acted scheme. -/
noncomputable def gluedQuotientBaseChangeIso
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    pullback (gluedQuotientMap ρ)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅ X :=
  (asIso (gluedQuotientBaseChangeLift ρ)).symm

@[simp]
theorem gluedQuotientBaseChangeIso_inv
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    (gluedQuotientBaseChangeIso ρ).inv =
      gluedQuotientBaseChangeLift ρ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The global base-change isomorphism lies over `Spec L`. -/
@[reassoc]
theorem gluedQuotientBaseChangeIso_hom_f
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    (gluedQuotientBaseChangeIso ρ).hom ≫ f =
      pullback.snd (gluedQuotientMap ρ)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  apply (cancel_epi (gluedQuotientBaseChangeIso ρ).inv).1
  calc
    (gluedQuotientBaseChangeIso ρ).inv ≫
          ((gluedQuotientBaseChangeIso ρ).hom ≫ f) =
        ((gluedQuotientBaseChangeIso ρ).inv ≫
          (gluedQuotientBaseChangeIso ρ).hom) ≫ f :=
      (Category.assoc _ _ _).symm
    _ = f := (gluedQuotientBaseChangeIso ρ).inv_hom_id_assoc f
    _ = gluedQuotientBaseChangeLift ρ ≫
        pullback.snd (gluedQuotientMap ρ)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
      (gluedQuotientBaseChangeLift_snd ρ).symm
    _ = (gluedQuotientBaseChangeIso ρ).inv ≫
        pullback.snd (gluedQuotientMap ρ)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
      rw [gluedQuotientBaseChangeIso_inv]

set_option backward.isDefEq.respectTransparency false in
/-- The global base-change isomorphism is Galois-equivariant. -/
theorem gluedQuotientBaseChangeIso_isEquivariant
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    (pullbackSemilinearGalAction K L (gluedQuotientMap ρ)).IsEquivariant ρ
      (gluedQuotientBaseChangeIso ρ).hom := by
  intro gamma
  apply (cancel_epi (gluedQuotientBaseChangeIso ρ).inv).1
  have h := gluedQuotientBaseChangeLift_isEquivariant ρ gamma
  have h' : (ρ.act gamma).hom ≫ (gluedQuotientBaseChangeIso ρ).inv =
      (gluedQuotientBaseChangeIso ρ).inv ≫
        ((pullbackSemilinearGalAction K L (gluedQuotientMap ρ)).act gamma).hom := by
    simpa only [gluedQuotientBaseChangeIso_inv] using h
  calc
    (gluedQuotientBaseChangeIso ρ).inv ≫
          (((pullbackSemilinearGalAction K L
            (gluedQuotientMap ρ)).act gamma).hom ≫
            (gluedQuotientBaseChangeIso ρ).hom) =
        ((gluedQuotientBaseChangeIso ρ).inv ≫
          ((pullbackSemilinearGalAction K L
            (gluedQuotientMap ρ)).act gamma).hom) ≫
            (gluedQuotientBaseChangeIso ρ).hom :=
      (Category.assoc _ _ _).symm
    _ = ((ρ.act gamma).hom ≫
          (gluedQuotientBaseChangeIso ρ).inv) ≫
            (gluedQuotientBaseChangeIso ρ).hom :=
      congrArg (fun z => z ≫ (gluedQuotientBaseChangeIso ρ).hom) h'.symm
    _ = (ρ.act gamma).hom := by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = ((gluedQuotientBaseChangeIso ρ).inv ≫
          (gluedQuotientBaseChangeIso ρ).hom) ≫ (ρ.act gamma).hom := by
      rw [Iso.inv_hom_id, Category.id_comp]
    _ = (gluedQuotientBaseChangeIso ρ).inv ≫
        ((gluedQuotientBaseChangeIso ρ).hom ≫
          (ρ.act gamma).hom) := Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The pinned global base-change isomorphism induces the glued quotient
projection. -/
theorem gluedQuotientBaseChangeIso_inv_fst
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    (gluedQuotientBaseChangeIso ρ).inv ≫
        pullback.fst (gluedQuotientMap ρ)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      gluedQuotientProjection ρ := by
  rw [gluedQuotientBaseChangeIso_inv, gluedQuotientBaseChangeLift_fst]

/-- The glued invariant-ring quotient charts carry a specified global finite
Galois quotient witness. -/
noncomputable def gluedGaloisQuotientWitness
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    GaloisQuotientWitnessWithProjection ρ (gluedQuotient ρ)
      (gluedQuotientMap ρ) (gluedQuotientProjection ρ) :=
  galoisQuotientWitnessOfInvariantProjection ρ (gluedQuotientProjection ρ)
    (gluedQuotientBaseChangeIso ρ)
    (gluedQuotientBaseChangeIso_hom_f ρ)
    (gluedQuotientBaseChangeIso_isEquivariant ρ)
    (gluedQuotientBaseChangeIso_inv_fst ρ)
    (act_hom_gluedQuotientProjection ρ)

/-- The quotient obtained by gluing stable affine invariant-ring charts is the
finite Galois quotient of the original semilinear action. -/
theorem isGaloisQuotient_glued
    [FiniteDimensional K L] [IsGalois K L] [HasStableAffineCover K L ρ] :
    IsGaloisQuotient ρ (gluedQuotientMap ρ) := by
  let w := gluedGaloisQuotientWitness ρ
  exact ⟨w.e, w.over, w.equivariant, w.universal⟩

/-- Every finite Galois action whose orbits lie in affine opens has a scheme
quotient.  The orbit hypothesis is already a parameter of
`HasGaloisQuotient`; no additional hypothesis is introduced here. -/
instance hasGaloisQuotient_of_orbitsInAffineOpen
    [FiniteDimensional K L] [IsGalois K L] [ρ.OrbitsInAffineOpen] :
    HasGaloisQuotient ρ where
  exists_quotient :=
    ⟨gluedQuotient ρ, gluedQuotientMap ρ, isGaloisQuotient_glued ρ⟩

/-- The glued quotient as an object over `Spec K`, in the exact category used
by Picard representability. -/
noncomputable def gluedQuotientOver [FiniteDimensional K L] [IsGalois K L] :
    Over (Spec (CommRingCat.of K)) := Over.mk (gluedQuotientMap ρ)

end StableAffineOpen

end AlgebraicJacobian.GaloisDescent
