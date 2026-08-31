/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.FinitenessP1
import AlgebraicJacobian.Projective.TwoChartCoordinates

/-!
# Projective coordinates from a finite map to the projective line

The two standard affine charts of `P1` carry inverse Laurent coordinates.
For a finite morphism to `P1`, finite module generators on their inverse
images can be aligned after one positive common twist. The resulting
homogeneous coordinates define compatible local maps, which glue to a map to
an integral projective space and hence to relative projective space over the
base field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open MvPolynomial HomogeneousLocalization AlgebraicGeometry

namespace AlgebraicGeometry

namespace LaurentChartPair

variable {k : Type u} [Field k]

/-- The polynomial coordinate on the first chart of a Laurent chart pair. -/
noncomputable def coord0 (D : LaurentChartPair k) : Γ(P1 k, D.U₀) :=
  D.Γ₀.symm Polynomial.X

/-- The polynomial coordinate on the second chart of a Laurent chart pair. -/
noncomputable def coord1 (D : LaurentChartPair k) : Γ(P1 k, D.U₁) :=
  D.Γ₁.symm Polynomial.X

/-- The two Laurent coordinates restrict to mutually inverse overlap
sections. -/
theorem res_coord_mul (D : LaurentChartPair k) :
    ((P1 k).presheaf.map
      (homOfLE (inf_le_left : D.U₀ ⊓ D.U₁ ≤ D.U₀)).op).hom (coord0 D) *
    ((P1 k).presheaf.map
      (homOfLE (inf_le_right : D.U₀ ⊓ D.U₁ ≤ D.U₁)).op).hom (coord1 D) = 1 := by
  obtain ⟨U₀, U₁, U₀₁, hle₀, hle₁, hinf, ha₀, ha₁, ha₀₁, hsup,
    G₀, G₁, G₀₁, hr₀, hr₁⟩ := D
  subst hinf
  change ((P1 k).presheaf.map (homOfLE hle₀).op).hom (G₀.symm Polynomial.X) *
      ((P1 k).presheaf.map (homOfLE hle₁).op).hom (G₁.symm Polynomial.X) = 1
  apply G₀₁.injective
  rw [map_mul, hr₀, hr₁, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
    Polynomial.toLaurent_X, Polynomial.aeval_X, ← LaurentPolynomial.T_add]
  norm_num

end LaurentChartPair

namespace P1FiniteMap

variable {k : Type u} [Field k]

local notation "𝒜" => homogeneousSubmodule (Fin 2) k

noncomputable local instance : (P1 k).Over (Spec (.of k)) :=
  ⟨P1.structureMap k⟩

noncomputable local instance :
    Algebra k Γ(P1 k, P1.chartOpen k 0) :=
  ((P1 k).overAlgebraMap k (P1.chartOpen k 0)).toAlgebra

noncomputable local instance :
    Algebra k Γ(P1 k, P1.chartOpen k 1) :=
  ((P1 k).overAlgebraMap k (P1.chartOpen k 1)).toAlgebra

/-- The coordinate `X₁ / X₀` on the first standard chart of `P1`. -/
noncomputable def coord0 : Γ(P1 k, P1.chartOpen k 0) :=
  (P1.laurentChartPair k).coord0

/-- The coordinate `X₀ / X₁` on the second standard chart of `P1`. -/
noncomputable def coord1 : Γ(P1 k, P1.chartOpen k 1) :=
  (P1.laurentChartPair k).coord1

/-- The polynomial chart equivalence sends the first coordinate to `X`. -/
@[simp]
theorem chartSectionsEquiv0_coord0 :
    P1.chartSectionsEquiv₀ k (coord0 (k := k)) = Polynomial.X :=
  RingEquiv.apply_symm_apply _ _

/-- The polynomial chart equivalence sends the second coordinate to `X`. -/
@[simp]
theorem chartSectionsEquiv1_coord1 :
    P1.chartSectionsEquiv₁ k (coord1 (k := k)) = Polynomial.X :=
  RingEquiv.apply_symm_apply _ _

/-- The first Laurent coordinate agrees with the homogeneous-localization
chart coordinate. -/
theorem coord0_eq_awayToSection :
    coord0 (k := k) =
      (Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1) := by
  apply (P1.chartSectionsEquiv₀ k).injective
  rw [chartSectionsEquiv0_coord0, P1.chartSectionsEquiv₀_awayToSection,
    P1.awayAlgEquiv_chartCoord]

/-- The second Laurent coordinate agrees with the homogeneous-localization
chart coordinate. -/
theorem coord1_eq_awayToSection :
    coord1 (k := k) =
      (Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0) := by
  apply (P1.chartSectionsEquiv₁ k).injective
  rw [chartSectionsEquiv1_coord1, P1.chartSectionsEquiv₁_awayToSection,
    P1.awayAlgEquiv_chartCoord]

/-- The two standard coordinates restrict to mutually inverse sections on
the chart overlap. -/
theorem restriction_coord_mul :
    ((P1 k).presheaf.map
      (homOfLE (inf_le_left :
        P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤ P1.chartOpen k 0)).op).hom
        (coord0 (k := k)) *
    ((P1 k).presheaf.map
      (homOfLE (inf_le_right :
        P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤ P1.chartOpen k 1)).op).hom
        (coord1 (k := k)) = 1 :=
  (P1.laurentChartPair k).res_coord_mul

/-- The first coordinate cuts out the overlap inside `P1`. -/
theorem basicOpen_coord0 :
    (P1 k).basicOpen (coord0 (k := k)) =
      P1.chartOpen k 0 ⊓ P1.chartOpen k 1 := by
  rw [coord0_eq_awayToSection, P1.basicOpen_awayToSection_chartCoord]

/-- The second coordinate cuts out the overlap inside `P1`. -/
theorem basicOpen_coord1 :
    (P1 k).basicOpen (coord1 (k := k)) =
      P1.chartOpen k 0 ⊓ P1.chartOpen k 1 := by
  rw [coord1_eq_awayToSection, P1.basicOpen_awayToSection_chartCoord, inf_comm]

private theorem chartSectionsEquiv0_symm_C (c : k) :
    (P1.chartSectionsEquiv₀ k).symm (Polynomial.C c) =
      (Proj.awayToSection 𝒜 (X 0)).hom
        (algebraMap k (Away 𝒜 (X 0)) c) := by
  apply (P1.chartSectionsEquiv₀ k).injective
  rw [RingEquiv.apply_symm_apply, P1.chartSectionsEquiv₀_awayToSection,
    AlgEquiv.commutes, Polynomial.algebraMap_eq]

private theorem chartSectionsEquiv1_symm_C (c : k) :
    (P1.chartSectionsEquiv₁ k).symm (Polynomial.C c) =
      (Proj.awayToSection 𝒜 (X 1)).hom
        (algebraMap k (Away 𝒜 (X 1)) c) := by
  apply (P1.chartSectionsEquiv₁ k).injective
  rw [RingEquiv.apply_symm_apply, P1.chartSectionsEquiv₁_awayToSection,
    AlgEquiv.commutes, Polynomial.algebraMap_eq]

/-- The first polynomial chart equivalence respects the structural
`k`-algebra map. -/
theorem chartSectionsEquiv0_overAlgebraMap (c : k) :
    (P1.chartSectionsEquiv₀ k).symm (Polynomial.C c) =
      algebraMap k Γ(P1 k, P1.chartOpen k 0) c := by
  have hcomp :
      (Scheme.ΓSpecIso (.of k)).inv ≫ (P1.structureMap k).appTop ≫
          (P1 k).presheaf.map
            (homOfLE (le_top : P1.chartOpen k 0 ≤ ⊤)).op =
        CommRingCat.ofHom (algebraMap k (Away 𝒜 (X 0))) ≫
          Proj.awayToSection 𝒜 (X 0) := by
    rw [P1.structureMap_appTop_awayToSection k (P1.X_mem k 0) one_pos,
      Iso.inv_hom_id_assoc]
  have hPA :
      (P1 k).overAlgebraMap k (P1.chartOpen k 0) c =
        (Proj.awayToSection 𝒜 (X 0)).hom
          (algebraMap k (Away 𝒜 (X 0)) c) :=
    congr((CommRingCat.Hom.hom $hcomp) c)
  change _ = (P1 k).overAlgebraMap k (P1.chartOpen k 0) c
  rw [chartSectionsEquiv0_symm_C, hPA]

/-- The second polynomial chart equivalence respects the structural
`k`-algebra map. -/
theorem chartSectionsEquiv1_overAlgebraMap (c : k) :
    (P1.chartSectionsEquiv₁ k).symm (Polynomial.C c) =
      algebraMap k Γ(P1 k, P1.chartOpen k 1) c := by
  have hcomp :
      (Scheme.ΓSpecIso (.of k)).inv ≫ (P1.structureMap k).appTop ≫
          (P1 k).presheaf.map
            (homOfLE (le_top : P1.chartOpen k 1 ≤ ⊤)).op =
        CommRingCat.ofHom (algebraMap k (Away 𝒜 (X 1))) ≫
          Proj.awayToSection 𝒜 (X 1) := by
    rw [P1.structureMap_appTop_awayToSection k (P1.X_mem k 1) one_pos,
      Iso.inv_hom_id_assoc]
  have hPA :
      (P1 k).overAlgebraMap k (P1.chartOpen k 1) c =
        (Proj.awayToSection 𝒜 (X 1)).hom
          (algebraMap k (Away 𝒜 (X 1)) c) :=
    congr((CommRingCat.Hom.hom $hcomp) c)
  change _ = (P1 k).overAlgebraMap k (P1.chartOpen k 1) c
  rw [chartSectionsEquiv1_symm_C, hPA]

/-- Powers of the first chart coordinate span its polynomial section ring
over `k`. -/
theorem span_pow_coord0 :
    ⊤ ≤ Submodule.span k
      (Set.range fun n : ℕ => coord0 (k := k) ^ n) := by
  intro z _
  let p : Polynomial k := P1.chartSectionsEquiv₀ k z
  have hz : z = (P1.chartSectionsEquiv₀ k).symm p :=
    ((P1.chartSectionsEquiv₀ k).symm_apply_apply z).symm
  rw [hz]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact Submodule.add_mem _ hp hq
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        chartSectionsEquiv0_overAlgebraMap]
      have hcoord :
          (P1.chartSectionsEquiv₀ k).symm Polynomial.X = coord0 (k := k) := by
        apply (P1.chartSectionsEquiv₀ k).injective
        rw [RingEquiv.apply_symm_apply, chartSectionsEquiv0_coord0]
      rw [hcoord]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨n, rfl⟩)

/-- Powers of the second chart coordinate span its polynomial section ring
over `k`. -/
theorem span_pow_coord1 :
    ⊤ ≤ Submodule.span k
      (Set.range fun n : ℕ => coord1 (k := k) ^ n) := by
  intro z _
  let p : Polynomial k := P1.chartSectionsEquiv₁ k z
  have hz : z = (P1.chartSectionsEquiv₁ k).symm p :=
    ((P1.chartSectionsEquiv₁ k).symm_apply_apply z).symm
  rw [hz]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact Submodule.add_mem _ hp hq
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        chartSectionsEquiv1_overAlgebraMap]
      have hcoord :
          (P1.chartSectionsEquiv₁ k).symm Polynomial.X = coord1 (k := k) := by
        apply (P1.chartSectionsEquiv₁ k).injective
        rw [RingEquiv.apply_symm_apply, chartSectionsEquiv1_coord1]
      rw [hcoord]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨n, rfl⟩)

end P1FiniteMap

end AlgebraicGeometry
