/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2ModuleKSheaf
import HartshorneLib.Chapter4P1Structure
import HartshorneLib.Chapter4P1Overlap

/-!
# Projective-line input for finite-map cohomology

This file records the geometric identities used by the two-lattice proof of finiteness of
`H^1(X, O_X)` along a finite morphism `X -> P1`. They identify the structure algebra map,
the two chart coordinates, and their overlap restrictions with `T` and `T^-1` in the
Laurent polynomial ring.

The proof pattern is adapted from the corresponding projective-line finiteness API in the
Algebraic Jacobian Challenge Rebuild project.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry

section OverAlgebraMap

variable {k : Type u} [CommRing k]

/-- Pullback along a morphism over `Spec k` intertwines the structure maps on sections. -/
lemma Scheme.Hom.appTop_map_appLE {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] (pi : X ⟶ Y)
    (hpi : pi ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k))
    {U : Y.Opens} {V : X.Opens} (e : V ≤ pi ⁻¹ᵁ U) :
    (Y ↘ Spec (.of k)).appTop ≫ Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
        pi.appLE U V e =
      (X ↘ Spec (.of k)).appTop ≫
        X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
  rw [Scheme.Hom.map_appLE]
  change (Y ↘ Spec (.of k)).appTop ≫ pi.appTop ≫
      X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op = _
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hpi]

/-- Elementwise form of `Scheme.Hom.appTop_map_appLE` for the structure algebra map. -/
lemma Scheme.Hom.appLE_overAlgebraMap {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] (pi : X ⟶ Y)
    (hpi : pi ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k))
    {U : Y.Opens} {V : X.Opens} (e : V ≤ pi ⁻¹ᵁ U) (r : k) :
    (pi.appLE U V e).hom (Y.overAlgebraMap k U r) = X.overAlgebraMap k V r := by
  have h := pi.appTop_map_appLE hpi e
  have h2 := congr((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ $h)
  exact congr((CommRingCat.Hom.hom $h2) r)

end OverAlgebraMap

namespace P1

variable (k : Type u) [Field k]

local notation "Astd" => homogeneousSubmodule (Fin 2) k

/-- The affine model of a homogeneous basic open is a morphism over `Spec k`. -/
theorem awayIota_structureMap {f : MvPolynomial (Fin 2) k} {m : ℕ}
    (f_deg : f ∈ Astd m) (hm : 0 < m) :
    Proj.awayι Astd f f_deg hm ≫ P1.structureMap k =
      Spec.map (CommRingCat.ofHom (algebraMap k (Away Astd f))) := by
  change Proj.awayι Astd f f_deg hm ≫
      (Proj.toSpecZero Astd ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Astd 0)))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (Away Astd f)))
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The inclusion of a standard basic open factors through its affine model. -/
theorem basicOpen_iota_eq {f : MvPolynomial (Fin 2) k} {m : ℕ}
    (f_deg : f ∈ Astd m) (hm : 0 < m) :
    (Proj.basicOpen Astd f).ι =
      Proj.basicOpenToSpec Astd f ≫ Proj.awayι Astd f f_deg hm := by
  rw [← Proj.basicOpenIsoSpec_inv_ι Astd f f_deg hm,
    ← Proj.basicOpenIsoSpec_hom Astd f f_deg hm, Iso.hom_inv_id_assoc]

/-- The structure algebra map on `D_+(f)` is the homogeneous-localization algebra map. -/
theorem structureMap_appTop_awayToSection {f : MvPolynomial (Fin 2) k} {m : ℕ}
    (f_deg : f ∈ Astd m) (hm : 0 < m) :
    (P1.structureMap k).appTop ≫
        (P1 k).presheaf.map (homOfLE (le_top : Proj.basicOpen Astd f ≤ ⊤)).op =
      (Scheme.ΓSpecIso (.of k)).hom ≫
        CommRingCat.ofHom (algebraMap k (Away Astd f)) ≫
        Proj.awayToSection Astd f := by
  have h1 : (Proj.basicOpen Astd f).ι ≫ P1.structureMap k =
      Proj.basicOpenToSpec Astd f ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (Away Astd f))) := by
    rw [basicOpen_iota_eq k f_deg hm, Category.assoc,
      awayIota_structureMap k f_deg hm]
  have h2 := congrArg Scheme.Hom.appTop h1
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h2
  have h3 : (Proj.basicOpenToSpec Astd f).appTop =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection Astd f ≫
        (Proj.basicOpen Astd f).topIso.inv :=
    Proj.basicOpenToSpec_app_top Astd f
  rw [h3, Scheme.ΓSpecIso_naturality_assoc] at h2
  have h4 : (Proj.basicOpen Astd f).ι.appTop ≫
      (Proj.basicOpen Astd f).topIso.hom =
      (P1 k).presheaf.map (homOfLE (le_top : Proj.basicOpen Astd f ≤ ⊤)).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp, ← op_comp]
    exact congrArg _ (congrArg Quiver.Hom.op (Subsingleton.elim _ _))
  have h5 := congr($h2 ≫ (Proj.basicOpen Astd f).topIso.hom)
  rw [Category.assoc, h4] at h5
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h5
  exact h5

/-- The localization element associated to `(X_i, X_j)` is the chart coordinate. -/
theorem isLocalizationElem_X_eq (i j : Fin 2) :
    Away.isLocalizationElem (X_mem k i) (X_mem k j) = chartCoord k i j := by
  rw [Away.isLocalizationElem, chartCoord_eq]
  congr 1
  exact pow_one _

/-- The chart coordinate `X_j / X_i` cuts out the overlap of the two standard charts. -/
theorem basicOpen_awayToSection_chartCoord (i j : Fin 2) :
    (P1 k).basicOpen ((Proj.awayToSection Astd (X i)).hom (chartCoord k i j)) =
      chartOpen k i ⊓ chartOpen k j := by
  change (Proj Astd).basicOpen
      ((Proj.awayToSection Astd (X i)).hom (chartCoord k i j)) =
    Proj.basicOpen Astd (X i) ⊓ Proj.basicOpen Astd (X j)
  have hpre : (Proj.basicOpen Astd (X i)).ι ⁻¹ᵁ
        ((Proj Astd).basicOpen
          ((Proj.awayToSection Astd (X i)).hom (chartCoord k i j))) =
      (Proj.basicOpen Astd (X i)).ι ⁻¹ᵁ Proj.basicOpen Astd (X j) := by
    rw [← Scheme.Opens.toSpecΓ_preimage_basicOpen]
    conv_rhs => rw [basicOpen_iota_eq k (X_mem k i) one_pos]
    change _ = Proj.basicOpenToSpec Astd (X i) ⁻¹ᵁ
      (Proj.awayι Astd (X i) (X_mem k i) one_pos ⁻¹ᵁ
        Proj.basicOpen Astd (X j))
    rw [Proj.awayι_preimage_basicOpen Astd (X_mem k i) one_pos
      (X_mem k j) one_pos, isLocalizationElem_X_eq k i j]
    rfl
  have himg := congrArg (fun W => (Proj.basicOpen Astd (X i)).ι ''ᵁ W) hpre
  simp only [Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι] at himg
  have hle : (Proj Astd).basicOpen
      ((Proj.awayToSection Astd (X i)).hom (chartCoord k i j)) ≤
      Proj.basicOpen Astd (X i) := (Proj Astd).basicOpen_le _
  calc
    (Proj Astd).basicOpen
        ((Proj.awayToSection Astd (X i)).hom (chartCoord k i j)) =
        Proj.basicOpen Astd (X i) ⊓
          (Proj Astd).basicOpen
            ((Proj.awayToSection Astd (X i)).hom (chartCoord k i j)) :=
      (inf_eq_right.mpr hle).symm
    _ = Proj.basicOpen Astd (X i) ⊓ Proj.basicOpen Astd (X j) := himg

/-- Under the overlap identification, `T` is the restriction of `X_1 / X_0`. -/
theorem overlapSectionsEquiv_symm_T :
    (overlapSectionsEquiv k).symm (LaurentPolynomial.T 1) =
      ((P1 k).presheaf.map (homOfLE (overlap_le_left k)).op).hom
        ((Proj.awayToSection Astd (X 0)).hom (chartCoord k 0 1)) := by
  apply (overlapSectionsEquiv k).injective
  rw [RingEquiv.apply_symm_apply, res_awayToSection_left,
    overlapSectionsEquiv_awayToSection, overlapAlgEquiv_awayToOverlapLeft,
    awayAlgEquiv_chartCoord k fin_zero_ne_one, Polynomial.toLaurent_X]

/-- Under the overlap identification, `T^-1` is the restriction of `X_0 / X_1`. -/
theorem overlapSectionsEquiv_symm_T_neg :
    (overlapSectionsEquiv k).symm (LaurentPolynomial.T (-1)) =
      ((P1 k).presheaf.map (homOfLE (overlap_le_right k)).op).hom
        ((Proj.awayToSection Astd (X 1)).hom (chartCoord k 1 0)) := by
  apply (overlapSectionsEquiv k).injective
  rw [RingEquiv.apply_symm_apply, res_awayToSection_right,
    overlapSectionsEquiv_awayToSection,
    overlapAlgEquiv_awayToOverlapRight_chartCoord]

/-- The overlap equivalence preserves the structure algebra map from `k`. -/
theorem overlapSectionsEquiv_symm_algebraMap (r : k) :
    (overlapSectionsEquiv k).symm (algebraMap k (LaurentPolynomial k) r) =
      (Proj.awayToSection Astd (X 0 * X 1)).hom
        (algebraMap k (Away Astd (X 0 * X 1)) r) := by
  apply (overlapSectionsEquiv k).injective
  rw [RingEquiv.apply_symm_apply, overlapSectionsEquiv_awayToSection]
  exact ((overlapAlgEquiv k).commutes r).symm

end P1

section Preimages

variable {k : Type u} [Field k]
variable {Y : Scheme.{u}} (pi : Y ⟶ P1 k)

/-- The inverse image of a standard chart under an affine morphism is affine. -/
theorem isAffineOpen_preimage_chartOpen [IsAffineHom pi] (i : Fin 2) :
    IsAffineOpen (pi ⁻¹ᵁ P1.chartOpen k i) :=
  (P1.isAffineOpen_chartOpen k i).preimage pi

/-- The inverse images of the standard charts cover the source. -/
theorem preimage_chartOpen_sup :
    pi ⁻¹ᵁ P1.chartOpen k 0 ⊔ pi ⁻¹ᵁ P1.chartOpen k 1 = ⊤ := by
  rw [← Scheme.Hom.preimage_sup, P1.chartOpen_sup, Scheme.Hom.preimage_top]

/-- A finite morphism gives a finite section map on each standard chart. -/
theorem finite_app_chartOpen [IsFinite pi] (i : Fin 2) :
    RingHom.Finite (pi.app (P1.chartOpen k i)).hom :=
  pi.finite_app _ (P1.isAffineOpen_chartOpen k i)

/-- A finite morphism gives a finite section map on the standard chart overlap. -/
theorem finite_app_overlap [IsFinite pi] :
    RingHom.Finite (pi.app (Proj.basicOpen (homogeneousSubmodule (Fin 2) k)
      (X 0 * X 1))).hom :=
  pi.finite_app _ (P1.isAffineOpen_overlap k)

end Preimages

end AlgebraicGeometry
