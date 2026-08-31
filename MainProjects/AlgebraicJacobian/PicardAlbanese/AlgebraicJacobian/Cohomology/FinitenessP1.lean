/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.ModuleKSheaf
import AlgebraicJacobian.Curve.P1Charts

/-!
# The `ℙ¹`-side inputs for the finiteness of `H¹`

Auxiliary results consumed by the two-lattice finiteness argument of
`AlgebraicJacobian.Cohomology.Finiteness`:

* the generic naturality of the structure algebra map of a scheme over `Spec k` under a
  morphism over `Spec k` (`Scheme.Hom.appTop_map_appLE`, `Scheme.Hom.appLE_overAlgebraMap`);
* on `ℙ¹` itself: the affine models of the standard basic opens are morphisms over `Spec k`
  (`P1.awayι_structureMap`), the structure algebra map on a basic open is the algebra map of
  the homogeneous localization (`P1.structureMap_appTop_awayToSection`), and the
  scheme-level basic open of the chart coordinate `t = Xⱼ/Xᵢ ∈ Γ(D₊(Xᵢ))` is the chart
  overlap (`P1.basicOpen_awayToSection_chartCoord`);
* the identification of the Laurent generators `T`, `T⁻¹`, and the scalars of
  `Γ(ℙ¹, D₊(X₀X₁)) ≃+* k[T,T⁻¹]` as restrictions of explicit sections on the two charts
  (`P1.overlapSectionsEquiv_symm_T`, `…_T_neg`, `…_algebraMap`).
-/

set_option autoImplicit false
/- Scheme-theoretic unification (mixing `P1 k` with `Proj 𝒜`, `Γ(X, U)` with functor
applications) needs defeq checks through semireducible definitions, as in mathlib's own
algebraic-geometry files. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry

section OverAlgebraMap

/-! ### Pulling back the structure algebra map along a morphism over `Spec k` -/

variable {k : Type u} [CommRing k]

/-- For a morphism `π : X ⟶ Y` of schemes over `Spec k` (compatibly with the structure
morphisms), pulling back sections along `π` intertwines the structure algebra maps, in
morphism form: restricting the structure sections of `Y` from `⊤` to `U` and applying
`π.appLE U V e` equals the structure sections of `X` restricted from `⊤` to `V`. -/
lemma Scheme.Hom.appTop_map_appLE {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] (π : X ⟶ Y) (hπ : π ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k))
    {U : Y.Opens} {V : X.Opens} (e : V ≤ π ⁻¹ᵁ U) :
    (Y ↘ Spec (.of k)).appTop ≫ Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
        π.appLE U V e =
      (X ↘ Spec (.of k)).appTop ≫ X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
  rw [Scheme.Hom.map_appLE]
  change (Y ↘ Spec (.of k)).appTop ≫ π.appTop ≫
      X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op = _
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hπ]

/-- Elementwise form of `Scheme.Hom.appTop_map_appLE`, phrased through
`Scheme.overAlgebraMap`: `π` pulls the structure algebra map of `Y` back to that of `X`. -/
lemma Scheme.Hom.appLE_overAlgebraMap {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] (π : X ⟶ Y) (hπ : π ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k))
    {U : Y.Opens} {V : X.Opens} (e : V ≤ π ⁻¹ᵁ U) (r : k) :
    (π.appLE U V e).hom (Y.overAlgebraMap k U r) = X.overAlgebraMap k V r := by
  have h := π.appTop_map_appLE hπ e
  have h2 := congr((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ $h)
  exact congr((CommRingCat.Hom.hom $h2) r)

end OverAlgebraMap

namespace P1

/-! ### The chart coordinates of `ℙ¹`: structure map and basic opens -/

variable (k : Type u) [Field k]

/-- The standard grading of `k[X₀, X₁]`, the graded ring underlying `P1 k`. -/
local notation "𝒜" => homogeneousSubmodule (Fin 2) k

/-- The affine chart inclusions `Spec (k[X₀,X₁]_f)₀ ⟶ ℙ¹` are morphisms over `Spec k`,
for any homogeneous `f` of positive degree (generalizing `P1.chartι_structureMap`). -/
theorem awayι_structureMap {f : MvPolynomial (Fin 2) k} {m : ℕ} (f_deg : f ∈ 𝒜 m)
    (hm : 0 < m) :
    Proj.awayι 𝒜 f f_deg hm ≫ structureMap k =
      Spec.map (CommRingCat.ofHom (algebraMap k (Away 𝒜 f))) := by
  change Proj.awayι 𝒜 f f_deg hm ≫
      (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0)))) = _
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The inclusion of a standard basic open of `ℙ¹` factors through its affine model. -/
theorem basicOpen_ι_eq {f : MvPolynomial (Fin 2) k} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.basicOpen 𝒜 f).ι = Proj.basicOpenToSpec 𝒜 f ≫ Proj.awayι 𝒜 f f_deg hm := by
  rw [← Proj.basicOpenIsoSpec_inv_ι 𝒜 f f_deg hm, ← Proj.basicOpenIsoSpec_hom 𝒜 f f_deg hm,
    Iso.hom_inv_id_assoc]

/-- The structure algebra map of `ℙ¹` restricted to a standard basic open `D₊(f)` is the
composite `Γ(Spec k, ⊤) ≅ k → (k[X₀,X₁]_f)₀ → Γ(ℙ¹, D₊(f))`, in morphism form. -/
theorem structureMap_appTop_awayToSection {f : MvPolynomial (Fin 2) k} {m : ℕ}
    (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (structureMap k).appTop ≫
        (P1 k).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 f ≤ ⊤)).op =
      (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom (algebraMap k (Away 𝒜 f)) ≫
        Proj.awayToSection 𝒜 f := by
  have h1 : (Proj.basicOpen 𝒜 f).ι ≫ structureMap k =
      Proj.basicOpenToSpec 𝒜 f ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (Away 𝒜 f))) := by
    rw [basicOpen_ι_eq k f_deg hm, Category.assoc, awayι_structureMap k f_deg hm]
  have h2 := congrArg Scheme.Hom.appTop h1
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h2
  have h3 : (Proj.basicOpenToSpec 𝒜 f).appTop =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 f ≫
        (Proj.basicOpen 𝒜 f).topIso.inv :=
    Proj.basicOpenToSpec_app_top 𝒜 f
  rw [h3, Scheme.ΓSpecIso_naturality_assoc] at h2
  have h4 : (Proj.basicOpen 𝒜 f).ι.appTop ≫ (Proj.basicOpen 𝒜 f).topIso.hom =
      (P1 k).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 f ≤ ⊤)).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp, ← op_comp]
    exact congrArg _ (congrArg Quiver.Hom.op (Subsingleton.elim _ _))
  have h5 := congr($h2 ≫ (Proj.basicOpen 𝒜 f).topIso.hom)
  rw [Category.assoc, h4] at h5
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h5
  exact h5

/-- `g^d/f^e = Xⱼ/Xᵢ`: the mathlib localization element of the pair `(Xᵢ, Xⱼ)` is the chart
coordinate (generalizing `P1.isLocalizationElem_eq` to both charts). -/
theorem isLocalizationElem_X_eq (i j : Fin 2) :
    Away.isLocalizationElem (X_mem k i) (X_mem k j) = chartCoord k i j := by
  rw [Away.isLocalizationElem, chartCoord_eq]
  congr 1
  exact pow_one _

/-- **The chart coordinate cuts out the overlap**: on `ℙ¹`, the scheme-level basic open of
the section `t = Xⱼ/Xᵢ ∈ Γ(D₊(Xᵢ))` is the chart overlap `D₊(Xᵢ) ⊓ D₊(Xⱼ)`. -/
theorem basicOpen_awayToSection_chartCoord (i j : Fin 2) :
    (P1 k).basicOpen ((Proj.awayToSection 𝒜 (X i)).hom (chartCoord k i j)) =
      chartOpen k i ⊓ chartOpen k j := by
  change (Proj 𝒜).basicOpen ((Proj.awayToSection 𝒜 (X i)).hom (chartCoord k i j)) =
    Proj.basicOpen 𝒜 (X i) ⊓ Proj.basicOpen 𝒜 (X j)
  have hpre : (Proj.basicOpen 𝒜 (X i)).ι ⁻¹ᵁ
        ((Proj 𝒜).basicOpen ((Proj.awayToSection 𝒜 (X i)).hom (chartCoord k i j))) =
      (Proj.basicOpen 𝒜 (X i)).ι ⁻¹ᵁ Proj.basicOpen 𝒜 (X j) := by
    rw [← Scheme.Opens.toSpecΓ_preimage_basicOpen]
    conv_rhs => rw [basicOpen_ι_eq k (X_mem k i) one_pos]
    change _ = Proj.basicOpenToSpec 𝒜 (X i) ⁻¹ᵁ
      (Proj.awayι 𝒜 (X i) (X_mem k i) one_pos ⁻¹ᵁ Proj.basicOpen 𝒜 (X j))
    rw [Proj.awayι_preimage_basicOpen 𝒜 (X_mem k i) one_pos (X_mem k j) one_pos,
      isLocalizationElem_X_eq k i j]
    rfl
  have himg := congrArg (fun W => (Proj.basicOpen 𝒜 (X i)).ι ''ᵁ W) hpre
  simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    at himg
  have hle : (Proj 𝒜).basicOpen ((Proj.awayToSection 𝒜 (X i)).hom (chartCoord k i j)) ≤
      Proj.basicOpen 𝒜 (X i) := (Proj 𝒜).basicOpen_le _
  calc (Proj 𝒜).basicOpen ((Proj.awayToSection 𝒜 (X i)).hom (chartCoord k i j))
      = Proj.basicOpen 𝒜 (X i) ⊓
          (Proj 𝒜).basicOpen ((Proj.awayToSection 𝒜 (X i)).hom (chartCoord k i j)) :=
        (inf_eq_right.mpr hle).symm
    _ = Proj.basicOpen 𝒜 (X i) ⊓ Proj.basicOpen 𝒜 (X j) := himg

/-! ### The Laurent generators as restrictions from the charts -/

/-- Under the overlap identification, `T` is the restriction to the overlap of the chart-0
coordinate `X₁/X₀ ∈ Γ(D₊(X₀))`. -/
theorem overlapSectionsEquiv_symm_T :
    (overlapSectionsEquiv k).symm (LaurentPolynomial.T 1) =
      ((P1 k).presheaf.map (homOfLE (overlap_le_left k)).op).hom
        ((Proj.awayToSection 𝒜 (X 0)).hom (chartCoord k 0 1)) := by
  apply (overlapSectionsEquiv k).injective
  rw [RingEquiv.apply_symm_apply, res_awayToSection_left, overlapSectionsEquiv_awayToSection,
    overlapAlgEquiv_awayToOverlapLeft, awayAlgEquiv_chartCoord k fin_zero_ne_one,
    Polynomial.toLaurent_X]

/-- Under the overlap identification, `T⁻¹` is the restriction to the overlap of the
chart-1 coordinate `X₀/X₁ ∈ Γ(D₊(X₁))`. -/
theorem overlapSectionsEquiv_symm_T_neg :
    (overlapSectionsEquiv k).symm (LaurentPolynomial.T (-1)) =
      ((P1 k).presheaf.map (homOfLE (overlap_le_right k)).op).hom
        ((Proj.awayToSection 𝒜 (X 1)).hom (chartCoord k 1 0)) := by
  apply (overlapSectionsEquiv k).injective
  rw [RingEquiv.apply_symm_apply, res_awayToSection_right, overlapSectionsEquiv_awayToSection,
    overlapAlgEquiv_awayToOverlapRight_chartCoord]

/-- The overlap identification matches the algebra map of the homogeneous localization
with that of the Laurent polynomial ring. -/
theorem overlapSectionsEquiv_symm_algebraMap (r : k) :
    (overlapSectionsEquiv k).symm (algebraMap k (LaurentPolynomial k) r) =
      (Proj.awayToSection 𝒜 (X 0 * X 1)).hom (algebraMap k (Away 𝒜 (X 0 * X 1)) r) := by
  apply (overlapSectionsEquiv k).injective
  rw [RingEquiv.apply_symm_apply, overlapSectionsEquiv_awayToSection]
  exact ((overlapAlgEquiv k).commutes r).symm

end P1

end AlgebraicGeometry
