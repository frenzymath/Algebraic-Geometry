/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.P1

/-!
# The Laurent chart pair on the projective line

Continuation of `AlgebraicJacobian.Curve.P1`: the overlap `D₊(X₀X₁)` of the two standard
charts of `P1 k` and its identification with the Laurent polynomial ring, the section-level
chart identifications, and the bundled chart package.

* `P1.overlapAlgEquiv : (k[X₀,X₁]_(X₀X₁))₀ ≃ₐ[k] k[T,T⁻¹]`, with the two restriction maps
  `P1.awayToOverlapLeft/Right` becoming `t ↦ T` and `t ↦ T⁻¹`
  (`P1.overlapAlgEquiv_awayToOverlapLeft`/`Right`);
* the *Laurent span* property `P1.exists_awayToOverlap_add`: every element of the overlap
  ring is a sum of restrictions from the two charts;
* section-level versions of all of the above (`P1.chartSectionsEquiv₀/₁`,
  `P1.overlapSectionsEquiv`, `P1.overlapSectionsEquiv_res_left/right`);
* the package `AlgebraicGeometry.LaurentChartPair` with canonical term
  `P1.laurentChartPair k`, and the span property `LaurentChartPair.exists_res_add_res`
  for any such package. This package is exactly what the two-lattice finiteness argument
  for `H¹(C, 𝒪_C)` consumes.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

open MvPolynomial HomogeneousLocalization

namespace P1

variable (k : Type u) [Field k]

/-- The standard grading of `k[X₀, X₁]`, the graded ring underlying `P1 k`. -/
local notation "𝒜" => homogeneousSubmodule (Fin 2) k

/-! ### The overlap `D₊(X₀X₁)` and the identification with Laurent polynomials -/

/-- The restriction map from the chart `D₊(X₀)` to the overlap `D₊(X₀X₁)`. -/
noncomputable def awayToOverlapLeft :
    Away 𝒜 (X 0) →+* Away 𝒜 (X 0 * X 1) :=
  awayMap 𝒜 (X_mem k 1) rfl

/-- The restriction map from the chart `D₊(X₁)` to the overlap `D₊(X₀X₁)`. -/
noncomputable def awayToOverlapRight :
    Away 𝒜 (X 1) →+* Away 𝒜 (X 0 * X 1) :=
  awayMap 𝒜 (X_mem k 0) (mul_comm (X 0) (X 1))

theorem awayToOverlapLeft_eq :
    awayToOverlapLeft k = awayMap 𝒜 (X_mem k 1)
      (rfl : (X 0 : MvPolynomial (Fin 2) k) * X 1 = X 0 * X 1) :=
  rfl

theorem awayToOverlapRight_eq :
    awayToOverlapRight k = awayMap 𝒜 (X_mem k 0) (mul_comm (X 0) (X 1)) :=
  rfl

theorem awayToOverlapLeft_algebraMap (r : k) :
    awayToOverlapLeft k (algebraMap k _ r) = algebraMap k _ r :=
  awayMap_fromZeroRingHom 𝒜 (X_mem k 1)
    (rfl : (X 0 : MvPolynomial (Fin 2) k) * X 1 = X 0 * X 1) (algebraMap k (𝒜 0) r)

theorem awayToOverlapRight_algebraMap (r : k) :
    awayToOverlapRight k (algebraMap k _ r) = algebraMap k _ r :=
  awayMap_fromZeroRingHom 𝒜 (X_mem k 0) (mul_comm (X 0) (X 1))
    (algebraMap k (𝒜 0) r)

noncomputable instance : Algebra (Away 𝒜 (X 0)) (Away 𝒜 (X 0 * X 1)) :=
  (awayToOverlapLeft k).toAlgebra

noncomputable instance : Algebra (Away 𝒜 (X 1)) (Away 𝒜 (X 0 * X 1)) :=
  (awayToOverlapRight k).toAlgebra

theorem isLocalizationElem_eq :
    Away.isLocalizationElem (X_mem k 0) (X_mem k 1) = chartCoord k 0 1 := by
  rw [Away.isLocalizationElem, chartCoord_eq]
  congr 1
  exact pow_one _

/-- The overlap ring is the localization of the chart ring `(k[X₀,X₁]_(X₀))₀ = k[t]` away
from the chart coordinate `t = X₁/X₀`. -/
instance : IsLocalization.Away (chartCoord k 0 1) (Away 𝒜 (X 0 * X 1)) := by
  have h : IsLocalization.Away (Away.isLocalizationElem (X_mem k 0) (X_mem k 1))
      (Away 𝒜 (X 0 * X 1)) :=
    Away.isLocalization_mul (X_mem k 0) (X_mem k 1)
      (rfl : (X 0 : MvPolynomial (Fin 2) k) * X 1 = X 0 * X 1) one_ne_zero
  rwa [isLocalizationElem_eq] at h

/-- The overlap identification as a ring equivalence; see `P1.overlapAlgEquiv` for the
`k`-algebra version. -/
noncomputable def overlapRingEquiv :
    Away 𝒜 (X 0 * X 1) ≃+* LaurentPolynomial k :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (chartCoord k 0 1))
    (T := Submonoid.powers (Polynomial.X : Polynomial k))
    (Away 𝒜 (X 0 * X 1)) (LaurentPolynomial k)
    (awayAlgEquiv k fin_zero_ne_one).toRingEquiv
    (by rw [Submonoid.map_powers]
        exact congrArg _ (awayAlgEquiv_chartCoord k fin_zero_ne_one))

theorem overlapRingEquiv_awayToOverlapLeft (z : Away 𝒜 (X 0)) :
    overlapRingEquiv k (awayToOverlapLeft k z) =
      Polynomial.toLaurent (awayAlgEquiv k fin_zero_ne_one z) := by
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent]
  exact IsLocalization.ringEquivOfRingEquiv_eq _ _

/-- The overlap identification: the section ring `(k[X₀,X₁]_(X₀X₁))₀` of the chart overlap is
the ring of Laurent polynomials over `k`, with `T = X₁/X₀`. -/
noncomputable def overlapAlgEquiv :
    Away 𝒜 (X 0 * X 1) ≃ₐ[k] LaurentPolynomial k :=
  { overlapRingEquiv k with
    commutes' := fun r => by
      change overlapRingEquiv k (algebraMap k _ r) = _
      rw [← awayToOverlapLeft_algebraMap, overlapRingEquiv_awayToOverlapLeft,
        AlgEquiv.commutes, ← Polynomial.C_eq_algebraMap, Polynomial.toLaurent_C,
        LaurentPolynomial.C_eq_algebraMap] }

theorem overlapAlgEquiv_apply (z : Away 𝒜 (X 0 * X 1)) :
    overlapAlgEquiv k z = overlapRingEquiv k z :=
  rfl

/-- Through the chart identifications, the left restriction map to the overlap is the
canonical map `k[t] → k[T,T⁻¹]`, `t ↦ T`. -/
theorem overlapAlgEquiv_awayToOverlapLeft (z : Away 𝒜 (X 0)) :
    overlapAlgEquiv k (awayToOverlapLeft k z) =
      Polynomial.toLaurent (awayAlgEquiv k fin_zero_ne_one z) :=
  overlapRingEquiv_awayToOverlapLeft k z

theorem awayToOverlap_mul_eq_one :
    awayToOverlapLeft k (chartCoord k 0 1) * awayToOverlapRight k (chartCoord k 1 0) = 1 := by
  rw [awayToOverlapLeft_eq, awayToOverlapRight_eq, chartCoord_eq k 0 1, chartCoord_eq k 1 0,
    awayMap_mk, awayMap_mk, ext_iff_val, val_mul, val_one, Away.val_mk, Away.val_mk,
    Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

theorem overlapAlgEquiv_awayToOverlapRight_chartCoord :
    overlapAlgEquiv k (awayToOverlapRight k (chartCoord k 1 0)) = LaurentPolynomial.T (-1) := by
  have h1 : (LaurentPolynomial.T 1 : LaurentPolynomial k) *
      overlapAlgEquiv k (awayToOverlapRight k (chartCoord k 1 0)) = 1 := by
    rw [show (LaurentPolynomial.T 1 : LaurentPolynomial k) = Polynomial.toLaurent Polynomial.X
        from Polynomial.toLaurent_X.symm,
      ← awayAlgEquiv_chartCoord k fin_zero_ne_one,
      ← overlapAlgEquiv_awayToOverlapLeft, ← map_mul, awayToOverlap_mul_eq_one, map_one]
  calc overlapAlgEquiv k (awayToOverlapRight k (chartCoord k 1 0))
      = (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) *
          overlapAlgEquiv k (awayToOverlapRight k (chartCoord k 1 0)) := by
        rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero, one_mul]
    _ = LaurentPolynomial.T (-1) := by rw [mul_assoc, h1, mul_one]

/-- Through the chart identifications, the right restriction map to the overlap is the map
`k[t] → k[T,T⁻¹]`, `t ↦ T⁻¹`. -/
theorem overlapAlgEquiv_awayToOverlapRight (z : Away 𝒜 (X 1)) :
    overlapAlgEquiv k (awayToOverlapRight k z) =
      Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k)
        (awayAlgEquiv k fin_one_ne_zero z) := by
  obtain ⟨p, rfl⟩ := polyToAway_surjective k fin_one_ne_zero z
  rw [awayAlgEquiv_polyToAway]
  induction p using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial n a =>
    simp only [polyToAway_monomial, map_mul, map_pow,
      overlapAlgEquiv_awayToOverlapRight_chartCoord, awayToOverlapRight_algebraMap,
      AlgEquiv.commutes, Polynomial.aeval_monomial]

/-! ### The Laurent span property on the overlap -/

/-- **Laurent span, ring level**: every element of the overlap ring is the sum of a
restriction from the left chart and a restriction from the right chart. -/
theorem exists_awayToOverlap_add (w : Away 𝒜 (X 0 * X 1)) :
    ∃ (p : Away 𝒜 (X 0)) (q : Away 𝒜 (X 1)),
      w = awayToOverlapLeft k p + awayToOverlapRight k q := by
  obtain ⟨f₁, f₂, hf⟩ := LaurentPolynomial.exists_toLaurent_add_aeval (overlapAlgEquiv k w)
  refine ⟨(awayAlgEquiv k fin_zero_ne_one).symm f₁,
    (awayAlgEquiv k fin_one_ne_zero).symm f₂, (overlapAlgEquiv k).injective ?_⟩
  rw [map_add, overlapAlgEquiv_awayToOverlapLeft, overlapAlgEquiv_awayToOverlapRight,
    AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hf]

/-! ### Section-level identifications -/

theorem awayToSection_surjective {m : ℕ} (f : MvPolynomial (Fin 2) k) (f_deg : f ∈ 𝒜 m)
    (hm : 0 < m) : Function.Surjective (Proj.awayToSection 𝒜 f).hom := fun z => by
  obtain ⟨w, hw⟩ := (Proj.basicOpenIsoAway 𝒜 f f_deg hm).commRingCatIsoToRingEquiv.surjective z
  exact ⟨w, hw⟩

theorem overlap_le_left : Proj.basicOpen 𝒜 (X 0 * X 1) ≤ chartOpen k 0 :=
  Proj.basicOpen_mono 𝒜 _ _ ⟨X 1, rfl⟩

theorem overlap_le_right : Proj.basicOpen 𝒜 (X 0 * X 1) ≤ chartOpen k 1 :=
  Proj.basicOpen_mono 𝒜 _ _ ⟨X 0, mul_comm (X 0) (X 1)⟩

theorem isAffineOpen_overlap : IsAffineOpen (Proj.basicOpen 𝒜 (X 0 * X 1)) :=
  Proj.isAffineOpen_basicOpen 𝒜 _ (X_mul_X_mem k) two_pos

/-- Restriction of sections from the left chart to the overlap corresponds to
`P1.awayToOverlapLeft` under `Proj.awayToSection`. -/
theorem res_awayToSection_left (p : Away 𝒜 (X 0)) :
    ((P1 k).presheaf.map (homOfLE (overlap_le_left k)).op).hom
        ((Proj.awayToSection 𝒜 (X 0)).hom p) =
      (Proj.awayToSection 𝒜 (X 0 * X 1)).hom (awayToOverlapLeft k p) := by
  have h := Proj.awayMap_awayToSection 𝒜 (X_mem k 1)
    (rfl : (X 0 : MvPolynomial (Fin 2) k) * X 1 = X 0 * X 1)
  have h' := congr((CommRingCat.Hom.hom $h) p)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h'
  exact h'.symm

/-- Restriction of sections from the right chart to the overlap corresponds to
`P1.awayToOverlapRight` under `Proj.awayToSection`. -/
theorem res_awayToSection_right (q : Away 𝒜 (X 1)) :
    ((P1 k).presheaf.map (homOfLE (overlap_le_right k)).op).hom
        ((Proj.awayToSection 𝒜 (X 1)).hom q) =
      (Proj.awayToSection 𝒜 (X 0 * X 1)).hom (awayToOverlapRight k q) := by
  have h := Proj.awayMap_awayToSection 𝒜 (X_mem k 0) (mul_comm (X 0) (X 1))
  have h' := congr((CommRingCat.Hom.hom $h) q)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h'
  exact h'.symm

private theorem iso_symm_hom_apply {R S : CommRingCat.{u}} (e : R ≅ S) (x : R) :
    e.commRingCatIsoToRingEquiv.symm (e.hom.hom x) = x := by
  change e.inv.hom (e.hom.hom x) = x
  have h := congr((CommRingCat.Hom.hom $(e.hom_inv_id)) x)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply,
    RingHom.id_apply] at h
  exact h

/-- The identification of the section ring of the chart `D₊(X₀)` with `k[t]`, `t = X₁/X₀`. -/
noncomputable def chartSectionsEquiv₀ : Γ(P1 k, chartOpen k 0) ≃+* Polynomial k :=
  ((Proj.basicOpenIsoAway 𝒜 (X 0) (X_mem k 0) one_pos).commRingCatIsoToRingEquiv).symm.trans
    (awayAlgEquiv k fin_zero_ne_one).toRingEquiv

/-- The identification of the section ring of the chart `D₊(X₁)` with `k[t]`, `t = X₀/X₁`. -/
noncomputable def chartSectionsEquiv₁ : Γ(P1 k, chartOpen k 1) ≃+* Polynomial k :=
  ((Proj.basicOpenIsoAway 𝒜 (X 1) (X_mem k 1) one_pos).commRingCatIsoToRingEquiv).symm.trans
    (awayAlgEquiv k fin_one_ne_zero).toRingEquiv

/-- The identification of the section ring of the chart overlap `D₊(X₀X₁)` with the Laurent
polynomial ring, `T = X₁/X₀`. -/
noncomputable def overlapSectionsEquiv :
    Γ(P1 k, Proj.basicOpen 𝒜 (X 0 * X 1)) ≃+* LaurentPolynomial k :=
  ((Proj.basicOpenIsoAway 𝒜 (X 0 * X 1)
    (X_mul_X_mem k) two_pos).commRingCatIsoToRingEquiv).symm.trans
    (overlapAlgEquiv k).toRingEquiv

theorem chartSectionsEquiv₀_awayToSection (p : Away 𝒜 (X 0)) :
    chartSectionsEquiv₀ k ((Proj.awayToSection 𝒜 (X 0)).hom p) =
      awayAlgEquiv k fin_zero_ne_one p := by
  change (((Proj.basicOpenIsoAway 𝒜 (X 0) (X_mem k 0)
      one_pos).commRingCatIsoToRingEquiv).symm.trans
      (awayAlgEquiv k fin_zero_ne_one).toRingEquiv)
      ((Proj.awayToSection 𝒜 (X 0)).hom p) = _
  rw [RingEquiv.trans_apply, ← Proj.basicOpenIsoAway_hom 𝒜 (X 0) (X_mem k 0) one_pos,
    iso_symm_hom_apply]
  rfl

theorem chartSectionsEquiv₁_awayToSection (q : Away 𝒜 (X 1)) :
    chartSectionsEquiv₁ k ((Proj.awayToSection 𝒜 (X 1)).hom q) =
      awayAlgEquiv k fin_one_ne_zero q := by
  change (((Proj.basicOpenIsoAway 𝒜 (X 1) (X_mem k 1)
      one_pos).commRingCatIsoToRingEquiv).symm.trans
      (awayAlgEquiv k fin_one_ne_zero).toRingEquiv)
      ((Proj.awayToSection 𝒜 (X 1)).hom q) = _
  rw [RingEquiv.trans_apply, ← Proj.basicOpenIsoAway_hom 𝒜 (X 1) (X_mem k 1) one_pos,
    iso_symm_hom_apply]
  rfl

theorem overlapSectionsEquiv_awayToSection (w : Away 𝒜 (X 0 * X 1)) :
    overlapSectionsEquiv k ((Proj.awayToSection 𝒜 (X 0 * X 1)).hom w) =
      overlapAlgEquiv k w := by
  change (((Proj.basicOpenIsoAway 𝒜 (X 0 * X 1)
      (X_mul_X_mem k) two_pos).commRingCatIsoToRingEquiv).symm.trans
      (overlapAlgEquiv k).toRingEquiv)
      ((Proj.awayToSection 𝒜 (X 0 * X 1)).hom w) = _
  rw [RingEquiv.trans_apply, ← Proj.basicOpenIsoAway_hom 𝒜 (X 0 * X 1)
    (X_mul_X_mem k) two_pos, iso_symm_hom_apply]
  rfl

/-- Through the section-level identifications, restriction from the left chart to the
overlap is `t ↦ T`. -/
theorem overlapSectionsEquiv_res_left (a : Γ(P1 k, chartOpen k 0)) :
    overlapSectionsEquiv k (((P1 k).presheaf.map (homOfLE (overlap_le_left k)).op).hom a) =
      Polynomial.toLaurent (chartSectionsEquiv₀ k a) := by
  obtain ⟨p, rfl⟩ := awayToSection_surjective k (X 0) (X_mem k 0) one_pos a
  rw [res_awayToSection_left, overlapSectionsEquiv_awayToSection,
    chartSectionsEquiv₀_awayToSection, overlapAlgEquiv_awayToOverlapLeft]

/-- Through the section-level identifications, restriction from the right chart to the
overlap is `t ↦ T⁻¹`. -/
theorem overlapSectionsEquiv_res_right (b : Γ(P1 k, chartOpen k 1)) :
    overlapSectionsEquiv k (((P1 k).presheaf.map (homOfLE (overlap_le_right k)).op).hom b) =
      Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k)
        (chartSectionsEquiv₁ k b) := by
  obtain ⟨q, rfl⟩ := awayToSection_surjective k (X 1) (X_mem k 1) one_pos b
  rw [res_awayToSection_right, overlapSectionsEquiv_awayToSection,
    chartSectionsEquiv₁_awayToSection, overlapAlgEquiv_awayToOverlapRight]

end P1

/-! ### The bundled chart package -/

/-- A **Laurent chart pair** on the projective line over `k`: two affine opens covering
`P1 k` with a distinguished affine overlap, whose section rings are polynomial rings `k[t]`,
whose overlap section ring is the Laurent polynomial ring, and such that the two restriction
maps become `t ↦ T` and `t ↦ T⁻¹`.

The canonical example is `P1.laurentChartPair k` (the two standard charts). The Laurent span
property `LaurentChartPair.exists_res_add_res` holds for any such pair; this package is
exactly what the two-lattice finiteness argument for `H¹(C, 𝒪_C)` consumes. -/
structure LaurentChartPair (k : Type u) [Field k] where
  /-- The left chart. -/
  U₀ : (P1 k).Opens
  /-- The right chart. -/
  U₁ : (P1 k).Opens
  /-- The overlap. -/
  U₀₁ : (P1 k).Opens
  le_left : U₀₁ ≤ U₀
  le_right : U₀₁ ≤ U₁
  inf_eq : U₀ ⊓ U₁ = U₀₁
  isAffineOpen_U₀ : IsAffineOpen U₀
  isAffineOpen_U₁ : IsAffineOpen U₁
  isAffineOpen_U₀₁ : IsAffineOpen U₀₁
  /-- The two charts cover `P1 k`. -/
  sup_eq_top : U₀ ⊔ U₁ = ⊤
  /-- The sections on the left chart form a polynomial ring. -/
  Γ₀ : Γ(P1 k, U₀) ≃+* Polynomial k
  /-- The sections on the right chart form a polynomial ring. -/
  Γ₁ : Γ(P1 k, U₁) ≃+* Polynomial k
  /-- The sections on the overlap form a Laurent polynomial ring. -/
  Γ₀₁ : Γ(P1 k, U₀₁) ≃+* LaurentPolynomial k
  /-- Through the identifications, restriction from the left chart is `t ↦ T`. -/
  res_left : ∀ a, Γ₀₁ (((P1 k).presheaf.map (homOfLE le_left).op).hom a) =
    Polynomial.toLaurent (Γ₀ a)
  /-- Through the identifications, restriction from the right chart is `t ↦ T⁻¹`. -/
  res_right : ∀ b, Γ₀₁ (((P1 k).presheaf.map (homOfLE le_right).op).hom b) =
    Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k) (Γ₁ b)

namespace LaurentChartPair

variable {k : Type u} [Field k] (D : LaurentChartPair k)

/-- **Laurent span** for any Laurent chart pair: every section on the overlap is the sum of a
restriction from the left chart and a restriction from the right chart. This is the
surjectivity half of the Mayer–Vietoris difference map for the two-chart cover. -/
theorem exists_res_add_res (z : Γ(P1 k, D.U₀₁)) :
    ∃ (a : Γ(P1 k, D.U₀)) (b : Γ(P1 k, D.U₁)),
      z = ((P1 k).presheaf.map (homOfLE D.le_left).op).hom a +
          ((P1 k).presheaf.map (homOfLE D.le_right).op).hom b := by
  obtain ⟨p, q, hpq⟩ := LaurentPolynomial.exists_toLaurent_add_aeval (D.Γ₀₁ z)
  refine ⟨D.Γ₀.symm p, D.Γ₁.symm q, D.Γ₀₁.injective ?_⟩
  rw [map_add, D.res_left, D.res_right, RingEquiv.apply_symm_apply,
    RingEquiv.apply_symm_apply, hpq]

end LaurentChartPair

namespace P1

variable (k : Type u) [Field k]

local notation "𝒜" => homogeneousSubmodule (Fin 2) k

/-- The canonical Laurent chart pair on `P1 k`: the two standard charts `D₊(X₀)`, `D₊(X₁)`
with coordinates `t = X₁/X₀` resp. `s = X₀/X₁`, and overlap coordinate `T = X₁/X₀`. -/
noncomputable def laurentChartPair : LaurentChartPair k where
  U₀ := chartOpen k 0
  U₁ := chartOpen k 1
  U₀₁ := Proj.basicOpen 𝒜 (X 0 * X 1)
  le_left := overlap_le_left k
  le_right := overlap_le_right k
  inf_eq := chartOpen_inf k
  isAffineOpen_U₀ := isAffineOpen_chartOpen k 0
  isAffineOpen_U₁ := isAffineOpen_chartOpen k 1
  isAffineOpen_U₀₁ := isAffineOpen_overlap k
  sup_eq_top := chartOpen_sup k
  Γ₀ := chartSectionsEquiv₀ k
  Γ₁ := chartSectionsEquiv₁ k
  Γ₀₁ := overlapSectionsEquiv k
  res_left := overlapSectionsEquiv_res_left k
  res_right := overlapSectionsEquiv_res_right k

end P1

end AlgebraicGeometry

