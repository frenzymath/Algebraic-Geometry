/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.PointFiberIdeal
import AlgebraicJacobian.Curve.GraphDivisor
import AlgebraicJacobian.RiemannRoch.GraphSectionEval

/-!
# The graph chart and its kernel presentation (G-D8, multiplicity input)

For a `K`-point `t : overSpec k K ⟶ C` of the challenge curve, this file builds the affine
chart of the fibre curve `C_K := (C ⊗ overSpec k K).left` on which the ideal of the graph
section is principal on the transported point generator — the multiplicity half of G-D8's
degree-1 certificate.

With `p₀ := t (default)` the image point, `U := (Over.diagonalChartData C).chart p₀` the frozen
étale-coordinate chart and `F := Γ(Spec K, ⊤)`:

* `AlgebraicGeometry.graphCoordEval` — the point pullback `c := t^♯ : Γ(C, U) →ₐ[k] F`;
* `AlgebraicGeometry.graphGen` — the point generator `u ⊗ 1 − 1 ⊗ c u ∈ Γ(C, U) ⊗[k] F`;
* `AlgebraicGeometry.graphChart` — the affine chart `D(1 − eliftF) ⊆ 𝔚(U, ⊤)` of `C_K`,
  the basic open of the pushed diagonal idempotent, containing the graph point;
* `AlgebraicGeometry.graphChartEqn` — the transported point generator on the chart;
* `AlgebraicGeometry.ker_graphSectionEval_eq_span_graphChartEqn` — **the kernel
  presentation**: on the chart, the kernel of the evaluation at the graph section is the
  principal ideal on the transported point generator.  This is
  `AlgebraicJacobian.Diagonal.ker_pointEv_map_localization_eq` (the pushed B0 diagonal-ideal
  engine) read through the landed basic-open localization seam
  (`Over.isLocalization_away_basicOpen_productChartSections`);
* `AlgebraicGeometry.finrank_quotient_span_graphChartEqn` — the colength of the graph
  equation on the chart is **one** (with `GraphSectionEval`'s
  `finrank_quotient_ker_graphSectionEval`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open Module (finrank)
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom]
  {K : Type u} [Field K] [Algebra k K] (t : overSpec k K ⟶ C)

/-! ## The chart data at the image point -/

/-- The frozen étale-coordinate chart of `C` at the image point `p₀ := t (default)` of the
`K`-point `t`.  An `abbrev`, so that the frozen chart-data instances (`coordAlgebra`,
`isScalarTower`) transport to it by unfolding. -/
noncomputable abbrev graphBaseChart : C.left.Opens :=
  (Over.diagonalChartData C).chart (t.left.base default)

lemma isAffineOpen_graphBaseChart : IsAffineOpen (graphBaseChart C t) :=
  (Over.diagonalChartData C).isAffineOpen _

lemma basePoint_mem_graphBaseChart : t.left.base default ∈ graphBaseChart C t :=
  (Over.diagonalChartData C).mem _

lemma top_le_preimage_graphBaseChart : ⊤ ≤ t.left ⁻¹ᵁ graphBaseChart C t := by
  intro z _
  have hz : z = (default : (overSpec k K).left) := Subsingleton.elim _ _
  subst hz
  exact basePoint_mem_graphBaseChart C t

/-- **The point pullback** `c := t^♯ : Γ(C, U) →ₐ[k] Γ(Spec K, ⊤)` on the chart at the
image point. -/
noncomputable def graphCoordEval :
    Γ(C.left, graphBaseChart C t) →ₐ[k] Γ((overSpec k K).left, ⊤) :=
  Over.appLEAlgHom t (graphBaseChart C t) ⊤ (top_le_preimage_graphBaseChart C t)

/-- **The point generator** `u ⊗ 1 − 1 ⊗ c u` of the graph section on the chart tensor
ring (`AlgebraicJacobian.Diagonal.pointGen` with the transported coordinate). -/
noncomputable def graphGen :
    Γ(C.left, graphBaseChart C t) ⊗[k] Γ((overSpec k K).left, ⊤) :=
  letI : Algebra (Polynomial k) Γ(C.left, graphBaseChart C t) :=
    (Over.diagonalChartData C).coordAlgebra (t.left.base default)
  AlgebraicJacobian.Diagonal.coord k Γ(C.left, graphBaseChart C t) ⊗ₜ[k] 1
    - 1 ⊗ₜ[k] graphCoordEval C t
        (AlgebraicJacobian.Diagonal.coord k Γ(C.left, graphBaseChart C t))

/-- The push of the frozen diagonal idempotent lift along the point pullback. -/
noncomputable def graphElift :
    Γ(C.left, graphBaseChart C t) ⊗[k] Γ((overSpec k K).left, ⊤) :=
  Algebra.TensorProduct.map (AlgHom.id k Γ(C.left, graphBaseChart C t))
    (graphCoordEval C t)
    ((Over.diagonalChartData C).elift (t.left.base default))

/-- **The graph chart**: the basic open `D(1 − eliftF)` of the product chart `𝔚(U, ⊤)` of
the fibre curve, on which the graph ideal is principal on the point generator.  An
`abbrev`, so that the ambient `basicOpen` localization instances fire on it. -/
noncomputable abbrev graphChart : (C ⊗ overSpec k K).left.Opens :=
  (C ⊗ overSpec k K).left.basicOpen
    (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
      (isAffineOpen_top_overSpec k K) (1 - graphElift C t))

lemma isAffineOpen_graphChart : IsAffineOpen (graphChart C t) :=
  Over.isAffineOpen_basicOpen_productChartSections C (overSpec k K) _ _ _

lemma graphChart_le_productChart :
    graphChart C t
      ≤ Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤ :=
  (C ⊗ overSpec k K).left.basicOpen_le _

/-- **The graph equation on the chart**: the transported point generator, restricted to
the graph chart. -/
noncomputable def graphChartEqn : Γ((C ⊗ overSpec k K).left, graphChart C t) :=
  ((C ⊗ overSpec k K).left.presheaf.map (homOfLE (graphChart_le_productChart C t)).op).hom
    (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
      (isAffineOpen_top_overSpec k K) (graphGen C t))

/-! ## The tensor-level evaluation and the section evaluation -/

/-- The tensor-level point evaluation `Γ(C, U) ⊗[k] F → F`, `a ⊗ λ ↦ c a · λ`
(`AlgebraicJacobian.Diagonal.pointEv` with the transported coordinate). -/
noncomputable def graphTensorEval :
    Γ(C.left, graphBaseChart C t) ⊗[k] Γ((overSpec k K).left, ⊤)
      →ₐ[k] Γ((overSpec k K).left, ⊤) :=
  Algebra.TensorProduct.lift (graphCoordEval C t) (AlgHom.id k _)
    (fun _ _ => Commute.all _ _)

@[simp] lemma graphTensorEval_tmul (a : Γ(C.left, graphBaseChart C t))
    (b : Γ((overSpec k K).left, ⊤)) :
    graphTensorEval C t (a ⊗ₜ[k] b) = graphCoordEval C t a * b := by
  rw [graphTensorEval, Algebra.TensorProduct.lift_tmul]
  rfl

/-- The tensor evaluation of a second-factor push is the point pullback of the
multiplication — hence the pushed idempotent evaluates to zero. -/
lemma graphTensorEval_map (z : Γ(C.left, graphBaseChart C t) ⊗[k]
      Γ(C.left, graphBaseChart C t)) :
    graphTensorEval C t
        (Algebra.TensorProduct.map (AlgHom.id k Γ(C.left, graphBaseChart C t))
          (graphCoordEval C t) z)
      = graphCoordEval C t (Algebra.TensorProduct.lmul' k z) := by
  induction z with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul, graphTensorEval_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
      rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The pushed idempotent lift evaluates to zero: the graph chart contains the graph
point. -/
lemma graphTensorEval_graphElift : graphTensorEval C t (graphElift C t) = 0 := by
  rw [graphElift, graphTensorEval_map,
    (Over.diagonalChartData C).lmul'_elift (t.left.base default), map_zero]

/-- The graph point lies in the product chart `𝔚(U, ⊤)`. -/
lemma graphPoint_mem_productChart :
    Over.graphPoint C t
      ∈ Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤ := by
  rw [Over.mem_productChart]
  refine ⟨?_, trivial⟩
  rw [Over.fst_graphPoint]
  exact basePoint_mem_graphBaseChart C t

/-- **The evaluation of an identified tensor at the graph section** is the tensor-level
point evaluation: `σ_t^♯ (pcs y) = ev y`.  The lift-app rule at `q = σ_t = lift t 𝟙`. -/
theorem graphSectionEval_productChartSections
    (y : Γ(C.left, graphBaseChart C t) ⊗[k] Γ((overSpec k K).left, ⊤)) :
    graphSectionEval t (graphPoint_mem_productChart C t)
        (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
          (isAffineOpen_top_overSpec k K) y)
      = graphTensorEval C t y := by
  induction y with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | tmul a b =>
      rw [graphTensorEval_tmul]
      have hb' : (⊤ : (overSpec k K).left.Opens)
          ≤ (𝟙 (overSpec k K) : overSpec k K ⟶ _).left ⁻¹ᵁ ⊤ := by
        intro z _; trivial
      have key := Over.appLE_productChartSections_tmul
        (X := C) (T := overSpec k K) (isAffineOpen_graphBaseChart C t)
        (isAffineOpen_top_overSpec k K) (q := Over.sectionOfPoint t) (a := t)
        (b := 𝟙 (overSpec k K)) (Over.sectionOfPoint_fst t) (Over.sectionOfPoint_snd t)
        (W := ⊤)
        (Over.top_le_sectionOfPoint_preimage t (graphPoint_mem_productChart C t))
        (top_le_preimage_graphBaseChart C t) hb' a b
      rw [show graphSectionEval t (graphPoint_mem_productChart C t)
          (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
            (isAffineOpen_top_overSpec k K) (a ⊗ₜ[k] b))
        = ((Over.sectionOfPoint t).left.appLE
            (Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤) ⊤
            (Over.top_le_sectionOfPoint_preimage t (graphPoint_mem_productChart C t))).hom
            (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
              (isAffineOpen_top_overSpec k K) (a ⊗ₜ[k] b)) from rfl, key]
      congr 1

/-- The graph point lies in the graph chart: the pushed idempotent evaluates to `1 ≠ 0`
at the graph section. -/
theorem graphPoint_mem_graphChart : Over.graphPoint C t ∈ graphChart C t := by
  refine (Scheme.mem_basicOpen _ _ _ (graphPoint_mem_productChart C t)).mpr ?_
  by_contra hnu
  have hker := ker_graphSectionEval_eq_primeIdealOf t
    (Over.isAffineOpen_productChart C (overSpec k K)
      (isAffineOpen_graphBaseChart C t) (isAffineOpen_top_overSpec k K))
    (graphPoint_mem_productChart C t)
  -- a non-unit germ lies in the prime of the point, i.e. in the kernel of the evaluation
  letI : Algebra Γ((C ⊗ overSpec k K).left,
      Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤)
      ((C ⊗ overSpec k K).left.presheaf.stalk (Over.graphPoint C t)) :=
    (C ⊗ overSpec k K).left.presheaf.algebra_section_stalk
      ⟨Over.graphPoint C t, graphPoint_mem_productChart C t⟩
  haveI hloc : IsLocalization.AtPrime
      ((C ⊗ overSpec k K).left.presheaf.stalk (Over.graphPoint C t))
      ((Over.isAffineOpen_productChart C (overSpec k K)
          (isAffineOpen_graphBaseChart C t)
          (isAffineOpen_top_overSpec k K)).primeIdealOf
        ⟨Over.graphPoint C t, graphPoint_mem_productChart C t⟩).asIdeal :=
    (Over.isAffineOpen_productChart C (overSpec k K) (isAffineOpen_graphBaseChart C t)
      (isAffineOpen_top_overSpec k K)).isLocalization_stalk _
  have hmem : Over.productChartSections C (overSpec k K)
        (isAffineOpen_graphBaseChart C t) (isAffineOpen_top_overSpec k K)
        (1 - graphElift C t)
      ∈ RingHom.ker (graphSectionEval t (graphPoint_mem_productChart C t)) := by
    rw [hker]
    rw [show ((C ⊗ overSpec k K).left.presheaf.germ _ (Over.graphPoint C t)
        (graphPoint_mem_productChart C t)).hom
          (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
            (isAffineOpen_top_overSpec k K) (1 - graphElift C t))
        = algebraMap _ ((C ⊗ overSpec k K).left.presheaf.stalk (Over.graphPoint C t))
            (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
              (isAffineOpen_top_overSpec k K) (1 - graphElift C t)) from rfl] at hnu
    have := (IsLocalization.AtPrime.isUnit_to_map_iff
      ((C ⊗ overSpec k K).left.presheaf.stalk (Over.graphPoint C t))
      ((Over.isAffineOpen_productChart C (overSpec k K)
          (isAffineOpen_graphBaseChart C t)
          (isAffineOpen_top_overSpec k K)).primeIdealOf
        ⟨Over.graphPoint C t, graphPoint_mem_productChart C t⟩).asIdeal
      (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
        (isAffineOpen_top_overSpec k K) (1 - graphElift C t)))
    exact not_not.mp fun hmem' => hnu (this.mpr hmem')
  rw [RingHom.mem_ker, graphSectionEval_productChartSections, map_sub, map_one,
    graphTensorEval_graphElift, sub_zero] at hmem
  have hone : (1 : Γ((overSpec k K).left, ⊤)) ≠ 0 := by
    letI : Field Γ((overSpec k K).left, ⊤) :=
      (isField_sections_top_overSpec (k := k) (K := K)).toField
    exact one_ne_zero
  exact hone hmem

/-! ## The kernel presentation on the graph chart -/

/-- **The kernel presentation of the graph ideal** (the multiplicity input of G-D8's
degree-1 certificate): on the graph chart, the kernel of the evaluation at the graph
section is the principal ideal on the graph equation.  The pushed B0 diagonal-ideal engine
(`ker_pointEv_map_localization_eq`), read through the basic-open localization seam. -/
theorem ker_graphSectionEval_eq_span_graphChartEqn :
    RingHom.ker (graphSectionEval t (graphPoint_mem_graphChart C t))
      = Ideal.span {graphChartEqn C t} := by
  classical
  set B := Γ(C.left, graphBaseChart C t)
  set F := Γ((overSpec k K).left, ⊤)
  letI : Algebra (Polynomial k) B :=
    (Over.diagonalChartData C).coordAlgebra (t.left.base default)
  haveI : IsScalarTower k (Polynomial k) B :=
    (Over.diagonalChartData C).isScalarTower (t.left.base default)
  letI : Algebra (Polynomial k) F :=
    ((graphCoordEval C t).toRingHom.comp (algebraMap (Polynomial k) B)).toAlgebra
  haveI : IsScalarTower k (Polynomial k) F := .of_algebraMap_eq fun p => by
    rw [show algebraMap (Polynomial k) F
        = (graphCoordEval C t).toRingHom.comp (algebraMap (Polynomial k) B) from rfl,
      RingHom.comp_apply, ← IsScalarTower.algebraMap_apply k (Polynomial k) B]
    exact ((graphCoordEval C t).commutes _).symm
  set c : B →ₐ[Polynomial k] F :=
    { toRingHom := (graphCoordEval C t).toRingHom, commutes' := fun p => rfl } with hc
  -- the localization structure on the chart sections
  letI : Algebra (B ⊗[k] F) Γ((C ⊗ overSpec k K).left, graphChart C t) :=
    ((algebraMap Γ((C ⊗ overSpec k K).left,
          Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤)
        Γ((C ⊗ overSpec k K).left, graphChart C t)).comp
      (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
        (isAffineOpen_top_overSpec k K)).toRingHom).toAlgebra
  haveI hlocz : IsLocalization.Away (1 - AlgebraicJacobian.Diagonal.mapRight c
        ((Over.diagonalChartData C).elift (t.left.base default)))
      Γ((C ⊗ overSpec k K).left, graphChart C t) := by
    have hbr : AlgebraicJacobian.Diagonal.mapRight c
        ((Over.diagonalChartData C).elift (t.left.base default)) = graphElift C t := rfl
    rw [hbr]
    exact Over.isLocalization_away_basicOpen_productChartSections C (overSpec k K)
      (isAffineOpen_graphBaseChart C t) (isAffineOpen_top_overSpec k K)
      (1 - graphElift C t)
  -- the pushed diagonal-ideal keystone
  have hkey := AlgebraicJacobian.Diagonal.ker_pointEv_map_localization_eq c
    ((Over.diagonalChartData C).elift (t.left.base default))
    ((Over.diagonalChartData C).isIdempotentElem_baseChange_elift (t.left.base default))
    ((Over.diagonalChartData C).ker_lmul'_eq_span_baseChange_elift (t.left.base default))
    Γ((C ⊗ overSpec k K).left, graphChart C t)
  -- identify the two evaluations and the two generators
  have hev : AlgebraicJacobian.Diagonal.pointEv c = graphTensorEval C t := rfl
  have hgen : AlgebraicJacobian.Diagonal.pointGen k B F = graphGen C t := rfl
  have halg : ∀ y : B ⊗[k] F,
      algebraMap (B ⊗[k] F) Γ((C ⊗ overSpec k K).left, graphChart C t) y
        = ((C ⊗ overSpec k K).left.presheaf.map
            (homOfLE (graphChart_le_productChart C t)).op).hom
            (Over.productChartSections C (overSpec k K)
              (isAffineOpen_graphBaseChart C t) (isAffineOpen_top_overSpec k K) y) :=
    fun _ => rfl
  have hEqn : algebraMap (B ⊗[k] F) Γ((C ⊗ overSpec k K).left, graphChart C t)
      (graphGen C t) = graphChartEqn C t := rfl
  -- the evaluation on the chart is the localized tensor evaluation
  have hεalg : ∀ y : B ⊗[k] F,
      graphSectionEval t (graphPoint_mem_graphChart C t)
          (algebraMap (B ⊗[k] F) Γ((C ⊗ overSpec k K).left, graphChart C t) y)
        = graphTensorEval C t y := by
    intro y
    rw [halg y, graphSectionEval_res t (graphPoint_mem_graphChart C t)
      (graphChart_le_productChart C t), graphSectionEval_productChartSections]
  refine le_antisymm ?_ ?_
  · -- ker ε ⊆ span: clear denominators into the tensor ring
    intro z hz
    rw [RingHom.mem_ker] at hz
    obtain ⟨⟨b, s⟩, hb⟩ := IsLocalization.surj
      (M := Submonoid.powers (1 - AlgebraicJacobian.Diagonal.mapRight c
        ((Over.diagonalChartData C).elift (t.left.base default)))) z
    obtain ⟨n, hs⟩ := s.2
    have hεs : graphSectionEval t (graphPoint_mem_graphChart C t)
        (algebraMap (B ⊗[k] F) Γ((C ⊗ overSpec k K).left, graphChart C t) (s : B ⊗[k] F))
        = 1 := by
      rw [hεalg, ← hs, map_pow]
      rw [show AlgebraicJacobian.Diagonal.mapRight c
          ((Over.diagonalChartData C).elift (t.left.base default)) = graphElift C t from rfl]
      rw [map_sub, map_one, graphTensorEval_graphElift, sub_zero, one_pow]
    have hεb : graphTensorEval C t b = 0 := by
      have := congrArg (graphSectionEval t (graphPoint_mem_graphChart C t)) hb
      rw [map_mul, hz, zero_mul, hεalg] at this
      exact this.symm
    have hbmem : algebraMap (B ⊗[k] F) Γ((C ⊗ overSpec k K).left, graphChart C t) b
        ∈ (RingHom.ker (AlgebraicJacobian.Diagonal.pointEv c)).map
          (algebraMap (B ⊗[k] F) Γ((C ⊗ overSpec k K).left, graphChart C t)) := by
      refine Ideal.mem_map_of_mem _ ?_
      rw [RingHom.mem_ker, hev]
      exact hεb
    rw [hkey] at hbmem
    have hunit : IsUnit (algebraMap (B ⊗[k] F)
        Γ((C ⊗ overSpec k K).left, graphChart C t) (s : B ⊗[k] F)) :=
      IsLocalization.map_units _ s
    have hz' : z = algebraMap (B ⊗[k] F) Γ((C ⊗ overSpec k K).left, graphChart C t) b
        * ↑hunit.unit⁻¹ := by
      rw [eq_comm, Units.mul_inv_eq_iff_eq_mul]
      rw [← hb]
      rfl
    rw [hz', ← hEqn]
    exact Ideal.mul_mem_right _ _ hbmem
  · -- span ⊆ ker ε: the generator evaluates to zero
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      ← hEqn, hεalg, ← hgen, ← hev]
    exact AlgebraicJacobian.Diagonal.pointEv_pointGen c

/-- **The colength of the graph equation on the graph chart is one** (the multiplicity ·
residue product of the degree-1 certificate). -/
theorem finrank_quotient_span_graphChartEqn :
    letI := Scheme.overSectionsAlgebra K (C ⊗ overSpec k K).left (graphChart C t)
    finrank K (Γ((C ⊗ overSpec k K).left, graphChart C t)
        ⧸ Ideal.span {graphChartEqn C t}) = 1 := by
  rw [← ker_graphSectionEval_eq_span_graphChartEqn C t]
  exact finrank_quotient_ker_graphSectionEval t (graphPoint_mem_graphChart C t)

end AlgebraicGeometry
