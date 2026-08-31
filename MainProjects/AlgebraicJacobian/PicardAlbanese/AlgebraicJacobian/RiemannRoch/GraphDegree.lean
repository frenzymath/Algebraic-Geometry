/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.GraphChart

/-!
# The degree-1 certificate of the graph class (G-D8 keystone)

For the challenge curve `C` over `k` and a `K`-point `t : overSpec k K ⟶ C`, the Picard
class of the graph divisor `Γ_t ⊆ C_K := (C ⊗ overSpec k K).left` has degree exactly one:

`AlgebraicGeometry.classDeg_graphPicClass : classDeg K (Over.graphPicClass C t) = 1`.

This is THE degree certificate of the Abel element (`informal/spec-g-d8.md`): both factors
of the Abel class restrict at a field point to graph classes, so this single constant
certifies membership in `pic0Subgroup`.

## The route

* **Support** (`Curve/GraphFibre.lean`): the graph has the single point
  `x_t := Over.graphPoint C t` (`mem_range_diagonal_graphLift_iff`), so away from `x_t` the
  pulled diagonal equation is `1` (`presentationElem_graphLocalEquations_of_ne`) and the
  presentation divisor of `Γ_t` is the one-point divisor
  `single x_t (ord_{x_t})` (`presentationDivisor_graphLocalEquations`).
* **The overlap identity** (`presentationElem_graphLocalEquations_val`): near `x_t` the
  pulled diagonal equation agrees with the transported point generator `graphChartEqn` of
  `RiemannRoch/GraphChart.lean` — the lift-app rule `Over.appLE_productChartSections_sub`
  on the overlap of the pullback member and the product chart `𝔚(U, ⊤)`, pushed into the
  function field at `η`.
* **Multiplicity · residue in one shot**: the SB-3b chart colength dictionary
  (`finrank_quotient_span_section`) on the graph chart reads
  `ord_{x_t}(g) · [κ(x_t) : K] = dim_K Γ(D(1−ẽ)) ⧸ (graphChartEqn) = 1`, the right-hand
  side being the landed `finrank_quotient_span_graphChartEqn` (the evaluation at the graph
  section has kernel `(graphChartEqn)` and a copy of `K` as quotient).
* **Closedness of the graph point** (`graphPoint_ne_genericPoint`): the graph ideal is a
  *nonzero* maximal ideal of the chart — `graphChartEqn ≠ 0` because the point generator is
  a nonzerodivisor of the tensor ring (the B1 engine, uniform in the second factor) and the
  chart is a localization of it.
* E-i (`classDeg_picClass`) + `deg_single'` close.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open Module (finrank)
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Over.sectionsAlgebra Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  {K : Type u} [Field K] [Algebra k K] (t : overSpec k K ⟶ C)

/-! ## The graph equation is nonzero -/

omit [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- **The point generator is a nonzerodivisor** of the chart tensor ring: the B1 regularity
engine `tmul_one_sub_one_tmul_mem_nonZeroDivisors`, uniform in the second tensor factor. -/
lemma graphGen_mem_nonZeroDivisors :
    graphGen C t
      ∈ nonZeroDivisors
          (Γ(C.left, graphBaseChart C t) ⊗[k] Γ((overSpec k K).left, ⊤)) := by
  letI := (Over.diagonalChartData C).coordAlgebra (t.left.base default)
  haveI := (Over.diagonalChartData C).isScalarTower (t.left.base default)
  haveI := (Over.diagonalChartData C).etale (t.left.base default)
  exact AlgebraicJacobian.Diagonal.tmul_one_sub_one_tmul_mem_nonZeroDivisors _

omit [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- **The graph equation is nonzero**: the graph chart is a localization of the tensor ring
(away from `1 − ẽ_F`), which sends the nonzerodivisor `graphGen` to a nonzero element
because the chart sections are nontrivial (they evaluate onto the field `Γ(Spec K, ⊤)`). -/
lemma graphChartEqn_ne_zero : graphChartEqn C t ≠ 0 := by
  intro h0
  -- the chart sections are nontrivial: they evaluate onto a field
  have hone : (1 : Γ((C ⊗ overSpec k K).left, graphChart C t)) ≠ 0 := by
    intro h1
    have h2 := congrArg (graphSectionEval t (graphPoint_mem_graphChart C t)) h1
    rw [map_one, map_zero] at h2
    letI : Field Γ((overSpec k K).left, ⊤) :=
      (isField_sections_top_overSpec (k := k) (K := K)).toField
    exact one_ne_zero h2
  -- the localization structure of the chart over the tensor ring
  letI : Algebra (Γ(C.left, graphBaseChart C t) ⊗[k] Γ((overSpec k K).left, ⊤))
      Γ((C ⊗ overSpec k K).left, graphChart C t) :=
    ((algebraMap Γ((C ⊗ overSpec k K).left,
          Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤)
        Γ((C ⊗ overSpec k K).left, graphChart C t)).comp
      (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
        (isAffineOpen_top_overSpec k K)).toRingHom).toAlgebra
  haveI : IsLocalization.Away (1 - graphElift C t)
      Γ((C ⊗ overSpec k K).left, graphChart C t) :=
    Over.isLocalization_away_basicOpen_productChartSections C (overSpec k K)
      (isAffineOpen_graphBaseChart C t) (isAffineOpen_top_overSpec k K)
      (1 - graphElift C t)
  have hEqn : algebraMap (Γ(C.left, graphBaseChart C t) ⊗[k] Γ((overSpec k K).left, ⊤))
      Γ((C ⊗ overSpec k K).left, graphChart C t) (graphGen C t) = graphChartEqn C t := rfl
  rw [← hEqn] at h0
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (1 - graphElift C t))
    Γ((C ⊗ overSpec k K).left, graphChart C t) (graphGen C t)).mp h0
  have hm0 : (m : Γ(C.left, graphBaseChart C t) ⊗[k] Γ((overSpec k K).left, ⊤)) = 0 :=
    (mem_nonZeroDivisors_iff.mp (graphGen_mem_nonZeroDivisors C t)).2 _ hm
  -- zero in the multiplicative set makes the localization trivial
  have hunit := IsLocalization.map_units
    Γ((C ⊗ overSpec k K).left, graphChart C t) m
  rw [hm0, map_zero] at hunit
  exact hone (isUnit_zero_iff.mp hunit).symm

/-! ## The graph point is closed -/

omit [IsProper C.hom] in
/-- **The graph point is not the generic point**: its prime on the graph chart is the
*nonzero* ideal `(graphChartEqn)`, and points of nonzero primes are closed. -/
theorem graphPoint_ne_genericPoint :
    Over.graphPoint C t ≠ genericPoint (C ⊗ overSpec k K).left := by
  have hbot : ((isAffineOpen_graphChart C t).primeIdealOf
      ⟨Over.graphPoint C t, graphPoint_mem_graphChart C t⟩).asIdeal ≠ ⊥ := by
    rw [← ker_graphSectionEval_eq_primeIdealOf t (isAffineOpen_graphChart C t)
      (graphPoint_mem_graphChart C t), ker_graphSectionEval_eq_span_graphChartEqn C t,
      ne_eq, Ideal.span_singleton_eq_bot]
    exact graphChartEqn_ne_zero C t
  have h1 := (isAffineOpen_graphChart C t).fromSpec_base_ne_genericPoint hbot
  rwa [(isAffineOpen_graphChart C t).fromSpec_primeIdealOf
    ⟨Over.graphPoint C t, graphPoint_mem_graphChart C t⟩] at h1

omit [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- **The graph equation is a unit away from the graph point**: on the graph chart the ideal
`(graphChartEqn)` is the *maximal* ideal of the graph point, so at any other closed point
the germ is invertible. -/
lemma isUnit_germ_graphChartEqn_of_ne {z : (C ⊗ overSpec k K).left}
    (hz : z ∈ graphChart C t) (hzx : z ≠ Over.graphPoint C t) :
    IsUnit (((C ⊗ overSpec k K).left.presheaf.germ (graphChart C t) z hz).hom
      (graphChartEqn C t)) := by
  by_contra hn
  letI : Algebra Γ((C ⊗ overSpec k K).left, graphChart C t)
      ((C ⊗ overSpec k K).left.presheaf.stalk z) :=
    (C ⊗ overSpec k K).left.presheaf.algebra_section_stalk ⟨z, hz⟩
  haveI := (isAffineOpen_graphChart C t).isLocalization_stalk ⟨z, hz⟩
  -- the equation lies in the prime of `z`
  have hmem : graphChartEqn C t
      ∈ ((isAffineOpen_graphChart C t).primeIdealOf ⟨z, hz⟩).asIdeal := by
    have hiff := IsLocalization.AtPrime.isUnit_to_map_iff
      ((C ⊗ overSpec k K).left.presheaf.stalk z)
      ((isAffineOpen_graphChart C t).primeIdealOf ⟨z, hz⟩).asIdeal (graphChartEqn C t)
    refine not_not.mp fun hmem' => hn ?_
    rw [show ((C ⊗ overSpec k K).left.presheaf.germ (graphChart C t) z hz).hom
        (graphChartEqn C t)
      = algebraMap Γ((C ⊗ overSpec k K).left, graphChart C t)
          ((C ⊗ overSpec k K).left.presheaf.stalk z) (graphChartEqn C t) from rfl]
    exact hiff.mpr hmem'
  -- so the maximal prime of the graph point is contained in it, hence equal
  have hle : ((isAffineOpen_graphChart C t).primeIdealOf
        ⟨Over.graphPoint C t, graphPoint_mem_graphChart C t⟩).asIdeal
      ≤ ((isAffineOpen_graphChart C t).primeIdealOf ⟨z, hz⟩).asIdeal := by
    rw [← ker_graphSectionEval_eq_primeIdealOf t (isAffineOpen_graphChart C t)
      (graphPoint_mem_graphChart C t), ker_graphSectionEval_eq_span_graphChartEqn C t]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have hmax : ((isAffineOpen_graphChart C t).primeIdealOf
      ⟨Over.graphPoint C t, graphPoint_mem_graphChart C t⟩).asIdeal.IsMaximal := by
    rw [← ker_graphSectionEval_eq_primeIdealOf t (isAffineOpen_graphChart C t)
      (graphPoint_mem_graphChart C t)]
    exact isMaximal_ker_graphSectionEval t (graphPoint_mem_graphChart C t)
  have heq : (isAffineOpen_graphChart C t).primeIdealOf
        ⟨Over.graphPoint C t, graphPoint_mem_graphChart C t⟩
      = (isAffineOpen_graphChart C t).primeIdealOf ⟨z, hz⟩ :=
    PrimeSpectrum.ext (hmax.eq_of_le
      ((isAffineOpen_graphChart C t).primeIdealOf ⟨z, hz⟩).isPrime.ne_top hle)
  have hpt := congrArg (isAffineOpen_graphChart C t).fromSpec.base heq
  rw [(isAffineOpen_graphChart C t).fromSpec_primeIdealOf,
    (isAffineOpen_graphChart C t).fromSpec_primeIdealOf] at hpt
  exact hzx hpt.symm

/-! ## The trivializing elements of the graph presentation -/

/-- **Away from the graph point the trivializing element is `1`**: the graph lift misses the
diagonal there (`mem_range_diagonal_graphLift_iff`), so the pulled equation is the constant
`1` (`diagonalEqn_of_notMem`). -/
lemma presentationElem_graphLocalEquations_of_ne {x : (C ⊗ overSpec k K).left}
    (hx : x ≠ Over.graphPoint C t) :
    (Over.graphLocalEquations C t).presentation.elem x = 1 := by
  have hnot : (lift (fst C (overSpec k K)) (snd C (overSpec k K) ≫ t)).left.base x
      ∉ Set.range (Over.diagonal C).left.base := fun h =>
    hx ((Over.mem_range_diagonal_graphLift_iff t).mp h)
  have h1 : (Over.graphLocalEquations C t).eqn x = 1 := by
    rw [show (Over.graphLocalEquations C t).eqn x
        = Scheme.LocalEquations.pullbackEqn
            (lift (fst C (overSpec k K)) (snd C (overSpec k K) ≫ t)).left
            (Over.diagonalLocalEquations C) x from rfl,
      Scheme.LocalEquations.pullbackEqn]
    change ((lift (fst C (overSpec k K)) (snd C (overSpec k K) ≫ t)).left.appLE
        _ _ _).hom (Over.diagonalEqn (Over.diagonalChartData C) _) = 1
    rw [Over.diagonalEqn_of_notMem (Over.diagonalChartData C) hnot, map_one]
  refine Units.ext ?_
  rw [Scheme.LocalEquations.presentation_elem_val, h1, map_one, Units.val_one]

/-- **The overlap identity at the graph point** (the KEY identity of G-D8, section level):
the rational function trivializing the graph divisor at the graph point — the germ at `η`
of the pulled diagonal equation — is the germ at `η` of the transported point generator
`graphChartEqn`.  Both restrict, on the overlap of the pullback member with the product
chart `𝔚(U, ⊤)`, to `fst^♯ u − (snd ≫ t)^♯ u` (the lift-app rule
`Over.appLE_productChartSections_sub` on each side). -/
theorem presentationElem_graphLocalEquations_val :
    ((Over.graphLocalEquations C t).presentation.elem (Over.graphPoint C t) :
        (C ⊗ overSpec k K).left.functionField)
      = ((C ⊗ overSpec k K).left.presheaf.germ (graphChart C t)
            (genericPoint (C ⊗ overSpec k K).left)
            (Scheme.genericPoint_mem_of_nonempty
              ⟨Over.graphPoint C t, graphPoint_mem_graphChart C t⟩)).hom
          (graphChartEqn C t) := by
  classical
  set data := Over.diagonalChartData C with hdata
  set q := lift (fst C (overSpec k K)) (snd C (overSpec k K) ≫ t) with hq
  set E₀ := Over.diagonalLocalEquations C with hE₀
  set x_t := Over.graphPoint C t with hxt
  have ha : q ≫ fst C C = fst C (overSpec k K) := lift_fst _ _
  have hb : q ≫ snd C C = snd C (overSpec k K) ≫ t := lift_snd _ _
  have hqx : q.left.base x_t ∈ Set.range (Over.diagonal C).left.base :=
    (Over.mem_range_diagonal_graphLift_iff t).mpr rfl
  have h1 : q.left ≫ (fst C C).left = (fst C (overSpec k K)).left := by
    rw [← Over.comp_left, ha]
  have hp0 : (fst C C).left.base (q.left.base x_t) = t.left.base default := by
    calc (fst C C).left.base (q.left.base x_t)
        = (q.left ≫ (fst C C).left).base x_t := rfl
      _ = (fst C (overSpec k K)).left.base x_t := by rw [h1]
      _ = t.left.base default := Over.fst_graphPoint t
  -- the master overlap identity, at a generalized image point
  have key : ∀ (p : C.left), (fst C C).left.base (q.left.base x_t) = p →
      ∀ hmem : (⊤ : (overSpec k K).left.Opens) ≤ t.left ⁻¹ᵁ data.chart p,
      letI := data.coordAlgebra p
      ((C ⊗ overSpec k K).left.presheaf.map (homOfLE (inf_le_left :
            (E₀.cover.pullback q.left).opens x_t
                ⊓ Over.productChart C (overSpec k K) (data.chart p) ⊤
              ≤ (E₀.cover.pullback q.left).opens x_t)).op).hom
          (Scheme.LocalEquations.pullbackEqn q.left E₀ x_t)
        = ((C ⊗ overSpec k K).left.presheaf.map (homOfLE (inf_le_right :
              (E₀.cover.pullback q.left).opens x_t
                  ⊓ Over.productChart C (overSpec k K) (data.chart p) ⊤
                ≤ Over.productChart C (overSpec k K) (data.chart p) ⊤)).op).hom
            (Over.productChartSections C (overSpec k K) (data.isAffineOpen p)
              (isAffineOpen_top_overSpec k K)
              (AlgebraicJacobian.Diagonal.coord k Γ(C.left, data.chart p) ⊗ₜ[k] 1
                - 1 ⊗ₜ[k] (t.left.appLE (data.chart p) ⊤ hmem).hom
                    (AlgebraicJacobian.Diagonal.coord k Γ(C.left, data.chart p)))) := by
    rintro p rfl hmem
    letI := data.coordAlgebra ((fst C C).left.base (q.left.base x_t))
    haveI := data.isScalarTower ((fst C C).left.base (q.left.base x_t))
    have hcov : E₀.cover.opens (q.left.base x_t)
        = Over.diagonalChart C
            (data.isAffineOpen ((fst C C).left.base (q.left.base x_t)))
            (data.elift ((fst C C).left.base (q.left.base x_t))) :=
      Over.diagonalCover_opens_of_mem data hqx
    have hle𝔠 : Over.diagonalChart C
          (data.isAffineOpen ((fst C C).left.base (q.left.base x_t)))
          (data.elift ((fst C C).left.base (q.left.base x_t)))
        ≤ Over.productChart C C (data.chart ((fst C C).left.base (q.left.base x_t)))
            (data.chart ((fst C C).left.base (q.left.base x_t))) :=
      Over.diagonalChart_le_productChart C _ _
    have hoYd : (E₀.cover.pullback q.left).opens x_t
        = q.left ⁻¹ᵁ Over.diagonalChart C
            (data.isAffineOpen ((fst C C).left.base (q.left.base x_t)))
            (data.elift ((fst C C).left.base (q.left.base x_t))) := by
      rw [Scheme.PointedCover.pullback_opens, hcov]
    set W := (E₀.cover.pullback q.left).opens x_t
        ⊓ Over.productChart C (overSpec k K)
            (data.chart ((fst C C).left.base (q.left.base x_t))) ⊤ with hWdef
    have hW_opensY : W ≤ (E₀.cover.pullback q.left).opens x_t := inf_le_left
    have hW𝔓 : W ≤ Over.productChart C (overSpec k K)
        (data.chart ((fst C C).left.base (q.left.base x_t))) ⊤ := inf_le_right
    have hW𝔠 : W ≤ q.left ⁻¹ᵁ Over.productChart C C
        (data.chart ((fst C C).left.base (q.left.base x_t)))
        (data.chart ((fst C C).left.base (q.left.base x_t))) :=
      (hW_opensY.trans hoYd.le).trans (q.left.preimage_mono hle𝔠)
    have hWa : W ≤ (fst C (overSpec k K)).left ⁻¹ᵁ
        data.chart ((fst C C).left.base (q.left.base x_t)) :=
      hW𝔓.trans (Over.productChart_le_fst_preimage C (overSpec k K) _ _)
    have hoY_snd : (E₀.cover.pullback q.left).opens x_t
        ≤ (snd C (overSpec k K) ≫ t).left ⁻¹ᵁ
            data.chart ((fst C C).left.base (q.left.base x_t)) := by
      rw [hoYd]
      exact (q.left.preimage_mono hle𝔠).trans (Over.preimage_productChart_le_snd hb _ _)
    have hWb : W ≤ (snd C (overSpec k K) ≫ t).left ⁻¹ᵁ
        data.chart ((fst C C).left.base (q.left.base x_t)) :=
      hW_opensY.trans hoY_snd
    have hWb' : W ≤ (snd C (overSpec k K)).left ⁻¹ᵁ (⊤ : (overSpec k K).left.Opens) := by
      intro z _; trivial
    -- the diagonal equation as a restriction of the transported diagonal generator
    have hchart : data.chartEqn ((fst C C).left.base (q.left.base x_t))
        = ((C ⊗ C).left.presheaf.map (homOfLE hle𝔠).op).hom
            (Over.productChartSections C C
              (data.isAffineOpen ((fst C C).left.base (q.left.base x_t)))
              (data.isAffineOpen ((fst C C).left.base (q.left.base x_t)))
              (AlgebraicJacobian.Diagonal.diagGen (k := k)
                (B := Γ(C.left, data.chart ((fst C C).left.base (q.left.base x_t)))))) :=
      Over.diagonalChartEqn_def C _ _
    have hdeqn : Over.diagonalEqn data (q.left.base x_t)
        = ((C ⊗ C).left.presheaf.map (homOfLE hcov.le).op).hom
            (data.chartEqn ((fst C C).left.base (q.left.base x_t))) := by
      rw [Over.diagonalEqn, dif_pos hqx]
      rfl
    have hEeqn : E₀.eqn (q.left.base x_t)
        = ((C ⊗ C).left.presheaf.map (homOfLE (hcov.le.trans hle𝔠)).op).hom
            (Over.productChartSections C C
              (data.isAffineOpen ((fst C C).left.base (q.left.base x_t)))
              (data.isAffineOpen ((fst C C).left.base (q.left.base x_t)))
              (AlgebraicJacobian.Diagonal.diagGen (k := k)
                (B := Γ(C.left, data.chart ((fst C C).left.base (q.left.base x_t)))))) := by
      rw [show E₀.eqn (q.left.base x_t) = Over.diagonalEqn data (q.left.base x_t) from rfl,
        hdeqn, hchart, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
    -- both sides restrict to `fst^♯ u − (snd ≫ t)^♯ u`
    have hLHS : ((C ⊗ overSpec k K).left.presheaf.map (homOfLE hW_opensY).op).hom
          (Scheme.LocalEquations.pullbackEqn q.left E₀ x_t)
        = (fst C (overSpec k K)).left.appLE
            (data.chart ((fst C C).left.base (q.left.base x_t))) W hWa
            (AlgebraicJacobian.Diagonal.coord k
              Γ(C.left, data.chart ((fst C C).left.base (q.left.base x_t))))
          - (snd C (overSpec k K) ≫ t).left.appLE
            (data.chart ((fst C C).left.base (q.left.base x_t))) W hWb
            (AlgebraicJacobian.Diagonal.coord k
              Γ(C.left, data.chart ((fst C C).left.base (q.left.base x_t)))) := by
      rw [Scheme.LocalEquations.pullbackEqn_res q.left E₀ x_t hW_opensY, hEeqn,
        ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, AlgebraicJacobian.Diagonal.diagGen,
        Over.appLE_productChartSections_sub _ _ ha hb hW𝔠 hWa hWb _ _]
    have hRHS : ((C ⊗ overSpec k K).left.presheaf.map (homOfLE hW𝔓).op).hom
          (Over.productChartSections C (overSpec k K)
            (data.isAffineOpen ((fst C C).left.base (q.left.base x_t)))
            (isAffineOpen_top_overSpec k K)
            (AlgebraicJacobian.Diagonal.coord k
                Γ(C.left, data.chart ((fst C C).left.base (q.left.base x_t))) ⊗ₜ[k] 1
              - 1 ⊗ₜ[k] (t.left.appLE
                  (data.chart ((fst C C).left.base (q.left.base x_t))) ⊤ hmem).hom
                  (AlgebraicJacobian.Diagonal.coord k
                    Γ(C.left, data.chart ((fst C C).left.base (q.left.base x_t))))))
        = (fst C (overSpec k K)).left.appLE
            (data.chart ((fst C C).left.base (q.left.base x_t))) W hWa
            (AlgebraicJacobian.Diagonal.coord k
              Γ(C.left, data.chart ((fst C C).left.base (q.left.base x_t))))
          - (snd C (overSpec k K)).left.appLE ⊤ W hWb'
            ((t.left.appLE (data.chart ((fst C C).left.base (q.left.base x_t))) ⊤ hmem).hom
              (AlgebraicJacobian.Diagonal.coord k
                Γ(C.left, data.chart ((fst C C).left.base (q.left.base x_t))))) := by
      rw [map_sub, map_sub, Over.productChartSections_tmul_one,
        Over.productChartSections_one_tmul, ← CommRingCat.comp_apply,
        ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
    have hsnd : ((snd C (overSpec k K)).left.appLE ⊤ W hWb').hom
          ((t.left.appLE (data.chart ((fst C C).left.base (q.left.base x_t))) ⊤ hmem).hom
            (AlgebraicJacobian.Diagonal.coord k
              Γ(C.left, data.chart ((fst C C).left.base (q.left.base x_t)))))
        = ((snd C (overSpec k K) ≫ t).left.appLE
            (data.chart ((fst C C).left.base (q.left.base x_t))) W hWb).hom
            (AlgebraicJacobian.Diagonal.coord k
              Γ(C.left, data.chart ((fst C C).left.base (q.left.base x_t)))) := by
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      rfl
    rw [hLHS, hRHS, hsnd]
  -- instantiate at the image point of `t`
  have hkey : ((C ⊗ overSpec k K).left.presheaf.map (homOfLE (inf_le_left :
        (E₀.cover.pullback q.left).opens x_t
            ⊓ Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤
          ≤ (E₀.cover.pullback q.left).opens x_t)).op).hom
        (Scheme.LocalEquations.pullbackEqn q.left E₀ x_t)
      = ((C ⊗ overSpec k K).left.presheaf.map (homOfLE (inf_le_right :
            (E₀.cover.pullback q.left).opens x_t
                ⊓ Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤
              ≤ Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤)).op).hom
          (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
            (isAffineOpen_top_overSpec k K) (graphGen C t)) :=
    key (t.left.base default) hp0 (top_le_preimage_graphBaseChart C t)
  -- push both sides into the function field at `η`
  have hx_tW : x_t ∈ (E₀.cover.pullback q.left).opens x_t
      ⊓ Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤ :=
    ⟨(E₀.cover.pullback q.left).mem_opens x_t, graphPoint_mem_productChart C t⟩
  have hηW : genericPoint (C ⊗ overSpec k K).left
      ∈ (E₀.cover.pullback q.left).opens x_t
        ⊓ Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤ :=
    Scheme.genericPoint_mem_of_nonempty ⟨x_t, hx_tW⟩
  have e1 := (C ⊗ overSpec k K).left.presheaf.germ_res_apply
    (homOfLE (inf_le_left : (E₀.cover.pullback q.left).opens x_t
        ⊓ Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤
      ≤ (E₀.cover.pullback q.left).opens x_t))
    (genericPoint (C ⊗ overSpec k K).left) hηW
    (Scheme.LocalEquations.pullbackEqn q.left E₀ x_t)
  have e2 := (C ⊗ overSpec k K).left.presheaf.germ_res_apply
    (homOfLE (inf_le_right : (E₀.cover.pullback q.left).opens x_t
        ⊓ Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤
      ≤ Over.productChart C (overSpec k K) (graphBaseChart C t) ⊤))
    (genericPoint (C ⊗ overSpec k K).left) hηW
    (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
      (isAffineOpen_top_overSpec k K) (graphGen C t))
  have e3 := (C ⊗ overSpec k K).left.presheaf.germ_res_apply
    (homOfLE (graphChart_le_productChart C t))
    (genericPoint (C ⊗ overSpec k K).left)
    (Scheme.genericPoint_mem_of_nonempty
      ⟨Over.graphPoint C t, graphPoint_mem_graphChart C t⟩)
    (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
      (isAffineOpen_top_overSpec k K) (graphGen C t))
  have h0 : ((Over.graphLocalEquations C t).presentation.elem (Over.graphPoint C t) :
        (C ⊗ overSpec k K).left.functionField)
      = ((C ⊗ overSpec k K).left.presheaf.germ
            ((E₀.cover.pullback q.left).opens x_t)
            (genericPoint (C ⊗ overSpec k K).left)
            ((E₀.cover.pullback q.left).genericPoint_mem_opens x_t)).hom
          (Scheme.LocalEquations.pullbackEqn q.left E₀ x_t) := rfl
  rw [h0,
    show graphChartEqn C t = ((C ⊗ overSpec k K).left.presheaf.map
        (homOfLE (graphChart_le_productChart C t)).op).hom
      (Over.productChartSections C (overSpec k K) (isAffineOpen_graphBaseChart C t)
        (isAffineOpen_top_overSpec k K) (graphGen C t)) from rfl,
    e3, ← e1, hkey, e2]

/-! ## The presentation divisor of the graph -/

/-- **The presentation divisor of the graph is a one-point divisor** at the graph point. -/
theorem presentationDivisor_graphLocalEquations :
    Scheme.presentationDivisor K (Over.graphLocalEquations C t).presentation
      = Scheme.CurveDivisor.single (graphPoint_ne_genericPoint C t)
          (Multiplicative.toAdd
            (Scheme.ordZ ((C ⊗ overSpec k K).left ↘ Spec (CommRingCat.of K))
              (graphPoint_ne_genericPoint C t)
              ((Over.graphLocalEquations C t).presentation.elem (Over.graphPoint C t)))) := by
  refine Scheme.CurveDivisor.ext_coeffAt (fun x hxg => ?_)
  rw [Scheme.coeffAt_presentationDivisor]
  by_cases hxx : x = Over.graphPoint C t
  · subst hxx
    exact (Scheme.CurveDivisor.coeffAt_single_self hxg _).symm
  · rw [presentationElem_graphLocalEquations_of_ne C t hxx, map_one, toAdd_one,
      Scheme.CurveDivisor.coeffAt_single_of_ne (graphPoint_ne_genericPoint C t) hxg hxx]

/-! ## The keystone: the graph class has degree one -/

/-- **THE degree-1 certificate** (G-D8 keystone): the Picard class of the graph divisor of a
`K`-point has degree exactly one.  The presentation divisor is `ord_{x_t}(g) · x_t`
(`presentationDivisor_graphLocalEquations`), and the SB-3b chart colength dictionary on the
graph chart reads `ord_{x_t}(g) · [κ(x_t) : K] = dim_K Γ ⧸ (graphChartEqn) = 1` — the
multiplicity–residue product collapses in one shot through the evaluation at the graph
section. -/
theorem classDeg_graphPicClass : classDeg K (Over.graphPicClass C t) = 1 := by
  classical
  have hx := graphPoint_ne_genericPoint C t
  have hη : genericPoint (C ⊗ overSpec k K).left ∈ graphChart C t :=
    Scheme.genericPoint_mem_of_nonempty
      ⟨Over.graphPoint C t, graphPoint_mem_graphChart C t⟩
  -- the class of the graph is the class of its presentation divisor
  have h1 : Over.graphPicClass C t
      = Scheme.CurveDivisor.picClass K
          (Scheme.presentationDivisor K (Over.graphLocalEquations C t).presentation) := by
    rw [Scheme.CurveDivisor.picClass_presentationDivisor K,
      Scheme.LocalEquations.presentation_picClass]
    rfl
  rw [h1, classDeg_picClass, presentationDivisor_graphLocalEquations,
    Scheme.CurveDivisor.deg_single']
  -- the chart colength dictionary on the graph chart
  have hval : (((Over.graphLocalEquations C t).presentation.elem (Over.graphPoint C t) :
        (C ⊗ overSpec k K).left.functionFieldˣ) :
        (C ⊗ overSpec k K).left.functionField)
      = ((C ⊗ overSpec k K).left.presheaf.germ (graphChart C t)
          (genericPoint (C ⊗ overSpec k K).left) hη).hom (graphChartEqn C t) :=
    presentationElem_graphLocalEquations_val C t
  have hdict := finrank_quotient_span_section K (isAffineOpen_graphChart C t) hη
    ((Over.graphLocalEquations C t).presentation.elem (Over.graphPoint C t)) hval
    ({⟨Over.graphPoint C t, hx⟩} :
      Finset {x : (C ⊗ overSpec k K).left // x ≠ genericPoint (C ⊗ overSpec k K).left})
    (fun p hp => by
      rw [Finset.mem_singleton.mp hp]
      exact graphPoint_mem_graphChart C t)
    (fun z hzc hzg hznot =>
      isUnit_germ_graphChartEqn_of_ne C t hzc (fun he => hznot (by
        rw [Finset.mem_singleton]
        exact Subtype.ext he)))
  rw [Finset.sum_singleton, finrank_quotient_span_graphChartEqn C t] at hdict
  exact_mod_cast hdict.symm

end AlgebraicGeometry
