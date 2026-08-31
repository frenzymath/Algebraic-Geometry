/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.DiagonalEquations
import AlgebraicJacobian.Picard.LocalEquationsPullback
import AlgebraicJacobian.Picard.Rigidification

/-!
# The graph of a curve point as an effective divisor (deg-D4c)

The final assembly of the graph-divisor campaign (`informal/deg-d4-recon.md` §4 step 3,
`informal/deg-d4b-worksheet.md` §D6).  For a curve `C` smooth of relative dimension one and
separated over `Spec k`, a test object `T` and a point `t : T ⟶ C` (a morphism in
`Over (Spec k)`), the **graph** `Γ_t ⊆ (C ⊗ T).left` is realized as the pullback of the
diagonal divisor `Δ ⊆ (C ⊗ C).left` (`Over.diagonalLocalEquations`,
`Curve/DiagonalEquations.lean`) along the lift `lift (fst C T) (snd C T ≫ t) : C ⊗ T ⟶ C ⊗ C`.

The pullback is the landed `Scheme.LocalEquations.pullback` (`Picard/LocalEquationsPullback.lean`),
which takes the regularity of the pulled-back equations as an explicit hypothesis `hreg`.
Discharging `hreg` is the brick's real content: on the pullback cover the pulled diagonal
equation is, on a suitable affine product chart, a restriction of `u ⊗ 1 − 1 ⊗ t^♯u`
(via the two-factor lift-app rule `Over.appLE_productChartSections_sub`,
`Curve/ProductCharts.lean`), which is a nonzerodivisor by the B1 regularity engine
`AlgebraicJacobian.Diagonal.tmul_one_sub_one_tmul_mem_nonZeroDivisors` (uniform in the second
factor — no integrality of `C ⊗ T` is used); the germ form follows from
`AlgebraicGeometry.IsAffineOpen.germ_mem_nonZeroDivisors` (`Curve/DiagonalChart.lean`).

## Main declarations

* `AlgebraicGeometry.Over.graph_pullback_regular` — the `hreg` discharge: the pulled-back
  diagonal equation is germ-regular at every point of the pullback cover.
* `AlgebraicGeometry.Over.graphLocalEquations` — the graph `Γ_t` as a
  `(C ⊗ T).left.LocalEquations`.
* `AlgebraicGeometry.Over.graphPicClass` — its Picard class `𝒪(Γ_t)`.
* `AlgebraicGeometry.Over.whiskerLeft_comp_graphLift` — the base-change whisker square:
  `(C ◁ g) ≫ (graph lift of t) = graph lift of (g ≫ t)`.
* `AlgebraicGeometry.Over.graphLocalEquations_base_change` — the class of `Γ_{g ≫ t}` is the
  pullback of the class of `Γ_t` along `C ◁ g`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace
open scoped TensorProduct nonZeroDivisors

namespace AlgebraicGeometry

namespace Over

-- The `k`-algebra structure on sections of objects over `Spec k`
-- (`Cohomology/SectionsBaseChange.lean`); reactivated as the landed diagonal files mandate.
attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k] {C T : Over (Spec (.of k))}

/-! ## The base-change whisker square -/

variable (C) in
/-- **The graph-lift whisker square** (base-change geometry): whiskering the graph lift of a
point `t : T ⟶ C` by `C ◁ g` is the graph lift of the restricted point `g ≫ t`.  Proved by
the cartesian-product universal property (`hom_ext`), the exemplar being
`Over.sectionOfPoint_naturality` (`Picard/Rigidification.lean`). -/
lemma whiskerLeft_comp_graphLift {T' : Over (Spec (.of k))} (g : T' ⟶ T) (t : T ⟶ C) :
    (C ◁ g) ≫ lift (fst C T) (snd C T ≫ t)
      = lift (fst C T') (snd C T' ≫ g ≫ t) := by
  refine hom_ext _ _ ?_ ?_
  · rw [Category.assoc, lift_fst, whiskerLeft_fst, lift_fst]
  · rw [Category.assoc, lift_snd, ← Category.assoc, whiskerLeft_snd, Category.assoc, lift_snd]

/-! ## The regularity discharge (the brick's real content) -/

/-- **The `hreg` discharge for the graph pullback**: for the diagonal divisor cut out by chart
data `data` and a point `t : T ⟶ C`, the pullback of the diagonal equation along
`lift (fst C T) (snd C T ≫ t)` is germ-regular at every point of the pullback cover.

Off the diagonal the equation is `1`, whose germ is a unit.  On the diagonal, the pulled-back
equation restricts, on an affine product chart `𝔚(U, V)` through the point (with `U` the chart
of the first projection and `V` an affine of `T.left`), to
`productChartSections (u ⊗ 1 − 1 ⊗ t^♯u)` (the lift-app rule
`Over.appLE_productChartSections_sub` with the projection identities of `lift`); the tensor is a
nonzerodivisor by the B1 engine
`AlgebraicJacobian.Diagonal.tmul_one_sub_one_tmul_mem_nonZeroDivisors`, and the germ follows from
`IsAffineOpen.germ_mem_nonZeroDivisors` on the affine chart, matched to the pullback germ through
`germ_res_apply` on the overlap. -/
theorem graph_pullback_regular (data : DiagonalChartData C) [IsSeparated C.hom] (t : T ⟶ C)
    (y z : (C ⊗ T).left)
    (hz : z ∈ ((diagonalLocalEquationsOfData data).cover.pullback
        (lift (fst C T) (snd C T ≫ t)).left).opens y) :
    ((C ⊗ T).left.presheaf.germ _ z hz).hom
        (Scheme.LocalEquations.pullbackEqn (lift (fst C T) (snd C T ≫ t)).left
          (diagonalLocalEquationsOfData data) y)
      ∈ ((C ⊗ T).left.presheaf.stalk z)⁰ := by
  set q := lift (fst C T) (snd C T ≫ t) with hq
  set E := diagonalLocalEquationsOfData data with hE
  set opensY := (E.cover.pullback q.left).opens y with hopensY
  have ha : q ≫ fst C C = fst C T := by rw [hq]; exact lift_fst _ _
  have hb : q ≫ snd C C = snd C T ≫ t := by rw [hq]; exact lift_snd _ _
  by_cases hp : q.left.base y ∈ Set.range (diagonal C).left.base
  · -- On the diagonal: the real content.
    set p₀ := (fst C C).left.base (q.left.base y) with hp0
    -- the chart of the first projection and its étale-coordinate package
    letI := data.coordAlgebra p₀
    haveI := data.isScalarTower p₀
    haveI := data.etale p₀
    have hcov : E.cover.opens (q.left.base y)
        = diagonalChart C (data.isAffineOpen p₀) (data.elift p₀) :=
      diagonalCover_opens_of_mem data hp
    have hle𝔠 : diagonalChart C (data.isAffineOpen p₀) (data.elift p₀)
        ≤ productChart C C (data.chart p₀) (data.chart p₀) :=
      diagonalChart_le_productChart C (data.isAffineOpen p₀) (data.elift p₀)
    -- opensY is the `q`-preimage of the diagonal member
    have hoYd : opensY = q.left ⁻¹ᵁ diagonalChart C (data.isAffineOpen p₀) (data.elift p₀) := by
      rw [hopensY, Scheme.PointedCover.pullback_opens, hcov]
    -- the two projection-preimage bounds
    have hoY_fst : opensY ≤ (fst C T).left ⁻¹ᵁ data.chart p₀ := by
      rw [hoYd]
      exact (q.left.preimage_mono hle𝔠).trans (preimage_productChart_le_fst ha _ _)
    have hoY_snd : opensY ≤ (snd C T ≫ t).left ⁻¹ᵁ data.chart p₀ := by
      rw [hoYd]
      exact (q.left.preimage_mono hle𝔠).trans (preimage_productChart_le_snd hb _ _)
    -- membership of `z` in the two preimages
    have hz_fst : (fst C T).left.base z ∈ data.chart p₀ := hoY_fst hz
    have hz_sndt : t.left.base ((snd C T).left.base z) ∈ data.chart p₀ := hoY_snd hz
    -- choose an affine `V ∋ (snd C T) z` inside `t ⁻¹ᵁ U`
    obtain ⟨V, hV, hzV, hVsub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := T.left) (x := (snd C T).left.base z)
        (U := t.left ⁻¹ᵁ data.chart p₀) hz_sndt
    have hVt : V ≤ t.left ⁻¹ᵁ data.chart p₀ := hVsub
    -- the affine product chart of the source through `z`
    set 𝔓 := productChart C T (data.chart p₀) V with h𝔓
    have hz𝔓 : z ∈ 𝔓 := (mem_productChart C T).mpr ⟨hz_fst, hzV⟩
    -- the pulled coordinate `b := t^♯ u ∈ Γ(T.left, V)` and the source tensor
    set b : Γ(T.left, V) :=
      (t.left.appLE (data.chart p₀) V hVt).hom
        (AlgebraicJacobian.Diagonal.coord k Γ(C.left, data.chart p₀)) with hbdef
    set τ : Γ(C.left, data.chart p₀) ⊗[k] Γ(T.left, V) :=
      AlgebraicJacobian.Diagonal.coord k Γ(C.left, data.chart p₀) ⊗ₜ[k] (1 : Γ(T.left, V))
        - (1 : Γ(C.left, data.chart p₀)) ⊗ₜ[k] b with hτdef
    -- the overlap `W`, containing `z`, refining both `opensY` and `𝔓`
    set W := opensY ⊓ 𝔓 with hW
    have hW_opensY : W ≤ opensY := inf_le_left
    have hW𝔓 : W ≤ 𝔓 := inf_le_right
    have hzW : z ∈ W := ⟨hz, hz𝔓⟩
    -- the component bounds on `W`
    have hWa : W ≤ (fst C T).left ⁻¹ᵁ data.chart p₀ := hW𝔓.trans inf_le_left
    have hWb : W ≤ (snd C T ≫ t).left ⁻¹ᵁ data.chart p₀ := hW_opensY.trans hoY_snd
    have hWb' : W ≤ (snd C T).left ⁻¹ᵁ V := hW𝔓.trans inf_le_right
    have hW𝔠 : W ≤ q.left ⁻¹ᵁ productChart C C (data.chart p₀) (data.chart p₀) :=
      (hW_opensY.trans hoYd.le).trans (q.left.preimage_mono hle𝔠)
    -- the diagonal equation as a restriction of the transported diagonal generator
    have hchart : data.chartEqn p₀
        = ((C ⊗ C).left.presheaf.map (homOfLE hle𝔠).op).hom
            (productChartSections C C (data.isAffineOpen p₀) (data.isAffineOpen p₀)
              (AlgebraicJacobian.Diagonal.diagGen (k := k) (B := Γ(C.left, data.chart p₀)))) :=
      diagonalChartEqn_def C (data.isAffineOpen p₀) (data.elift p₀)
    have hdeqn : diagonalEqn data (q.left.base y)
        = ((C ⊗ C).left.presheaf.map (homOfLE hcov.le).op).hom (data.chartEqn p₀) := by
      rw [diagonalEqn, dif_pos hp]; rfl
    have hEeqn : E.eqn (q.left.base y)
        = ((C ⊗ C).left.presheaf.map (homOfLE (hcov.le.trans hle𝔠)).op).hom
            (productChartSections C C (data.isAffineOpen p₀) (data.isAffineOpen p₀)
              (AlgebraicJacobian.Diagonal.diagGen (k := k) (B := Γ(C.left, data.chart p₀)))) := by
      rw [show E.eqn (q.left.base y) = diagonalEqn data (q.left.base y) from rfl, hdeqn, hchart,
        ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]; rfl
    -- the `snd`-component identity for `t^♯ u`
    have hsnd_eq : ((snd C T).left.appLE V W hWb').hom b
        = ((snd C T ≫ t).left.appLE (data.chart p₀) W hWb).hom
            (AlgebraicJacobian.Diagonal.coord k Γ(C.left, data.chart p₀)) := by
      rw [hbdef, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]; rfl
    -- KEY: `res_W (pulled equation) = res_W (productChartSections τ)`
    have hKEY : ((C ⊗ T).left.presheaf.map (homOfLE hW_opensY).op).hom
          (Scheme.LocalEquations.pullbackEqn q.left E y)
        = ((C ⊗ T).left.presheaf.map (homOfLE hW𝔓).op).hom
            (productChartSections C T (data.isAffineOpen p₀) hV τ) := by
      have hLHS : ((C ⊗ T).left.presheaf.map (homOfLE hW_opensY).op).hom
            (Scheme.LocalEquations.pullbackEqn q.left E y)
          = (fst C T).left.appLE (data.chart p₀) W hWa
              (AlgebraicJacobian.Diagonal.coord k Γ(C.left, data.chart p₀))
            - (snd C T ≫ t).left.appLE (data.chart p₀) W hWb
              (AlgebraicJacobian.Diagonal.coord k Γ(C.left, data.chart p₀)) := by
        rw [Scheme.LocalEquations.pullbackEqn_res q.left E y hW_opensY, hEeqn,
          ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, AlgebraicJacobian.Diagonal.diagGen,
          appLE_productChartSections_sub _ _ ha hb hW𝔠 hWa hWb _ _]
      have hRHS : ((C ⊗ T).left.presheaf.map (homOfLE hW𝔓).op).hom
            (productChartSections C T (data.isAffineOpen p₀) hV τ)
          = (fst C T).left.appLE (data.chart p₀) W hWa
              (AlgebraicJacobian.Diagonal.coord k Γ(C.left, data.chart p₀))
            - (snd C T).left.appLE V W hWb' b := by
        rw [hτdef, map_sub, map_sub, productChartSections_tmul_one, productChartSections_one_tmul,
          ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
          Scheme.Hom.appLE_map]
      rw [hLHS, hRHS, hsnd_eq]
    -- the source tensor is a nonzerodivisor (B1 engine), hence so is its image and its germ
    have hτ : τ ∈ (Γ(C.left, data.chart p₀) ⊗[k] Γ(T.left, V))⁰ := by
      rw [hτdef]
      exact AlgebraicJacobian.Diagonal.tmul_one_sub_one_tmul_mem_nonZeroDivisors b
    have hτ' : productChartSections C T (data.isAffineOpen p₀) hV τ
        ∈ Γ((C ⊗ T).left, 𝔓)⁰ := by
      have hflat : ((productChartSections C T (data.isAffineOpen p₀) hV).toRingHom :
          _ →+* _).Flat :=
        RingHom.Flat.of_bijective (productChartSections C T (data.isAffineOpen p₀) hV).bijective
      exact RingHom.Flat.mem_nonZeroDivisors hflat hτ
    -- transport the germ across the overlap
    have hgerm : ((C ⊗ T).left.presheaf.germ opensY z hz).hom
          (Scheme.LocalEquations.pullbackEqn q.left E y)
        = ((C ⊗ T).left.presheaf.germ 𝔓 z hz𝔓).hom
            (productChartSections C T (data.isAffineOpen p₀) hV τ) := by
      have e1 := (C ⊗ T).left.presheaf.germ_res_apply (homOfLE hW_opensY) z hzW
        (Scheme.LocalEquations.pullbackEqn q.left E y)
      have e2 := (C ⊗ T).left.presheaf.germ_res_apply (homOfLE hW𝔓) z hzW
        (productChartSections C T (data.isAffineOpen p₀) hV τ)
      rw [← e1, ← e2, hKEY]
    rw [hgerm]
    exact (isAffineOpen_productChart C T (data.isAffineOpen p₀) hV).germ_mem_nonZeroDivisors hτ'
      hz𝔓
  · -- Off the diagonal: the pulled equation is `1`.
    have h1 : Scheme.LocalEquations.pullbackEqn q.left E y = 1 := by
      rw [Scheme.LocalEquations.pullbackEqn]
      change (q.left.appLE _ _ _).hom (diagonalEqn data (q.left.base y)) = 1
      rw [diagonalEqn_of_notMem data hp, map_one]
    rw [h1, map_one]
    exact one_mem _

/-! ## The graph divisor and its Picard class -/

variable (C) in
/-- **The graph of a curve point as an effective divisor in local equations** (deg-D4c): for `C`
smooth of relative dimension one and separated over `Spec k`, a test object `T` and a point
`t : T ⟶ C`, the graph `Γ_t ⊆ (C ⊗ T).left` presented by `Scheme.LocalEquations` as the pullback
of the diagonal divisor along `lift (fst C T) (snd C T ≫ t)`. -/
noncomputable def graphLocalEquations [SmoothOfRelativeDimension 1 C.hom] [IsSeparated C.hom]
    (t : T ⟶ C) : (C ⊗ T).left.LocalEquations :=
  (diagonalLocalEquations C).pullback (lift (fst C T) (snd C T ≫ t)).left
    (graph_pullback_regular (diagonalChartData C) t)

variable (C) in
/-- **The Picard class of the graph divisor** `𝒪(Γ_t)`.  What the downstream `abelElement`
(G-D8) consumes: on `T = C`, `graphPicClass C (𝟙 C)` and `graphPicClass C` of a general point,
with the base-change law `graphLocalEquations_base_change`. -/
noncomputable def graphPicClass [SmoothOfRelativeDimension 1 C.hom] [IsSeparated C.hom]
    (t : T ⟶ C) : (C ⊗ T).left.CechPic :=
  (graphLocalEquations C t).picClass

variable (C) in
/-- The graph Picard class is the pullback of the diagonal class `𝒪(Δ)` along the graph lift —
the unfolding through the landed `LocalEquations.picClass_pullback`. -/
lemma graphPicClass_eq [SmoothOfRelativeDimension 1 C.hom] [IsSeparated C.hom] (t : T ⟶ C) :
    graphPicClass C t
      = Scheme.CechPic.map (lift (fst C T) (snd C T ≫ t)).left (diagonalPicClass C) := by
  rw [graphPicClass, graphLocalEquations, Scheme.LocalEquations.picClass_pullback]
  rfl

variable (C) in
/-- **Base change of the graph class** (deg-D4c): the Picard class of the graph `Γ_{g ≫ t}` of
the restricted point is the pullback of the class of `Γ_t` along `C ◁ g`.  Immediate from
`graphPicClass_eq`, the contravariant functoriality `CechPic.map_comp`, and the whisker square
`whiskerLeft_comp_graphLift`. -/
theorem graphLocalEquations_base_change [SmoothOfRelativeDimension 1 C.hom] [IsSeparated C.hom]
    {T' : Over (Spec (.of k))} (g : T' ⟶ T) (t : T ⟶ C) :
    graphPicClass C (g ≫ t)
      = Scheme.CechPic.map (C ◁ g).left (graphPicClass C t) := by
  rw [graphPicClass_eq, graphPicClass_eq, ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
    ← Over.comp_left, whiskerLeft_comp_graphLift]

end Over

end AlgebraicGeometry
