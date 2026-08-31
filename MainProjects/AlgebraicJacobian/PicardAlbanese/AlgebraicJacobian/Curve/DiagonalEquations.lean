/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.DiagonalChartData
import AlgebraicJacobian.Picard.DivisorClass

/-!
# The diagonal divisor in local equations (deg-D4b, brick B5, part 2)

Assembling the deliverables of bricks B0–B4 (the diagonal member, its equation, the per-chart
kernel computation, regularity, the diag–off overlap unit) and the frozen chart choice
`Over.DiagonalChartData` (part 1) into the effective divisor of the diagonal, as a
`Scheme.LocalEquations` on the curve square `(C ⊗ C).left`, and its Picard class — the
deg-D4b headline.

## Main declarations

* `AlgebraicGeometry.Over.exists_isUnit_of_span_singleton_eq` — the *regular-generators
  mini-lemma* (worksheet D3): two generators of the same principal ideal, one of which is a
  nonzerodivisor, differ by a unit.  This is the ring core of the diag–diag ratio.
* `AlgebraicGeometry.Over.diagonalCover`, `AlgebraicGeometry.Over.diagonalEqn` — the pointed
  cover of `(C ⊗ C).left` (diagonal points get their chart's diagonal member `𝔇`, off-diagonal
  points get the complement `Δᶜ`) and its local equation (`diagonalChartEqn` on `𝔇`, the
  constant `1` on `Δᶜ`).
* `AlgebraicGeometry.Over.diagonalLocalEquations` — the diagonal as a
  `(C ⊗ C).left.LocalEquations`.
* `AlgebraicGeometry.Over.diagonalPicClass` — its Picard class `𝒪(Δ)`, the deg-D4b headline.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace
open scoped nonZeroDivisors TensorProduct

namespace AlgebraicGeometry

namespace Over

/-! ## Ring-level and sheaf-level helpers -/

/-- **The regular-generators mini-lemma** (worksheet D3): if `span {a} = span {b}` and `a` is a
nonzerodivisor, then `a` and `b` differ by a unit, `a = u * b`.  From `a ∈ span {b}` and
`b ∈ span {a}` we get `a = c * b`, `b = d * a`, hence `(1 - c * d) * a = 0`; regularity of `a`
forces `c * d = 1`, so `c` is a unit. -/
theorem exists_isUnit_of_span_singleton_eq {R : Type*} [CommRing R] {a b : R}
    (hab : Ideal.span {a} = Ideal.span {b}) (ha : a ∈ R⁰) :
    ∃ u : Rˣ, a = (u : R) * b := by
  have haS : a ∈ Ideal.span {b} := hab ▸ Ideal.subset_span rfl
  have hbS : b ∈ Ideal.span {a} := hab ▸ Ideal.subset_span rfl
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp haS
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hbS
  -- `(1 - c * d) * a = 0`, so `c * d = 1` by regularity of `a`
  have h0 : (1 - c * d) * a = 0 := by rw [sub_mul, one_mul, mul_assoc, hd, hc, sub_self]
  have h1 : 1 - c * d = 0 :=
    (mul_left_mem_nonZeroDivisors_eq_zero_iff ha).mp (by rw [mul_comm]; exact h0)
  have hcd : c * d = 1 := (sub_eq_zero.mp h1).symm
  exact ⟨⟨c, d, hcd, by rw [mul_comm]; exact hcd⟩, by rw [← hc]⟩

variable {k : Type u} [Field k]

/-- **Section regularity from germ regularity.** If the germ of a section `s` over an open `W`
is a nonzerodivisor at every point of `W`, then `s` is a nonzerodivisor in `Γ(X, W)`.  Sections
inject into the product of their germs (`section_ext`), so germwise nonzerodivisibility
propagates.  (This is the content of the landed
`Scheme.LocalEquations.eqn_restrict_mem_nonZeroDivisors`, factored standalone for the diag–diag
overlap regularity.) -/
theorem section_mem_nonZeroDivisors_of_germ {X : Scheme.{u}} {W : X.Opens} (s : Γ(X, W))
    (h : ∀ (y : X) (hy : y ∈ W),
      (X.presheaf.germ W y hy).hom s ∈ (X.presheaf.stalk y)⁰) :
    s ∈ Γ(X, W)⁰ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro t ht
  apply TopCat.Presheaf.section_ext X.sheaf W t 0
  intro y hy
  rw [map_zero]
  have key : (X.presheaf.germ W y hy).hom t * (X.presheaf.germ W y hy).hom s = 0 := by
    rw [← map_mul, ht, map_zero]
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff (h y hy)).mp (by rw [mul_comm] at key; exact key)

/-- **Units on a sub-open of a basic open.** The restriction of a section `s` to any open `W`
contained in its basic open `D(s)` is a unit.  Factor `W ≤ D(s) ≤ V` and restrict the unit
`s|D(s)` (`RingedSpace.isUnit_res_basicOpen`). -/
theorem isUnit_res_of_le_basicOpen {X : Scheme.{u}} {V W : X.Opens} (s : Γ(X, V))
    (hWV : W ≤ V) (hWb : W ≤ X.basicOpen s) :
    IsUnit ((X.presheaf.map (homOfLE hWV).op).hom s) := by
  have hsplit : homOfLE hWV = homOfLE hWb ≫ homOfLE (X.basicOpen_le s) :=
    Subsingleton.elim _ _
  rw [hsplit, op_comp, Functor.map_comp, CommRingCat.comp_apply]
  exact (X.toRingedSpace.isUnit_res_basicOpen s).map _

/-- Restriction of a section along `W ≤ V ≤ U` composes to restriction along `W ≤ U`. -/
private lemma res_comp {X : Scheme.{u}} {W V U : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s)
      = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-! ## The per-chart diagonal equation, packaged on the frozen chart data

The section `chartEqn data p` is `Curve/DiagonalChart.lean`'s `diagonalChartEqn` with the frozen
coordinate instance `data.coordAlgebra p` baked into its *definition*; its type
`Γ((C ⊗ C).left, diagonalChart ..)` mentions no algebra instance, so the downstream cover,
equation and kernel lemmas speak of `chartEqn data p` without carrying instances. -/

attribute [local instance] Over.sectionsAlgebra

namespace DiagonalChartData

variable {C : Over (Spec (.of k))} (data : DiagonalChartData C) (p : C.left)

/-- The diagonal equation on the chart at `p`, with the frozen étale coordinate. -/
noncomputable def chartEqn :
    Γ((C ⊗ C).left, diagonalChart C (data.isAffineOpen p) (data.elift p)) :=
  letI := data.coordAlgebra p
  diagonalChartEqn C (data.isAffineOpen p) (data.elift p)

/-- **The per-chart kernel presentation** (brick B4's D3 display), on the frozen data: the
kernel ideal sheaf of `δ` on the diagonal member is principal on `chartEqn`. -/
theorem ker_ideal_eq_span_chartEqn [IsSeparated C.hom] :
    ((diagonal C).left.ker).ideal
        ⟨diagonalChart C (data.isAffineOpen p) (data.elift p),
          isAffineOpen_diagonalChart C (data.isAffineOpen p) (data.elift p)⟩
      = Ideal.span {chartEqn data p} := by
  letI := data.coordAlgebra p
  haveI := data.isScalarTower p
  exact diagonal_ker_ideal_diagonalChart C (data.isAffineOpen p) (data.elift p)
    (data.isIdempotentElem_baseChange_elift p) (data.ker_lmul'_eq_span_baseChange_elift p)

/-- **Germ regularity** of the chart equation (brick B4/D2), on the frozen data. -/
theorem germ_chartEqn_mem_nonZeroDivisors {y : (C ⊗ C).left}
    (hy : y ∈ diagonalChart C (data.isAffineOpen p) (data.elift p)) :
    ((C ⊗ C).left.presheaf.germ _ y hy).hom (chartEqn data p)
      ∈ ((C ⊗ C).left.presheaf.stalk y)⁰ := by
  letI := data.coordAlgebra p
  haveI := data.isScalarTower p
  haveI := data.etale p
  exact germ_diagonalChartEqn_mem_nonZeroDivisors C (data.isAffineOpen p) (data.elift p) hy

/-- **The diag–off overlap identity** (brick B4/D4), on the frozen data. -/
theorem chartEqn_inf_diagonalComplement [IsSeparated C.hom] :
    diagonalChart C (data.isAffineOpen p) (data.elift p) ⊓ diagonalComplement C
      = (C ⊗ C).left.basicOpen (chartEqn data p) := by
  letI := data.coordAlgebra p
  haveI := data.isScalarTower p
  exact diagonalChart_inf_diagonalComplement C (data.isAffineOpen p) (data.elift p)
    (data.isIdempotentElem_baseChange_elift p) (data.ker_lmul'_eq_span_baseChange_elift p)

/-- **The span of the restricted chart equation is the kernel ideal on the sub-open** (brick
B4/D3 through `IdealSheafData.map_ideal`): for an affine `W ≤ 𝔇(p)`,
`span {chartEqn|W} = ((δ C).left.ker).ideal ⟨W⟩`. -/
theorem span_res_chartEqn [IsSeparated C.hom] {W : (C ⊗ C).left.Opens}
    (hW : W ≤ diagonalChart C (data.isAffineOpen p) (data.elift p)) (hW_aff : IsAffineOpen W) :
    Ideal.span {((C ⊗ C).left.presheaf.map (homOfLE hW).op).hom (chartEqn data p)}
      = ((diagonal C).left.ker).ideal ⟨W, hW_aff⟩ := by
  have hmap := ((diagonal C).left.ker).map_ideal (U := ⟨W, hW_aff⟩)
    (V := ⟨diagonalChart C (data.isAffineOpen p) (data.elift p),
      isAffineOpen_diagonalChart C (data.isAffineOpen p) (data.elift p)⟩) hW
  rw [ker_ideal_eq_span_chartEqn data p, Ideal.map_span, Set.image_singleton] at hmap
  exact hmap

/-- **Section regularity of the restricted chart equation**: every restriction of `chartEqn` to
a sub-open is a nonzerodivisor (germs are nonzerodivisors, and sections inject into germs). -/
theorem res_chartEqn_mem_nonZeroDivisors {W : (C ⊗ C).left.Opens}
    (hW : W ≤ diagonalChart C (data.isAffineOpen p) (data.elift p)) :
    ((C ⊗ C).left.presheaf.map (homOfLE hW).op).hom (chartEqn data p) ∈ Γ((C ⊗ C).left, W)⁰ := by
  apply section_mem_nonZeroDivisors_of_germ
  intro y hy
  rw [TopCat.Presheaf.germ_res_apply]
  exact germ_chartEqn_mem_nonZeroDivisors data p (hW hy)

end DiagonalChartData

/-! ## The pointed cover and its local equation -/

open Classical in
/-- **The diagonal pointed cover** (worksheet D4): a point on the diagonal `Δ` gets the diagonal
member `𝔇(chart)` of the chart at its first projection; a point off `Δ` gets the complement
`Δᶜ`. -/
noncomputable def diagonalCover {C : Over (Spec (.of k))} (data : DiagonalChartData C)
    [IsSeparated C.hom] : (C ⊗ C).left.PointedCover where
  opens z :=
    if z ∈ Set.range (diagonal C).left.base then
      diagonalChart C (data.isAffineOpen ((fst C C).left.base z))
        (data.elift ((fst C C).left.base z))
    else diagonalComplement C
  mem_opens z := by
    by_cases h : z ∈ Set.range (diagonal C).left.base
    · rw [if_pos h]
      have hz : (diagonal C).left.base ((fst C C).left.base z) = z :=
        (mem_range_diagonal_iff C).mp h
      have hmem := diagonal_base_mem_diagonalChart C
        (data.isAffineOpen ((fst C C).left.base z)) (data.elift ((fst C C).left.base z))
        (data.lmul'_elift ((fst C C).left.base z)) (data.mem ((fst C C).left.base z))
      rwa [hz] at hmem
    · rw [if_neg h]
      exact (mem_diagonalComplement_iff C).mpr h

variable {C : Over (Spec (.of k))} (data : DiagonalChartData C) [IsSeparated C.hom]

/-- The diagonal cover on a diagonal point is the diagonal member of the chart. -/
lemma diagonalCover_opens_of_mem {z : (C ⊗ C).left}
    (h : z ∈ Set.range (diagonal C).left.base) :
    (diagonalCover data).opens z
      = diagonalChart C (data.isAffineOpen ((fst C C).left.base z))
          (data.elift ((fst C C).left.base z)) :=
  if_pos h

/-- The diagonal cover on an off-diagonal point is the complement. -/
lemma diagonalCover_opens_of_notMem {z : (C ⊗ C).left}
    (h : z ∉ Set.range (diagonal C).left.base) :
    (diagonalCover data).opens z = diagonalComplement C :=
  if_neg h

open Classical in
/-- **The local equation of the diagonal divisor**: the chart equation on a diagonal member, the
constant `1` on the complement. -/
noncomputable def diagonalEqn (z : (C ⊗ C).left) :
    Γ((C ⊗ C).left, (diagonalCover data).opens z) :=
  if h : z ∈ Set.range (diagonal C).left.base then
    ((C ⊗ C).left.presheaf.map
        (homOfLE (le_of_eq (diagonalCover_opens_of_mem data h))).op).hom
      (data.chartEqn ((fst C C).left.base z))
  else 1

/-- The diagonal equation on a diagonal point, restricted to a sub-open, is the chart equation
restricted there. -/
lemma diagonalEqn_res_of_mem {z : (C ⊗ C).left} (h : z ∈ Set.range (diagonal C).left.base)
    {W : (C ⊗ C).left.Opens} (hW : W ≤ (diagonalCover data).opens z) :
    ((C ⊗ C).left.presheaf.map (homOfLE hW).op).hom (diagonalEqn data z)
      = ((C ⊗ C).left.presheaf.map
            (homOfLE (hW.trans (le_of_eq (diagonalCover_opens_of_mem data h)))).op).hom
          (data.chartEqn ((fst C C).left.base z)) := by
  rw [diagonalEqn, dif_pos h]
  exact res_comp hW (le_of_eq (diagonalCover_opens_of_mem data h)) _

/-- The diagonal equation on an off-diagonal point is `1`. -/
lemma diagonalEqn_of_notMem {z : (C ⊗ C).left} (h : z ∉ Set.range (diagonal C).left.base) :
    diagonalEqn data z = 1 := by
  rw [diagonalEqn, dif_neg h]

/-! ## The diagonal local-equation system and its Picard class -/

/-- **The diagonal as an effective divisor in local equations, from frozen chart data**
(deg-D4b): the pointed cover `diagonalCover`, the local equation `diagonalEqn`, germ-regular
everywhere, with the overlap ratios units — the diag–diag ratio through the kernel ideal sheaf
and the regular-generators mini-lemma, the diag–off ratio through the basic-open unit.  The
curve-level headline `Over.diagonalLocalEquations` instantiates this at the frozen
`diagonalChartData C`. -/
noncomputable def diagonalLocalEquationsOfData :
    (C ⊗ C).left.LocalEquations where
  cover := diagonalCover data
  eqn := diagonalEqn data
  regular := by
    intro z y hy
    by_cases h : z ∈ Set.range (diagonal C).left.base
    · rw [diagonalEqn, dif_pos h, TopCat.Presheaf.germ_res_apply]
      exact data.germ_chartEqn_mem_nonZeroDivisors _ _
    · rw [diagonalEqn_of_notMem data h, map_one]
      exact one_mem _
  ratio_isUnit := by
    intro x y
    by_cases h : x ∈ Set.range (diagonal C).left.base <;>
      by_cases h' : y ∈ Set.range (diagonal C).left.base
    · -- diag–diag: the regular-generators mini-lemma on the affine overlap
      have hWx : (diagonalCover data).opens x ⊓ (diagonalCover data).opens y
          ≤ diagonalChart C (data.isAffineOpen ((fst C C).left.base x))
              (data.elift ((fst C C).left.base x)) :=
        inf_le_left.trans (le_of_eq (diagonalCover_opens_of_mem data h))
      have hWy : (diagonalCover data).opens x ⊓ (diagonalCover data).opens y
          ≤ diagonalChart C (data.isAffineOpen ((fst C C).left.base y))
              (data.elift ((fst C C).left.base y)) :=
        inf_le_right.trans (le_of_eq (diagonalCover_opens_of_mem data h'))
      have hWaff : IsAffineOpen
          ((diagonalCover data).opens x ⊓ (diagonalCover data).opens y) := by
        rw [diagonalCover_opens_of_mem data h, diagonalCover_opens_of_mem data h']
        exact (isAffineOpen_diagonalChart C (data.isAffineOpen _) (data.elift _)).inf
          (isAffineOpen_diagonalChart C (data.isAffineOpen _) (data.elift _))
      have hspan : Ideal.span {((C ⊗ C).left.presheaf.map (homOfLE hWx).op).hom
            (data.chartEqn ((fst C C).left.base x))}
          = Ideal.span {((C ⊗ C).left.presheaf.map (homOfLE hWy).op).hom
            (data.chartEqn ((fst C C).left.base y))} := by
        rw [data.span_res_chartEqn _ hWx hWaff, data.span_res_chartEqn _ hWy hWaff]
      obtain ⟨u, hu⟩ := exists_isUnit_of_span_singleton_eq hspan
        (data.res_chartEqn_mem_nonZeroDivisors _ hWx)
      refine ⟨u, ?_⟩
      rw [diagonalEqn_res_of_mem data h, diagonalEqn_res_of_mem data h']
      exact hu
    · -- diag–off: `chartEqn` is a unit on the overlap `⊆ 𝔇 ⊓ Δᶜ = D(chartEqn)`
      have hWx : (diagonalCover data).opens x ⊓ (diagonalCover data).opens y
          ≤ diagonalChart C (data.isAffineOpen ((fst C C).left.base x))
              (data.elift ((fst C C).left.base x)) :=
        inf_le_left.trans (le_of_eq (diagonalCover_opens_of_mem data h))
      have hWb : (diagonalCover data).opens x ⊓ (diagonalCover data).opens y
          ≤ (C ⊗ C).left.basicOpen (data.chartEqn ((fst C C).left.base x)) := by
        rw [diagonalCover_opens_of_mem data h, diagonalCover_opens_of_notMem data h']
        exact (data.chartEqn_inf_diagonalComplement _).le
      have haU := isUnit_res_of_le_basicOpen (data.chartEqn ((fst C C).left.base x)) hWx hWb
      refine ⟨haU.unit, ?_⟩
      rw [diagonalEqn_res_of_mem data h, diagonalEqn_of_notMem data h', map_one, mul_one,
        IsUnit.unit_spec]
    · -- off–diag: the inverse unit
      have hWy : (diagonalCover data).opens x ⊓ (diagonalCover data).opens y
          ≤ diagonalChart C (data.isAffineOpen ((fst C C).left.base y))
              (data.elift ((fst C C).left.base y)) :=
        inf_le_right.trans (le_of_eq (diagonalCover_opens_of_mem data h'))
      have hWb : (diagonalCover data).opens x ⊓ (diagonalCover data).opens y
          ≤ (C ⊗ C).left.basicOpen (data.chartEqn ((fst C C).left.base y)) := by
        rw [diagonalCover_opens_of_notMem data h, diagonalCover_opens_of_mem data h', inf_comm]
        exact (data.chartEqn_inf_diagonalComplement _).le
      have hbU := isUnit_res_of_le_basicOpen (data.chartEqn ((fst C C).left.base y)) hWy hWb
      refine ⟨hbU.unit⁻¹, ?_⟩
      rw [diagonalEqn_of_notMem data h, map_one, diagonalEqn_res_of_mem data h']
      exact (Units.inv_mul_of_eq hbU.unit_spec).symm
    · -- off–off: identical member `Δᶜ`, ratio `1`
      refine ⟨1, ?_⟩
      rw [diagonalEqn_of_notMem data h, diagonalEqn_of_notMem data h', map_one, map_one,
        Units.val_one, one_mul]

/-- The Picard class `𝒪(Δ)` of the diagonal divisor cut out by the given chart data. -/
noncomputable def diagonalPicClassOfData : (C ⊗ C).left.CechPic :=
  (diagonalLocalEquationsOfData data).picClass

/-! ## The curve-level headline (worksheet target) -/

variable (C) in
/-- **The diagonal of the smooth relative curve as an effective divisor in local equations**
(deg-D4b, the campaign headline): for `C` smooth of relative dimension one and separated over
`Spec k`, the diagonal `Δ ⊆ (C ⊗ C).left` presented by `Scheme.LocalEquations`, using the
frozen étale-coordinate chart data `diagonalChartData C`.  deg-D4c realizes the graph `Γ_t` as
its pullback along `lift (fst C T) (snd C T ≫ t)`. -/
noncomputable def diagonalLocalEquations [SmoothOfRelativeDimension 1 C.hom] :
    (C ⊗ C).left.LocalEquations :=
  diagonalLocalEquationsOfData (diagonalChartData C)

variable (C) in
/-- **The Picard class of the diagonal divisor** `𝒪(Δ)` — the deg-D4b headline. -/
noncomputable def diagonalPicClass [SmoothOfRelativeDimension 1 C.hom] :
    (C ⊗ C).left.CechPic :=
  (diagonalLocalEquations C).picClass

end Over

end AlgebraicGeometry
