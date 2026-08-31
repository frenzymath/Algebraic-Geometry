/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.PullbackCarrier
import AlgebraicJacobian.Curve.DiagonalClosed
import AlgebraicJacobian.Cohomology.SectionsBaseChange

/-!
# The graph square and the graph fibre (G-D8, support input)

For a curve `C` over `k`, a test object `T` and a point `t : T ⟶ C`, the **graph square**

```
      T   --t-->   C
      |σ_t         |Δ
      v            v
   C ⊗ T --q--> C ⊗ C
```

(`σ_t := Over.sectionOfPoint t` the section of the projection, `Δ := Over.diagonal C`,
`q := lift (fst C T) (snd C T ≫ t)` the graph lift of `Curve/GraphDivisor.lean`) is a
**pullback square of schemes** — the graph is the base change of the diagonal.  Proved by
paste-cancellation on the landed bridge `Over.isPullback_left` (the single point where `⊗`
meets scheme-level pullbacks), with no separatedness and no instance hypotheses.

Consequence, by the topological surjectivity of scheme pullbacks onto fibre products
(mathlib `AlgebraicGeometry.Scheme.Pullback.range_snd`): the `q`-preimage of the diagonal
is exactly the range of the section.  On an affine field test `T = overSpec k K` the test
has a single point, so the graph has a **single point** `Over.graphPoint t` — the support
statement of G-D8's degree-1 certificate (`RiemannRoch/GraphDegree.lean`).

## Main declarations

* `AlgebraicGeometry.Over.sectionOfPoint_comp_graphLift` — the commuting graph square.
* `AlgebraicGeometry.Over.isPullback_graphLift` — the graph square is a pullback (general
  test `T`; Wave-7's base-change bookkeeping re-instantiates this).
* `AlgebraicGeometry.Over.range_sectionOfPoint_left` — `range σ_t = q ⁻¹ Δ`.
* `AlgebraicGeometry.Over.graphPoint` — the section point of a field test, with
  `mem_range_diagonal_graphLift_iff : q z ∈ Δ ↔ z = graphPoint t`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

namespace Over

variable {k : Type u} [Field k] {C T : Over (Spec (.of k))}

/-! ## The graph square -/

/-- **The graph square commutes**: the section of the projection followed by the graph
lift is the point followed by the diagonal. -/
lemma sectionOfPoint_comp_graphLift (t : T ⟶ C) :
    sectionOfPoint t ≫ lift (fst C T) (snd C T ≫ t) = t ≫ diagonal C := by
  refine hom_ext _ _ ?_ ?_
  · rw [Category.assoc, lift_fst, sectionOfPoint_fst, Category.assoc, diagonal_fst,
      Category.comp_id]
  · rw [Category.assoc, lift_snd, ← Category.assoc, sectionOfPoint_snd, Category.id_comp,
      Category.assoc, diagonal_snd, Category.comp_id]

/-- **The graph square is a pullback of schemes** (G-D8 support input; general test `T`):
the graph of `t : T ⟶ C` is the base change of the diagonal of `C` along the graph lift.
Paste-cancellation on the landed `Over.isPullback_left` squares: first the middle square
`(C ⊗ T, snd) → (C ⊗ C, snd)` over `t` by horizontal cancellation, then the graph square
by vertical cancellation against the identity square of `t.left`. -/
theorem isPullback_graphLift (t : T ⟶ C) :
    IsPullback t.left (sectionOfPoint t).left (diagonal C).left
      (lift (fst C T) (snd C T ≫ t)).left := by
  set q := lift (fst C T) (snd C T ≫ t) with hq
  -- the middle square: `C ⊗ T` is the base change of `snd : C ⊗ C ⟶ C` along `t`
  have h1 : q.left ≫ (fst C C).left = (fst C T).left := by
    rw [← Over.comp_left, hq, lift_fst]
  have h2 : t.left ≫ C.hom = T.hom := Over.w t
  have s1 : IsPullback (q.left ≫ (fst C C).left) (snd C T).left C.hom
      (t.left ≫ C.hom) := by
    rw [h1, h2]; exact Over.isPullback_left C T
  have p1 : q.left ≫ (snd C C).left = (snd C T).left ≫ t.left := by
    rw [← Over.comp_left, hq, lift_snd, Over.comp_left]
  have hB : IsPullback q.left (snd C T).left (snd C C).left t.left :=
    IsPullback.of_right s1 p1 (Over.isPullback_left C C)
  -- the top square, by vertical cancellation against the identity square
  have hσs : (sectionOfPoint t).left ≫ (snd C T).left = 𝟙 T.left := by
    rw [← Over.comp_left, sectionOfPoint_snd]; rfl
  have hΔs : (diagonal C).left ≫ (snd C C).left = 𝟙 C.left :=
    diagonal_left_snd_left C
  have hid : IsPullback t.left (𝟙 T.left) (𝟙 C.left) t.left :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩
  have s2 : IsPullback t.left ((sectionOfPoint t).left ≫ (snd C T).left)
      ((diagonal C).left ≫ (snd C C).left) t.left := by
    rw [hσs, hΔs]; exact hid
  have p2 : t.left ≫ (diagonal C).left = (sectionOfPoint t).left ≫ q.left := by
    rw [← Over.comp_left, ← Over.comp_left, hq, sectionOfPoint_comp_graphLift]
  exact IsPullback.of_bot s2 p2 hB

/-! ## The graph fibre -/

/-- **The range of the section is the graph-lift preimage of the diagonal** — the
topological content of the graph square, through the surjectivity of scheme pullbacks onto
topological fibre products (`Scheme.Pullback.range_snd`). -/
theorem range_sectionOfPoint_left (t : T ⟶ C) :
    Set.range (sectionOfPoint t).left.base
      = (lift (fst C T) (snd C T ≫ t)).left.base ⁻¹'
          Set.range (diagonal C).left.base := by
  have h := isPullback_graphLift t
  have hsurj : Function.Surjective h.isoPullback.hom.base :=
    (Scheme.homeoOfIso h.isoPullback).surjective
  have hcomp : ⇑(sectionOfPoint t).left.base
      = ⇑(pullback.snd (diagonal C).left
            (lift (fst C T) (snd C T ≫ t)).left).base
          ∘ ⇑h.isoPullback.hom.base := by
    funext z
    have hh := h.isoPullback_hom_snd
    change (sectionOfPoint t).left.base z = _
    calc (sectionOfPoint t).left.base z
        = (h.isoPullback.hom ≫ pullback.snd (diagonal C).left
            (lift (fst C T) (snd C T ≫ t)).left).base z := by rw [hh]
      _ = (pullback.snd (diagonal C).left
            (lift (fst C T) (snd C T ≫ t)).left).base
              (h.isoPullback.hom.base z) := rfl
  rw [hcomp, hsurj.range_comp]
  exact Scheme.Pullback.range_snd _ _

section FieldTest

variable {K : Type u} [Field K] [Algebra k K]

noncomputable instance : Unique ((overSpec k K).left) :=
  inferInstanceAs (Unique (PrimeSpectrum K))

variable (C) in
/-- **The graph point**: the image of the unique point of the affine field test under the
section of the projection — the single point of the graph `Γ_t ⊆ C_K`. -/
noncomputable def graphPoint (t : overSpec k K ⟶ C) : (C ⊗ overSpec k K).left :=
  (sectionOfPoint t).left.base default

/-- On a field test the range of the section is the singleton of the graph point. -/
lemma range_sectionOfPoint_left_eq_singleton (t : overSpec k K ⟶ C) :
    Set.range (sectionOfPoint t).left.base = {graphPoint C t} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rw [Unique.eq_default w]
    rfl
  · rintro rfl
    exact ⟨default, rfl⟩

/-- **The graph fibre is the graph point** (the G-D8 support statement): a point of the
fibre curve maps into the diagonal under the graph lift exactly when it is the graph
point. -/
theorem mem_range_diagonal_graphLift_iff (t : overSpec k K ⟶ C)
    {z : (C ⊗ overSpec k K).left} :
    (lift (fst C (overSpec k K)) (snd C (overSpec k K) ≫ t)).left.base z
        ∈ Set.range (diagonal C).left.base
      ↔ z = graphPoint C t := by
  have h : z ∈ (lift (fst C (overSpec k K))
        (snd C (overSpec k K) ≫ t)).left.base ⁻¹' Set.range (diagonal C).left.base
      ↔ z ∈ Set.range (sectionOfPoint t).left.base := by
    rw [range_sectionOfPoint_left]
  rw [show ((lift (fst C (overSpec k K)) (snd C (overSpec k K) ≫ t)).left.base z
      ∈ Set.range (diagonal C).left.base) ↔ _ from h,
    range_sectionOfPoint_left_eq_singleton, Set.mem_singleton_iff]

/-- The first projection of the graph point is the image point of `t`. -/
lemma fst_graphPoint (t : overSpec k K ⟶ C) :
    (fst C (overSpec k K)).left.base (graphPoint C t) = t.left.base default := by
  have h : (sectionOfPoint t).left ≫ (fst C (overSpec k K)).left = t.left := by
    rw [← Over.comp_left, sectionOfPoint_fst]
  calc (fst C (overSpec k K)).left.base ((sectionOfPoint t).left.base default)
      = ((sectionOfPoint t).left ≫ (fst C (overSpec k K)).left).base default := rfl
    _ = t.left.base default := by rw [h]

/-- The graph lift sends the graph point onto the diagonal, at the image point of `t`. -/
lemma graphLift_graphPoint (t : overSpec k K ⟶ C) :
    (lift (fst C (overSpec k K)) (snd C (overSpec k K) ≫ t)).left.base (graphPoint C t)
      = (diagonal C).left.base (t.left.base default) := by
  have h : (sectionOfPoint t).left
        ≫ (lift (fst C (overSpec k K)) (snd C (overSpec k K) ≫ t)).left
      = t.left ≫ (diagonal C).left := by
    rw [← Over.comp_left, sectionOfPoint_comp_graphLift, Over.comp_left]
  calc (lift (fst C (overSpec k K)) (snd C (overSpec k K) ≫ t)).left.base
        ((sectionOfPoint t).left.base default)
      = ((sectionOfPoint t).left
          ≫ (lift (fst C (overSpec k K)) (snd C (overSpec k K) ≫ t)).left).base default :=
        rfl
    _ = (t.left ≫ (diagonal C).left).base default := by rw [h]
    _ = (diagonal C).left.base (t.left.base default) := rfl

end FieldTest

end Over

end AlgebraicGeometry
