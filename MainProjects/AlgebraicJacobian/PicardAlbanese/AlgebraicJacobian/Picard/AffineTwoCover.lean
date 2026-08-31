/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.SectionsBaseChange
import AlgebraicJacobian.Curve.MapToP1

/-!
# Affine two-chart covers, and their pullback along the base-change projection

An **affine two-chart cover** of a scheme `Y` (`Scheme.AffineTwoCover`) is a pair of affine
opens `V₀, V₁` covering `Y` whose overlap `V₀ ⊓ V₁` is again affine. This file provides:

* the structure `Scheme.AffineTwoCover`;
* **existence** for the challenge curve: the smooth, proper, geometrically irreducible curve
  `C/k` admits an affine two-chart cover (`Scheme.AffineTwoCover.nonempty_of_curve`), obtained
  as the preimages of the two standard charts of `ℙ¹` under a finite `k`-morphism `C ⟶ ℙ¹`
  (`exists_isFinite_toP1`, `AlgebraicJacobian.Curve.MapToP1`); the overlap is affine because it
  is the preimage of the affine chart overlap `D₊(X₀X₁)`;
* **stability under base change**: an affine two-chart cover of `C.left` pulls back, along the
  first projection `(C ⊗ overSpec k R).left ⟶ C.left`, to an affine two-chart cover of
  `(C ⊗ overSpec k R).left`, for any `k`-algebra `R` (`Scheme.AffineTwoCover.pullbackProd`).
  The key input is that the first projection is an affine morphism: it is the base change of
  `overSpec k R ⟶ Spec k` (itself affine, being a morphism between affine schemes) along
  `C.hom` (`Over.isAffineHom_fst_left`), and preimages of affine opens under an affine
  morphism are affine.

## Main declarations

* `AlgebraicGeometry.Scheme.AffineTwoCover` — the structure.
* `AlgebraicGeometry.Scheme.AffineTwoCover.nonempty_of_curve` — existence for the curve.
* `AlgebraicGeometry.Over.isAffineHom_fst_left` — the first projection of a base change along
  an affine morphism is affine.
* `AlgebraicGeometry.Scheme.AffineTwoCover.pullbackProd` — the pullback of an affine two-chart
  cover along the first projection `(C ⊗ overSpec k R).left ⟶ C.left`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-! ## The structure -/

/-- An **affine two-chart cover** of a scheme `Y`: two affine opens `V₀, V₁` covering `Y`
whose overlap `V₀ ⊓ V₁` is again affine. -/
structure Scheme.AffineTwoCover (Y : Scheme.{u}) : Type u where
  /-- The first chart. -/
  V₀ : Y.Opens
  /-- The second chart. -/
  V₁ : Y.Opens
  /-- The first chart is affine. -/
  isAffineOpen₀ : IsAffineOpen V₀
  /-- The second chart is affine. -/
  isAffineOpen₁ : IsAffineOpen V₁
  /-- The two charts cover `Y`. -/
  sup_eq_top : V₀ ⊔ V₁ = ⊤
  /-- The overlap of the two charts is affine. -/
  isAffineOpen_inf : IsAffineOpen (V₀ ⊓ V₁)

/-- The overlap of the two charts of an affine two-chart cover is contained in the first
chart. -/
theorem Scheme.AffineTwoCover.inf_le_left {Y : Scheme.{u}} (D : Y.AffineTwoCover) :
    D.V₀ ⊓ D.V₁ ≤ D.V₀ :=
  _root_.inf_le_left

/-- The overlap of the two charts of an affine two-chart cover is contained in the second
chart. -/
theorem Scheme.AffineTwoCover.inf_le_right {Y : Scheme.{u}} (D : Y.AffineTwoCover) :
    D.V₀ ⊓ D.V₁ ≤ D.V₁ :=
  _root_.inf_le_right

/-! ## Existence: the two chart preimages of a finite map to the projective line -/

section Existence

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- **Existence of an affine two-chart cover of the curve**: the smooth, proper,
geometrically irreducible curve `C/k` admits an affine two-chart cover, obtained as the
preimages of the two standard charts of `ℙ¹` under a finite `k`-morphism `C ⟶ ℙ¹`
(`exists_isFinite_toP1`). The charts are affine and cover `C.left`
(`isAffineOpen_preimage_chartOpen`, `preimage_chartOpen_sup`); the overlap is affine because
it is the preimage of the affine chart overlap `D₊(X₀X₁)` (`P1.isAffineOpen_overlap`), via
`P1.chartOpen_inf` and preimage commuting with `⊓`. -/
theorem Scheme.AffineTwoCover.nonempty_of_curve : Nonempty C.left.AffineTwoCover := by
  obtain ⟨π, hfin, -⟩ := exists_isFinite_toP1 (C := C)
  haveI := hfin
  -- restated with the ambient scheme literally `P1 k` (as `P1.chartOpen` is stated), so that
  -- `.preimage π` below unifies against `π : C.left ⟶ P1 k` without unfolding `P1`.
  have hinf : IsAffineOpen (P1.chartOpen k 0 ⊓ P1.chartOpen k 1) := by
    rw [P1.chartOpen_inf k]
    exact P1.isAffineOpen_overlap k
  refine ⟨{ V₀ := π ⁻¹ᵁ P1.chartOpen k 0
            V₁ := π ⁻¹ᵁ P1.chartOpen k 1
            isAffineOpen₀ := isAffineOpen_preimage_chartOpen π 0
            isAffineOpen₁ := isAffineOpen_preimage_chartOpen π 1
            sup_eq_top := preimage_chartOpen_sup π
            isAffineOpen_inf := ?_ }⟩
  rw [← Scheme.Hom.preimage_inf]
  exact hinf.preimage π

end Existence

/-! ## Pullback along the base-change projection -/

/-- **The first projection of a base change along an affine morphism is affine**: for `X, T`
objects of `Over S`, `(fst X T).left` is (up to the defeq `Over.fst_left`/`Over.tensorObj_left`)
the pullback of `T.hom` along `X.hom`, i.e. `Limits.pullback.fst X.hom T.hom`
(`Over.isPullback_left`, flipped so that the affine leg `T.hom` lines up with the class field
`IsStableUnderBaseChange.of_isPullback`); affineness is stable under base change
(`isAffineHom_isStableUnderBaseChange`). -/
instance Over.isAffineHom_fst_left {S : Scheme.{u}} (X T : Over S) [IsAffineHom T.hom] :
    IsAffineHom (fst X T).left :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (Over.isPullback_left X T).flip ‹_›

/-- The underlying scheme of `overSpec k A` is affine (restated from `overSpec_left`, which
identifies it with `Spec (.of A)`, so that instance search finds it without unfolding the
`abbrev overSpec`). -/
instance isAffine_overSpec_left {k : Type u} [Field k] {A : Type u} [CommRing A]
    [Algebra k A] : IsAffine (overSpec k A).left := by
  rw [overSpec_left]; infer_instance

/-- The structure morphism `overSpec k A ⟶ Spec k` is affine: it is a morphism between affine
schemes. -/
instance isAffineHom_overSpec_hom {k : Type u} [Field k] {A : Type u} [CommRing A]
    [Algebra k A] : IsAffineHom (overSpec k A).hom :=
  isAffineHom_of_isAffine _

section PullbackProd

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}

/-- **Base change of an affine two-chart cover**: an affine two-chart cover `D` of `C.left`
pulls back, along the first projection `(C ⊗ overSpec k R).left ⟶ C.left`, to an affine
two-chart cover of `(C ⊗ overSpec k R).left`, for any `k`-algebra `R`. The charts are the
preimages of `D`'s charts under the first projection. All four fields follow from `D`'s
fields: the first projection is an affine morphism (`Over.isAffineHom_fst_left`, since
`overSpec k R ⟶ Spec k` is a morphism between affine schemes hence affine), preimage of an
affine open under an affine morphism is affine, and preimage commutes with `⊔`, `⊓`, `⊤`. -/
noncomputable def Scheme.AffineTwoCover.pullbackProd (D : C.left.AffineTwoCover)
    (R : Type u) [CommRing R] [Algebra k R] :
    (C ⊗ overSpec k R).left.AffineTwoCover where
  V₀ := (fst C (overSpec k R)).left ⁻¹ᵁ D.V₀
  V₁ := (fst C (overSpec k R)).left ⁻¹ᵁ D.V₁
  isAffineOpen₀ := D.isAffineOpen₀.preimage (fst C (overSpec k R)).left
  isAffineOpen₁ := D.isAffineOpen₁.preimage (fst C (overSpec k R)).left
  sup_eq_top := by
    rw [← Scheme.Hom.preimage_sup, D.sup_eq_top, Scheme.Hom.preimage_top]
  isAffineOpen_inf := by
    rw [← Scheme.Hom.preimage_inf]
    exact D.isAffineOpen_inf.preimage (fst C (overSpec k R)).left

end PullbackProd

end AlgebraicGeometry
