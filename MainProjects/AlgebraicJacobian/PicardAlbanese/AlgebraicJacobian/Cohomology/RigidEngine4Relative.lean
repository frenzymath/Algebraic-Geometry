/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RigidEngine4Twist
import AlgebraicJacobian.Cohomology.RelativeSectionsLinear
import AlgebraicJacobian.RiemannRoch.FLVFiberToolkit

/-!
# RE-4 — the pinned relative cover: coordinates, E-i finiteness, and freeness

The geometric half of the Layer-2 discharge (`informal/w4-rigid-engine-worksheet.md` §4,
RE-4 + RE-4b): everything the engine's pair data and hypotheses need on the **pinned
relative cover** — the base change to an affine test ring `R` of the chart-preimage cover
of the challenge curve along a finite `π : C ⟶ ℙ¹`.

* `AlgebraicGeometry.fiberTwoCover π` — the pinned cover as an `AffineTwoCover`:
  charts `fiberChart₀/₁ π = π⁻¹D₊(Xᵢ)`, overlap `π⁻¹D₊(X₀X₁)`.
* `preimage_inf_eq_basicOpen_fiberCoord₁` — the chart-1 twin of the landed
  `preimage_inf_eq_basicOpen_fiberCoord` (public re-derivation of
  `Cohomology.Finiteness.preimage_inf_eq_basicOpen_right`).
* `fiberPolyHom₀/₁` — the chart polynomial algebras `k[t] →+* Γ(C, Vᵢ)` through
  `P1.chartSectionsEquiv₀/₁`, with `…_X` (the coordinate), `…_finite` (E-i,
  `finite_app_chartOpen`), and `…_algebraMap` (the scalar compatibility, through the
  structure-morphism factorization `hπ : π ≫ P1.structureMap k = C.hom`).
* `moduleFinite_aeval'_mulLeft_fiberCoord₀/₁` — **E-i in the engine's pinned `AEval'`
  spelling** at the field level: `Γ(C, Vᵢ)` is a finite `k[t]`-module for `t` acting as
  multiplication by the pulled-back chart coordinate.
* `relFiberCoord₀/₁` — the relative chart coordinates `t₀ᴿ, t₁ᴿ` (pullbacks along the
  first projection), with `relCover_fiberTwoCover_inf_eq_basicOpen₀/₁` (the
  overlap-as-basic-open identifications on the pinned relative cover, via
  `Scheme.preimage_basicOpen`) and `relFiberCoord_mul` (`t₀ᴿ · t₁ᴿ = 1` on the overlap,
  the pulled-back `P1.chartCoord` relation).
* `moduleFinite_aeval'_mulSectionEnd_relFiberCoord₀/₁` — **the relative E-i** (RE-4b):
  `AEval'`-finiteness over `R[t]` of the relative chart lattices, by
  `RigidEngine.moduleFinite_aeval'_baseChange` transported along `relSectionsBaseChange`.
* `free_relSections` — freeness of the relative section modules (`k`-basis is an
  `R`-basis through `relSectionsBaseChange`), feeding the engine's flatness/projectivity.

The final assembly — the pair data of the relative twisted sheaf and the engine keystones
— is in `AlgebraicJacobian.Cohomology.RigidEngine4Engine`.
-/

set_option autoImplicit false
/- Scheme-theoretic unification (mixing `P1 k` with `Proj 𝒜`, `Γ(X, U)` with functor
applications) needs defeq checks through semireducible definitions, as in mathlib's own
algebraic-geometry files and the sibling `Cohomology/Finiteness.lean`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MvPolynomial
open HomogeneousLocalization TopologicalSpace Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The standard grading of `k[X₀, X₁]`, the graded ring underlying `P1 k`. -/
local notation "𝒜" => homogeneousSubmodule (Fin 2) k

section Cover

variable {Y : Scheme.{u}} (π : Y ⟶ P1 k)

/-! ## The pinned affine two-chart cover -/

/-- **The pinned affine two-chart cover** of a scheme with an affine (e.g. finite)
morphism to `ℙ¹`: the chart preimages `V₀ = π⁻¹D₊(X₀)`, `V₁ = π⁻¹D₊(X₁)`, with affine
overlap `π⁻¹D₊(X₀X₁)`. This is the cover on which the whole rigid-engine campaign runs;
its base change `relCover C R (fiberTwoCover π)` is the pinned relative cover. -/
noncomputable def fiberTwoCover [IsAffineHom π] : Y.AffineTwoCover where
  V₀ := fiberChart₀ π
  V₁ := fiberChart₁ π
  isAffineOpen₀ := isAffineOpen_preimage_chartOpen π 0
  isAffineOpen₁ := isAffineOpen_preimage_chartOpen π 1
  sup_eq_top := preimage_chartOpen_sup π
  isAffineOpen_inf := by
    have h : fiberChart₀ π ⊓ fiberChart₁ π = π ⁻¹ᵁ Proj.basicOpen 𝒜 (X 0 * X 1) := by
      rw [← Scheme.Hom.preimage_inf, P1.chartOpen_inf]
    rw [h]
    exact (P1.isAffineOpen_overlap k).preimage π

@[simp]
lemma fiberTwoCover_V₀ [IsAffineHom π] : (fiberTwoCover π).V₀ = fiberChart₀ π := rfl

@[simp]
lemma fiberTwoCover_V₁ [IsAffineHom π] : (fiberTwoCover π).V₁ = fiberChart₁ π := rfl

/-- **The two-cover overlap is the basic open of `t₁`** — the chart-1 twin of the landed
`preimage_inf_eq_basicOpen_fiberCoord` (public re-derivation of the `private`
`Cohomology.Finiteness.preimage_inf_eq_basicOpen_right`). -/
theorem preimage_inf_eq_basicOpen_fiberCoord₁ :
    fiberChart₀ π ⊓ fiberChart₁ π = Y.basicOpen (fiberCoord₁ π) := by
  have h : π ⁻¹ᵁ ((P1 k).basicOpen
        ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0)))
      = Y.basicOpen (fiberCoord₁ π) :=
    Scheme.preimage_basicOpen π _
  rw [P1.basicOpen_awayToSection_chartCoord k 1 0, Scheme.Hom.preimage_inf] at h
  rw [← h, inf_comm]

/-! ## The chart polynomial algebras -/

/-- The chart-0 polynomial algebra map `k[t] →+* Γ(Y, V₀)`, `t ↦ t₀ = π^*(X₁/X₀)`:
`π`'s section map on the chart composed with the chart identification
`Γ(ℙ¹, D₊(X₀)) ≃ k[t]`. -/
noncomputable def fiberPolyHom₀ : Polynomial k →+* Γ(Y, fiberChart₀ π) :=
  ((π.app (P1.chartOpen k 0)).hom).comp (P1.chartSectionsEquiv₀ k).symm.toRingHom

/-- The chart-1 polynomial algebra map `k[t] →+* Γ(Y, V₁)`, `t ↦ t₁ = π^*(X₀/X₁)`. -/
noncomputable def fiberPolyHom₁ : Polynomial k →+* Γ(Y, fiberChart₁ π) :=
  ((π.app (P1.chartOpen k 1)).hom).comp (P1.chartSectionsEquiv₁ k).symm.toRingHom

/-- **E-i, chart 0**: the chart polynomial algebra is a finite ring map
(`finite_app_chartOpen` through the chart identification). -/
theorem fiberPolyHom₀_finite [IsFinite π] : (fiberPolyHom₀ π).Finite :=
  (finite_app_chartOpen π 0).comp (P1.chartSectionsEquiv₀ k).symm.finite

/-- **E-i, chart 1**. -/
theorem fiberPolyHom₁_finite [IsFinite π] : (fiberPolyHom₁ π).Finite :=
  (finite_app_chartOpen π 1).comp (P1.chartSectionsEquiv₁ k).symm.finite

/-- The chart-0 polynomial algebra sends `t` to the pulled-back chart coordinate. -/
theorem fiberPolyHom₀_X : fiberPolyHom₀ π Polynomial.X = fiberCoord π := by
  have h : (P1.chartSectionsEquiv₀ k).symm Polynomial.X
      = (Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1) := by
    apply (P1.chartSectionsEquiv₀ k).injective
    rw [RingEquiv.apply_symm_apply, P1.chartSectionsEquiv₀_awayToSection,
      P1.awayAlgEquiv_chartCoord]
  change (π.app (P1.chartOpen k 0)).hom ((P1.chartSectionsEquiv₀ k).symm Polynomial.X)
    = fiberCoord π
  rw [h]
  rfl

/-- The chart-1 polynomial algebra sends `t` to the pulled-back inverse coordinate. -/
theorem fiberPolyHom₁_X : fiberPolyHom₁ π Polynomial.X = fiberCoord₁ π := by
  have h : (P1.chartSectionsEquiv₁ k).symm Polynomial.X
      = (Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0) := by
    apply (P1.chartSectionsEquiv₁ k).injective
    rw [RingEquiv.apply_symm_apply, P1.chartSectionsEquiv₁_awayToSection,
      P1.awayAlgEquiv_chartCoord]
  change (π.app (P1.chartOpen k 1)).hom ((P1.chartSectionsEquiv₁ k).symm Polynomial.X)
    = fiberCoord₁ π
  rw [h]
  rfl

end Cover

/-! ## The scalar compatibility and the field-level `AEval'` finiteness -/

section FieldLevel

variable (C : Over (Spec (.of k))) (π : C.left ⟶ P1 k)

attribute [local instance] Over.sectionsAlgebra

/-- (Implementation) The constants of the chart polynomial algebra: the composite
`k → k[t] → Γ(ℙ¹, D₊(Xᵢ))` is the structure algebra map of `ℙ¹`. -/
private lemma chartSectionsEquiv₀_symm_C (c : k) :
    (P1.chartSectionsEquiv₀ k).symm (Polynomial.C c)
      = (Proj.awayToSection 𝒜 (X 0)).hom (algebraMap k (Away 𝒜 (X 0)) c) := by
  apply (P1.chartSectionsEquiv₀ k).injective
  rw [RingEquiv.apply_symm_apply, P1.chartSectionsEquiv₀_awayToSection,
    AlgEquiv.commutes, Polynomial.algebraMap_eq]

private lemma chartSectionsEquiv₁_symm_C (c : k) :
    (P1.chartSectionsEquiv₁ k).symm (Polynomial.C c)
      = (Proj.awayToSection 𝒜 (X 1)).hom (algebraMap k (Away 𝒜 (X 1)) c) := by
  apply (P1.chartSectionsEquiv₁ k).injective
  rw [RingEquiv.apply_symm_apply, P1.chartSectionsEquiv₁_awayToSection,
    AlgEquiv.commutes, Polynomial.algebraMap_eq]

/-- **Scalar compatibility of the chart-0 polynomial algebra**: constants go to the
`Over.sectionsAlgebra` structure map of the curve — `π` pulls the structure algebra map
of `ℙ¹` back to that of `C` (`hπ` is the structure-morphism factorization supplied by
`Curve/MapToP1.exists_isFinite_isDominant_toP1`). -/
theorem fiberPolyHom₀_algebraMap (hπ : π ≫ P1.structureMap k = C.hom) (c : k) :
    fiberPolyHom₀ π (Polynomial.C c) = algebraMap k Γ(C.left, fiberChart₀ π) c := by
  letI : (P1 k).Over (Spec (.of k)) := ⟨P1.structureMap k⟩
  letI : C.left.Over (Spec (.of k)) := ⟨C.hom⟩
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (P1.structureMap k).appTop ≫
      (P1 k).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 (X 0) ≤ ⊤)).op =
      CommRingCat.ofHom (algebraMap k (Away 𝒜 (X 0))) ≫ Proj.awayToSection 𝒜 (X 0) := by
    rw [P1.structureMap_appTop_awayToSection k (P1.X_mem k 0) one_pos,
      Iso.inv_hom_id_assoc]
  have hPA : (P1 k).overAlgebraMap k (P1.chartOpen k 0) c =
      (Proj.awayToSection 𝒜 (X 0)).hom (algebraMap k (Away 𝒜 (X 0)) c) :=
    congr((CommRingCat.Hom.hom $hcomp) c)
  have happ : (π.app (P1.chartOpen k 0)).hom
        ((P1 k).overAlgebraMap k (P1.chartOpen k 0) c)
      = C.left.overAlgebraMap k (fiberChart₀ π) c := by
    rw [Scheme.Hom.app_eq_appLE]
    exact π.appLE_overAlgebraMap
      (show π ≫ ((P1 k) ↘ Spec (.of k)) = C.left ↘ Spec (.of k) from hπ) le_rfl c
  calc fiberPolyHom₀ π (Polynomial.C c)
      = (π.app (P1.chartOpen k 0)).hom
          ((P1.chartSectionsEquiv₀ k).symm (Polynomial.C c)) := rfl
    _ = (π.app (P1.chartOpen k 0)).hom
          ((P1 k).overAlgebraMap k (P1.chartOpen k 0) c) := by
        rw [chartSectionsEquiv₀_symm_C, ← hPA]
    _ = C.left.overAlgebraMap k (fiberChart₀ π) c := happ
    _ = algebraMap k Γ(C.left, fiberChart₀ π) c := rfl

/-- **Scalar compatibility of the chart-1 polynomial algebra**. -/
theorem fiberPolyHom₁_algebraMap (hπ : π ≫ P1.structureMap k = C.hom) (c : k) :
    fiberPolyHom₁ π (Polynomial.C c) = algebraMap k Γ(C.left, fiberChart₁ π) c := by
  letI : (P1 k).Over (Spec (.of k)) := ⟨P1.structureMap k⟩
  letI : C.left.Over (Spec (.of k)) := ⟨C.hom⟩
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (P1.structureMap k).appTop ≫
      (P1 k).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 (X 1) ≤ ⊤)).op =
      CommRingCat.ofHom (algebraMap k (Away 𝒜 (X 1))) ≫ Proj.awayToSection 𝒜 (X 1) := by
    rw [P1.structureMap_appTop_awayToSection k (P1.X_mem k 1) one_pos,
      Iso.inv_hom_id_assoc]
  have hPA : (P1 k).overAlgebraMap k (P1.chartOpen k 1) c =
      (Proj.awayToSection 𝒜 (X 1)).hom (algebraMap k (Away 𝒜 (X 1)) c) :=
    congr((CommRingCat.Hom.hom $hcomp) c)
  have happ : (π.app (P1.chartOpen k 1)).hom
        ((P1 k).overAlgebraMap k (P1.chartOpen k 1) c)
      = C.left.overAlgebraMap k (fiberChart₁ π) c := by
    rw [Scheme.Hom.app_eq_appLE]
    exact π.appLE_overAlgebraMap
      (show π ≫ ((P1 k) ↘ Spec (.of k)) = C.left ↘ Spec (.of k) from hπ) le_rfl c
  calc fiberPolyHom₁ π (Polynomial.C c)
      = (π.app (P1.chartOpen k 1)).hom
          ((P1.chartSectionsEquiv₁ k).symm (Polynomial.C c)) := rfl
    _ = (π.app (P1.chartOpen k 1)).hom
          ((P1 k).overAlgebraMap k (P1.chartOpen k 1) c) := by
        rw [chartSectionsEquiv₁_symm_C, ← hPA]
    _ = C.left.overAlgebraMap k (fiberChart₁ π) c := happ
    _ = algebraMap k Γ(C.left, fiberChart₁ π) c := rfl

/-- **E-i in the engine's pinned `AEval'` spelling, chart 0, field level**: the chart
sections `Γ(C, V₀)` form a finite `k[t]`-module for `t` acting as multiplication by the
pulled-back coordinate `t₀`. -/
theorem moduleFinite_aeval'_mulLeft_fiberCoord₀ [IsFinite π]
    (hπ : π ≫ P1.structureMap k = C.hom) :
    Module.Finite (Polynomial k) (Module.AEval'
      (LinearMap.mulLeft k (fiberCoord π) :
        Module.End k Γ(C.left, fiberChart₀ π))) := by
  refine AlgebraicJacobian.RigidEngine.moduleFinite_aeval'_of_ringHom_finite
    (fiberPolyHom₀ π) (fiberPolyHom₀_finite π) _ (fun a => ?_) (fun c a => ?_)
  · rw [fiberPolyHom₀_X]
    rfl
  · rw [fiberPolyHom₀_algebraMap C π hπ c]
    exact Algebra.smul_def c a

/-- **E-i in the engine's pinned `AEval'` spelling, chart 1, field level**. -/
theorem moduleFinite_aeval'_mulLeft_fiberCoord₁ [IsFinite π]
    (hπ : π ≫ P1.structureMap k = C.hom) :
    Module.Finite (Polynomial k) (Module.AEval'
      (LinearMap.mulLeft k (fiberCoord₁ π) :
        Module.End k Γ(C.left, fiberChart₁ π))) := by
  refine AlgebraicJacobian.RigidEngine.moduleFinite_aeval'_of_ringHom_finite
    (fiberPolyHom₁ π) (fiberPolyHom₁_finite π) _ (fun a => ?_) (fun c a => ?_)
  · rw [fiberPolyHom₁_X]
    rfl
  · rw [fiberPolyHom₁_algebraMap C π hπ c]
    exact Algebra.smul_def c a

end FieldLevel

/-! ## The relative coordinates on the pinned relative cover -/

section Relative

variable (C : Over (Spec (.of k))) (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k)

attribute [local instance] Scheme.overModule Over.sectionsAlgebra

/-- **The relative chart-0 coordinate** `t₀ᴿ ∈ Γ(C_R, V₀ᴿ)`: the pullback of the
pulled-back chart coordinate `t₀` along the first projection. -/
noncomputable def relFiberCoord₀ [IsAffineHom π] :
    Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀) :=
  relPullbackSection C R (fiberChart₀ π) (fiberCoord π)

/-- **The relative chart-1 coordinate** `t₁ᴿ ∈ Γ(C_R, V₁ᴿ)`. -/
noncomputable def relFiberCoord₁ [IsAffineHom π] :
    Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₁) :=
  relPullbackSection C R (fiberChart₁ π) (fiberCoord₁ π)

/-- Pullback of curve sections to the relative curve is multiplicative. -/
lemma relPullbackSection_mul (V : C.left.Opens) (s t : Γ(C.left, V)) :
    relPullbackSection C R V (s * t)
      = relPullbackSection C R V s * relPullbackSection C R V t := by
  change ((fst C (overSpec k R)).left.appLE V
    ((fst C (overSpec k R)).left ⁻¹ᵁ V) le_rfl).hom (s * t) = _
  rw [map_mul]
  rfl

/-- **The relative overlap is the basic open of `t₀ᴿ`** — the pinned relative form of
the overlap-as-basic-open identification, from `Scheme.preimage_basicOpen` and the landed
field-level `preimage_inf_eq_basicOpen_fiberCoord`. -/
theorem relCover_fiberTwoCover_inf_eq_basicOpen₀ [IsAffineHom π] :
    (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁
      = (relCurve C R).basicOpen (relFiberCoord₀ C R π) := by
  have h1 : (fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁
      = C.left.basicOpen (fiberCoord π) := preimage_inf_eq_basicOpen_fiberCoord π
  have h3 : (fst C (overSpec k R)).left ⁻¹ᵁ C.left.basicOpen (fiberCoord π)
      = (relCurve C R).basicOpen
          (((fst C (overSpec k R)).left.app (fiberChart₀ π)).hom (fiberCoord π)) :=
    Scheme.preimage_basicOpen (fst C (overSpec k R)).left (fiberCoord π)
  rw [relCover_inf, h1, h3]
  congr 1
  exact (congr($(Scheme.Hom.appLE_eq_app (fst C (overSpec k R)).left
    (U := fiberChart₀ π)).hom (fiberCoord π))).symm

/-- **The relative overlap is the basic open of `t₁ᴿ`**. -/
theorem relCover_fiberTwoCover_inf_eq_basicOpen₁ [IsAffineHom π] :
    (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁
      = (relCurve C R).basicOpen (relFiberCoord₁ C R π) := by
  have h1 : (fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁
      = C.left.basicOpen (fiberCoord₁ π) := preimage_inf_eq_basicOpen_fiberCoord₁ π
  have h3 : (fst C (overSpec k R)).left ⁻¹ᵁ C.left.basicOpen (fiberCoord₁ π)
      = (relCurve C R).basicOpen
          (((fst C (overSpec k R)).left.app (fiberChart₁ π)).hom (fiberCoord₁ π)) :=
    Scheme.preimage_basicOpen (fst C (overSpec k R)).left (fiberCoord₁ π)
  rw [relCover_inf, h1, h3]
  congr 1
  exact (congr($(Scheme.Hom.appLE_eq_app (fst C (overSpec k R)).left
    (U := fiberChart₁ π)).hom (fiberCoord₁ π))).symm

/-- **The relative coordinates multiply to `1` on the overlap** — the pulled-back
`P1.chartCoord` relation (`fiberCoord_mul_fiberCoord₁_res` pushed through the first
projection). -/
theorem relFiberCoord_mul [IsAffineHom π] :
    (relCurve C R).resHom (inf_le_left : (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁ ≤ (relCover C R (fiberTwoCover π)).V₀)
        (relFiberCoord₀ C R π) *
      (relCurve C R).resHom (inf_le_right : (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁ ≤ (relCover C R (fiberTwoCover π)).V₁)
        (relFiberCoord₁ C R π) = 1 := by
  set f := (fst C (overSpec k R)).left with hf
  have hle : (relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁
      ≤ f ⁻¹ᵁ (fiberChart₀ π ⊓ fiberChart₁ π) :=
    le_of_eq (relCover_inf C R (fiberTwoCover π))
  have h₀ : (relCurve C R).resHom (inf_le_left : _ ≤ (relCover C R (fiberTwoCover π)).V₀)
        (relFiberCoord₀ C R π)
      = (f.appLE (fiberChart₀ π ⊓ fiberChart₁ π) _ hle).hom
          ((C.left.presheaf.map (homOfLE (inf_le_left :
            fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₀ π)).op).hom (fiberCoord π)) := by
    have e1 := congr((CommRingCat.Hom.hom $(Scheme.Hom.appLE_map f
      (le_rfl : f ⁻¹ᵁ fiberChart₀ π ≤ f ⁻¹ᵁ fiberChart₀ π)
      (homOfLE (inf_le_left : (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁ ≤
          (relCover C R (fiberTwoCover π)).V₀)).op)) (fiberCoord π))
    have e2 := congr((CommRingCat.Hom.hom $(Scheme.Hom.map_appLE f hle
      (homOfLE (inf_le_left :
        fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₀ π)).op)) (fiberCoord π))
    exact e1.trans e2.symm
  have h₁ : (relCurve C R).resHom (inf_le_right : _ ≤ (relCover C R (fiberTwoCover π)).V₁)
        (relFiberCoord₁ C R π)
      = (f.appLE (fiberChart₀ π ⊓ fiberChart₁ π) _ hle).hom
          ((C.left.presheaf.map (homOfLE (inf_le_right :
            fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₁ π)).op).hom (fiberCoord₁ π)) := by
    have e1 := congr((CommRingCat.Hom.hom $(Scheme.Hom.appLE_map f
      (le_rfl : f ⁻¹ᵁ fiberChart₁ π ≤ f ⁻¹ᵁ fiberChart₁ π)
      (homOfLE (inf_le_right : (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁ ≤
          (relCover C R (fiberTwoCover π)).V₁)).op)) (fiberCoord₁ π))
    have e2 := congr((CommRingCat.Hom.hom $(Scheme.Hom.map_appLE f hle
      (homOfLE (inf_le_right :
        fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₁ π)).op)) (fiberCoord₁ π))
    exact e1.trans e2.symm
  rw [h₀, h₁]
  have hkey := congrArg
    (CommRingCat.Hom.hom (f.appLE (fiberChart₀ π ⊓ fiberChart₁ π) _ hle))
    (fiberCoord_mul_fiberCoord₁_res π)
  rw [map_mul, map_one] at hkey
  exact hkey

/-! ## The relative E-i (RE-4b) and freeness -/

/-- (Implementation) The base-change equivalence intertwines multiplication by the chart
coordinate with multiplication by its pullback, on pure tensors (chart 0). Stated in the
`RelativeSectionsLinear` spelling so that all rewrites stay in one presentation of the
relative section modules. -/
private lemma relSectionsBaseChange_mul_fiberCoord₀ [IsAffineHom π] (a : R)
    (s : Γ(C.left, fiberChart₀ π)) :
    relSectionsBaseChange C R (isAffineOpen_preimage_chartOpen π 0).isCompact
        (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated
        (a ⊗ₜ[k] (fiberCoord π * s))
      = relPullbackSection C R (fiberChart₀ π) (fiberCoord π) *
          relSectionsBaseChange C R (isAffineOpen_preimage_chartOpen π 0).isCompact
            (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated (a ⊗ₜ[k] s) := by
  rw [relSectionsBaseChange_tmul, relSectionsBaseChange_tmul, relPullbackSection_mul]
  ring

/-- (Implementation) Chart-1 twin of `relSectionsBaseChange_mul_fiberCoord₀`. -/
private lemma relSectionsBaseChange_mul_fiberCoord₁ [IsAffineHom π] (a : R)
    (s : Γ(C.left, fiberChart₁ π)) :
    relSectionsBaseChange C R (isAffineOpen_preimage_chartOpen π 1).isCompact
        (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated
        (a ⊗ₜ[k] (fiberCoord₁ π * s))
      = relPullbackSection C R (fiberChart₁ π) (fiberCoord₁ π) *
          relSectionsBaseChange C R (isAffineOpen_preimage_chartOpen π 1).isCompact
            (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated (a ⊗ₜ[k] s) := by
  rw [relSectionsBaseChange_tmul, relSectionsBaseChange_tmul, relPullbackSection_mul]
  ring

/-- **The relative E-i, chart 0** (RE-4b): the relative chart lattice `Γ(C_R, V₀ᴿ)` is a
finite `R[t]`-module for `t` acting as multiplication by `t₀ᴿ` — the field-level E-i
base-changed (`moduleFinite_aeval'_baseChange`) and transported along
`relSectionsBaseChange`. -/
theorem moduleFinite_aeval'_mulSectionEnd_relFiberCoord₀ [IsFinite π]
    (hπ : π ≫ P1.structureMap k = C.hom) :
    Module.Finite (Polynomial R) (Module.AEval'
      (Scheme.mulSectionEnd R (relFiberCoord₀ C R π))) := by
  haveI := moduleFinite_aeval'_mulLeft_fiberCoord₀ C π hπ
  haveI := AlgebraicJacobian.RigidEngine.moduleFinite_aeval'_baseChange R
    (LinearMap.mulLeft k (fiberCoord π) : Module.End k Γ(C.left, fiberChart₀ π))
  refine AlgebraicJacobian.RigidEngine.moduleFinite_aeval'_of_linearEquiv
    (LinearMap.baseChange R
      (LinearMap.mulLeft k (fiberCoord π) : Module.End k Γ(C.left, fiberChart₀ π)))
    (Scheme.mulSectionEnd R (relFiberCoord₀ C R π))
    (relSectionsBaseChange C R (isAffineOpen_preimage_chartOpen π 0).isCompact
      (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated) (fun x => ?_)
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a s =>
    rw [LinearMap.baseChange_tmul, LinearMap.mulLeft_apply]
    exact relSectionsBaseChange_mul_fiberCoord₀ C R π a s

/-- **The relative E-i, chart 1** (RE-4b). -/
theorem moduleFinite_aeval'_mulSectionEnd_relFiberCoord₁ [IsFinite π]
    (hπ : π ≫ P1.structureMap k = C.hom) :
    Module.Finite (Polynomial R) (Module.AEval'
      (Scheme.mulSectionEnd R (relFiberCoord₁ C R π))) := by
  haveI := moduleFinite_aeval'_mulLeft_fiberCoord₁ C π hπ
  haveI := AlgebraicJacobian.RigidEngine.moduleFinite_aeval'_baseChange R
    (LinearMap.mulLeft k (fiberCoord₁ π) : Module.End k Γ(C.left, fiberChart₁ π))
  refine AlgebraicJacobian.RigidEngine.moduleFinite_aeval'_of_linearEquiv
    (LinearMap.baseChange R
      (LinearMap.mulLeft k (fiberCoord₁ π) : Module.End k Γ(C.left, fiberChart₁ π)))
    (Scheme.mulSectionEnd R (relFiberCoord₁ C R π))
    (relSectionsBaseChange C R (isAffineOpen_preimage_chartOpen π 1).isCompact
      (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated) (fun x => ?_)
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a s =>
    rw [LinearMap.baseChange_tmul, LinearMap.mulLeft_apply]
    exact relSectionsBaseChange_mul_fiberCoord₁ C R π a s

/-- **Freeness of the relative section modules**: a `k`-basis of `Γ(C, V)` is an
`R`-basis of `Γ(C_R, V_R)` through `relSectionsBaseChange` (worksheet §3.1: the overlap
module of the pair is free, hence flat and projective). -/
theorem free_relSections (V : C.left.Opens) (hV : IsCompact (V : Set C.left))
    (hV' : IsQuasiSeparated (V : Set C.left)) :
    Module.Free R Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V) :=
  Module.Free.of_equiv (relSectionsBaseChange C R hV hV')

end Relative

end AlgebraicGeometry
