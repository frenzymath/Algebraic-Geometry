/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.TwoLattice
import AlgebraicJacobian.RiemannRoch.Ledger.FinitenessP1
import AlgebraicJacobian.RiemannRoch.Ledger.TwoCover
import AlgebraicJacobian.RiemannRoch.Ledger.MapToP1

/-!
# Finiteness of `H¹(X, 𝒪_X)` via a finite morphism to the projective line

For a scheme `X` over `Spec k` equipped with a **finite** `k`-morphism `π : X ⟶ ℙ¹`, this
file proves that the degree-one cohomology of the structure sheaf of `X` (as a sheaf of
`k`-modules on the small Zariski site, `Sheaf.HModule`) is a finite `k`-module — and derives
the instance for the smooth proper geometrically irreducible curve of the challenge, so that
`genus` is the dimension of an honestly finite-dimensional vector space.

The proof is the *two-lattice ladder* of `AlgebraicJacobian.Algebra.TwoLattice` run on the
Mayer–Vietoris cokernel of `AlgebraicJacobian.Cohomology.TwoCover`:

* `V i := π ⁻¹ᵁ D₊(Xᵢ)` is an affine open cover of `X`
  (`isAffineOpen_preimage_chartOpen`, `preimage_chartOpen_sup`), so
  `H¹ₖ(X, 𝒪) ≃ₗ[k] Γ(V₀ ⊓ V₁) ⧸ range (res₀ - res₁)` (`TwoCover.h1CokEquiv`);
* `N := Γ(X, V₀ ⊓ V₁)` is a module over the Laurent polynomial ring `k[T;T⁻¹]` through
  `π`'s map on sections over the chart overlap and the identification
  `Γ(ℙ¹, D₊(X₀X₁)) ≃ k[T,T⁻¹]` (`P1.overlapSectionsEquiv`); it is module-finite because `π`
  is finite (`finite_app_overlap`);
* `Q₀, Q₁ :=` the images of `Γ(V₀), Γ(V₁)` in `N` are `k`-submodules with
  `range (res₀ - res₁) = Q₀ ⊔ Q₁`; `Q₀` is stable under `T` because `T` is the restriction
  of the chart-0 coordinate, which extends to `V₀` (symmetrically for `Q₁` and `T⁻¹`); and
  `V₀ ⊓ V₁` is the basic open of the pulled-back chart coordinate inside the affine `V₀`
  (`P1.basicOpen_awayToSection_chartCoord`), so
  `IsAffineOpen.isLocalization_of_eq_basicOpen` provides the surjectivity-up-to-powers
  hypotheses of the two-lattice lemma.

The `ℙ¹`-side identifications live in `AlgebraicJacobian.Cohomology.FinitenessP1`.

## Main declarations

* `AlgebraicGeometry.moduleFinite_hModule_one_of_isFinite_toP1` — **the conditional
  finiteness theorem**: if `π : X ⟶ ℙ¹` is finite with `π ≫ P1.structureMap k = X ↘ Spec k`,
  then `Module.Finite k (H¹ₖ(X, 𝒪_X))`.
* `AlgebraicGeometry.moduleFinite_hModule_one` — the instance for the challenge curve
  `C` (smooth, proper, geometrically irreducible over `k`), consuming
  `exists_isFinite_toP1`; it is keyed on exactly the `letI : C.left.Over (Spec (.of k))`
  spelling used by `genus` in `AlgebraicJacobian.Challenge`.

`FiniteDimensional k (H¹ₖ(C, 𝒪_C))` is *definitionally* the statement of the instance
(`FiniteDimensional` is an abbreviation for `Module.Finite`), so no separate corollary is
needed.
-/

set_option autoImplicit false
/- Scheme-theoretic unification (mixing `P1 k` with `Proj 𝒜`, `Γ(X, U)` with functor
applications) needs defeq checks through semireducible definitions, as in mathlib's own
algebraic-geometry files. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry


section Glue

/-! ### The geometric glue: the two-lattice ladder on the chart-preimage cover -/

variable {k : Type u} [Field k]

/-- The standard grading of `k[X₀, X₁]`, the graded ring underlying `P1 k`. -/
local notation "𝒜" => homogeneousSubmodule (Fin 2) k

attribute [local instance] Scheme.overModule

variable {Y : Scheme.{u}} (π : Y ⟶ P1 k)

private lemma preimage_overlap_eq :
    π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1 =
      π ⁻¹ᵁ Proj.basicOpen 𝒜 (X 0 * X 1) := by
  rw [← Scheme.Hom.preimage_inf, P1.chartOpen_inf k]

private lemma preimage_overlap_le :
    π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1 ≤
      π ⁻¹ᵁ Proj.basicOpen 𝒜 (X 0 * X 1) :=
  (preimage_overlap_eq π).le

/-- The `k[T;T⁻¹]`-algebra structure map on the sections of the chart-preimage overlap:
`π`'s map on sections over `D₊(X₀X₁)` composed with the Laurent identification. Only used
as a local `Algebra` instance inside the finiteness argument. -/
private noncomputable def overlapLaurentHom :
    LaurentPolynomial k →+* Γ(Y, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) :=
  ((π.appLE (Proj.basicOpen 𝒜 (X 0 * X 1)) _ (preimage_overlap_le π)).hom).comp
    (P1.overlapSectionsEquiv k).symm.toRingHom

/-- `T` acts on the overlap sections as multiplication by the restriction of the
pulled-back chart-0 coordinate, which extends to `π ⁻¹ᵁ D₊(X₀)`. -/
private lemma overlapLaurentHom_T_one :
    overlapLaurentHom π (LaurentPolynomial.T 1) =
      (Y.presheaf.map (homOfLE (inf_le_left : _ ⊓ _ ≤ π ⁻¹ᵁ P1.chartOpen k 0)).op).hom
        ((π.app (P1.chartOpen k 0)).hom
          ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1))) := by
  change (π.appLE (Proj.basicOpen 𝒜 (X 0 * X 1)) _ (preimage_overlap_le π)).hom
      ((P1.overlapSectionsEquiv k).symm (LaurentPolynomial.T 1)) = _
  rw [P1.overlapSectionsEquiv_symm_T]
  calc (π.appLE (Proj.basicOpen 𝒜 (X 0 * X 1)) _ (preimage_overlap_le π)).hom
        (((P1 k).presheaf.map (homOfLE (P1.overlap_le_left k)).op).hom
          ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1)))
      = ((P1 k).presheaf.map (homOfLE (P1.overlap_le_left k)).op ≫
          π.appLE (Proj.basicOpen 𝒜 (X 0 * X 1)) _ (preimage_overlap_le π)).hom
          ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1)) := rfl
    _ = (π.appLE (P1.chartOpen k 0) _ ((preimage_overlap_le π).trans
          ((Opens.map π.base).map (homOfLE (P1.overlap_le_left k))).le)).hom
          ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1)) := by
        rw [Scheme.Hom.map_appLE]
    _ = (π.app (P1.chartOpen k 0) ≫
          Y.presheaf.map (homOfLE (inf_le_left : _ ⊓ _ ≤ π ⁻¹ᵁ P1.chartOpen k 0)).op).hom
          ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1)) := by
        rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
    _ = _ := rfl

/-- `T⁻¹` acts on the overlap sections as multiplication by the restriction of the
pulled-back chart-1 coordinate, which extends to `π ⁻¹ᵁ D₊(X₁)`. -/
private lemma overlapLaurentHom_T_neg_one :
    overlapLaurentHom π (LaurentPolynomial.T (-1)) =
      (Y.presheaf.map (homOfLE (inf_le_right : _ ⊓ _ ≤ π ⁻¹ᵁ P1.chartOpen k 1)).op).hom
        ((π.app (P1.chartOpen k 1)).hom
          ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0))) := by
  change (π.appLE (Proj.basicOpen 𝒜 (X 0 * X 1)) _ (preimage_overlap_le π)).hom
      ((P1.overlapSectionsEquiv k).symm (LaurentPolynomial.T (-1))) = _
  rw [P1.overlapSectionsEquiv_symm_T_neg]
  calc (π.appLE (Proj.basicOpen 𝒜 (X 0 * X 1)) _ (preimage_overlap_le π)).hom
        (((P1 k).presheaf.map (homOfLE (P1.overlap_le_right k)).op).hom
          ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0)))
      = ((P1 k).presheaf.map (homOfLE (P1.overlap_le_right k)).op ≫
          π.appLE (Proj.basicOpen 𝒜 (X 0 * X 1)) _ (preimage_overlap_le π)).hom
          ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0)) := rfl
    _ = (π.appLE (P1.chartOpen k 1) _ ((preimage_overlap_le π).trans
          ((Opens.map π.base).map (homOfLE (P1.overlap_le_right k))).le)).hom
          ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0)) := by
        rw [Scheme.Hom.map_appLE]
    _ = (π.app (P1.chartOpen k 1) ≫
          Y.presheaf.map (homOfLE (inf_le_right : _ ⊓ _ ≤ π ⁻¹ᵁ P1.chartOpen k 1)).op).hom
          ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0)) := by
        rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
    _ = _ := rfl

/-- The Laurent algebra structure map is compatible with the structure algebra map of `Y`
over `k`. This is the input for the `IsScalarTower k k[T;T⁻¹] Γ(Y, V₀ ⊓ V₁)` instance. -/
private lemma overlapLaurentHom_algebraMap [Y.Over (Spec (.of k))]
    (hπ : π ≫ P1.structureMap k = Y ↘ Spec (.of k)) (r : k) :
    overlapLaurentHom π (algebraMap k (LaurentPolynomial k) r) =
      Y.overAlgebraMap k (π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) r := by
  letI : (P1 k).Over (Spec (.of k)) := ⟨P1.structureMap k⟩
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (P1.structureMap k).appTop ≫
      (P1 k).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 (X 0 * X 1) ≤ ⊤)).op =
      CommRingCat.ofHom (algebraMap k (Away 𝒜 (X 0 * X 1))) ≫
        Proj.awayToSection 𝒜 (X 0 * X 1) := by
    rw [P1.structureMap_appTop_awayToSection k (P1.X_mul_X_mem k) two_pos,
      Iso.inv_hom_id_assoc]
  have hPA : (P1 k).overAlgebraMap k (Proj.basicOpen 𝒜 (X 0 * X 1)) r =
      (Proj.awayToSection 𝒜 (X 0 * X 1)).hom (algebraMap k (Away 𝒜 (X 0 * X 1)) r) :=
    congr((CommRingCat.Hom.hom $hcomp) r)
  have hLHS := π.appLE_overAlgebraMap hπ (preimage_overlap_le π) r
  change (π.appLE (Proj.basicOpen 𝒜 (X 0 * X 1)) _ (preimage_overlap_le π)).hom
      ((P1.overlapSectionsEquiv k).symm (algebraMap k (LaurentPolynomial k) r)) = _
  rw [P1.overlapSectionsEquiv_symm_algebraMap, ← hPA]
  exact hLHS

/-- The chart-preimage overlap is the basic open of the pulled-back chart-0 coordinate. -/
private lemma preimage_inf_eq_basicOpen_left :
    π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1 =
      Y.basicOpen ((π.app (P1.chartOpen k 0)).hom
        ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1))) := by
  have h : π ⁻¹ᵁ ((P1 k).basicOpen
        ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1))) =
      Y.basicOpen ((π.app (P1.chartOpen k 0)).hom
        ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1))) :=
    Scheme.preimage_basicOpen π _
  rw [P1.basicOpen_awayToSection_chartCoord k 0 1, Scheme.Hom.preimage_inf] at h
  exact h

/-- The chart-preimage overlap is the basic open of the pulled-back chart-1 coordinate. -/
private lemma preimage_inf_eq_basicOpen_right :
    π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1 =
      Y.basicOpen ((π.app (P1.chartOpen k 1)).hom
        ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0))) := by
  have h : π ⁻¹ᵁ ((P1 k).basicOpen
        ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0))) =
      Y.basicOpen ((π.app (P1.chartOpen k 1)).hom
        ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0))) :=
    Scheme.preimage_basicOpen π _
  rw [P1.basicOpen_awayToSection_chartCoord k 1 0, Scheme.Hom.preimage_inf] at h
  rw [← h, inf_comm]

variable (U₀ U₁ : Y.Opens)

variable (k) in
/-- The `k`-linear restriction map `Γ(Y, U₀) →ₗ[k] Γ(Y, U₀ ⊓ U₁)`, with the
`Scheme.overModule` structures (the left leg of the Mayer–Vietoris difference map). -/
private noncomputable def resLeft [Y.Over (Spec (.of k))] :
    Γ(Y, U₀) →ₗ[k] Γ(Y, U₀ ⊓ U₁) :=
  ((Y.moduleKSheaf k).obj.map (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op).hom

variable (k) in
/-- The `k`-linear restriction map `Γ(Y, U₁) →ₗ[k] Γ(Y, U₀ ⊓ U₁)`, with the
`Scheme.overModule` structures (the right leg of the Mayer–Vietoris difference map). -/
private noncomputable def resRight [Y.Over (Spec (.of k))] :
    Γ(Y, U₁) →ₗ[k] Γ(Y, U₀ ⊓ U₁) :=
  ((Y.moduleKSheaf k).obj.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op).hom

variable {U₀ U₁} in
/-- The restriction-difference map of the two-cover has range `Q₀ ⊔ Q₁`, the join of the
images of the two restriction maps. -/
private lemma range_diff_eq [Y.Over (Spec (.of k))] :
    LinearMap.range (TwoCover.diff k Y U₀ U₁) =
      LinearMap.range (resLeft k (Y := Y) U₀ U₁) ⊔
        LinearMap.range (resRight k (Y := Y) U₀ U₁) := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro x ⟨t, rfl⟩
    rw [TwoCover.diff_apply]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨t.1, rfl⟩)
      (Submodule.mem_sup_right ⟨t.2, rfl⟩)
  · rintro x ⟨s, rfl⟩
    refine ⟨(s, 0), ?_⟩
    rw [TwoCover.diff_apply]
    change Y.resHom inf_le_left s - Y.resHom inf_le_right 0 = Y.resHom inf_le_left s
    rw [map_zero, sub_zero]
  · rintro x ⟨s, rfl⟩
    refine ⟨(0, -s), ?_⟩
    rw [TwoCover.diff_apply]
    change Y.resHom inf_le_left 0 - Y.resHom inf_le_right (-s) = Y.resHom inf_le_right s
    rw [map_zero, map_neg, zero_sub, neg_neg]

/-- **The two-lattice ladder on the chart-preimage cover**: for a finite `π : Y ⟶ ℙ¹` over
`Spec k`, the Mayer–Vietoris cokernel of the affine cover `π⁻¹D₊(X₀), π⁻¹D₊(X₁)` is a
finite `k`-module. -/
private theorem moduleFinite_h1Cok [Y.Over (Spec (.of k))] [IsFinite π]
    (hπ : π ≫ P1.structureMap k = Y ↘ Spec (.of k)) :
    Module.Finite k
      (TwoCover.H1Cok k Y (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)) := by
  classical
  have hV₀ : IsAffineOpen (π ⁻¹ᵁ P1.chartOpen k 0) := isAffineOpen_preimage_chartOpen π 0
  have hV₁ : IsAffineOpen (π ⁻¹ᵁ P1.chartOpen k 1) := isAffineOpen_preimage_chartOpen π 1
  -- the Laurent module structure on the overlap sections
  letI : Algebra (LaurentPolynomial k)
      Γ(Y, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) :=
    (overlapLaurentHom π).toAlgebra
  -- the compatible `k`-structure
  haveI : IsScalarTower k (LaurentPolynomial k)
      Γ(Y, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) := by
    refine ⟨fun a b n => ?_⟩
    rw [Algebra.smul_def ((a • b : LaurentPolynomial k)) n, Algebra.smul_def b n,
      Scheme.overModule_smul_def, RingHom.algebraMap_toAlgebra, Algebra.smul_def a b,
      map_mul, overlapLaurentHom_algebraMap π hπ, mul_assoc]
  -- module-finiteness over the Laurent polynomials, from finiteness of `π`
  haveI : Module.Finite (LaurentPolynomial k)
      Γ(Y, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) := by
    have h1 : ((Y.presheaf.map (homOfLE (preimage_overlap_le π)).op).hom).Finite := by
      refine RingHom.Finite.of_surjective _ ?_
      rw [show homOfLE (preimage_overlap_le π) = eqToHom (preimage_overlap_eq π) from
        Subsingleton.elim _ _]
      exact ((ConcreteCategory.isIso_iff_bijective
        (Y.presheaf.map (eqToHom (preimage_overlap_eq π)).op)).mp inferInstance).2
    have h2 : ((π.appLE (Proj.basicOpen 𝒜 (X 0 * X 1)) _
        (preimage_overlap_le π)).hom).Finite :=
      h1.comp (finite_app_overlap π)
    exact h2.comp (P1.overlapSectionsEquiv k).symm.finite
  -- `Q₀` is stable under `T`
  have hstab₀ : ∀ x ∈ LinearMap.range (resLeft k (Y := Y)
        (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)),
      (LaurentPolynomial.T 1 : LaurentPolynomial k) • x ∈
        LinearMap.range (resLeft k (Y := Y)
          (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)) := by
    rintro x ⟨s, rfl⟩
    refine ⟨(π.app (P1.chartOpen k 0)).hom
      ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1)) * s, ?_⟩
    change (Y.presheaf.map (homOfLE inf_le_left).op).hom
        ((π.app (P1.chartOpen k 0)).hom
          ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1)) * s) = _
    rw [map_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra, overlapLaurentHom_T_one]
    rfl
  -- `Q₁` is stable under `T⁻¹`
  have hstab₁ : ∀ x ∈ LinearMap.range (resRight k (Y := Y)
        (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)),
      (LaurentPolynomial.T (-1) : LaurentPolynomial k) • x ∈
        LinearMap.range (resRight k (Y := Y)
          (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)) := by
    rintro x ⟨s, rfl⟩
    refine ⟨(π.app (P1.chartOpen k 1)).hom
      ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0)) * s, ?_⟩
    change (Y.presheaf.map (homOfLE inf_le_right).op).hom
        ((π.app (P1.chartOpen k 1)).hom
          ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0)) * s) = _
    rw [map_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      overlapLaurentHom_T_neg_one]
    rfl
  -- surjectivity up to powers of `T` towards `Q₀`
  have hloc₀ : ∀ n : Γ(Y, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1),
      ∃ m : ℕ, ((LaurentPolynomial.T 1 : LaurentPolynomial k) ^ m) • n ∈
        LinearMap.range (resLeft k (Y := Y)
          (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)) := by
    intro n
    have key : ∃ (m : ℕ) (a : Γ(Y, π ⁻¹ᵁ P1.chartOpen k 0)),
        n * ((Y.presheaf.map (homOfLE inf_le_left).op).hom
            ((π.app (P1.chartOpen k 0)).hom
              ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1)))) ^ m =
          (Y.presheaf.map (homOfLE inf_le_left).op).hom a := by
      letI : Algebra Γ(Y, π ⁻¹ᵁ P1.chartOpen k 0)
          Γ(Y, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) :=
        ((Y.presheaf.map (homOfLE inf_le_left).op).hom).toAlgebra
      haveI := hV₀.isLocalization_of_eq_basicOpen
        ((π.app (P1.chartOpen k 0)).hom
          ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1)))
        (homOfLE inf_le_left) (preimage_inf_eq_basicOpen_left π)
      obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj
        ((π.app (P1.chartOpen k 0)).hom
          ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord k 0 1))) n
      rw [RingHom.algebraMap_toAlgebra] at ha
      exact ⟨m, a, ha⟩
    obtain ⟨m, a, ha⟩ := key
    refine ⟨m, a, ?_⟩
    change (Y.presheaf.map (homOfLE inf_le_left).op).hom a = _
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow, overlapLaurentHom_T_one,
      ← ha, mul_comm]
  -- surjectivity up to powers of `T⁻¹` towards `Q₁`
  have hloc₁ : ∀ n : Γ(Y, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1),
      ∃ m : ℕ, ((LaurentPolynomial.T (-1) : LaurentPolynomial k) ^ m) • n ∈
        LinearMap.range (resRight k (Y := Y)
          (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)) := by
    intro n
    have key : ∃ (m : ℕ) (a : Γ(Y, π ⁻¹ᵁ P1.chartOpen k 1)),
        n * ((Y.presheaf.map (homOfLE inf_le_right).op).hom
            ((π.app (P1.chartOpen k 1)).hom
              ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0)))) ^ m =
          (Y.presheaf.map (homOfLE inf_le_right).op).hom a := by
      letI : Algebra Γ(Y, π ⁻¹ᵁ P1.chartOpen k 1)
          Γ(Y, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) :=
        ((Y.presheaf.map (homOfLE inf_le_right).op).hom).toAlgebra
      haveI := hV₁.isLocalization_of_eq_basicOpen
        ((π.app (P1.chartOpen k 1)).hom
          ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0)))
        (homOfLE inf_le_right) (preimage_inf_eq_basicOpen_right π)
      obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj
        ((π.app (P1.chartOpen k 1)).hom
          ((Proj.awayToSection 𝒜 (X 1)).hom (P1.chartCoord k 1 0))) n
      rw [RingHom.algebraMap_toAlgebra] at ha
      exact ⟨m, a, ha⟩
    obtain ⟨m, a, ha⟩ := key
    refine ⟨m, a, ?_⟩
    change (Y.presheaf.map (homOfLE inf_le_right).op).hom a = _
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow,
      overlapLaurentHom_T_neg_one, ← ha, mul_comm]
  -- run the two-lattice ladder and transport to the cokernel
  haveI hquot := LaurentPolynomial.moduleFinite_quotient_sup_of_exists_pow_smul_mem
    hstab₀ hstab₁ hloc₀ hloc₁
  exact Module.Finite.equiv (Submodule.quotEquivOfEq _ _
    (range_diff_eq (U₀ := π ⁻¹ᵁ P1.chartOpen k 0) (U₁ := π ⁻¹ᵁ P1.chartOpen k 1)).symm)

end Glue

section Main

variable {k : Type u} [Field k]

/-- **Finiteness of `H¹` along a finite map to the projective line** (the conditional
form, quantified over the finite morphism): let `X` be a scheme over `Spec k` and
`π : X ⟶ ℙ¹` a finite morphism with `π ≫ P1.structureMap k = X ↘ Spec k`. Then the
degree-one cohomology of the structure sheaf of `X` as a sheaf of `k`-modules on the small
Zariski site is a finite `k`-module. -/
theorem moduleFinite_hModule_one_of_isFinite_toP1 {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (π : X ⟶ P1 k) [IsFinite π] (hπ : π ≫ P1.structureMap k = X ↘ Spec (.of k)) :
    Module.Finite k (Sheaf.HModule (X.moduleKSheaf k) 1) := by
  haveI := moduleFinite_h1Cok π hπ
  exact Module.Finite.equiv
    (TwoCover.h1CokEquiv k X (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)
      (preimage_chartOpen_sup π) (isAffineOpen_preimage_chartOpen π 0)
      (isAffineOpen_preimage_chartOpen π 1)).symm

/-- **Finiteness of `H¹(C, 𝒪_C)` for the challenge curve**: for a smooth, proper,
geometrically irreducible curve `C` over the field `k`, the degree-one cohomology of the
structure sheaf is a finite-dimensional `k`-vector space. This is the instance making
`AlgebraicGeometry.genus` the dimension of an honestly finite-dimensional space; it is
keyed on the same `letI : C.left.Over (Spec (.of k))` spelling used by `genus`. -/
instance moduleFinite_hModule_one (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) := by
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  obtain ⟨π, hfin, hcomp⟩ := exists_isFinite_toP1 (C := C)
  haveI := hfin
  exact moduleFinite_hModule_one_of_isFinite_toP1 π hcomp

end Main

end AlgebraicGeometry
