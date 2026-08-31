/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.GraphFibre
import AlgebraicJacobian.Curve.BaseChangeInstances
import AlgebraicJacobian.Picard.PicEtSections
import AlgebraicJacobian.RiemannRoch.ChartColength

/-!
# Evaluation at the graph section (G-D8, residue input)

For the challenge curve `C` over `k`, a field extension `K` and a `K`-point
`t : overSpec k K ⟶ C`, the section `σ_t := Over.sectionOfPoint t` of the projection
`C_K := (C ⊗ overSpec k K).left → Spec K` evaluates sections of any open `W` containing the
graph point `x_t := Over.graphPoint t` into `F := Γ(Spec K, ⊤) ≅ K`:

* `AlgebraicGeometry.graphSectionEval t hx : Γ(C_K, W) →+* F` — the evaluation `σ_t^♯`;
* `AlgebraicGeometry.graphSectionEval_algebraMap` / `bijective_graphSectionEval_algebraMap`
  — the evaluation splits the `K`-structure of `Scheme.overSectionsAlgebra` (through the
  second projection): the composite `K → Γ(C_K, W) → F` is the (bijective) canonical map
  `(ΓSpecIso K).inv`;
* `AlgebraicGeometry.ker_graphSectionEval_eq_primeIdealOf` — on an affine `W` the kernel of
  the evaluation is the prime of the graph point: the point ↔ evaluation dictionary,
  through the locality of the stalk map of `σ_t`;
* `AlgebraicGeometry.isMaximal_ker_graphSectionEval`,
  `AlgebraicGeometry.finrank_quotient_ker_graphSectionEval` — the quotient by the kernel is
  a copy of `K`: `finrank K (Γ(C_K, W) ⧸ ker σ_t^♯) = 1`.  This is the residue half of
  G-D8's degree-1 certificate (`RiemannRoch/GraphDegree.lean`): combined with the chart
  colength dictionary it reads `ord · residueDeg = 1` at the graph point.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open Module (finrank)

namespace AlgebraicGeometry

attribute [local instance] Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  {K : Type u} [Field K] [Algebra k K]

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- Any open of the fibre curve containing the graph point pulls back to everything on the
one-point test: `⊤ ≤ σ_t⁻¹ W`. -/
lemma Over.top_le_sectionOfPoint_preimage (t : overSpec k K ⟶ C)
    {W : (C ⊗ overSpec k K).left.Opens} (hx : Over.graphPoint C t ∈ W) :
    ⊤ ≤ (Over.sectionOfPoint t).left ⁻¹ᵁ W := by
  intro z _
  have hz : z = (default : (overSpec k K).left) := Subsingleton.elim _ _
  subst hz
  exact hx

/-- **Evaluation at the graph section**: pullback of sections along `σ_t` from an open `W`
containing the graph point, into `F := Γ(Spec K, ⊤)`. -/
noncomputable def graphSectionEval (t : overSpec k K ⟶ C)
    {W : (C ⊗ overSpec k K).left.Opens} (hx : Over.graphPoint C t ∈ W) :
    Γ((C ⊗ overSpec k K).left, W) →+* Γ((overSpec k K).left, ⊤) :=
  ((Over.sectionOfPoint t).left.appLE W ⊤ (Over.top_le_sectionOfPoint_preimage t hx)).hom

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- Evaluation commutes with restriction of the open. -/
lemma graphSectionEval_res (t : overSpec k K ⟶ C)
    {W W' : (C ⊗ overSpec k K).left.Opens} (hx : Over.graphPoint C t ∈ W')
    (hWW : W' ≤ W) (y : Γ((C ⊗ overSpec k K).left, W)) :
    graphSectionEval t hx
        (((C ⊗ overSpec k K).left.presheaf.map (homOfLE hWW).op).hom y)
      = graphSectionEval t (hWW hx) y := by
  rw [graphSectionEval, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

/-! ## The `K`-structure splits along the evaluation -/

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- **The evaluation splits the `K`-structure**: the composite of the structure map
`K → Γ(C_K, W)` (of `Scheme.overSectionsAlgebra`, through the second projection) with the
evaluation at the graph section is the canonical identification `(ΓSpecIso K).inv`. -/
theorem graphSectionEval_algebraMap (t : overSpec k K ⟶ C)
    {W : (C ⊗ overSpec k K).left.Opens} (hx : Over.graphPoint C t ∈ W) (r : K) :
    graphSectionEval t hx (algebraMap K Γ((C ⊗ overSpec k K).left, W) r)
      = (Scheme.ΓSpecIso (CommRingCat.of K)).inv r := by
  have hcomp : (Over.sectionOfPoint t).left ≫ (snd C (overSpec k K)).left
      = 𝟙 ((overSpec k K).left) := by
    rw [← Over.comp_left, Over.sectionOfPoint_snd]
    rfl
  have hmor : CommRingCat.ofHom
        (algebraMap K Γ((C ⊗ overSpec k K).left, W))
        ≫ (Over.sectionOfPoint t).left.appLE W ⊤
          (Over.top_le_sectionOfPoint_preimage t hx)
      = (Scheme.ΓSpecIso (CommRingCat.of K)).inv := by
    have h1 : CommRingCat.ofHom (algebraMap K Γ((C ⊗ overSpec k K).left, W))
        = (Scheme.ΓSpecIso (CommRingCat.of K)).inv
            ≫ (snd C (overSpec k K)).left.appLE ⊤ W
              (le_top.trans (Scheme.Hom.preimage_top _).ge) := rfl
    have hid : (𝟙 ((overSpec k K).left) : (overSpec k K).left ⟶ _).appLE ⊤ ⊤
          (le_top.trans (Scheme.Hom.preimage_top
            (𝟙 ((overSpec k K).left) : (overSpec k K).left ⟶ _)).ge)
        = 𝟙 Γ((overSpec k K).left, ⊤) := by
      rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
      exact (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)
    rw [h1, Category.assoc, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_congr_hom hcomp ⊤ ⊤ _
        (le_top.trans (Scheme.Hom.preimage_top _).ge),
      hid]
    exact Category.comp_id _
  exact congr($(hmor).hom r)

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- The composite `K → Γ(C_K, W) → F` is bijective. -/
theorem bijective_graphSectionEval_algebraMap (t : overSpec k K ⟶ C)
    {W : (C ⊗ overSpec k K).left.Opens} (hx : Over.graphPoint C t ∈ W) :
    Function.Bijective ((graphSectionEval t hx).comp
      (algebraMap K Γ((C ⊗ overSpec k K).left, W))) := by
  have h : ((graphSectionEval t hx).comp
        (algebraMap K Γ((C ⊗ overSpec k K).left, W)) : K → Γ((overSpec k K).left, ⊤))
      = ⇑(Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := by
    funext r
    exact graphSectionEval_algebraMap t hx r
  rw [h]
  exact (ConcreteCategory.isIso_iff_bijective
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv).mp inferInstance

/-- The target of the evaluation is a field (a copy of `K`). -/
lemma isField_sections_top_overSpec :
    IsField Γ((overSpec k K).left, ⊤) :=
  (Over.overSpecΓTopAlgEquiv k K).toMulEquiv.isField (Field.toIsField K)

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- The evaluation is surjective. -/
theorem surjective_graphSectionEval (t : overSpec k K ⟶ C)
    {W : (C ⊗ overSpec k K).left.Opens} (hx : Over.graphPoint C t ∈ W) :
    Function.Surjective (graphSectionEval t hx) := fun y => by
  obtain ⟨r, hr⟩ := (bijective_graphSectionEval_algebraMap t hx).2 y
  exact ⟨algebraMap K Γ((C ⊗ overSpec k K).left, W) r, hr⟩

/-! ## The kernel of the evaluation is the prime of the graph point -/

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- **The point ↔ evaluation dictionary**: on an affine open `W` containing the graph
point, the kernel of the evaluation at the graph section is the prime ideal of the graph
point.  Both inclusions go through the locality of the stalk map of `σ_t`: a section is a
unit at `x_t` exactly when its evaluation is nonzero in the field `F`. -/
theorem ker_graphSectionEval_eq_primeIdealOf (t : overSpec k K ⟶ C)
    {W : (C ⊗ overSpec k K).left.Opens} (hW : IsAffineOpen W)
    (hx : Over.graphPoint C t ∈ W) :
    RingHom.ker (graphSectionEval t hx)
      = (hW.primeIdealOf ⟨Over.graphPoint C t, hx⟩).asIdeal := by
  letI : Algebra Γ((C ⊗ overSpec k K).left, W)
      ((C ⊗ overSpec k K).left.presheaf.stalk (Over.graphPoint C t)) :=
    (C ⊗ overSpec k K).left.presheaf.algebra_section_stalk ⟨Over.graphPoint C t, hx⟩
  haveI hloc : IsLocalization.AtPrime
      ((C ⊗ overSpec k K).left.presheaf.stalk (Over.graphPoint C t))
      (hW.primeIdealOf ⟨Over.graphPoint C t, hx⟩).asIdeal :=
    hW.isLocalization_stalk ⟨Over.graphPoint C t, hx⟩
  have hgerm : ∀ f : Γ((C ⊗ overSpec k K).left, W),
      ¬ IsUnit (((C ⊗ overSpec k K).left.presheaf.germ W (Over.graphPoint C t) hx).hom f)
        ↔ f ∈ (hW.primeIdealOf ⟨Over.graphPoint C t, hx⟩).asIdeal := by
    intro f
    rw [show ((C ⊗ overSpec k K).left.presheaf.germ W (Over.graphPoint C t) hx).hom f
        = algebraMap Γ((C ⊗ overSpec k K).left, W)
            ((C ⊗ overSpec k K).left.presheaf.stalk (Over.graphPoint C t)) f from rfl,
      IsLocalization.AtPrime.isUnit_to_map_iff
        ((C ⊗ overSpec k K).left.presheaf.stalk (Over.graphPoint C t))
        (hW.primeIdealOf ⟨Over.graphPoint C t, hx⟩).asIdeal f]
    exact not_not
  -- the germ of the evaluated section on the one-point test
  have hstalk : ∀ f : Γ((C ⊗ overSpec k K).left, W),
      ((overSpec k K).left.presheaf.germ ⊤ default trivial).hom (graphSectionEval t hx f)
        = ((Over.sectionOfPoint t).left.stalkMap default).hom
            (((C ⊗ overSpec k K).left.presheaf.germ W (Over.graphPoint C t) hx).hom f) := by
    intro f
    have h1 : graphSectionEval t hx f
        = ((overSpec k K).left.presheaf.map
            (homOfLE (Over.top_le_sectionOfPoint_preimage t hx)).op).hom
            (((Over.sectionOfPoint t).left.app W).hom f) := rfl
    rw [h1, TopCat.Presheaf.germ_res_apply]
    exact ((Over.sectionOfPoint t).left.germ_stalkMap_apply W default hx f).symm
  refine le_antisymm ?_ ?_
  · -- `ε f = 0 → f ∈ p`: the stalk map preserves units
    intro f hf
    rw [RingHom.mem_ker] at hf
    rw [← hgerm f]
    intro hunit
    have h1 : IsUnit (((overSpec k K).left.presheaf.germ ⊤ default trivial).hom
        (graphSectionEval t hx f)) := by
      rw [hstalk f]
      exact hunit.map ((Over.sectionOfPoint t).left.stalkMap default).hom
    rw [hf, map_zero] at h1
    exact not_isUnit_zero h1
  · -- `f ∈ p → ε f = 0`: the target is a field and the stalk map reflects units
    intro f hf
    rw [RingHom.mem_ker]
    by_contra hne
    have hFunit : IsUnit (graphSectionEval t hx f) := by
      letI : Field Γ((overSpec k K).left, ⊤) := isField_sections_top_overSpec.toField
      exact isUnit_iff_ne_zero.mpr hne
    have h1 : IsUnit (((Over.sectionOfPoint t).left.stalkMap default).hom
        (((C ⊗ overSpec k K).left.presheaf.germ W (Over.graphPoint C t) hx).hom f)) := by
      rw [← hstalk f]
      exact hFunit.map ((overSpec k K).left.presheaf.germ ⊤ default trivial).hom
    have h2 : IsUnit (((C ⊗ overSpec k K).left.presheaf.germ W
        (Over.graphPoint C t) hx).hom f) :=
      isUnit_of_map_unit ((Over.sectionOfPoint t).left.stalkMap default).hom _ h1
    exact ((hgerm f).mpr hf) h2

/-! ## The quotient by the kernel is a copy of `K` -/

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- The quotient of the chart by the kernel of the evaluation has `K`-dimension one. -/
theorem finrank_quotient_ker_graphSectionEval (t : overSpec k K ⟶ C)
    {W : (C ⊗ overSpec k K).left.Opens} (hx : Over.graphPoint C t ∈ W) :
    finrank K (Γ((C ⊗ overSpec k K).left, W)
        ⧸ RingHom.ker (graphSectionEval t hx)) = 1 := by
  set F := Γ((overSpec k K).left, ⊤)
  set χ : K →+* F :=
    (graphSectionEval t hx).comp (algebraMap K Γ((C ⊗ overSpec k K).left, W)) with hχ
  letI : Algebra K F := χ.toAlgebra
  -- the evaluation as a `K`-algebra homomorphism
  set εa : Γ((C ⊗ overSpec k K).left, W) →ₐ[K] F :=
    { toRingHom := graphSectionEval t hx, commutes' := fun r => rfl } with hεa
  have hker : RingHom.ker εa = RingHom.ker (graphSectionEval t hx) := rfl
  have hsurj : Function.Surjective εa := surjective_graphSectionEval t hx
  have e1 : (Γ((C ⊗ overSpec k K).left, W) ⧸ RingHom.ker εa) ≃ₐ[K] F :=
    Ideal.quotientKerAlgEquivOfSurjective hsurj
  have e2 : K ≃ₗ[K] F :=
    LinearEquiv.ofBijective (Algebra.linearMap K F)
      (bijective_graphSectionEval_algebraMap t hx)
  calc finrank K (Γ((C ⊗ overSpec k K).left, W) ⧸ RingHom.ker (graphSectionEval t hx))
      = finrank K F := by rw [← hker]; exact e1.toLinearEquiv.finrank_eq
    _ = finrank K K := e2.symm.finrank_eq
    _ = 1 := Module.finrank_self K

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- The kernel of the evaluation is a maximal ideal (the quotient is a field). -/
theorem isMaximal_ker_graphSectionEval (t : overSpec k K ⟶ C)
    {W : (C ⊗ overSpec k K).left.Opens} (hx : Over.graphPoint C t ∈ W) :
    (RingHom.ker (graphSectionEval t hx)).IsMaximal := by
  have hfield : IsField (Γ((C ⊗ overSpec k K).left, W)
      ⧸ RingHom.ker (graphSectionEval t hx)) := by
    have e : (Γ((C ⊗ overSpec k K).left, W)
        ⧸ RingHom.ker (graphSectionEval t hx)) ≃+* Γ((overSpec k K).left, ⊤) :=
      RingHom.quotientKerEquivOfSurjective (surjective_graphSectionEval t hx)
    exact e.toMulEquiv.isField isField_sections_top_overSpec
  exact Ideal.Quotient.maximal_of_isField _ hfield

end AlgebraicGeometry
