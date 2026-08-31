/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffKit
import AlgebraicJacobian.Picard.DivisorFamilyZarFunctor

/-!
# Conditional final packaging of divisor representability

DDR-9.F7 has two logically separate parts: lifting the affine equivalences to arbitrary
tests, and packaging the resulting natural equivalences as a `RepresentableBy` datum.
This file formalizes the second part.  `DivRepGlobalData` records the general-test
pullback, classification map, inverse laws, and naturality.  Its `representableBy`
constructor is the final categorical packaging.

The affine-to-general lift is intentionally not assumed to exist implicitly: a caller
must provide every field of `DivRepGlobalData`.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Grassmannian Scheme

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftDivRepKit :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant pi]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : ℕ)
variable (b1 : Module.Basis (Fin r1) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

local notation "DivOver" =>
  divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm)

/-- The exact general-test data needed for the final F7 packaging.  In the intended
construction, `pull` is assembled from the affine forward maps and `classify` by
gluing the affine backward classifiers. -/
structure DivRepGlobalData where
  pull : ∀ {T : Over (Spec (CommRingCat.of k))},
    (T ⟶ DivOver) → divFamZar C pi g T
  classify : ∀ {T : Over (Spec (CommRingCat.of k))},
    divFamZar C pi g T → (T ⟶ DivOver)
  classify_pull : ∀ {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ DivOver),
    classify (pull v) = v
  pull_classify : ∀ {T : Over (Spec (CommRingCat.of k))} (F : divFamZar C pi g T),
    pull (classify F) = F
  pull_comp : ∀ {T T' : Over (Spec (CommRingCat.of k))} (f : T' ⟶ T)
    (v : T ⟶ DivOver),
    pull (f ≫ v) = divFamZar.map C pi g f (pull v)

namespace DivRepGlobalData

/-- The general-test equivalence underlying the represented functor. -/
noncomputable def equiv
    (D : DivRepGlobalData hpi g r1 r2 b1 b2)
    (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ DivOver) ≃ divFamZar C pi g T where
  toFun := D.pull
  invFun := D.classify
  left_inv := D.classify_pull
  right_inv := D.pull_classify

set_option linter.unusedSectionVars false in
@[simp]
theorem equiv_apply
    (D : DivRepGlobalData hpi g r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ DivOver) :
    equiv (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) D T v
      = D.pull v :=
  rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem equiv_symm_apply
    (D : DivRepGlobalData hpi g r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZar C pi g T) :
    (equiv (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) D T).symm F
      = D.classify F :=
  rfl

/-- The final F7 categorical packaging: natural general-test pullback equivalences
represent the locally certified divisor functor by `DivScheme`. -/
noncomputable def representableBy
    (D : DivRepGlobalData hpi g r1 r2 b1 b2) :
    (divFunctor C pi g).RepresentableBy DivOver where
  homEquiv {T} :=
    equiv (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) D T
  homEquiv_comp {T T'} f v := by
    change D.pull (f ≫ v) = divFamZar.map C pi g f (D.pull v)
    exact D.pull_comp f v

set_option linter.unusedSectionVars false in
@[simp]
theorem representableBy_homEquiv_apply
    (D : DivRepGlobalData hpi g r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ DivOver) :
    (representableBy (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1)
      (b2 := b2) D).homEquiv v = D.pull v :=
  rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem representableBy_homEquiv_symm_apply
    (D : DivRepGlobalData hpi g r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZar C pi g T) :
    (representableBy (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1)
      (b2 := b2) D).homEquiv.symm F = D.classify F :=
  rfl

end DivRepGlobalData

end Curve

end AlgebraicGeometry
