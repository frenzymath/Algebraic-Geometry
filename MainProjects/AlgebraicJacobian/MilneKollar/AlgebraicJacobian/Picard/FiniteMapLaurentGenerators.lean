/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.TwistedProjectiveCoordinates
import AlgebraicJacobian.RiemannRoch.Adelic.FinitenessP1

/-!
# Aligned generators for a finite map over two Laurent charts

For a finite morphism C -> Y and Laurent chart data on Y, the two inverse
images of the standard charts are affine. Their section rings are finite
modules over the corresponding chart rings of Y.

This file applies TwoChart.exists_uniform_twisted_generators to those two
finite modules. It produces one positive twist and finite generating families
whose restrictions agree up to the common Laurent transition factor. The
result is stated entirely in the source section rings, in the exact form
consumed by TwistedCoordinates.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Adelic

variable {k : Type u} [Field k]
variable {Y C : Over (Spec (CommRingCat.of k))}

/-- The pullback of the first Laurent coordinate to the first source chart. -/
def LaurentChartData.pullbackX (D : LaurentChartData Y) (pi : C ⟶ Y) :
    Γ(C.left, pi.left ⁻¹ᵁ D.V₀) :=
  (pi.left.app D.V₀).hom D.x

/-- The pullback of the second Laurent coordinate to the second source chart. -/
def LaurentChartData.pullbackY (D : LaurentChartData Y) (pi : C ⟶ Y) :
    Γ(C.left, pi.left ⁻¹ᵁ D.V₁) :=
  (pi.left.app D.V₁).hom D.y

/-- Restriction from the first source chart to the pulled-back overlap. -/
def LaurentChartData.sourceRestriction0 (D : LaurentChartData Y)
    (pi : C ⟶ Y) :
    Γ(C.left, pi.left ⁻¹ᵁ D.V₀) →+*
      Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) :=
  (C.left.presheaf.map
    (homOfLE (pi.left.preimage_mono
      (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀))).op).hom

/-- Restriction from the second source chart to the pulled-back overlap. -/
def LaurentChartData.sourceRestriction1 (D : LaurentChartData Y)
    (pi : C ⟶ Y) :
    Γ(C.left, pi.left ⁻¹ᵁ D.V₁) →+*
      Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) :=
  (C.left.presheaf.map
    (homOfLE (pi.left.preimage_mono
      (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁))).op).hom

/-- The pulled-back Laurent coordinates remain mutually inverse on the source
overlap. -/
theorem LaurentChartData.sourceRestriction_mul (D : LaurentChartData Y)
    (pi : C ⟶ Y) :
    D.sourceRestriction0 pi (D.pullbackX pi) *
      D.sourceRestriction1 pi (D.pullbackY pi) = 1 := by
  have h0 : D.sourceRestriction0 pi (D.pullbackX pi) =
      (pi.left.app (D.V₀ ⊓ D.V₁)).hom
        ((Y.left.presheaf.map
          (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op).hom D.x) := by
    have h := congrArg
      (fun g : Γ(Y.left, D.V₀) ⟶
          Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) => g.hom D.x)
      (pi.left.naturality
        (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op)
    exact h.symm
  have h1 : D.sourceRestriction1 pi (D.pullbackY pi) =
      (pi.left.app (D.V₀ ⊓ D.V₁)).hom
        ((Y.left.presheaf.map
          (homOfLE (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁)).op).hom D.y) := by
    have h := congrArg
      (fun g : Γ(Y.left, D.V₁) ⟶
          Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) => g.hom D.y)
      (pi.left.naturality
        (homOfLE (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁)).op)
    exact h.symm
  rw [h0, h1, ← map_mul, D.res_x_mul_res_y, map_one]

/-- Aligned source-ring generators for the two pulled-back Laurent charts. -/
structure LaurentChartData.FiniteMapGenerators (D : LaurentChartData Y)
    (pi : C ⟶ Y) : Type u where
  n0 : ℕ
  n1 : ℕ
  d : ℕ
  aa : Fin n0 ⊕ Fin n1 → Γ(C.left, pi.left ⁻¹ᵁ D.V₀)
  bb : Fin n0 ⊕ Fin n1 → Γ(C.left, pi.left ⁻¹ᵁ D.V₁)
  pos : 0 < d
  compatible : ∀ i,
    D.sourceRestriction0 pi (aa i) =
      (D.sourceRestriction0 pi (D.pullbackX pi)) ^ d *
        D.sourceRestriction1 pi (bb i)
  span0 :
    letI : Algebra Γ(Y.left, D.V₀) Γ(C.left, pi.left ⁻¹ᵁ D.V₀) :=
      RingHom.toAlgebra (pi.left.app D.V₀).hom
    Submodule.span Γ(Y.left, D.V₀) (Set.range aa) = ⊤
  span1 :
    letI : Algebra Γ(Y.left, D.V₁) Γ(C.left, pi.left ⁻¹ᵁ D.V₁) :=
      RingHom.toAlgebra (pi.left.app D.V₁).hom
    Submodule.span Γ(Y.left, D.V₁) (Set.range bb) = ⊤

/-- A finite morphism over Laurent chart data admits aligned finite source
generators after one positive common twist. No projectivity or rational-point
hypothesis is used. -/
theorem LaurentChartData.nonempty_finiteMapGenerators
    (D : LaurentChartData Y) (pi : C ⟶ Y) [IsFinite pi.left] :
    Nonempty (D.FiniteMapGenerators pi) := by
  classical
  letI iA0 : Algebra Γ(Y.left, D.V₀) Γ(C.left, pi.left ⁻¹ᵁ D.V₀) :=
    RingHom.toAlgebra (pi.left.app D.V₀).hom
  letI iA1 : Algebra Γ(Y.left, D.V₁) Γ(C.left, pi.left ⁻¹ᵁ D.V₁) :=
    RingHom.toAlgebra (pi.left.app D.V₁).hom
  letI iA01 : Algebra Γ(Y.left, D.V₀ ⊓ D.V₁)
      Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) :=
    RingHom.toAlgebra (pi.left.app (D.V₀ ⊓ D.V₁)).hom
  haveI hfin0 : Module.Finite Γ(Y.left, D.V₀)
      Γ(C.left, pi.left ⁻¹ᵁ D.V₀) :=
    pi.left.finite_app D.V₀ D.isAffineOpen_V₀
  haveI hfin1 : Module.Finite Γ(Y.left, D.V₁)
      Γ(C.left, pi.left ⁻¹ᵁ D.V₁) :=
    pi.left.finite_app D.V₁ D.isAffineOpen_V₁
  let rho0 : Γ(Y.left, D.V₀) →ₐ[ℤ] Γ(Y.left, D.V₀ ⊓ D.V₁) :=
    ((Y.left.presheaf.map
      (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op).hom).toIntAlgHom
  let rho1 : Γ(Y.left, D.V₁) →ₐ[ℤ] Γ(Y.left, D.V₀ ⊓ D.V₁) :=
    ((Y.left.presheaf.map
      (homOfLE (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁)).op).hom).toIntAlgHom
  let sigma0 : Γ(C.left, pi.left ⁻¹ᵁ D.V₀) →ₗ[ℤ]
      Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) :=
    (D.sourceRestriction0 pi).toIntAlgHom.toLinearMap
  let sigma1 : Γ(C.left, pi.left ⁻¹ᵁ D.V₁) →ₗ[ℤ]
      Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) :=
    (D.sourceRestriction1 pi).toIntAlgHom.toLinearMap
  have htu : rho0 D.x * rho1 D.y = 1 := D.res_x_mul_res_y
  have hsigma0 : ∀ (c : Γ(Y.left, D.V₀))
      (m : Γ(C.left, pi.left ⁻¹ᵁ D.V₀)),
      sigma0 (c • m) = rho0 c • sigma0 m := by
    intro c m
    change D.sourceRestriction0 pi ((pi.left.app D.V₀).hom c * m) =
      (pi.left.app (D.V₀ ⊓ D.V₁)).hom (rho0 c) *
        D.sourceRestriction0 pi m
    rw [map_mul]
    congr 1
    have h := congrArg
      (fun g : Γ(Y.left, D.V₀) ⟶
          Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) => g.hom c)
      (pi.left.naturality
        (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op)
    exact h.symm
  have hsigma1 : ∀ (c : Γ(Y.left, D.V₁))
      (m : Γ(C.left, pi.left ⁻¹ᵁ D.V₁)),
      sigma1 (c • m) = rho1 c • sigma1 m := by
    intro c m
    change D.sourceRestriction1 pi ((pi.left.app D.V₁).hom c * m) =
      (pi.left.app (D.V₀ ⊓ D.V₁)).hom (rho1 c) *
        D.sourceRestriction1 pi m
    rw [map_mul]
    congr 1
    have h := congrArg
      (fun g : Γ(Y.left, D.V₁) ⟶
          Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) => g.hom c)
      (pi.left.naturality
        (homOfLE (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁)).op)
    exact h.symm
  let t := sigma0 (D.pullbackX pi)
  let u := sigma1 (D.pullbackY pi)
  have hWx : pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁) =
      C.left.basicOpen (D.pullbackX pi) := by
    rw [D.inf_eq_basicOpen_x, Scheme.preimage_basicOpen]
    rfl
  have hWy : pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁) =
      C.left.basicOpen (D.pullbackY pi) := by
    rw [D.inf_eq_basicOpen_y, Scheme.preimage_basicOpen]
    rfl
  have ht : t = (pi.left.app (D.V₀ ⊓ D.V₁)).hom (rho0 D.x) := by
    have h := congrArg
      (fun g : Γ(Y.left, D.V₀) ⟶
          Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) => g.hom D.x)
      (pi.left.naturality
        (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op)
    exact h.symm
  have hu : u = (pi.left.app (D.V₀ ⊓ D.V₁)).hom (rho1 D.y) := by
    have h := congrArg
      (fun g : Γ(Y.left, D.V₁) ⟶
          Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) => g.hom D.y)
      (pi.left.naturality
        (homOfLE (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁)).op)
    exact h.symm
  have hext0 : ∀ v : Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)),
      ∃ (n : ℕ) (m : Γ(C.left, pi.left ⁻¹ᵁ D.V₀)),
        rho0 D.x ^ n • v = sigma0 m := by
    intro v
    obtain ⟨n, m, hm⟩ := exists_pow_mul_eq_res
      (D.isAffineOpen_V₀.preimage pi.left) (D.pullbackX pi) hWx
        (pi.left.preimage_mono inf_le_left) v
    refine ⟨n, m, ?_⟩
    change (pi.left.app (D.V₀ ⊓ D.V₁)).hom (rho0 D.x ^ n) * v =
      sigma0 m
    rw [map_pow, ← ht]
    exact hm
  have hext1 : ∀ v : Γ(C.left, pi.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)),
      ∃ (n : ℕ) (m : Γ(C.left, pi.left ⁻¹ᵁ D.V₁)),
        rho1 D.y ^ n • v = sigma1 m := by
    intro v
    obtain ⟨n, m, hm⟩ := exists_pow_mul_eq_res
      (D.isAffineOpen_V₁.preimage pi.left) (D.pullbackY pi) hWy
        (pi.left.preimage_mono inf_le_right) v
    refine ⟨n, m, ?_⟩
    change (pi.left.app (D.V₀ ⊓ D.V₁)).hom (rho1 D.y ^ n) * v =
      sigma1 m
    rw [map_pow, ← hu]
    exact hm
  obtain ⟨n0, n1, d, aa, bb, hd, hab, hspan0, hspan1⟩ :=
    AlgebraicJacobian.TwoChart.exists_uniform_twisted_generators
      rho0 rho1 D.x D.y htu sigma0 sigma1 hsigma0 hsigma1 hext0 hext1
  refine ⟨{
    n0 := n0
    n1 := n1
    d := d
    aa := aa
    bb := bb
    pos := hd
    compatible := ?_
    span0 := hspan0
    span1 := hspan1 }⟩
  intro i
  have hi := hab i
  change D.sourceRestriction0 pi (aa i) =
    (pi.left.app (D.V₀ ⊓ D.V₁)).hom (rho0 D.x ^ d) *
      D.sourceRestriction1 pi (bb i) at hi
  rw [map_pow, ← ht] at hi
  exact hi

/-- The finite generator index lifted to the ambient scheme universe. -/
abbrev LaurentChartData.FiniteMapGenerators.LiftedIndex
    {D : LaurentChartData Y} {pi : C ⟶ Y} (G : D.FiniteMapGenerators pi) :=
  ULift.{u} (Fin G.n0 ⊕ Fin G.n1)

/-- The first generator family on the universe-lifted index. -/
def LaurentChartData.FiniteMapGenerators.liftedAA
    {D : LaurentChartData Y} {pi : C ⟶ Y} (G : D.FiniteMapGenerators pi) :
    G.LiftedIndex → Γ(C.left, pi.left ⁻¹ᵁ D.V₀) :=
  fun i => G.aa i.down

/-- The second generator family on the same universe-lifted index. -/
def LaurentChartData.FiniteMapGenerators.liftedBB
    {D : LaurentChartData Y} {pi : C ⟶ Y} (G : D.FiniteMapGenerators pi) :
    G.LiftedIndex → Γ(C.left, pi.left ⁻¹ᵁ D.V₁) :=
  fun i => G.bb i.down

@[simp]
theorem LaurentChartData.FiniteMapGenerators.liftedAA_up
    {D : LaurentChartData Y} {pi : C ⟶ Y} (G : D.FiniteMapGenerators pi)
    (i : Fin G.n0 ⊕ Fin G.n1) : G.liftedAA (ULift.up i) = G.aa i :=
  rfl

@[simp]
theorem LaurentChartData.FiniteMapGenerators.liftedBB_up
    {D : LaurentChartData Y} {pi : C ⟶ Y} (G : D.FiniteMapGenerators pi)
    (i : Fin G.n0 ⊕ Fin G.n1) : G.liftedBB (ULift.up i) = G.bb i :=
  rfl

theorem LaurentChartData.FiniteMapGenerators.range_liftedAA
    {D : LaurentChartData Y} {pi : C ⟶ Y} (G : D.FiniteMapGenerators pi) :
    Set.range G.liftedAA = Set.range G.aa := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.down, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨ULift.up i, rfl⟩

theorem LaurentChartData.FiniteMapGenerators.range_liftedBB
    {D : LaurentChartData Y} {pi : C ⟶ Y} (G : D.FiniteMapGenerators pi) :
    Set.range G.liftedBB = Set.range G.bb := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.down, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨ULift.up i, rfl⟩

/-- The complete first-chart twisted coordinates algebra-generate the source
chart over `k`. This discharges the algebra-generation premise of the affine
closed-immersion criterion. -/
theorem LaurentChartData.FiniteMapGenerators.adjoin_chart0
    (D : LaurentChartData Y) (pi : C ⟶ Y) (G : D.FiniteMapGenerators pi) :
    Algebra.adjoin k (Set.range
      (AlgebraicJacobian.TwoChart.TwistedCoordinates.chart0
        (R0 := Γ(C.left, pi.left ⁻¹ᵁ D.V₀))
        G.d (D.pullbackX pi) G.liftedAA)) = ⊤ := by
  letI : Algebra Γ(Y.left, D.V₀) Γ(C.left, pi.left ⁻¹ᵁ D.V₀) :=
    RingHom.toAlgebra (pi.left.app D.V₀).hom
  letI : IsScalarTower k Γ(Y.left, D.V₀)
      Γ(C.left, pi.left ⁻¹ᵁ D.V₀) :=
    IsScalarTower.of_algebraMap_eq fun c => (app_algebraMap pi D.V₀ c).symm
  change Algebra.adjoin k (Set.range
    (AlgebraicJacobian.TwoChart.TwistedCoordinates.chart0
      (R0 := Γ(C.left, pi.left ⁻¹ᵁ D.V₀))
      G.d (algebraMap Γ(Y.left, D.V₀)
        Γ(C.left, pi.left ⁻¹ᵁ D.V₀) D.x) G.liftedAA)) = ⊤
  exact AlgebraicJacobian.TwoChart.TwistedCoordinates.adjoin_chart0
    G.d G.pos D.x G.liftedAA D.span_pow_x (by
      rw [G.range_liftedAA]
      exact G.span0)

/-- The complete second-chart twisted coordinates algebra-generate the source
chart over `k`. -/
theorem LaurentChartData.FiniteMapGenerators.adjoin_chart1
    (D : LaurentChartData Y) (pi : C ⟶ Y) (G : D.FiniteMapGenerators pi) :
    Algebra.adjoin k (Set.range
      (AlgebraicJacobian.TwoChart.TwistedCoordinates.chart1
        (R1 := Γ(C.left, pi.left ⁻¹ᵁ D.V₁))
        G.d (D.pullbackY pi) G.liftedBB)) = ⊤ := by
  letI : Algebra Γ(Y.left, D.V₁) Γ(C.left, pi.left ⁻¹ᵁ D.V₁) :=
    RingHom.toAlgebra (pi.left.app D.V₁).hom
  letI : IsScalarTower k Γ(Y.left, D.V₁)
      Γ(C.left, pi.left ⁻¹ᵁ D.V₁) :=
    IsScalarTower.of_algebraMap_eq fun c => (app_algebraMap pi D.V₁ c).symm
  change Algebra.adjoin k (Set.range
    (AlgebraicJacobian.TwoChart.TwistedCoordinates.chart1
      (R1 := Γ(C.left, pi.left ⁻¹ᵁ D.V₁))
      G.d (algebraMap Γ(Y.left, D.V₁)
        Γ(C.left, pi.left ⁻¹ᵁ D.V₁) D.y) G.liftedBB)) = ⊤
  exact AlgebraicJacobian.TwoChart.TwistedCoordinates.adjoin_chart1
    G.d G.pos D.y G.liftedBB D.span_pow_y (by
      rw [G.range_liftedBB]
      exact G.span1)

end AlgebraicGeometry.Adelic
