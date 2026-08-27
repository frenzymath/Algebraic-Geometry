/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.P1SectionsFinite
import AlgebraicJacobian.Picard.ProjectiveCoordinateChart
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Projective coordinates from two aligned Laurent charts

This file turns the aligned generators produced by
TwoChart.exists_uniform_twisted_generators into homogeneous coordinate
families. For a positive twist d, it adjoins every degree-d base monomial:

* 1, x, ..., x^d on the first chart;
* y^d, ..., y, 1 on the second chart.

If t * u = 1 on the overlap and the extra generators satisfy
rho0 (aa i) = t^d * rho1 (bb i), then the complete coordinate families
differ by the common unit t^d. Consequently their normalized affine-chart
maps into the integral Proj agree on the overlap. These are the algebraic
coordinates used to globalize a finite map to the projective line.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicJacobian.TwoChart.TwistedCoordinates

variable {I R0 R1 R01 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R01]

/-- The degree-d base monomials followed by the aligned generators on the
x-chart. -/
def chart0 (d : ℕ) (x : R0) (aa : I → R0) :
    Fin (d + 1) ⊕ I → R0
  | Sum.inl r => x ^ (r : ℕ)
  | Sum.inr i => aa i

/-- The same degree-d base monomials in reverse order, followed by the
aligned generators on the y-chart. -/
def chart1 (d : ℕ) (y : R1) (bb : I → R1) :
    Fin (d + 1) ⊕ I → R1
  | Sum.inl r => y ^ (d - (r : ℕ))
  | Sum.inr i => bb i

@[simp]
theorem chart0_inl (d : ℕ) (x : R0) (aa : I → R0)
    (r : Fin (d + 1)) :
    chart0 d x aa (Sum.inl r) = x ^ (r : ℕ) := rfl

@[simp]
theorem chart0_inr (d : ℕ) (x : R0) (aa : I → R0) (i : I) :
    chart0 d x aa (Sum.inr i) = aa i := rfl

@[simp]
theorem chart1_inl (d : ℕ) (y : R1) (bb : I → R1)
    (r : Fin (d + 1)) :
    chart1 d y bb (Sum.inl r) = y ^ (d - (r : ℕ)) := rfl

@[simp]
theorem chart1_inr (d : ℕ) (y : R1) (bb : I → R1) (i : I) :
    chart1 d y bb (Sum.inr i) = bb i := rfl

/-- The first family is normalized at the degree-d monomial X0^d. -/
@[simp]
theorem chart0_zero (d : ℕ) (x : R0) (aa : I → R0) :
    chart0 d x aa (Sum.inl ⟨0, Nat.zero_lt_succ d⟩) = 1 := by
  simp

/-- The second family is normalized at the degree-d monomial X1^d. -/
@[simp]
theorem chart1_last (d : ℕ) (y : R1) (bb : I → R1) :
    chart1 d y bb (Sum.inl ⟨d, Nat.lt_succ_self d⟩) = 1 := by
  simp

/-- A positive twist ensures that the first family contains the base
coordinate x itself, not just the two endpoint monomials. -/
@[simp]
theorem chart0_one (d : ℕ) (hd : 0 < d) (x : R0) (aa : I → R0) :
    chart0 d x aa (Sum.inl ⟨1, Nat.succ_lt_succ hd⟩) = x := by
  simp

/-- A positive twist ensures that the second family contains the base
coordinate `y` itself. -/
@[simp]
theorem chart1_one (d : ℕ) (hd : 0 < d) (y : R1) (bb : I → R1) :
    chart1 d y bb (Sum.inl ⟨d - 1, by omega⟩) = y := by
  change y ^ (d - (d - 1)) = y
  rw [show d - (d - 1) = 1 by omega, pow_one]

/-- The complete chart families differ by the common factor rho0 x ^ d on
the overlap. The base-monomial case is the identity
t^r = t^d * u^(d-r) following from t * u = 1. -/
theorem map_chart (rho0 : R0 →+* R01) (rho1 : R1 →+* R01)
    (x : R0) (y : R1) (htu : rho0 x * rho1 y = 1)
    (d : ℕ) (aa : I → R0) (bb : I → R1)
    (hab : ∀ i, rho0 (aa i) = rho0 x ^ d * rho1 (bb i)) :
    ∀ j, rho0 (chart0 d x aa j) =
      rho0 x ^ d * rho1 (chart1 d y bb j) := by
  rintro (r | i)
  · simp only [chart0_inl, chart1_inl, map_pow]
    have hr : (r : ℕ) + (d - (r : ℕ)) = d :=
      Nat.add_sub_of_le (Nat.lt_succ_iff.mp r.isLt)
    calc
      rho0 x ^ (r : ℕ) =
          rho0 x ^ (r : ℕ) * 1 := (mul_one _).symm
      _ = rho0 x ^ (r : ℕ) *
          (rho0 x * rho1 y) ^ (d - (r : ℕ)) := by
        rw [htu, one_pow]
      _ = rho0 x ^ (r : ℕ) *
          (rho0 x ^ (d - (r : ℕ)) * rho1 y ^ (d - (r : ℕ))) := by
        rw [mul_pow]
      _ = rho0 x ^ d * rho1 y ^ (d - (r : ℕ)) := by
        rw [← mul_assoc, ← pow_add, hr]
  · simpa only [chart0_inr, chart1_inr] using hab i

/-- The common transition factor is a unit, together with the coordinate
scaling identity it controls. -/
theorem map_chart_unit (rho0 : R0 →+* R01) (rho1 : R1 →+* R01)
    (x : R0) (y : R1) (htu : rho0 x * rho1 y = 1)
    (d : ℕ) (aa : I → R0) (bb : I → R1)
    (hab : ∀ i, rho0 (aa i) = rho0 x ^ d * rho1 (bb i)) :
    IsUnit (rho0 x ^ d) ∧
      ∀ j, rho0 (chart0 d x aa j) =
        rho0 x ^ d * rho1 (chart1 d y bb j) :=
  ⟨(IsUnit.of_mul_eq_one _ htu).pow d,
    map_chart rho0 rho1 x y htu d aa bb hab⟩

/-- Enlarging a spanning family by the degree-d base monomials preserves
spanning on the first chart. -/
theorem span_chart0 {A : Type u} [Semiring A] [Module A R0]
    (d : ℕ) (x : R0) (aa : I → R0)
    (hspan : Submodule.span A (Set.range aa) = ⊤) :
    Submodule.span A (Set.range (chart0 d x aa)) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro z ⟨i, rfl⟩
  exact ⟨Sum.inr i, rfl⟩

/-- Enlarging a spanning family by the degree-d base monomials preserves
spanning on the second chart. -/
theorem span_chart1 {A : Type u} [Semiring A] [Module A R1]
    (d : ℕ) (y : R1) (bb : I → R1)
    (hspan : Submodule.span A (Set.range bb) = ⊤) :
    Submodule.span A (Set.range (chart1 d y bb)) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro z ⟨i, rfl⟩
  exact ⟨Sum.inr i, rfl⟩

private lemma adjoin_singleton_eq_top_of_span_pow_eq_top
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A] (x : A)
    (hpow : ⊤ ≤ Submodule.span k (Set.range fun n : ℕ => x ^ n)) :
    Algebra.adjoin k ({x} : Set A) = ⊤ := by
  have hle : Submodule.span k (Set.range fun n : ℕ => x ^ n) ≤
      (Algebra.adjoin k ({x} : Set A)).toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact Subalgebra.pow_mem _
      (Algebra.subset_adjoin (Set.mem_singleton x)) n
  apply top_unique
  intro z _
  exact hle (hpow (by trivial))

private lemma adjoin_eq_top_of_span_eq_top
    {A B I : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (aa : I → B) (haa : Submodule.span A (Set.range aa) = ⊤) :
    Algebra.adjoin A (Set.range aa) = ⊤ := by
  have hle : Submodule.span A (Set.range aa) ≤
      (Algebra.adjoin A (Set.range aa)).toSubmodule :=
    Submodule.span_le.mpr fun _ hz => Algebra.subset_adjoin hz
  apply top_unique
  intro z _
  exact hle (by rw [haa]; trivial)

set_option maxHeartbeats 800000 in
-- Kernel reduction of the nested `adjoin_eq_adjoin_union` proof exceeds the default budget.
/-- If the base ring is spanned by powers of `x` and `aa` spans the source as
a module over the base, the complete first-chart coordinate family generates
the source as a `k`-algebra. -/
theorem adjoin_chart0 {k A B : Type u}
    [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    (d : ℕ) (hd : 0 < d) (x : A) (aa : I → B)
    (hpow : ⊤ ≤ Submodule.span k (Set.range fun n : ℕ => x ^ n))
    (haa : Submodule.span A (Set.range aa) = ⊤) :
    Algebra.adjoin k
      (Set.range (chart0 d (algebraMap A B x) aa)) = ⊤ := by
  have hx := adjoin_singleton_eq_top_of_span_pow_eq_top x hpow
  have haa' := adjoin_eq_top_of_span_eq_top aa haa
  have hunion : Algebra.adjoin k
      ((algebraMap A B '' ({x} : Set A)) ∪ Set.range aa) = ⊤ := by
    rw [← Algebra.adjoin_eq_adjoin_union k ({x} : Set A) (Set.range aa) hx,
      haa']
    rfl
  apply top_unique
  rw [← hunion]
  apply Algebra.adjoin_mono
  rintro z (hz | hz)
  · obtain ⟨w, rfl, rfl⟩ := hz
    exact ⟨Sum.inl ⟨1, Nat.succ_lt_succ hd⟩,
      chart0_one d hd (algebraMap A B w) aa⟩
  · obtain ⟨i, rfl⟩ := hz
    exact ⟨Sum.inr i, rfl⟩

set_option maxHeartbeats 800000 in
-- The symmetric nested-adjoin proof has the same kernel reduction cost.
/-- If the base ring is spanned by powers of `y` and `bb` spans the source as
a module over the base, the complete second-chart coordinate family generates
the source as a `k`-algebra. -/
theorem adjoin_chart1 {k A B : Type u}
    [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    (d : ℕ) (hd : 0 < d) (y : A) (bb : I → B)
    (hpow : ⊤ ≤ Submodule.span k (Set.range fun n : ℕ => y ^ n))
    (hbb : Submodule.span A (Set.range bb) = ⊤) :
    Algebra.adjoin k
      (Set.range (chart1 d (algebraMap A B y) bb)) = ⊤ := by
  have hy := adjoin_singleton_eq_top_of_span_pow_eq_top y hpow
  have hbb' := adjoin_eq_top_of_span_eq_top bb hbb
  have hunion : Algebra.adjoin k
      ((algebraMap A B '' ({y} : Set A)) ∪ Set.range bb) = ⊤ := by
    rw [← Algebra.adjoin_eq_adjoin_union k ({y} : Set A) (Set.range bb) hy,
      hbb']
    rfl
  apply top_unique
  rw [← hunion]
  apply Algebra.adjoin_mono
  rintro z (hz | hz)
  · obtain ⟨w, rfl, rfl⟩ := hz
    exact ⟨Sum.inl ⟨d - 1, by omega⟩,
      chart1_one d hd (algebraMap A B w) bb⟩
  · obtain ⟨i, rfl⟩ := hz
    exact ⟨Sum.inr i, rfl⟩

/-- The two normalized affine-chart maps into projective space agree after
restriction to the overlap. This is the gluing equation for the finite-map
projective embedding. -/
theorem fromSpec_compat [Finite I]
    (rho0 : R0 →+* R01) (rho1 : R1 →+* R01)
    (x : R0) (y : R1) (htu : rho0 x * rho1 y = 1)
    (d : ℕ) (aa : I → R0) (bb : I → R1)
    (hab : ∀ i, rho0 (aa i) = rho0 x ^ d * rho1 (bb i)) :
    Spec.map (CommRingCat.ofHom rho0) ≫
        ProjectiveSpace.Coordinates.fromSpec
          (Sum.inl ⟨0, Nat.zero_lt_succ d⟩) (chart0 d x aa)
          (chart0_zero d x aa) =
      Spec.map (CommRingCat.ofHom rho1) ≫
        ProjectiveSpace.Coordinates.fromSpec
          (Sum.inl ⟨d, Nat.lt_succ_self d⟩) (chart1 d y bb)
          (chart1_last d y bb) := by
  rw [ProjectiveSpace.Coordinates.SpecMap_fromSpec,
    ProjectiveSpace.Coordinates.SpecMap_fromSpec]
  apply ProjectiveSpace.Coordinates.fromSpec_eq_of_unit_smul
      (lambda := rho0 x ^ d)
  · exact (IsUnit.of_mul_eq_one _ htu).pow d
  · exact map_chart rho0 rho1 x y htu d aa bb hab

/-- The normalized coordinate maps on two scheme opens agree after
restriction to their intersection. This is the direct input expected by the
scheme morphism gluing API. -/
theorem fromOpen_compat [Finite I] {X : Scheme.{u}} (U0 U1 : X.Opens)
    (x : Γ(X, U0)) (y : Γ(X, U1))
    (htu :
      (X.presheaf.map
          (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op).hom x *
        (X.presheaf.map
          (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op).hom y = 1)
    (d : ℕ) (aa : I → Γ(X, U0)) (bb : I → Γ(X, U1))
    (hab : ∀ i,
      (X.presheaf.map
          (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op).hom (aa i) =
        (X.presheaf.map
          (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op).hom x ^ d *
          (X.presheaf.map
            (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op).hom (bb i)) :
    X.homOfLE inf_le_left ≫
        ProjectiveSpace.Coordinates.fromOpen U0
          (Sum.inl ⟨0, Nat.zero_lt_succ d⟩) (chart0 d x aa)
          (chart0_zero d x aa) =
      X.homOfLE inf_le_right ≫
        ProjectiveSpace.Coordinates.fromOpen U1
          (Sum.inl ⟨d, Nat.lt_succ_self d⟩) (chart1 d y bb)
          (chart1_last d y bb) := by
  simp only [ProjectiveSpace.Coordinates.fromOpen]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  simpa only [Category.assoc, CommRingCat.ofHom_hom] using congrArg
    (fun f => (U0 ⊓ U1).toSpecΓ ≫ f)
    (fromSpec_compat
      (X.presheaf.map
        (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op).hom
      (X.presheaf.map
        (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op).hom
      x y htu d aa bb hab)

end AlgebraicJacobian.TwoChart.TwistedCoordinates
