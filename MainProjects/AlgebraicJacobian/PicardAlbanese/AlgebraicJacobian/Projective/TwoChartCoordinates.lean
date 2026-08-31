/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Projective.ProjectiveCoordinateChart
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Twisted coordinates on two Laurent charts

Finite modules on two charts admit aligned generators after a common positive
twist. The resulting homogeneous coordinate families agree on the overlap up
to a unit and algebra-generate the chart rings.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicJacobian.TwoChart

/-- Finite modules on two Laurent charts admit aligned generators after one
positive common twist. -/
theorem exists_uniform_twisted_generators
    {A C₀ C₁ C₀₁ M₀ M₁ V : Type*} [CommRing A]
    [CommRing C₀] [CommRing C₁] [CommRing C₀₁]
    [Algebra A C₀] [Algebra A C₁] [Algebra A C₀₁]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup V]
    [Module C₀ M₀] [Module C₁ M₁] [Module C₀₁ V]
    [Module A M₀] [Module A M₁] [Module A V]
    [Module.Finite C₀ M₀] [Module.Finite C₁ M₁]
    (ρ₀ : C₀ →ₐ[A] C₀₁) (ρ₁ : C₁ →ₐ[A] C₀₁) (x : C₀) (y : C₁)
    (htu : ρ₀ x * ρ₁ y = 1)
    (σ₀ : M₀ →ₗ[A] V) (σ₁ : M₁ →ₗ[A] V)
    (hσ₀ : ∀ (c : C₀) (m : M₀), σ₀ (c • m) = ρ₀ c • σ₀ m)
    (hσ₁ : ∀ (c : C₁) (m : M₁), σ₁ (c • m) = ρ₁ c • σ₁ m)
    (hext₀ : ∀ v : V, ∃ (n : ℕ) (m : M₀), ρ₀ x ^ n • v = σ₀ m)
    (hext₁ : ∀ v : V, ∃ (n : ℕ) (m : M₁), ρ₁ y ^ n • v = σ₁ m) :
    ∃ (n₀ n₁ d : ℕ) (aa : Fin n₀ ⊕ Fin n₁ → M₀)
      (bb : Fin n₀ ⊕ Fin n₁ → M₁),
      0 < d ∧
        (∀ i, σ₀ (aa i) = ρ₀ x ^ d • σ₁ (bb i)) ∧
        Submodule.span C₀ (Set.range aa) = ⊤ ∧
        Submodule.span C₁ (Set.range bb) = ⊤ := by
  classical
  have hpow : ∀ n : ℕ, ρ₀ x ^ n * ρ₁ y ^ n = 1 := fun n => by
    rw [← mul_pow, htu, one_pow]
  obtain ⟨n₀, g, hg⟩ := Module.Finite.exists_fin (R := C₀) (M := M₀)
  obtain ⟨n₁, g', hg'⟩ := Module.Finite.exists_fin (R := C₁) (M := M₁)
  choose nb b hb using fun i : Fin n₀ => hext₁ (σ₀ (g i))
  choose ma a ha using fun j : Fin n₁ => hext₀ (σ₁ (g' j))
  set d : ℕ := max (max (Finset.univ.sup nb) (Finset.univ.sup ma)) 1
  have hd : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hdb : ∀ i, nb i ≤ d := fun i =>
    le_trans (Finset.le_sup (Finset.mem_univ i))
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hda : ∀ j, ma j ≤ d := fun j =>
    le_trans (Finset.le_sup (Finset.mem_univ j))
      (le_trans (le_max_right _ _) (le_max_left _ _))
  let aa : Fin n₀ ⊕ Fin n₁ → M₀ :=
    Sum.elim g (fun j => x ^ (d - ma j) • a j)
  let bb : Fin n₀ ⊕ Fin n₁ → M₁ :=
    Sum.elim (fun i => y ^ (d - nb i) • b i) g'
  have hab : ∀ i, σ₀ (aa i) = ρ₀ x ^ d • σ₁ (bb i) := by
    rintro (i | j)
    · have e1 : σ₁ (bb (Sum.inl i)) = ρ₁ y ^ (d - nb i) • σ₁ (b i) := by
        simp only [bb, Sum.elim_inl]
        rw [hσ₁, map_pow]
      have e2 : ρ₀ x ^ d * ρ₁ y ^ (d - nb i) = ρ₀ x ^ nb i := by
        have hsplit : ρ₀ x ^ d = ρ₀ x ^ nb i * ρ₀ x ^ (d - nb i) := by
          rw [← pow_add]
          congr 1
          have := hdb i
          omega
        rw [hsplit, mul_assoc, hpow (d - nb i), mul_one]
      calc σ₀ (aa (Sum.inl i)) = σ₀ (g i) := by simp only [aa, Sum.elim_inl]
        _ = (1 : C₀₁) • σ₀ (g i) := (one_smul _ _).symm
        _ = (ρ₀ x ^ nb i * ρ₁ y ^ nb i) • σ₀ (g i) := by rw [hpow]
        _ = ρ₀ x ^ nb i • (ρ₁ y ^ nb i • σ₀ (g i)) := by rw [mul_smul]
        _ = ρ₀ x ^ nb i • σ₁ (b i) := by rw [hb i]
        _ = (ρ₀ x ^ d * ρ₁ y ^ (d - nb i)) • σ₁ (b i) := by rw [e2]
        _ = ρ₀ x ^ d • (ρ₁ y ^ (d - nb i) • σ₁ (b i)) := by rw [mul_smul]
        _ = ρ₀ x ^ d • σ₁ (bb (Sum.inl i)) := by rw [← e1]
    · have e3 : (d - ma j) + ma j = d := by
        have := hda j
        omega
      calc σ₀ (aa (Sum.inr j)) = σ₀ (x ^ (d - ma j) • a j) := by
              simp only [aa, Sum.elim_inr]
        _ = ρ₀ x ^ (d - ma j) • σ₀ (a j) := by rw [hσ₀, map_pow]
        _ = ρ₀ x ^ (d - ma j) • (ρ₀ x ^ ma j • σ₁ (g' j)) := by rw [ha j]
        _ = (ρ₀ x ^ (d - ma j) * ρ₀ x ^ ma j) • σ₁ (g' j) := by
              rw [mul_smul]
        _ = ρ₀ x ^ d • σ₁ (bb (Sum.inr j)) := by
              rw [← pow_add, e3]
              simp only [bb, Sum.elim_inr]
  have hspanaa : Submodule.span C₀ (Set.range aa) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hg]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, by simp only [aa, Sum.elim_inl]⟩
  have hspanbb : Submodule.span C₁ (Set.range bb) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hg']
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨Sum.inr j, by simp only [bb, Sum.elim_inr]⟩
  exact ⟨n₀, n₁, d, aa, bb, hd, hab, hspanaa, hspanbb⟩

namespace TwistedCoordinates

variable {I R0 R1 R01 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R01]

def chart0 (d : ℕ) (x : R0) (aa : I → R0) :
    Fin (d + 1) ⊕ I → R0
  | Sum.inl r => x ^ (r : ℕ)
  | Sum.inr i => aa i

def chart1 (d : ℕ) (y : R1) (bb : I → R1) :
    Fin (d + 1) ⊕ I → R1
  | Sum.inl r => y ^ (d - (r : ℕ))
  | Sum.inr i => bb i

@[simp] theorem chart0_inl (d : ℕ) (x : R0) (aa : I → R0) (r : Fin (d + 1)) :
    chart0 d x aa (Sum.inl r) = x ^ (r : ℕ) := rfl

@[simp] theorem chart0_inr (d : ℕ) (x : R0) (aa : I → R0) (i : I) :
    chart0 d x aa (Sum.inr i) = aa i := rfl

@[simp] theorem chart1_inl (d : ℕ) (y : R1) (bb : I → R1) (r : Fin (d + 1)) :
    chart1 d y bb (Sum.inl r) = y ^ (d - (r : ℕ)) := rfl

@[simp] theorem chart1_inr (d : ℕ) (y : R1) (bb : I → R1) (i : I) :
    chart1 d y bb (Sum.inr i) = bb i := rfl

@[simp] theorem chart0_zero (d : ℕ) (x : R0) (aa : I → R0) :
    chart0 d x aa (Sum.inl ⟨0, Nat.zero_lt_succ d⟩) = 1 := by simp

@[simp] theorem chart1_last (d : ℕ) (y : R1) (bb : I → R1) :
    chart1 d y bb (Sum.inl ⟨d, Nat.lt_succ_self d⟩) = 1 := by simp

@[simp] theorem chart0_one (d : ℕ) (hd : 0 < d) (x : R0) (aa : I → R0) :
    chart0 d x aa (Sum.inl ⟨1, Nat.succ_lt_succ hd⟩) = x := by simp

@[simp] theorem chart1_one (d : ℕ) (hd : 0 < d) (y : R1) (bb : I → R1) :
    chart1 d y bb (Sum.inl ⟨d - 1, by omega⟩) = y := by
  change y ^ (d - (d - 1)) = y
  rw [show d - (d - 1) = 1 by omega, pow_one]

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
      rho0 x ^ (r : ℕ) = rho0 x ^ (r : ℕ) * 1 := (mul_one _).symm
      _ = rho0 x ^ (r : ℕ) * (rho0 x * rho1 y) ^ (d - (r : ℕ)) := by
        rw [htu, one_pow]
      _ = rho0 x ^ (r : ℕ) *
          (rho0 x ^ (d - (r : ℕ)) * rho1 y ^ (d - (r : ℕ))) := by
        rw [mul_pow]
      _ = rho0 x ^ d * rho1 y ^ (d - (r : ℕ)) := by
        rw [← mul_assoc, ← pow_add, hr]
  · simpa only [chart0_inr, chart1_inr] using hab i

theorem span_chart0 {A : Type u} [Semiring A] [Module A R0]
    (d : ℕ) (x : R0) (aa : I → R0)
    (hspan : Submodule.span A (Set.range aa) = ⊤) :
    Submodule.span A (Set.range (chart0 d x aa)) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro z ⟨i, rfl⟩
  exact ⟨Sum.inr i, rfl⟩

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

end TwistedCoordinates

end AlgebraicJacobian.TwoChart
