/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Projective.FiniteMapProjectiveCoordinates

/-!
# Aligned generators for a finite map to the projective line

For a finite morphism to `P1`, the inverse images of the two standard affine
charts have section rings finite over the corresponding polynomial chart
rings. Denominator clearing on the overlap and the two-chart alignment lemma
produce finite generator families related by one positive Laurent twist.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open MvPolynomial HomogeneousLocalization AlgebraicGeometry

namespace AlgebraicGeometry.P1FiniteMap

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))}

noncomputable local instance : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

noncomputable local instance sourceChart0Algebra (pi : C.left ⟶ P1 k) :
    Algebra k Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) :=
  (C.left.overAlgebraMap k (pi ⁻¹ᵁ P1.chartOpen k 0)).toAlgebra

noncomputable local instance sourceChart1Algebra (pi : C.left ⟶ P1 k) :
    Algebra k Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) :=
  (C.left.overAlgebraMap k (pi ⁻¹ᵁ P1.chartOpen k 1)).toAlgebra

/-- The pullback of the first Laurent coordinate to the first source chart. -/
noncomputable def pullbackCoord0 (pi : C.left ⟶ P1 k) :
    Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) :=
  (pi.app (P1.chartOpen k 0)).hom (coord0 (k := k))

/-- The pullback of the second Laurent coordinate to the second source chart. -/
noncomputable def pullbackCoord1 (pi : C.left ⟶ P1 k) :
    Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) :=
  (pi.app (P1.chartOpen k 1)).hom (coord1 (k := k))

/-- Restriction from the first source chart to the pulled-back overlap. -/
noncomputable def sourceRestriction0 (pi : C.left ⟶ P1 k) :
    Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) →+*
      Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) :=
  (C.left.presheaf.map
    (homOfLE (pi.preimage_mono
      (inf_le_left : P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤
        P1.chartOpen k 0))).op).hom

/-- Restriction from the second source chart to the pulled-back overlap. -/
noncomputable def sourceRestriction1 (pi : C.left ⟶ P1 k) :
    Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) →+*
      Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) :=
  (C.left.presheaf.map
    (homOfLE (pi.preimage_mono
      (inf_le_right : P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤
        P1.chartOpen k 1))).op).hom

/-- The pulled-back Laurent coordinates remain mutually inverse on the
source overlap. -/
theorem sourceRestriction_mul (pi : C.left ⟶ P1 k) :
    sourceRestriction0 pi (pullbackCoord0 pi) *
      sourceRestriction1 pi (pullbackCoord1 pi) = 1 := by
  have h0 : sourceRestriction0 pi (pullbackCoord0 pi) =
      (pi.app (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)).hom
        (((P1 k).presheaf.map
          (homOfLE (inf_le_left : P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤
            P1.chartOpen k 0)).op).hom (coord0 (k := k))) := by
    have h := congrArg
      (fun g : Γ(P1 k, P1.chartOpen k 0) ⟶
          Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) =>
        g.hom (coord0 (k := k)))
      (pi.naturality
        (homOfLE (inf_le_left : P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤
          P1.chartOpen k 0)).op)
    exact h.symm
  have h1 : sourceRestriction1 pi (pullbackCoord1 pi) =
      (pi.app (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)).hom
        (((P1 k).presheaf.map
          (homOfLE (inf_le_right : P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤
            P1.chartOpen k 1)).op).hom (coord1 (k := k))) := by
    have h := congrArg
      (fun g : Γ(P1 k, P1.chartOpen k 1) ⟶
          Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) =>
        g.hom (coord1 (k := k)))
      (pi.naturality
        (homOfLE (inf_le_right : P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤
          P1.chartOpen k 1)).op)
    exact h.symm
  rw [h0, h1, ← map_mul, restriction_coord_mul, map_one]

/-- Aligned finite generator families on the two pulled-back standard
charts. -/
structure FiniteMapGenerators (pi : C.left ⟶ P1 k) : Type u where
  n0 : ℕ
  n1 : ℕ
  d : ℕ
  aa : Fin n0 ⊕ Fin n1 → Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0)
  bb : Fin n0 ⊕ Fin n1 → Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1)
  pos : 0 < d
  compatible : ∀ i,
    sourceRestriction0 pi (aa i) =
      sourceRestriction0 pi (pullbackCoord0 pi) ^ d *
        sourceRestriction1 pi (bb i)
  span0 :
    letI : Algebra Γ(P1 k, P1.chartOpen k 0)
        Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) :=
      (pi.app (P1.chartOpen k 0)).hom.toAlgebra
    Submodule.span Γ(P1 k, P1.chartOpen k 0) (Set.range aa) = ⊤
  span1 :
    letI : Algebra Γ(P1 k, P1.chartOpen k 1)
        Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) :=
      (pi.app (P1.chartOpen k 1)).hom.toAlgebra
    Submodule.span Γ(P1 k, P1.chartOpen k 1) (Set.range bb) = ⊤

/-- A finite morphism to `P1` admits aligned finite source generators after
one positive common twist. -/
theorem nonempty_finiteMapGenerators (pi : C.left ⟶ P1 k) [IsFinite pi] :
    Nonempty (FiniteMapGenerators pi) := by
  classical
  letI iA0 : Algebra Γ(P1 k, P1.chartOpen k 0)
      Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) :=
    (pi.app (P1.chartOpen k 0)).hom.toAlgebra
  letI iA1 : Algebra Γ(P1 k, P1.chartOpen k 1)
      Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) :=
    (pi.app (P1.chartOpen k 1)).hom.toAlgebra
  letI iA01 : Algebra Γ(P1 k, P1.chartOpen k 0 ⊓ P1.chartOpen k 1)
      Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) :=
    (pi.app (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)).hom.toAlgebra
  haveI hfin0 : Module.Finite Γ(P1 k, P1.chartOpen k 0)
      Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) :=
    pi.finite_app (P1.chartOpen k 0) (P1.isAffineOpen_chartOpen k 0)
  haveI hfin1 : Module.Finite Γ(P1 k, P1.chartOpen k 1)
      Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) :=
    pi.finite_app (P1.chartOpen k 1) (P1.isAffineOpen_chartOpen k 1)
  let rho0 : Γ(P1 k, P1.chartOpen k 0) →ₐ[ℤ]
      Γ(P1 k, P1.chartOpen k 0 ⊓ P1.chartOpen k 1) :=
    (((P1 k).presheaf.map
      (homOfLE (inf_le_left : P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤
        P1.chartOpen k 0)).op).hom).toIntAlgHom
  let rho1 : Γ(P1 k, P1.chartOpen k 1) →ₐ[ℤ]
      Γ(P1 k, P1.chartOpen k 0 ⊓ P1.chartOpen k 1) :=
    (((P1 k).presheaf.map
      (homOfLE (inf_le_right : P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤
        P1.chartOpen k 1)).op).hom).toIntAlgHom
  let sigma0 : Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) →ₗ[ℤ]
      Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) :=
    (sourceRestriction0 pi).toIntAlgHom.toLinearMap
  let sigma1 : Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) →ₗ[ℤ]
      Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) :=
    (sourceRestriction1 pi).toIntAlgHom.toLinearMap
  have htu : rho0 (coord0 (k := k)) * rho1 (coord1 (k := k)) = 1 :=
    restriction_coord_mul
  have hsigma0 : ∀ (c : Γ(P1 k, P1.chartOpen k 0))
      (m : Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0)),
      sigma0 (c • m) = rho0 c • sigma0 m := by
    intro c m
    change sourceRestriction0 pi
        ((pi.app (P1.chartOpen k 0)).hom c * m) =
      (pi.app (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)).hom (rho0 c) *
        sourceRestriction0 pi m
    rw [map_mul]
    congr 1
    have h := congrArg
      (fun g : Γ(P1 k, P1.chartOpen k 0) ⟶
          Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) =>
        g.hom c)
      (pi.naturality
        (homOfLE (inf_le_left : P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤
          P1.chartOpen k 0)).op)
    exact h.symm
  have hsigma1 : ∀ (c : Γ(P1 k, P1.chartOpen k 1))
      (m : Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1)),
      sigma1 (c • m) = rho1 c • sigma1 m := by
    intro c m
    change sourceRestriction1 pi
        ((pi.app (P1.chartOpen k 1)).hom c * m) =
      (pi.app (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)).hom (rho1 c) *
        sourceRestriction1 pi m
    rw [map_mul]
    congr 1
    have h := congrArg
      (fun g : Γ(P1 k, P1.chartOpen k 1) ⟶
          Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) =>
        g.hom c)
      (pi.naturality
        (homOfLE (inf_le_right : P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤
          P1.chartOpen k 1)).op)
    exact h.symm
  let t := sigma0 (pullbackCoord0 pi)
  let v := sigma1 (pullbackCoord1 pi)
  have hW0 : pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1) =
      C.left.basicOpen (pullbackCoord0 pi) := by
    have h : pi ⁻¹ᵁ ((P1 k).basicOpen (coord0 (k := k))) =
        C.left.basicOpen ((pi.app (P1.chartOpen k 0)).hom (coord0 (k := k))) :=
      Scheme.preimage_basicOpen pi _
    rw [basicOpen_coord0] at h
    exact h
  have hW1 : pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1) =
      C.left.basicOpen (pullbackCoord1 pi) := by
    have h : pi ⁻¹ᵁ ((P1 k).basicOpen (coord1 (k := k))) =
        C.left.basicOpen ((pi.app (P1.chartOpen k 1)).hom (coord1 (k := k))) :=
      Scheme.preimage_basicOpen pi _
    rw [basicOpen_coord1] at h
    exact h
  have ht : t =
      (pi.app (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)).hom
        (rho0 (coord0 (k := k))) := by
    have h := congrArg
      (fun g : Γ(P1 k, P1.chartOpen k 0) ⟶
          Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) =>
        g.hom (coord0 (k := k)))
      (pi.naturality
        (homOfLE (inf_le_left : P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤
          P1.chartOpen k 0)).op)
    exact h.symm
  have hv : v =
      (pi.app (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)).hom
        (rho1 (coord1 (k := k))) := by
    have h := congrArg
      (fun g : Γ(P1 k, P1.chartOpen k 1) ⟶
          Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) =>
        g.hom (coord1 (k := k)))
      (pi.naturality
        (homOfLE (inf_le_right : P1.chartOpen k 0 ⊓ P1.chartOpen k 1 ≤
          P1.chartOpen k 1)).op)
    exact h.symm
  have hext0 : ∀ z : Γ(C.left,
      pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)),
      ∃ (n : ℕ) (m : Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0)),
        rho0 (coord0 (k := k)) ^ n • z = sigma0 m := by
    intro z
    letI : Algebra Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0)
        Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) :=
      (sourceRestriction0 pi).toAlgebra
    haveI := ((P1.isAffineOpen_chartOpen k 0).preimage pi).isLocalization_of_eq_basicOpen
        (pullbackCoord0 pi)
        (homOfLE (pi.preimage_mono inf_le_left)) hW0
    obtain ⟨n, m, hm⟩ := IsLocalization.Away.surj (pullbackCoord0 pi) z
    refine ⟨n, m, ?_⟩
    change (pi.app (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)).hom
        (rho0 (coord0 (k := k)) ^ n) * z = sigma0 m
    rw [map_pow, ← ht]
    change sourceRestriction0 pi (pullbackCoord0 pi) ^ n * z =
      sourceRestriction0 pi m
    change z * sourceRestriction0 pi (pullbackCoord0 pi) ^ n =
      sourceRestriction0 pi m at hm
    exact (mul_comm _ _).trans hm
  have hext1 : ∀ z : Γ(C.left,
      pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)),
      ∃ (n : ℕ) (m : Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1)),
        rho1 (coord1 (k := k)) ^ n • z = sigma1 m := by
    intro z
    letI : Algebra Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1)
        Γ(C.left, pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)) :=
      (sourceRestriction1 pi).toAlgebra
    haveI := ((P1.isAffineOpen_chartOpen k 1).preimage pi).isLocalization_of_eq_basicOpen
        (pullbackCoord1 pi)
        (homOfLE (pi.preimage_mono inf_le_right)) hW1
    obtain ⟨n, m, hm⟩ := IsLocalization.Away.surj (pullbackCoord1 pi) z
    refine ⟨n, m, ?_⟩
    change (pi.app (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)).hom
        (rho1 (coord1 (k := k)) ^ n) * z = sigma1 m
    rw [map_pow, ← hv]
    change sourceRestriction1 pi (pullbackCoord1 pi) ^ n * z =
      sourceRestriction1 pi m
    change z * sourceRestriction1 pi (pullbackCoord1 pi) ^ n =
      sourceRestriction1 pi m at hm
    exact (mul_comm _ _).trans hm
  obtain ⟨n0, n1, d, aa, bb, hd, hab, hspan0, hspan1⟩ :=
    AlgebraicJacobian.TwoChart.exists_uniform_twisted_generators
      rho0 rho1 (coord0 (k := k)) (coord1 (k := k)) htu
        sigma0 sigma1 hsigma0 hsigma1 hext0 hext1
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
  change sourceRestriction0 pi (aa i) =
    (pi.app (P1.chartOpen k 0 ⊓ P1.chartOpen k 1)).hom
        (rho0 (coord0 (k := k)) ^ d) * sourceRestriction1 pi (bb i) at hi
  rw [map_pow, ← ht] at hi
  exact hi

namespace FiniteMapGenerators

variable {pi : C.left ⟶ P1 k} (G : FiniteMapGenerators pi)

/-- The finite generator index lifted to the ambient scheme universe. -/
abbrev LiftedIndex : Type u :=
  ULift.{u} (Fin G.n0 ⊕ Fin G.n1)

/-- The first generator family on the universe-lifted index. -/
def liftedAA : G.LiftedIndex → Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) :=
  fun i => G.aa i.down

/-- The second generator family on the universe-lifted index. -/
def liftedBB : G.LiftedIndex → Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) :=
  fun i => G.bb i.down

@[simp]
theorem liftedAA_up (i : Fin G.n0 ⊕ Fin G.n1) :
    G.liftedAA (ULift.up i) = G.aa i :=
  rfl

@[simp]
theorem liftedBB_up (i : Fin G.n0 ⊕ Fin G.n1) :
    G.liftedBB (ULift.up i) = G.bb i :=
  rfl

theorem range_liftedAA : Set.range G.liftedAA = Set.range G.aa := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.down, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨ULift.up i, rfl⟩

theorem range_liftedBB : Set.range G.liftedBB = Set.range G.bb := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.down, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨ULift.up i, rfl⟩

/-- The complete first-chart twisted coordinates algebra-generate the source
chart over `k`. -/
theorem adjoin_chart0 (hpi : pi ≫ P1.structureMap k = C.hom) :
    Algebra.adjoin k (Set.range
      (AlgebraicJacobian.TwoChart.TwistedCoordinates.chart0
        (R0 := Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0))
        G.d (pullbackCoord0 pi) G.liftedAA)) = ⊤ := by
  letI : (P1 k).Over (Spec (.of k)) := ⟨P1.structureMap k⟩
  letI : C.left.Over (Spec (.of k)) := ⟨C.hom⟩
  letI : Algebra k Γ(P1 k, P1.chartOpen k 0) :=
    ((P1 k).overAlgebraMap k (P1.chartOpen k 0)).toAlgebra
  letI : Algebra Γ(P1 k, P1.chartOpen k 0)
      Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) :=
    (pi.app (P1.chartOpen k 0)).hom.toAlgebra
  letI : Algebra k Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) :=
    (C.left.overAlgebraMap k (pi ⁻¹ᵁ P1.chartOpen k 0)).toAlgebra
  letI : IsScalarTower k Γ(P1 k, P1.chartOpen k 0)
      Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change C.left.overAlgebraMap k (pi ⁻¹ᵁ P1.chartOpen k 0) c =
        (pi.app (P1.chartOpen k 0)).hom
          ((P1 k).overAlgebraMap k (P1.chartOpen k 0) c)
      rw [Scheme.Hom.app_eq_appLE]
      exact (pi.appLE_overAlgebraMap hpi le_rfl c).symm
  change Algebra.adjoin k (Set.range
    (AlgebraicJacobian.TwoChart.TwistedCoordinates.chart0
      (R0 := Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0)) G.d
      (algebraMap Γ(P1 k, P1.chartOpen k 0)
        Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) (coord0 (k := k)))
      G.liftedAA)) = ⊤
  exact AlgebraicJacobian.TwoChart.TwistedCoordinates.adjoin_chart0
    G.d G.pos (coord0 (k := k)) G.liftedAA span_pow_coord0 (by
      rw [G.range_liftedAA]
      exact G.span0)

/-- The complete second-chart twisted coordinates algebra-generate the source
chart over `k`. -/
theorem adjoin_chart1 (hpi : pi ≫ P1.structureMap k = C.hom) :
    Algebra.adjoin k (Set.range
      (AlgebraicJacobian.TwoChart.TwistedCoordinates.chart1
        (R1 := Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1))
        G.d (pullbackCoord1 pi) G.liftedBB)) = ⊤ := by
  letI : (P1 k).Over (Spec (.of k)) := ⟨P1.structureMap k⟩
  letI : C.left.Over (Spec (.of k)) := ⟨C.hom⟩
  letI : Algebra k Γ(P1 k, P1.chartOpen k 1) :=
    ((P1 k).overAlgebraMap k (P1.chartOpen k 1)).toAlgebra
  letI : Algebra Γ(P1 k, P1.chartOpen k 1)
      Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) :=
    (pi.app (P1.chartOpen k 1)).hom.toAlgebra
  letI : Algebra k Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) :=
    (C.left.overAlgebraMap k (pi ⁻¹ᵁ P1.chartOpen k 1)).toAlgebra
  letI : IsScalarTower k Γ(P1 k, P1.chartOpen k 1)
      Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change C.left.overAlgebraMap k (pi ⁻¹ᵁ P1.chartOpen k 1) c =
        (pi.app (P1.chartOpen k 1)).hom
          ((P1 k).overAlgebraMap k (P1.chartOpen k 1) c)
      rw [Scheme.Hom.app_eq_appLE]
      exact (pi.appLE_overAlgebraMap hpi le_rfl c).symm
  change Algebra.adjoin k (Set.range
    (AlgebraicJacobian.TwoChart.TwistedCoordinates.chart1
      (R1 := Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1)) G.d
      (algebraMap Γ(P1 k, P1.chartOpen k 1)
        Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) (coord1 (k := k)))
      G.liftedBB)) = ⊤
  exact AlgebraicJacobian.TwoChart.TwistedCoordinates.adjoin_chart1
    G.d G.pos (coord1 (k := k)) G.liftedBB span_pow_coord1 (by
      rw [G.range_liftedBB]
      exact G.span1)

end FiniteMapGenerators

end AlgebraicGeometry.P1FiniteMap
