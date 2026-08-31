/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4P1FinitenessAPI

/-!
# Morphisms to the projective line from chart data

For a ring `A` under `k`, an element of `A` determines a morphism from `Spec A` to
`P1 k` through either standard affine chart.  The two descriptions agree when the
element is a unit.  These point-free identities are the local input for spreading a
rational function to a morphism on a smooth curve.
-/

set_option autoImplicit false

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

namespace P1

variable (k : Type u) [Field k]

local notation "𝒜" => homogeneousSubmodule (Fin 2) k

/-! ### Irreducibility of the projective line -/

instance : IsDomain (Away 𝒜 (X (0 : Fin 2))) :=
  MulEquiv.isDomain (Polynomial k) (awayAlgEquiv k fin_zero_ne_one).toRingEquiv.toMulEquiv

instance : IsDomain (Away 𝒜 (X (1 : Fin 2))) :=
  MulEquiv.isDomain (Polynomial k) (awayAlgEquiv k fin_one_ne_zero).toRingEquiv.toMulEquiv

instance : Nontrivial (Away 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1)) :=
  (overlapAlgEquiv k).toEquiv.nontrivial

theorem exists_mem_chartOpen_zero_of_isOpen {W : Set (P1 k)} (hW : IsOpen W)
    (hne : W.Nonempty) : ∃ z ∈ W, z ∈ chartOpen k 0 := by
  obtain ⟨w, hw⟩ := hne
  have hcover : w ∈ chartOpen k 0 ⊔ chartOpen k 1 := by
    rw [chartOpen_sup]
    trivial
  rw [TopologicalSpace.Opens.mem_sup] at hcover
  rcases hcover with h0 | h1
  · exact ⟨w, hw, h0⟩
  rw [← opensRange_chartι k 1] at h1
  obtain ⟨y, hy⟩ := h1
  have hOne : ((chartι k 1).base ⁻¹' (chartOpen k 0 : Set (P1 k))).Nonempty := by
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of
        (Away 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1)))) := inferInstance
    have hpover : (Proj.awayι 𝒜 _ (X_mul_X_mem k) two_pos).base z ∈
        Proj.basicOpen 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1) := by
      rw [← Proj.opensRange_awayι 𝒜 _ (X_mul_X_mem k) two_pos]
      exact ⟨z, rfl⟩
    have hp1 : (Proj.awayι 𝒜 _ (X_mul_X_mem k) two_pos).base z ∈ chartOpen k 1 :=
      overlap_le_right k hpover
    rw [← opensRange_chartι k 1] at hp1
    obtain ⟨y', hy'⟩ := hp1
    exact ⟨y', by rw [Set.mem_preimage, hy']; exact overlap_le_left k hpover⟩
  have hdense : Dense ((chartι k 1).base ⁻¹' (chartOpen k 0 : Set (P1 k))) :=
    IsOpen.dense ((chartOpen k 0).2.preimage (chartι k 1).continuous) hOne
  obtain ⟨y₀, hy₀W, hy₀O⟩ := hdense.inter_open_nonempty _
    (hW.preimage (chartι k 1).continuous) ⟨y, by rwa [Set.mem_preimage, hy]⟩
  exact ⟨(chartι k 1).base y₀, hy₀W, hy₀O⟩

instance : IrreducibleSpace (P1 k) := by
  have hne : Nonempty (P1 k) :=
    ⟨(chartι k 0).base (Nonempty.some inferInstance)⟩
  refine { toPreirreducibleSpace := ⟨?_⟩, toNonempty := hne }
  rintro u v hu hv ⟨a, -, ha⟩ ⟨b, -, hb⟩
  obtain ⟨a', ha'u, ha'0⟩ := exists_mem_chartOpen_zero_of_isOpen k hu ⟨a, ha⟩
  obtain ⟨b', hb'v, hb'0⟩ := exists_mem_chartOpen_zero_of_isOpen k hv ⟨b, hb⟩
  rw [← opensRange_chartι k 0] at ha'0 hb'0
  obtain ⟨a'', ha''⟩ := ha'0
  obtain ⟨b'', hb''⟩ := hb'0
  have hdense : Dense ((chartι k 0).base ⁻¹' u) :=
    IsOpen.dense (hu.preimage (chartι k 0).continuous)
      ⟨a'', by rwa [Set.mem_preimage, ha'']⟩
  obtain ⟨y₀, hy₀v, hy₀u⟩ := hdense.inter_open_nonempty _
    (hv.preimage (chartι k 0).continuous) ⟨b'', by rwa [Set.mem_preimage, hb'']⟩
  exact ⟨(chartι k 0).base y₀, trivial, hy₀u, hy₀v⟩

/-- The generic point of the standard chart is the generic point of P1. -/
theorem chartι_base_genericPoint :
    (chartι k 0).base (genericPoint (Spec (CommRingCat.of (Away 𝒜 (X (0 : Fin 2)))))) =
      genericPoint (P1 k) :=
  genericPoint_eq_of_isOpenImmersion (chartι k 0)

section FromSpecChart

variable {A : CommRingCat.{u}} (ρ : CommRingCat.of k ⟶ A)

/-- Evaluation of the section ring of `D₊(Xᵢ)` in a ring `A` under `k`. -/
noncomputable def chartEval (i : Fin 2) (a : A) :
    CommRingCat.of (Away 𝒜 (X i)) ⟶ A :=
  CommRingCat.ofHom ((Polynomial.eval₂RingHom ρ.hom a).comp (awayToPoly k i).toRingHom)

theorem chartEval_apply (i : Fin 2) (a : A) (z : Away 𝒜 (X i)) :
    (chartEval k ρ i a).hom z =
      Polynomial.eval₂ ρ.hom a (awayToPoly k i z) := rfl

theorem chartEval_chartCoord {i j : Fin 2} (hij : i ≠ j) (a : A) :
    (chartEval k ρ i a).hom (chartCoord k i j) = a := by
  rw [chartEval_apply, awayToPoly_chartCoord k hij, Polynomial.eval₂_X]

theorem chartEval_algebraMap (i : Fin 2) (a : A) (r : k) :
    (chartEval k ρ i a).hom (algebraMap k (Away 𝒜 (X i)) r) = ρ.hom r := by
  rw [chartEval_apply, AlgHom.commutes, Polynomial.algebraMap_eq, Polynomial.eval₂_C]

/-- The morphism through `D₊(Xᵢ)` sending the chart coordinate to `a`. -/
noncomputable def fromSpecChart (i : Fin 2) (a : A) : Spec A ⟶ P1 k :=
  Spec.map (chartEval k ρ i a) ≫ chartι k i

theorem chartι_structureMap (i : Fin 2) :
    chartι k i ≫ structureMap k =
      Spec.map (CommRingCat.ofHom (algebraMap k (Away 𝒜 (X i)))) := by
  exact awayIota_structureMap k (X_mem k i) one_pos

/-- `fromSpecChart` is a morphism over `k`. -/
theorem fromSpecChart_structureMap (i : Fin 2) (a : A) :
    fromSpecChart k ρ i a ≫ structureMap k = Spec.map ρ := by
  rw [fromSpecChart, Category.assoc, chartι_structureMap, ← Spec.map_comp]
  congr 1
  ext r
  exact chartEval_algebraMap k ρ i a r

/-- `fromSpecChart` is natural in the ring. -/
theorem SpecMap_fromSpecChart {A' : CommRingCat.{u}} (g : A ⟶ A') (i : Fin 2) (a : A) :
    Spec.map g ≫ fromSpecChart k ρ i a =
      fromSpecChart k (ρ ≫ g) i (g.hom a) := by
  rw [fromSpecChart, fromSpecChart, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext z
  change g.hom (Polynomial.eval₂ ρ.hom a (awayToPoly k i z)) =
    Polynomial.eval₂ (ρ ≫ g).hom (g.hom a) (awayToPoly k i z)
  rw [Polynomial.hom_eval₂, CommRingCat.hom_comp]

/-! ### The gluing identity -/

theorem SpecMap_awayToOverlapLeft_chartι :
    Spec.map (CommRingCat.ofHom (awayToOverlapLeft k)) ≫ chartι k 0 =
      Proj.awayι 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1)
        (X_mul_X_mem k) two_pos := by
  rw [awayToOverlapLeft_eq]
  exact Proj.SpecMap_awayMap_awayι 𝒜 (X_mem k 0) one_pos (X_mem k 1) rfl

theorem SpecMap_awayToOverlapRight_chartι :
    Spec.map (CommRingCat.ofHom (awayToOverlapRight k)) ≫ chartι k 1 =
      Proj.awayι 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1)
        (X_mul_X_mem k) two_pos := by
  rw [awayToOverlapRight_eq]
  exact Proj.SpecMap_awayMap_awayι 𝒜 (X_mem k 1) one_pos (X_mem k 0)
    (mul_comm (X 0) (X 1))

theorem algebraMap_awayToOverlapLeft :
    algebraMap (Away 𝒜 (X (0 : Fin 2)))
        (Away 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1)) =
      awayToOverlapLeft k := rfl

/-- The two chart descriptions agree on a unit of `A`. -/
theorem fromSpecChart_units (u : Aˣ) :
    fromSpecChart k ρ 0 (u : A) =
      fromSpecChart k ρ 1 ((u⁻¹ : Aˣ) : A) := by
  have hunit : IsUnit ((chartEval k ρ 0 (u : A)).hom (chartCoord k 0 1)) := by
    rw [chartEval_chartCoord k ρ fin_zero_ne_one]
    exact u.isUnit
  set ψ : Away 𝒜 ((X 0 : MvPolynomial (Fin 2) k) * X 1) →+* A :=
    IsLocalization.Away.lift (chartCoord k 0 1) hunit with hψ
  have hleft : ψ.comp (awayToOverlapLeft k) =
      (chartEval k ρ 0 (u : A)).hom := by
    refine RingHom.ext fun z => ?_
    rw [RingHom.comp_apply, ← algebraMap_awayToOverlapLeft]
    exact IsLocalization.Away.lift_eq (chartCoord k 0 1) hunit z
  have hTu : ψ (awayToOverlapLeft k (chartCoord k 0 1)) = (u : A) :=
    (RingHom.congr_fun hleft (chartCoord k 0 1)).trans
      (chartEval_chartCoord k ρ fin_zero_ne_one (u : A))
  have hSu : ψ (awayToOverlapRight k (chartCoord k 1 0)) =
      ((u⁻¹ : Aˣ) : A) := by
    have hmul := congrArg ψ (awayToOverlap_mul_eq_one k)
    rw [map_mul, map_one, hTu] at hmul
    exact (Units.inv_eq_of_mul_eq_one_right hmul).symm
  have hbase : (ψ.comp (awayToOverlapRight k)).comp
      (algebraMap k (Away 𝒜 (X 1))) = ρ.hom := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, awayToOverlapRight_algebraMap,
      ← awayToOverlapLeft_algebraMap, ← RingHom.comp_apply, hleft]
    exact chartEval_algebraMap k ρ 0 (u : A) c
  have hright : ψ.comp (awayToOverlapRight k) =
      (chartEval k ρ 1 ((u⁻¹ : Aˣ) : A)).hom := by
    refine RingHom.ext fun z => ?_
    obtain ⟨p, rfl⟩ := polyToAway_surjective k fin_one_ne_zero z
    rw [chartEval_apply]
    have hpoly := AlgHom.congr_fun
      (awayToPoly_comp_polyToAway k fin_one_ne_zero) p
    have hpoly' : awayToPoly k 1 (polyToAway k 1 0 p) = p := by
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hpoly
    rw [hpoly']
    change (ψ.comp (awayToOverlapRight k))
      (Polynomial.aeval (chartCoord k 1 0) p) = _
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hbase,
      RingHom.comp_apply, hSu]
  have hfactor₀ : chartEval k ρ 0 (u : A) =
      CommRingCat.ofHom (awayToOverlapLeft k) ≫ CommRingCat.ofHom ψ := by
    ext z
    exact (RingHom.congr_fun hleft z).symm
  have hfactor₁ : chartEval k ρ 1 ((u⁻¹ : Aˣ) : A) =
      CommRingCat.ofHom (awayToOverlapRight k) ≫ CommRingCat.ofHom ψ := by
    ext z
    exact (RingHom.congr_fun hright z).symm
  rw [fromSpecChart, fromSpecChart, hfactor₀, hfactor₁, Spec.map_comp,
    Spec.map_comp, Category.assoc, Category.assoc,
    SpecMap_awayToOverlapLeft_chartι, SpecMap_awayToOverlapRight_chartι]

/-! ### The generic point -/

/-- A transcendental chart value sends the generic point to the generic point of `P1`. -/
theorem fromSpecChart_base_genericPoint [IsDomain A] (a : A)
    (hinj : ∀ P : Polynomial k, P ≠ 0 →
      Polynomial.eval₂ ρ.hom a P ≠ 0) :
    (fromSpecChart k ρ 0 a).base (genericPoint (Spec A)) =
      genericPoint (P1 k) := by
  have hker : Function.Injective (chartEval k ρ 0 a).hom := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨p, rfl⟩ := polyToAway_surjective k fin_zero_ne_one z
    rw [chartEval_apply] at hz
    have hpoly := AlgHom.congr_fun
      (awayToPoly_comp_polyToAway k fin_zero_ne_one) p
    have hpoly' : awayToPoly k 0 (polyToAway k 0 1 p) = p := by
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hpoly
    rw [hpoly'] at hz
    by_contra hzne
    exact hinj p (fun h0 => hzne (by rw [h0, map_zero])) hz
  have h1 : (Spec.map (chartEval k ρ 0 a)).base
      (genericPoint (Spec A)) =
      genericPoint (Spec (CommRingCat.of (Away 𝒜 (X (0 : Fin 2))))) := by
    rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    exact Ideal.comap_bot_of_injective _ hker
  rw [fromSpecChart, Scheme.Hom.comp_apply, h1, chartι_base_genericPoint]

end FromSpecChart

end P1

end AlgebraicGeometry
