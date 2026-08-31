/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivScheme
import AlgebraicJacobian.RiemannRoch.CarveDegree

/-!
# DDR-6 — classify + factor: `divClassifyAff` (`informal/spec-dd-r.md` §3 item 6)

The classification of a certified divisor family through the carve locus: a family over
an affine test whose ε-pair is presented through a pair chart of the Grassmannian pair
and satisfies the carve `(♦)` factors **uniquely** through the closed immersion
`divSchemeι : DivScheme g ⟶ grPair` — DDR-1's universal property
(`divScheme_exists_factor_of_le_ker` + the `carveIdeal_le_ker_iff*` keystones) supplies
existence, DDR-7's hom-ext (`Mono divSchemeι` via `divScheme_hom_ext`) uniqueness.

## Layout

* **§1 The generic chart-framed classification**: for an arbitrary multiplier family,
  a chart map `w : R_{I,J} →ₐ[k] S` pulling the tautological pair back to a pair of
  submodules satisfying the carve kills the carve ideal
  (`carveIdeal_le_ker_of_map_pairTaut`), hence factors uniquely through the glued
  carve locus (`existsUnique_carveScheme_factor_of_map_pairTaut`).  The mechanism is
  the DDR-1 keystone `carveIdeal_le_ker_iff_carve_map` (the L1 carve transport):
  the pulled-back tautological pair *is* the framed pair, by `map_toSubmodule`.
* **§2 The conjugation kit**: the carve-pair arrow is invariant under conjugating the
  multiplier by ambient `k`-linear equivalences and mapping the submodule pair by
  their base changes (`carvePairArrow_map_baseChange_eq_zero_iff`) — the bridge
  between the abstract window ambients `H_M`, `H_{M+s}` of DD-4's `ε` and the
  coordinate ambients `Fin r → k` of the scheme side (spec §3 preamble).
* **§3 The campaign spelling** (`divClassifyAff`): a divisor family `F` over an affine
  test `S` whose ε-pair satisfies the carve in DDR-2's spelling
  (`carvePairArrow (windowShiftMul hπ g a) ε₁ ε₂ = 0`) and is chart-framed through the
  DD-4 boundary bases `b₁`, `b₂` factors uniquely through `divSchemeι`.  The window
  reindexing `H⁰(𝒪(s·F + M·F)) = H⁰(𝒪((M+s)·F))` is `windowShiftEquiv`, and the
  second boundary basis of `DivScheme` is its transport `b₂.map (windowShiftEquiv …).symm`
  (`divCarveMul_basis_map` identifies the coordinate multiplier with the conjugated
  `windowShiftMul` — DDR-2's multiplier and DDR-1's carve ideal agree on the nose).

## What is NOT here (recorded for the DDR-9 consumer)

The chart-frame data (`hw₁`/`hw₂`) is honest *input*: producing it from the finite
projective ε-certificates over a basic-open cover of `Spec S` (frame loci,
`matrixPoint_factors_chart_iff`, morphism gluing) is the affine-global assembly, and
ε-naturality along localizations (DD-4 Task 7, not landed) enters only there.  The
restated DDR-9 backward direction (spec Addendum 1) should glue the `v`'s of
`divClassifyAff` over a common refinement of its base cover and the frame cover,
matching overlaps by `divScheme_hom_ext`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

open Grassmannian

/-! ## §1 The generic chart-framed classification -/

section Generic

variable (k : Type u) [Field k] (g r₁ r₂ : ℕ)
variable {ι : Type u} (μ : ι → ((Fin r₁ → k) →ₗ[k] (Fin r₂ → k)))

/-- **The chart-framed classification keystone** (DDR-6): a chart map `w : R_{I,J} → S`
pulling the tautological pair back to a pair of submodules that satisfies the carve
`(♦)` over `S` kills the carve ideal `I_♦`.  Mechanism: the DDR-1 keystone
`carveIdeal_le_ker_iff_carve_map` reduces the kill condition to the carve for the
pulled-back tautological pair, which *is* the framed pair by `map_toSubmodule`. -/
theorem carveIdeal_le_ker_of_map_pairTaut
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    {S : Type u} [CommRing S] [Algebra k S]
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] S)
    {K₁ : Submodule S (TensorProduct k S (Fin r₁ → k))}
    {K₂ : Submodule S (TensorProduct k S (Fin r₂ → k))}
    (hw₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule = K₁)
    (hw₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule = K₂)
    (hcarve : ∀ m, carvePairArrow (μ m) K₁ K₂ = 0) :
    carveIdeal k g r₁ r₂ μ i j ≤ RingHom.ker w.toRingHom := by
  letI : Algebra (PairChartRing k g r₁ g r₂ i j) S := w.toAlgebra
  letI : IsScalarTower k (PairChartRing k g r₁ g r₂ i j) S :=
    IsScalarTower.of_algebraMap_eq' w.comp_algebraMap.symm
  have hgoal : carveIdeal k g r₁ r₂ μ i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) S) := by
    rw [carveIdeal_le_ker_iff_carve_map]
    intro m
    rw [← Module.Grassmannian.map_toSubmodule w (pairTautFst k g r₁ r₂ i j),
      ← Module.Grassmannian.map_toSubmodule w (pairTautSnd k g r₁ r₂ i j), hw₁, hw₂]
    exact hcarve m
  exact hgoal

/-- **The generic chart-framed classification** (DDR-6, existence + uniqueness): a
chart map presenting a carve-satisfying framed pair factors **uniquely** through the
glued carve locus `Z(♦)` — existence by DDR-1's universal property
(`carveScheme_exists_factor_of_le_ker`), uniqueness by the closed immersion being a
monomorphism (`carveScheme_hom_ext`, DDR-7's tail). -/
theorem existsUnique_carveScheme_factor_of_map_pairTaut
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    {S : Type u} [CommRing S] [Algebra k S]
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] S)
    {K₁ : Submodule S (TensorProduct k S (Fin r₁ → k))}
    {K₂ : Submodule S (TensorProduct k S (Fin r₂ → k))}
    (hw₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule = K₁)
    (hw₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule = K₂)
    (hcarve : ∀ m, carvePairArrow (μ m) K₁ K₂ = 0) :
    ∃! v : Spec (CommRingCat.of S) ⟶ carveScheme k g r₁ r₂ μ,
      v ≫ carveSchemeι k g r₁ r₂ μ
        = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j := by
  obtain ⟨v, hv⟩ := carveScheme_exists_factor_of_le_ker k g r₁ r₂ μ i j w.toRingHom
    (carveIdeal_le_ker_of_map_pairTaut k g r₁ r₂ μ i j w hw₁ hw₂ hcarve)
  exact ⟨v, hv, fun v' hv' => carveScheme_hom_ext k g r₁ r₂ μ v' v (hv'.trans hv.symm)⟩

end Generic

/-! ## §2 The conjugation kit -/

namespace Grassmannian

section Conj

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R]
variable {H₁ H₂ H₁' H₂' : Type u}
variable [AddCommGroup H₁] [Module k H₁] [AddCommGroup H₂] [Module k H₂]
variable [AddCommGroup H₁'] [Module k H₁'] [AddCommGroup H₂'] [Module k H₂']

/-- Base change of a `k`-linear equivalence composed with base change of its inverse is
the identity — the injectivity input of the conjugation transport. -/
theorem baseChange_symm_comp_baseChange (e : H₂ ≃ₗ[k] H₂') :
    LinearMap.baseChange R e.symm.toLinearMap ∘ₗ LinearMap.baseChange R e.toLinearMap
      = LinearMap.id := by
  rw [← LinearMap.baseChange_comp,
    show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from
      LinearMap.ext fun x => e.symm_apply_apply x,
    LinearMap.baseChange_id]

/-- **The conjugation transport of the carve-pair arrow**: conjugating the multiplier by
ambient `k`-linear equivalences and mapping the submodule pair by their base changes
does not move the vanishing of the carve-pair arrow.  The bridge between the abstract
window ambients of DD-4's `ε` and the coordinate ambients of the scheme side. -/
theorem carvePairArrow_map_baseChange_eq_zero_iff
    (e₁ : H₁ ≃ₗ[k] H₁') (e₂ : H₂ ≃ₗ[k] H₂') (μ : H₁ →ₗ[k] H₂)
    (K₁ : Submodule R (TensorProduct k R H₁)) (K₂ : Submodule R (TensorProduct k R H₂)) :
    carvePairArrow (e₂.toLinearMap ∘ₗ μ ∘ₗ e₁.symm.toLinearMap)
        (K₁.map (LinearMap.baseChange R e₁.toLinearMap))
        (K₂.map (LinearMap.baseChange R e₂.toLinearMap)) = 0
      ↔ carvePairArrow μ K₁ K₂ = 0 := by
  have hnat : ∀ y : TensorProduct k R H₁,
      LinearMap.baseChange R (e₂.toLinearMap ∘ₗ μ ∘ₗ e₁.symm.toLinearMap)
          (LinearMap.baseChange R e₁.toLinearMap y)
        = LinearMap.baseChange R e₂.toLinearMap (LinearMap.baseChange R μ y) := by
    have h1 : (e₂.toLinearMap ∘ₗ μ ∘ₗ e₁.symm.toLinearMap) ∘ₗ e₁.toLinearMap
        = e₂.toLinearMap ∘ₗ μ := LinearMap.ext fun x => by
      simp [LinearMap.comp_apply]
    have hcomp : LinearMap.baseChange R (e₂.toLinearMap ∘ₗ μ ∘ₗ e₁.symm.toLinearMap)
          ∘ₗ LinearMap.baseChange R e₁.toLinearMap
        = LinearMap.baseChange R e₂.toLinearMap ∘ₗ LinearMap.baseChange R μ := by
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h1]
    intro y
    exact LinearMap.congr_fun hcomp y
  have hinj : Function.Injective (LinearMap.baseChange R e₂.toLinearMap) :=
    Function.LeftInverse.injective
      (g := LinearMap.baseChange R e₂.symm.toLinearMap) fun z =>
        LinearMap.congr_fun (baseChange_symm_comp_baseChange (R := R) e₂) z
  rw [carvePairArrow_eq_zero_iff, carvePairArrow_eq_zero_iff]
  constructor
  · intro h y hy
    have h1 := h (LinearMap.baseChange R e₁.toLinearMap y) (Submodule.mem_map_of_mem hy)
    rw [hnat y] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    rwa [← hinj hzeq]
  · rintro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hnat y]
    exact Submodule.mem_map_of_mem (h y hy)

end Conj

end Grassmannian


end AlgebraicGeometry
