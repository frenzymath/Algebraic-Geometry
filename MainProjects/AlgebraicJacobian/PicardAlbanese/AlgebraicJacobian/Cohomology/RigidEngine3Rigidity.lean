/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# RE-3 — split/flat rigidity of the two-term pushforward complex (module coefficients)

This is the `RE-3` sub-brick of the wave-4 rigid two-term pushforward engine
(`AJCR.w4-rep`, worksheet `informal/w4-rigid-engine-worksheet.md`, §3.1 layer 3). It
formalises *split/flat rigidity* for the degree-zero cohomology of a two-term complex,
purely at the level of `R`-module algebra: no schemes appear (discipline note D1).

The engine's two-term complex is an `R`-linear map `δ : A →ₗ[R] B` (in the intended
application `A = M₀ × M₁`, `B = N`, and `δ (m₀, m₁) = ι₀ m₀ − ι₁ m₁`). Its cohomology is
`H⁰ := LinearMap.ker δ` and `H¹ := B ⧸ LinearMap.range δ`. On the *fibrewise-vanishing
locus* the hypothesis `Subsingleton H¹` holds, i.e. `δ` is surjective; combined with
flatness of the codomain `B` this makes the formation of `H⁰` commute with `⊗_R P` for
**every** `R`-module `P` — and, `R'`-linearly, with **every** base change `R → R'`.

This is Kleiman 3.10 (v)⟹(iii) in curve-lite form (worksheet §1.1): the
representing-functor bookkeeping `eq:Q` (`Hom(Q, N) ≅ f_*(L ⊗ f^*N)`) is delivered as the
module-coefficient clause `LinearMap.ker (δ.rTensor P) ≅ H⁰ ⊗ P`. No two-term complex of
finite projectives is ever constructed: `H⁰` is exhibited as `LinearMap.ker δ` directly and
its base change is on the nose.

Kernels do **not** commute with `⊗` without a hypothesis: for `δ = (· * p) : ℤ →ₗ ℤ` one
has `LinearMap.ker δ = 0` but `LinearMap.ker (δ.rTensor (ZMod p)) ≅ ZMod p` — the `h⁰` jump
is real. Flatness of `B` (which holds on the nose in the application, where `B` is `R`-free)
is exactly what rules it out.

## Main results (for `δ : A →ₗ[R] B` with `Function.Surjective δ`)

* `RigidEngine.rTensor_surjective`, `RigidEngine.subsingleton_coker_rTensor`: the coker of
  the base-changed complex vanishes for every `R`-module `P` (right-exactness of `⊗`).
* `RigidEngine.kerRTensorEquiv` (needs `Module.Flat R B`): the module-coefficient base
  change `LinearMap.ker δ ⊗[R] P ≃ₗ[R] LinearMap.ker (δ.rTensor P)`.
* `RigidEngine.kerBaseChangeEquiv` (needs `Module.Flat R B`): the `R'`-linear ring-map
  corollary `R' ⊗[R] LinearMap.ker δ ≃ₗ[R'] LinearMap.ker (δ.baseChange R')`.
* `RigidEngine.flat_ker` (needs `Module.Flat R A`, `Module.Projective R B`): `H⁰` is flat.
* `RigidEngine.projective_ker` (adds `IsNoetherianRing R`, `Module.Finite R H⁰`): `H⁰` is a
  finite projective `R`-module.

The consumer (RE-4) instantiates these with the two-lattice pair's `δ`; the finiteness of
`H⁰` (`Module.Finite R H⁰`) is supplied there from COH-0 (RE-1b).
-/

universe u v w

open scoped TensorProduct

namespace AlgebraicJacobian.RigidEngine

variable {R : Type u} [CommRing R]
variable {A : Type v} [AddCommGroup A] [Module R A]
variable {B : Type w} [AddCommGroup B] [Module R B]
variable (δ : A →ₗ[R] B)

/-- `δ` composed with the inclusion of its kernel is the zero map. -/
theorem comp_ker_subtype : δ ∘ₗ (LinearMap.ker δ).subtype = 0 := by
  ext x
  exact LinearMap.mem_ker.mp x.2

/-- **The `Subsingleton H¹ ⟹ δ surjective` bridge.** The engine's standing hypothesis on
the fibrewise-vanishing locus is `Subsingleton H¹` with `H¹ := B ⧸ LinearMap.range δ`; this
is exactly surjectivity of `δ`, the form every result below consumes. 
 * Provenance: CUSTOM.
-/
theorem surjective_of_subsingleton_quotient
    (h : Subsingleton (B ⧸ LinearMap.range δ)) : Function.Surjective δ := by
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_iff'.2 fun b => ?_
  exact (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)

/-- **Coker vanishing (map form).** If `δ` is surjective then so is its base change
`δ.rTensor P` along every `R`-module `P` (right-exactness of `⊗`). 
 * Provenance: CUSTOM.
-/
theorem rTensor_surjective (hδ : Function.Surjective δ)
    (P : Type*) [AddCommGroup P] [Module R P] :
    Function.Surjective (δ.rTensor P) :=
  LinearMap.rTensor_surjective P hδ

/-- **Coker vanishing (`Subsingleton` form).** The cokernel of the base-changed complex
`δ.rTensor P` is subsingleton for every `R`-module `P`; equivalently `H¹` base-changes to
zero (worksheet §3.1 layer 2). 
 * Provenance: CUSTOM.
-/
theorem subsingleton_coker_rTensor (hδ : Function.Surjective δ)
    (P : Type*) [AddCommGroup P] [Module R P] :
    Subsingleton ((B ⊗[R] P) ⧸ LinearMap.range (δ.rTensor P)) := by
  have h : LinearMap.range (δ.rTensor P) = ⊤ :=
    LinearMap.range_eq_top.mpr (rTensor_surjective δ hδ P)
  rw [h]; infer_instance

section BaseChange

variable [Module.Flat R B]

/-- The natural `R`-linear map `H⁰ ⊗ P → ker (δ ⊗ P)` induced by the inclusion of the
kernel, corestricted to the kernel of the base-changed complex. 
 * Provenance: ADAPTED.
-/
noncomputable def kerRTensorToKer (P : Type*) [AddCommGroup P] [Module R P] :
    (LinearMap.ker δ) ⊗[R] P →ₗ[R] LinearMap.ker (δ.rTensor P) :=
  LinearMap.codRestrict _ ((LinearMap.ker δ).subtype.rTensor P) fun c => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      comp_ker_subtype, LinearMap.rTensor_zero, LinearMap.zero_apply]

/-- **Module-coefficient base change of `H⁰` (worksheet §3.1 layer 3).** For a surjective
`δ : A →ₗ[R] B` with `B` flat, the formation of `H⁰ := LinearMap.ker δ` commutes with
`⊗_R P` for **every** `R`-module `P`:
`LinearMap.ker δ ⊗[R] P ≃ₗ[R] LinearMap.ker (δ.rTensor P)`, naturally. This is the
representing-functor clause of Kleiman `eq:Q`. 
 * Provenance: ADAPTED.
-/
noncomputable def kerRTensorEquiv (hδ : Function.Surjective δ)
    (P : Type*) [AddCommGroup P] [Module R P] :
    (LinearMap.ker δ) ⊗[R] P ≃ₗ[R] LinearMap.ker (δ.rTensor P) := by
  refine LinearEquiv.ofBijective (kerRTensorToKer δ P) ⟨?_, ?_⟩
  · -- injective: the inclusion of the kernel stays injective after `⊗ P` (flat codomain)
    have hlt : Function.Injective ((LinearMap.ker δ).subtype.lTensor P) :=
      LinearMap.lTensor_injective_of_exact_of_flat δ hδ (LinearMap.ker δ).subtype
        (LinearMap.ker δ).injective_subtype (LinearMap.exact_subtype_ker_map δ) P
    have hrt : Function.Injective ((LinearMap.ker δ).subtype.rTensor P) :=
      (LinearMap.lTensor_inj_iff_rTensor_inj (M := P)
        (f := (LinearMap.ker δ).subtype)).1 hlt
    intro x y hxy
    exact hrt (congrArg Subtype.val hxy)
  · -- surjective onto the kernel: right-exactness of `⊗` (no flatness needed here)
    rintro ⟨z, hz⟩
    have hexact : Function.Exact ((LinearMap.ker δ).subtype.rTensor P) (δ.rTensor P) :=
      rTensor_exact P (LinearMap.exact_subtype_ker_map δ) hδ
    obtain ⟨w, hw⟩ := (LinearMap.exact_iff.1 hexact ▸ hz :
      z ∈ LinearMap.range ((LinearMap.ker δ).subtype.rTensor P))
    exact ⟨w, Subtype.ext hw⟩

end BaseChange

section RingMap

variable [Module.Flat R B] (R' : Type*) [CommRing R'] [Algebra R R']

/-- The `R'`-linear map `R' ⊗ H⁰ → ker (δ_{R'})` induced by base change of the kernel
inclusion. 
 * Provenance: ADAPTED.
-/
noncomputable def kerBaseChangeToKer :
    R' ⊗[R] (LinearMap.ker δ) →ₗ[R'] LinearMap.ker (δ.baseChange R') :=
  LinearMap.codRestrict _ ((LinearMap.ker δ).subtype.baseChange R') fun c => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      comp_ker_subtype, LinearMap.baseChange_zero, LinearMap.zero_apply]

/-- **`R'`-linear ring-map base change of `H⁰` (worksheet §3.1 layer 3, ring case).** For a
surjective `δ : A →ₗ[R] B` with `B` flat and any `R`-algebra `R'`, formation of
`H⁰ := LinearMap.ker δ` commutes on the nose with base change `R → R'`, as an
`R'`-linear equivalence `R' ⊗[R] LinearMap.ker δ ≃ₗ[R'] LinearMap.ker (δ.baseChange R')`.
This is the `rigidEngine_baseChange` seam (`≃ₗ[R']`, never `Nonempty`; discipline note 3). 
 * Provenance: ADAPTED.
-/
noncomputable def kerBaseChangeEquiv (hδ : Function.Surjective δ) :
    R' ⊗[R] (LinearMap.ker δ) ≃ₗ[R'] LinearMap.ker (δ.baseChange R') := by
  refine LinearEquiv.ofBijective (kerBaseChangeToKer δ R') ⟨?_, ?_⟩
  · -- injective: base change of the kernel inclusion is injective (flat codomain)
    have hlt : Function.Injective ((LinearMap.ker δ).subtype.lTensor R') :=
      LinearMap.lTensor_injective_of_exact_of_flat δ hδ (LinearMap.ker δ).subtype
        (LinearMap.ker δ).injective_subtype (LinearMap.exact_subtype_ker_map δ) R'
    have hbc : Function.Injective ⇑((LinearMap.ker δ).subtype.baseChange R') := by
      rw [LinearMap.baseChange_eq_ltensor]; exact hlt
    intro x y hxy
    exact hbc (congrArg Subtype.val hxy)
  · -- surjective onto the kernel: right-exactness of `⊗` at the level of underlying maps
    rintro ⟨z, hz⟩
    have hexact : Function.Exact ((LinearMap.ker δ).subtype.lTensor R') (δ.lTensor R') :=
      lTensor_exact R' (LinearMap.exact_subtype_ker_map δ) hδ
    have hz' : (δ.lTensor R') z = 0 := by
      have := LinearMap.mem_ker.mp hz
      rwa [LinearMap.baseChange_eq_ltensor] at this
    obtain ⟨w, hw⟩ := (LinearMap.exact_iff.1 hexact ▸ LinearMap.mem_ker.mpr hz' :
      z ∈ LinearMap.range ((LinearMap.ker δ).subtype.lTensor R'))
    refine ⟨w, Subtype.ext ?_⟩
    change (LinearMap.ker δ).subtype.baseChange R' w = z
    rw [LinearMap.baseChange_eq_ltensor]
    exact hw

end RingMap

/-- **Flatness of `H⁰` (worksheet §3.1: "direct summand of `C⁰`").** If `δ` is surjective
with flat domain `A` and projective codomain `B`, then `δ` splits, exhibiting
`H⁰ := LinearMap.ker δ` as a retract of `A`; hence `H⁰` is flat. 
 * Provenance: CUSTOM.
-/
theorem flat_ker (hδ : Function.Surjective δ) [Module.Flat R A] [Module.Projective R B] :
    Module.Flat R (LinearMap.ker δ) := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property δ LinearMap.id hδ
  have hmem : ∀ a : A, ((LinearMap.id : A →ₗ[R] A) - σ ∘ₗ δ) a ∈ LinearMap.ker δ := by
    intro a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, sub_self]
  refine Module.Flat.of_retract (LinearMap.ker δ).subtype
    (((LinearMap.id : A →ₗ[R] A) - σ ∘ₗ δ).codRestrict (LinearMap.ker δ) hmem) ?_
  ext x
  simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
    LinearMap.sub_apply, LinearMap.id_apply]
  rw [show δ (x : A) = 0 from LinearMap.mem_ker.mp x.2, map_zero, sub_zero]

/-- **Finite projectivity of `H⁰` (worksheet §1.2 `finite_projective_h0`).** Over a
Noetherian ring, if `δ` is surjective with flat domain, projective codomain, and finite
kernel (the latter supplied by COH-0), then `H⁰ := LinearMap.ker δ` is a finite projective
`R`-module. The Noetherian hypothesis is spent only on `finite ⟹ finitely presented`. 
 * Provenance: ADAPTED.
-/
theorem projective_ker (hδ : Function.Surjective δ) [IsNoetherianRing R]
    [Module.Flat R A] [Module.Projective R B] [Module.Finite R (LinearMap.ker δ)] :
    Module.Projective R (LinearMap.ker δ) := by
  haveI : Module.Flat R (LinearMap.ker δ) := flat_ker δ hδ
  haveI : Module.FinitePresentation R (LinearMap.ker δ) :=
    Module.finitePresentation_of_finite R (LinearMap.ker δ)
  exact Module.Flat.projective_of_finitePresentation

end AlgebraicJacobian.RigidEngine
