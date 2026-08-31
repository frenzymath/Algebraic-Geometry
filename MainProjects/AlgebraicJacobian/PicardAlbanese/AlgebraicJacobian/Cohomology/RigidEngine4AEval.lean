/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-!
# RE-4b (algebra half) — transport of `AEval'` chart-lattice finiteness

The rigid engine's chart-lattice finiteness is pinned in the spelling
`Module.Finite R[X] (Module.AEval' e)` (`…RigidEngineLatticeModelHom`). This file provides
the three pure module-algebra transports by which the Layer-2 instantiation discharges it
(`informal/w4-rigid-engine-worksheet.md` §4, RE-4b):

* `AlgebraicJacobian.RigidEngine.aevalCongr` (+ `moduleFinite_aeval'_of_linearEquiv`) —
  transport along an equivariant `R`-linear equivalence (used to move between the twisted
  sheaf's chart sections and the structure-sheaf sections, and along the sections
  base-change equivalence).
* `AlgebraicJacobian.RigidEngine.moduleFinite_aeval'_of_ringHom_finite` — the field-level
  entry point: if `φ : k[X] →+* A` is a finite ring map and the endomorphism `e` acts as
  multiplication by `φ X` (with the `k`-scalar action being multiplication by `φ ∘ C`),
  then the `AEval'` lattice of `e` is `k[X]`-finite. Applied with
  `φ = π^* ∘ (chartSectionsEquiv)⁻¹` this is exactly the E-i input
  `Curve/MapToP1.finite_app_chartOpen`.
* `AlgebraicJacobian.RigidEngine.moduleFinite_aeval'_baseChange` — the relative step: an
  `AEval'`-finite lattice over `k[X]` base-changes to an `AEval'`-finite lattice of the
  base-changed endomorphism over `R[X]`, for any `k`-algebra `R` (finitely many
  generators, coefficients pushed through `Polynomial.map (algebraMap k R)`). Composed
  with `aevalCongr` along `relSectionsBaseChange`, this is "`Γ(V₀ᴿ) ≅ Γ(V₀) ⊗_k R` is
  finite over `R[t]`" — the relative E-i.

No schemes appear in this file (the D1 module-algebra discipline).
-/

set_option autoImplicit false

universe u v

open Polynomial

open scoped TensorProduct

namespace AlgebraicJacobian.RigidEngine

/-! ## Transport along an equivariant linear equivalence -/

section Congr

variable {S : Type u} [CommRing S]
variable {M : Type v} {M' : Type*}
variable [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M']

/-- **`AEval'` transport along an equivariant equivalence**: an `S`-linear equivalence
intertwining two endomorphisms induces an `S[X]`-linear equivalence of their `AEval'`
modules. 
 * Provenance: CUSTOM.
-/
noncomputable def aevalCongr (e : Module.End S M) (e' : Module.End S M')
    (φ : M ≃ₗ[S] M') (h : ∀ m : M, φ (e m) = e' (φ m)) :
    Module.AEval' e ≃ₗ[S[X]] Module.AEval' e' :=
  LinearEquiv.ofAEval e (φ.trans (Module.AEval'.of e')) fun m => by
    change Module.AEval'.of e' (φ (e m)) = (X : S[X]) • Module.AEval'.of e' (φ m)
    rw [h, Module.AEval'.X_smul_of]

/-- Finiteness of the `AEval'` lattice transports along an equivariant equivalence. 
 * Provenance: CUSTOM.
-/
theorem moduleFinite_aeval'_of_linearEquiv (e : Module.End S M) (e' : Module.End S M')
    (φ : M ≃ₗ[S] M') (h : ∀ m : M, φ (e m) = e' (φ m))
    [Module.Finite S[X] (Module.AEval' e)] :
    Module.Finite S[X] (Module.AEval' e') :=
  Module.Finite.equiv (aevalCongr e e' φ h)

end Congr

/-! ## The field-level entry point: finiteness from a finite ring map -/

section RingHomFinite

variable {k : Type u} [CommRing k]
variable {A : Type u} [CommRing A] [Module k A]

/-- (Implementation) Powers of an endomorphism acting as multiplication by `u` act as
multiplication by powers of `u`. -/
private lemma pow_apply_of_mul (e : Module.End k A) (u : A) (he : ∀ a : A, e a = u * a)
    (n : ℕ) (a : A) : (e ^ n) a = u ^ n * a := by
  induction n generalizing a with
  | zero => rw [pow_zero, Module.End.one_apply, pow_zero, one_mul]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, he, pow_succ', mul_assoc]

/-- **The polynomial action through a ring map.** If `e` acts as multiplication by `φ X`
and the `k`-scalars act as multiplication by `φ ∘ C`, then the `aeval`-action of any
polynomial `p` on `A` is multiplication by `φ p`. 
 * Provenance: CUSTOM.
-/
lemma aeval_apply_of_ringHom (φ : k[X] →+* A) (e : Module.End k A)
    (he : ∀ a : A, e a = φ X * a)
    (hC : ∀ (c : k) (a : A), c • a = φ (C c) * a)
    (p : k[X]) (a : A) : Polynomial.aeval e p a = φ p * a := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, hp, hq, map_add, add_mul]
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      pow_apply_of_mul e (φ X) he, hC, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul,
      map_pow, mul_assoc]

/-- **RE-4b, field-level entry point**: if `φ : k[X] →+* A` is a finite ring map, `e`
acts as multiplication by `φ X`, and the `k`-scalar action is multiplication by `φ ∘ C`,
then the chart lattice `Module.AEval' e` is a finite `k[X]`-module (the engine's pinned
finiteness spelling). With `φ = π^* ∘ (chartSectionsEquiv)⁻¹` this is
`finite_app_chartOpen` in `AEval'` form. 
 * Provenance: CUSTOM.
-/
theorem moduleFinite_aeval'_of_ringHom_finite (φ : k[X] →+* A) (hfin : φ.Finite)
    (e : Module.End k A) (he : ∀ a : A, e a = φ X * a)
    (hC : ∀ (c : k) (a : A), c • a = φ (C c) * a) :
    Module.Finite k[X] (Module.AEval' e) := by
  classical
  letI : Algebra k[X] A := φ.toAlgebra
  haveI : Module.Finite k[X] A := hfin
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k[X]) (M := A)
  refine ⟨⟨s.image fun a => Module.AEval'.of e a, ?_⟩⟩
  rw [eq_top_iff]
  rintro w -
  obtain ⟨a, rfl⟩ : ∃ a : A, Module.AEval'.of e a = w :=
    ⟨(Module.AEval'.of e).symm w, by simp⟩
  have ha : a ∈ Submodule.span k[X] (s : Set A) := by rw [hs]; trivial
  induction ha using Submodule.span_induction with
  | mem a has =>
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ has))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul p x hx ih =>
    have heq : Module.AEval'.of e (p • x) = p • Module.AEval'.of e x := by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
        ← aeval_apply_of_ringHom φ e he hC p x]
      exact Module.AEval.of_aeval_smul e p x
    rw [heq]
    exact Submodule.smul_mem _ _ ih

end RingHomFinite

/-! ## The relative step: base change of `AEval'` finiteness -/

section BaseChange

variable {k : Type u} [CommRing k] (R : Type u) [CommRing R] [Algebra k R]
variable {M : Type u} [AddCommGroup M] [Module k M]

/-- **Base change of the polynomial action on a pure tensor**: the `aeval`-action of the
coefficient-pushed polynomial `p.map (algebraMap k R)` through the base-changed
endomorphism computes the original action in the second tensor factor. 
 * Provenance: CUSTOM.
-/
lemma aeval_baseChange_map_apply_one_tmul (e : Module.End k M) (p : k[X]) (m : M) :
    Polynomial.aeval (LinearMap.baseChange R e) (p.map (algebraMap k R))
        ((1 : R) ⊗ₜ[k] m)
      = (1 : R) ⊗ₜ[k] (Polynomial.aeval e p m) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hq, map_add,
      LinearMap.add_apply, TensorProduct.tmul_add]
  | monomial n c =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, ← LinearMap.baseChange_pow,
      LinearMap.baseChange_tmul, TensorProduct.tmul_smul, algebraMap_smul]

/-- **RE-4b, relative step (base change of `AEval'` finiteness)**: if the chart lattice
`Module.AEval' e` is `k[X]`-finite, then the base-changed lattice
`Module.AEval' (e.baseChange R)` on `R ⊗[k] M` is `R[X]`-finite, for every `k`-algebra
`R`. Generators are `1 ⊗ mᵢ`, with polynomial coefficients pushed through
`Polynomial.map (algebraMap k R)`. 
 * Provenance: CUSTOM.
-/
theorem moduleFinite_aeval'_baseChange (e : Module.End k M)
    [Module.Finite k[X] (Module.AEval' e)] :
    Module.Finite R[X] (Module.AEval' (LinearMap.baseChange R e)) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k[X]) (M := Module.AEval' e)
  have key : ∀ z ∈ Submodule.span k[X] (s : Set (Module.AEval' e)),
      Module.AEval'.of (LinearMap.baseChange R e)
          ((1 : R) ⊗ₜ[k] (Module.AEval'.of e).symm z) ∈
        Submodule.span R[X] ↑(s.image fun z =>
          Module.AEval'.of (LinearMap.baseChange R e)
            ((1 : R) ⊗ₜ[k] (Module.AEval'.of e).symm z)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hzs =>
      exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hzs))
    | zero =>
      rw [map_zero, TensorProduct.tmul_zero, map_zero]
      exact Submodule.zero_mem _
    | add u v hu hv ihu ihv =>
      rw [map_add, TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ ihu ihv
    | smul p z hz ih =>
      have hsm : (Module.AEval'.of e).symm (p • z)
          = Polynomial.aeval e p ((Module.AEval'.of e).symm z) :=
        Module.AEval.of_symm_smul e p z
      have heq : Module.AEval'.of (LinearMap.baseChange R e)
          ((1 : R) ⊗ₜ[k] (Module.AEval'.of e).symm (p • z))
          = Polynomial.map (algebraMap k R) p •
            Module.AEval'.of (LinearMap.baseChange R e)
              ((1 : R) ⊗ₜ[k] (Module.AEval'.of e).symm z) := by
        rw [hsm,
          ← aeval_baseChange_map_apply_one_tmul R e p ((Module.AEval'.of e).symm z)]
        exact Module.AEval.of_aeval_smul _ _ _
      rw [heq]
      exact Submodule.smul_mem _ _ ih
  refine ⟨⟨s.image fun z => Module.AEval'.of (LinearMap.baseChange R e)
    ((1 : R) ⊗ₜ[k] (Module.AEval'.of e).symm z), ?_⟩⟩
  rw [eq_top_iff]
  rintro w -
  obtain ⟨x, rfl⟩ : ∃ x : R ⊗[k] M, Module.AEval'.of (LinearMap.baseChange R e) x = w :=
    ⟨(Module.AEval'.of (LinearMap.baseChange R e)).symm w, by simp⟩
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul r m =>
    have heq : Module.AEval'.of (LinearMap.baseChange R e) (r ⊗ₜ[k] m)
        = (Polynomial.C r : R[X]) •
          Module.AEval'.of (LinearMap.baseChange R e) ((1 : R) ⊗ₜ[k] m) := by
      rw [Module.AEval.C_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
    rw [heq]
    refine Submodule.smul_mem _ _ ?_
    have hmem := key (Module.AEval'.of e m) (by rw [hs]; trivial)
    rwa [LinearEquiv.symm_apply_apply] at hmem

end BaseChange

end AlgebraicJacobian.RigidEngine
