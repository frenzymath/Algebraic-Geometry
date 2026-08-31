/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Defs

/-!
# DAT-1 (1c) — module-algebra toolkit for the m-chart glued constructor

The three pure module-algebra transports that the glued-sheaf constructor of
`informal/spec-dat-1.md` (Stage (1c)) fires when discharging the projectivity and
`AEval'`-finiteness obligations of its glued section modules:

* `Module.Projective.prod` — a product of two projective modules is projective (a named
  restatement of the mathlib instance, exposed under the DAT-1 API name);
* `Module.Projective.of_free_algebra` — the (D5) projective-trans over a free algebra:
  if `A` is a free `R`-algebra and `P` is a projective `A`-module, then `P` is projective
  as an `R`-module (split `P` off `P →₀ A` over `A`, then restrict the splitting to `R`,
  where `P →₀ A` is `R`-free);
* `AlgebraicJacobian.RigidEngine.moduleFinite_aeval'_of_smul_finite` — the (D5) `AEval'`
  transitivity through a finite algebra: if the endomorphism `eA` of `A` acting as
  multiplication by `a₀` has `R[X]`-finite `AEval'` lattice and `M` is a finite
  `A`-module, then any endomorphism of `M` acting as `a₀ • ·` (the landed E-i spelling
  `Scheme.mulSectionEnd`) also has `R[X]`-finite `AEval'` lattice.

No schemes appear in this file (the D1 module-algebra discipline).
-/

set_option autoImplicit false

universe u v

open Polynomial

/-! ## Projectivity of a product -/

/-- **Product projectivity**: a product of two projective modules is projective. This is
the (anonymous) mathlib instance on `M × N`, restated under the DAT-1 API name. -/
theorem Module.Projective.prod {R : Type u} [Semiring R] {M : Type v} {N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [Module.Projective R M] [Module.Projective R N] :
    Module.Projective R (M × N) :=
  inferInstance

/-! ## Projectivity over a free algebra -/

/-- **Projectivity descends along a free algebra** ((D5) projective-trans): if `A` is a
free `R`-algebra and `P` is a projective `A`-module, then `P` is projective as an
`R`-module. The `A`-splitting `P →ₗ[A] (P →₀ A)` provided by `Module.projective_def'`
restricts to an `R`-splitting, and `P →₀ A` is a free (hence projective) `R`-module. -/
theorem Module.Projective.of_free_algebra {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]
    [Module.Free R A] [Module.Projective A P] :
    Module.Projective R P := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective A P›
  exact Module.Projective.of_split
    (LinearMap.restrictScalars R s)
    (LinearMap.restrictScalars R (Finsupp.linearCombination A _root_.id))
    (LinearMap.ext fun p => DFunLike.congr_fun hs p)

namespace AlgebraicJacobian.RigidEngine

/-! ## The `AEval'` transitivity through a finite algebra -/

section AEvalTrans

variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

omit [Algebra R A] [IsScalarTower R A M] in
/-- (Implementation) Powers of an endomorphism acting as `a₀ • ·` act as `a₀ ^ n • ·`. -/
private lemma pow_apply_of_smul (a₀ : A) (e : Module.End R M)
    (he : ∀ m : M, e m = a₀ • m) (n : ℕ) (m : M) : (e ^ n) m = a₀ ^ n • m := by
  induction n generalizing m with
  | zero => rw [pow_zero, Module.End.one_apply, pow_zero, one_smul]
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, he, pow_succ', mul_smul]

/-- **The polynomial action through the algebra**: if `e` acts as `a₀ • ·` for a scalar
`a₀ : A` in the tower `R → A → M`, then the `aeval`-action of any polynomial `p : R[X]`
on `M` is scalar multiplication by `Polynomial.aeval a₀ p`. -/
lemma aeval_apply_of_smul (a₀ : A) (e : Module.End R M) (he : ∀ m : M, e m = a₀ • m)
    (p : R[X]) (m : M) : Polynomial.aeval e p m = Polynomial.aeval a₀ p • m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, map_add, add_smul]
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, pow_apply_of_smul a₀ e he, mul_smul, algebraMap_smul]

/-- **DAT-1 (1c), the (D5) `AEval'` transitivity**: let `a₀ : A` in an `R`-algebra `A`,
let `eA` be the endomorphism of `A` acting as multiplication by `a₀` (the landed E-i
spelling `Scheme.mulSectionEnd`), and suppose its chart lattice `Module.AEval' eA` is a
finite `R[X]`-module. If `M` is a finite `A`-module, then any endomorphism `e` of `M`
acting as `a₀ • ·` also has `R[X]`-finite chart lattice `Module.AEval' e`. Generators:
`of e (bᵢ • mⱼ)` for `R[X]`-generators `bᵢ` of `AEval' eA` and `A`-generators `mⱼ` of
`M`. -/
theorem moduleFinite_aeval'_of_smul_finite (a₀ : A) (eA : Module.End R A)
    (heA : ∀ a : A, eA a = a₀ * a)
    [Module.Finite R[X] (Module.AEval' eA)] [Module.Finite A M]
    (e : Module.End R M) (he : ∀ m : M, e m = a₀ • m) :
    Module.Finite R[X] (Module.AEval' e) := by
  classical
  have heA' : ∀ a : A, eA a = a₀ • a := fun a => by rw [heA, smul_eq_mul]
  obtain ⟨sA, hsA⟩ := Module.Finite.fg_top (R := R[X]) (M := Module.AEval' eA)
  obtain ⟨sM, hsM⟩ := Module.Finite.fg_top (R := A) (M := M)
  -- Step 1: for an `A`-generator `m ∈ sM`, every `a • m` lies in the candidate span.
  have key : ∀ (a : A), ∀ m ∈ sM, Module.AEval'.of e (a • m) ∈
      Submodule.span R[X] ↑((sA ×ˢ sM).image fun bm =>
        Module.AEval'.of e ((Module.AEval'.of eA).symm bm.1 • bm.2)) := by
    intro a m hm
    have haux : ∀ z ∈ Submodule.span R[X] (sA : Set (Module.AEval' eA)),
        Module.AEval'.of e ((Module.AEval'.of eA).symm z • m) ∈
          Submodule.span R[X] ↑((sA ×ˢ sM).image fun bm =>
            Module.AEval'.of e ((Module.AEval'.of eA).symm bm.1 • bm.2)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem b hb =>
        exact Submodule.subset_span (Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨(b, m), Finset.mem_product.mpr ⟨hb, hm⟩, rfl⟩))
      | zero =>
        rw [map_zero, zero_smul, map_zero]
        exact Submodule.zero_mem _
      | add u v _ _ ihu ihv =>
        rw [map_add, add_smul, map_add]
        exact Submodule.add_mem _ ihu ihv
      | smul p z _ ih =>
        have hsymm : (Module.AEval'.of eA).symm (p • z)
            = Polynomial.aeval eA p ((Module.AEval'.of eA).symm z) :=
          Module.AEval.of_symm_smul eA p z
        have heq : Module.AEval'.of e ((Module.AEval'.of eA).symm (p • z) • m)
            = p • Module.AEval'.of e ((Module.AEval'.of eA).symm z • m) := by
          rw [hsymm, aeval_apply_of_smul a₀ eA heA' p, smul_eq_mul, mul_smul,
            ← aeval_apply_of_smul a₀ e he p]
          exact Module.AEval.of_aeval_smul e p _
        rw [heq]
        exact Submodule.smul_mem _ _ ih
    have hmem := haux (Module.AEval'.of eA a) (by rw [hsA]; trivial)
    rwa [LinearEquiv.symm_apply_apply] at hmem
  -- Step 2: strengthen over the `A`-span — `a • x` lands in the span for every `a`.
  have key₂ : ∀ x ∈ Submodule.span A (sM : Set M), ∀ a : A,
      Module.AEval'.of e (a • x) ∈
        Submodule.span R[X] ↑((sA ×ˢ sM).image fun bm =>
          Module.AEval'.of e ((Module.AEval'.of eA).symm bm.1 • bm.2)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem m hm => exact fun a => key a m hm
    | zero =>
      intro a
      rw [smul_zero, map_zero]
      exact Submodule.zero_mem _
    | add u v _ _ ihu ihv =>
      intro a
      rw [smul_add, map_add]
      exact Submodule.add_mem _ (ihu a) (ihv a)
    | smul b x _ ih =>
      intro a
      rw [smul_smul]
      exact ih (a * b)
  refine ⟨⟨(sA ×ˢ sM).image fun bm =>
    Module.AEval'.of e ((Module.AEval'.of eA).symm bm.1 • bm.2), ?_⟩⟩
  rw [eq_top_iff]
  rintro w -
  obtain ⟨x, rfl⟩ : ∃ x : M, Module.AEval'.of e x = w :=
    ⟨(Module.AEval'.of e).symm w, by simp⟩
  have hone := key₂ x (by rw [hsM]; trivial) 1
  rwa [one_smul] at hone

end AEvalTrans

end AlgebraicJacobian.RigidEngine
