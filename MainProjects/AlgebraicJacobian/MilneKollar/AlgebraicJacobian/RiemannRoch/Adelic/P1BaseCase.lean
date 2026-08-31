/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Computability.Reduce
import AlgebraicJacobian.Picard.ProjectiveSpace

/-!
# The ℙ¹ base case for adelic Riemann–Roch (node `N11a`) and the finite-map gate

This file is part of the **adelic Riemann–Roch lane** (see the lane design document).
It supplies the *base case* of the genus-finiteness keystone and the *gate class*
recording the classical existence of a finite map to the projective line; it does
**not** prove the keystone itself.

## The concrete ℙ¹ cohomology vanishing (`N11a`)

For the standard two-chart cover `{U₀, U₁}` of the projective line `ℙ¹_k`, with
affine coordinate `x` on `U₀` and `x⁻¹` on `U₁`, the Čech `H¹` is the cokernel
```
Γ(U₀ ∩ U₁, 𝒪) / (Γ(U₀, 𝒪) + Γ(U₁, 𝒪))  =  k[x, x⁻¹] / (k[x] + k[x⁻¹]).
```
This cokernel is **zero**, because every Laurent polynomial splits as a
nonnegative-degree part (in `k[x]`) plus a negative-degree part (in `k[x⁻¹]`).
This is `H¹(ℙ¹, 𝒪_{ℙ¹}) = 0`, the base case the keystone reduces to.

We phrase the split purely algebraically, at the level of `LaurentPolynomial R`
submodules, so the keystone can consume it after identifying the ℙ¹ chart rings:

* `Adelic.nonnegLaurentSubmodule R` — `k[x] ⊆ k[x, x⁻¹]`, spanned by `{xⁿ : 0 ≤ n}`;
* `Adelic.nonposLaurentSubmodule R` — `k[x⁻¹] ⊆ k[x, x⁻¹]`, spanned by `{xⁿ : n ≤ 0}`;
* `Adelic.nonneg_sup_nonpos_eq_top` — **the Laurent split**: their sum is everything;
* `Adelic.subsingleton_laurentCokernel` — hence the cokernel is a subsingleton.

## The finite-map gate (node `N9`)

* `Adelic.HasFiniteMapToP1 C` — a single-field `Prop` class asserting the existence
  of a finite `k`-morphism `C ⟶ ℙ¹_k`. This is a **gate** in the `HasPicScheme`
  style: it records a *Kleiman-independent classical existence statement* (any
  nonconstant rational function `x ∈ k(C)` with `[k(C) : k(x)] < ∞` yields such a
  map). It carries **no instance**; the future keystone `N11` consumes it, and the
  proved instance (transcendence degree one of `k(C)/k`) is later work.

## Finiteness of chart preimages under a finite morphism (node `N10`)

* `Adelic.isAffineOpen_preimage_of_isFinite`,
  `Adelic.module_finite_app_of_isFinite` — for **any** finite morphism `π : X ⟶ Y`
  and affine open `V ⊆ Y`, the preimage `π⁻¹V` is affine and its coordinate ring
  `Γ(X, π⁻¹V)` is a *finite module* over `Γ(Y, V)`. The keystone applies these to
  the two standard affine charts of `ℙ¹`, so that with a finite `π : C ⟶ ℙ¹` the
  chart preimages `π⁻¹U₀, π⁻¹U₁` are affine with coordinate rings finite over the
  ℙ¹ chart rings `k[x], k[x⁻¹]` (integral-closure finiteness).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits LaurentPolynomial

namespace AlgebraicGeometry.Adelic

/-! ### `N11a` — the Laurent split `k[x, x⁻¹] = k[x] + k[x⁻¹]` -/

section Laurent

variable (R : Type*) [CommRing R]

/-- The image of `k[x]` inside `k[x, x⁻¹]`: the `R`-submodule of `LaurentPolynomial R`
spanned by the monomials `xⁿ` of nonnegative degree.  This is the ℙ¹ chart ring
`Γ(U₀, 𝒪)` regarded inside `Γ(U₀ ∩ U₁, 𝒪) = k[x, x⁻¹]`. -/
noncomputable def nonnegLaurentSubmodule : Submodule R (LaurentPolynomial R) :=
  Submodule.span R (Set.range fun n : ℕ => (T (n : ℤ) : LaurentPolynomial R))

/-- The image of `k[x⁻¹]` inside `k[x, x⁻¹]`: the `R`-submodule of `LaurentPolynomial R`
spanned by the monomials `xⁿ` of nonpositive degree.  This is the ℙ¹ chart ring
`Γ(U₁, 𝒪)` regarded inside `Γ(U₀ ∩ U₁, 𝒪) = k[x, x⁻¹]`. -/
noncomputable def nonposLaurentSubmodule : Submodule R (LaurentPolynomial R) :=
  Submodule.span R (Set.range fun n : ℕ => (T (-(n : ℤ)) : LaurentPolynomial R))

variable {R}

/-- A monomial equals its constant coefficient scaling the pure power `xⁿ`. -/
lemma C_mul_T_eq_smul (a : R) (n : ℤ) :
    (C a * T n : LaurentPolynomial R) = a • T n := by
  simp [Algebra.smul_def]

/-- Every nonnegative pure power `xⁿ` lies in the `k[x]` part. -/
lemma T_mem_nonneg_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    (T n : LaurentPolynomial R) ∈ nonnegLaurentSubmodule R := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
  exact Submodule.subset_span ⟨m, rfl⟩

/-- Every nonpositive pure power `xⁿ` lies in the `k[x⁻¹]` part. -/
lemma T_mem_nonpos_of_nonpos {n : ℤ} (hn : n ≤ 0) :
    (T n : LaurentPolynomial R) ∈ nonposLaurentSubmodule R := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := by
    refine ⟨(-n).toNat, ?_⟩
    have := Int.toNat_of_nonneg (neg_nonneg.mpr hn)
    omega
  exact Submodule.subset_span ⟨m, rfl⟩

/-- **The Laurent split (node `N11a`).**  Inside `k[x, x⁻¹] = LaurentPolynomial R`, the
sum of the nonnegative part `k[x]` and the nonpositive part `k[x⁻¹]` is everything:
```
k[x, x⁻¹] = k[x] + k[x⁻¹].
```
Equivalently, the difference map `k[x] ⊕ k[x⁻¹] → k[x, x⁻¹]` is surjective, so the ℙ¹
Čech cokernel `Γ(U₀ ∩ U₁, 𝒪) / (Γ(U₀, 𝒪) + Γ(U₁, 𝒪))` vanishes: `H¹(ℙ¹, 𝒪_{ℙ¹}) = 0`. -/
theorem nonneg_sup_nonpos_eq_top :
    nonnegLaurentSubmodule R ⊔ nonposLaurentSubmodule R = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro f
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq => exact Submodule.add_mem _ hp hq
  | C_mul_T n a =>
    rw [C_mul_T_eq_smul]
    rcases le_total 0 n with hn | hn
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ a (T_mem_nonneg_of_nonneg hn))
    · exact Submodule.mem_sup_right (Submodule.smul_mem _ a (T_mem_nonpos_of_nonpos hn))

/-- **The ℙ¹ base case, cokernel form.**  The ℙ¹ Čech cokernel
`k[x, x⁻¹] / (k[x] + k[x⁻¹])` is a subsingleton — the concrete incarnation of
`H¹(ℙ¹, 𝒪_{ℙ¹}) = 0`. -/
theorem subsingleton_laurentCokernel :
    Subsingleton (LaurentPolynomial R ⧸
      (nonnegLaurentSubmodule R ⊔ nonposLaurentSubmodule R)) := by
  rw [nonneg_sup_nonpos_eq_top]
  infer_instance

end Laurent

/-! ### `N9` — the finite-map gate, and `N10` — finiteness of chart preimages -/

variable {k : Type u} [Field k]

/-- **The finite-map gate (node `N9`).**  A single-field `Prop` class asserting the
existence of a finite `k`-morphism from the curve `C` to the projective line
`ℙ¹_k = ℙ(ULift (Fin 2); Spec k)`.

Introduced as a **gate** in the `HasPicScheme` style: a *Kleiman-independent classical
existence statement* — any nonconstant rational function `x ∈ k(C)` determines a finite
morphism `C ⟶ ℙ¹_k` of degree `[k(C) : k(x)]`.

**Update (2026-07-27): this class is no longer instance-free, and the docstring above
used to say otherwise.**  For an AJC curve the gate is now *discharged*, by a chain that
is present and sorry-free:

* `hasFiniteMapToP1_of_existsNonconstantMapToP1` (`FiniteMapToP1.lean`) — nonconstant
  ⟹ finite, via Zariski's main theorem;
* `existsNonconstantMapToP1_of_existsNonconstantMapToProjInt` and
  `existsNonconstantMapToProjInt_of_ajc` (`NonconstantToP1.lean`) — the two-chart
  construction of a nonconstant map, for `[SmoothOfRelativeDimension 1] [IsProper]
  [GeometricallyIntegral]`.

So the "proved instance is later work" claim is obsolete: under the AJC ambient
hypotheses this synthesises.  The class is kept because the keystone `N11` is stated at
greater generality than the AJC curve, where it is still an honest hypothesis.

The witness is packaged as a morphism in the over-category `Over (Spec k)`, so it
automatically commutes with the structure maps: it is a genuine `k`-morphism. -/
class HasFiniteMapToP1 (C : Over (Spec (CommRingCat.of k))) : Prop where
  /-- There exists a finite `k`-morphism `C ⟶ ℙ¹_k`. -/
  nonempty_finite_map :
    ∃ π : C ⟶ Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k)),
      IsFinite π.left

/-- **Node `N10`, affine part.**  The preimage of an affine open under a finite
morphism is affine.  Applied by the keystone to the two standard affine charts
`U₀, U₁` of `ℙ¹`: with a finite `π : C ⟶ ℙ¹`, the preimages `π⁻¹U₀, π⁻¹U₁` are
affine. -/
theorem isAffineOpen_preimage_of_isFinite {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π]
    {V : Y.Opens} (hV : IsAffineOpen V) : IsAffineOpen (π ⁻¹ᵁ V) :=
  hV.preimage π

/-- **Node `N10`, finiteness part.**  For a finite morphism `π : X ⟶ Y` and an affine
open `V ⊆ Y`, the coordinate ring `Γ(X, π⁻¹V)` is a *finite module* over `Γ(Y, V)`
(via the induced ring map `π.app V`).  Applied by the keystone to the two standard
affine charts of `ℙ¹`: the chart preimage coordinate rings are finite modules over
the ℙ¹ chart rings `k[x]`, `k[x⁻¹]` (the integral-closure finiteness of a finite
morphism). -/
theorem module_finite_app_of_isFinite {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π]
    (V : Y.Opens) (hV : IsAffineOpen V) :
    letI := (π.app V).hom.toAlgebra
    Module.Finite Γ(Y, V) Γ(X, π ⁻¹ᵁ V) :=
  IsFinite.finite_app π V hV

end AlgebraicGeometry.Adelic
