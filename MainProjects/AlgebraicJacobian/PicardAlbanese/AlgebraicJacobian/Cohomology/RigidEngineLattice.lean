/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# RE-1a — the two-lattice pair: carriers, differential, cohomology, and maps

The **two-lattice pair** is the curve-lite avatar of a quasi-coherent module on `ℙ¹_R`
(`informal/w4-rigid-engine-worksheet.md` §1.2, Level 1): `R`-modules `M₀`, `M₁` (the two
chart lattices) and `N` (the overlap module), endomorphisms `t₀` of `M₀` and `t₁` of `M₁`
(the two chart coordinates — mutually inverse on the overlap) together with an *invertible*
endomorphism `tN` of `N`, and equivariant maps `ι₀ : M₀ →ₗ[R] N`, `ι₁ : M₁ →ₗ[R] N`
exhibiting `N` as the localization of each lattice at the powers of its chart coordinate.
The localization axioms are spelled bare-handedly (denominator clearing `denom₀/denom₁` and
defect annihilation `ann₀/ann₁` — term-for-term the `surj`/`exists_of_eq` axioms of
mathlib's `IsLocalizedModule` at `Submonoid.powers t`), the spelling recommended by the
worksheet's risk note 3 to avoid carrying two competing `R[X]`-module structures on `N`.

The two-term Čech complex of a pair is `diff : M₀ × M₁ →ₗ[R] N`, `(x, y) ↦ ι₀ x - ι₁ y`;
its cohomology is `H0 := ker diff` (a submodule of `M₀ × M₁`) and
`H1 := N ⧸ (range ι₀ ⊔ range ι₁)` (the cokernel of `diff`, by `range_diff_eq`). In the
geometric application `M₀, M₁` are the sections of a quasi-coherent sheaf on the pinned
affine two-cover `V₀ = π⁻¹D₊(X₀)`, `V₁ = π⁻¹D₊(X₁)` of the challenge curve, `N` the
overlap sections, and `H0`/`H1` compute the Čech cohomology of the sheaf (the vocabulary
of `AlgebraicJacobian.Cohomology.TwoCover`, `H1Cok`).

Maps of pairs (`TwoLatticePair.Hom`) are triples of `R`-linear maps commuting with the
coordinate actions and the localization maps; they induce maps on `H⁰` and `H¹`
(`Hom.h0Map`, `Hom.h1Map`).

## Main declarations

* `TwoLatticePair` — the two-lattice pair.
* `TwoLatticePair.diff`, `TwoLatticePair.H0`, `TwoLatticePair.H1`,
  `TwoLatticePair.range_diff_eq` — the two-term complex and its cohomology carriers.
* `TwoLatticePair.Hom` — maps of pairs; `Hom.h0Map`, `Hom.h1Map` — functoriality;
  `Hom.h1Map_surjective` — `H¹` is right exact in the pair.

The six-term exact sequence of a short exact sequence of pairs is in
`AlgebraicJacobian.Cohomology.RigidEngineLatticeSixTerm`; the `ℙ¹` line-bundle models and
the coherence theorems (COH-1/COH-0) are in `…LatticeModel`/`…LatticeCoherence`.
-/

set_option autoImplicit false

universe u

open Polynomial

variable (R : Type u) [CommRing R]
variable (M₀ : Type*) (M₁ : Type*) (N : Type*)
variable [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup N]
variable [Module R M₀] [Module R M₁] [Module R N]

/-- A **two-lattice pair** over the commutative ring `R`: the curve-lite avatar of a
quasi-coherent module on `ℙ¹_R`. `M₀` and `M₁` are the two chart lattices, `N` the overlap
module; `t₀`, `t₁`, `tN` are the chart-coordinate actions (`t₁` acting as the *inverse*
coordinate, and the overlap action `tN` invertible); `ι₀`, `ι₁` are the restriction maps
into the overlap, satisfying the bare-handed localization axioms (denominator clearing and
defect annihilation) at the powers of the respective coordinates. -/
structure TwoLatticePair where
  /-- The chart-0 coordinate action on the chart-0 lattice. -/
  t₀ : Module.End R M₀
  /-- The (inverse) chart-1 coordinate action on the chart-1 lattice. -/
  t₁ : Module.End R M₁
  /-- The invertible chart-0 coordinate action on the overlap module. -/
  tN : (Module.End R N)ˣ
  /-- The restriction of the chart-0 lattice into the overlap. -/
  ι₀ : M₀ →ₗ[R] N
  /-- The restriction of the chart-1 lattice into the overlap. -/
  ι₁ : M₁ →ₗ[R] N
  /-- `ι₀` intertwines `t₀` with the overlap action. -/
  ι₀_comm : ∀ x : M₀, ι₀ (t₀ x) = tN.val (ι₀ x)
  /-- `ι₁` intertwines `t₁` with the *inverse* overlap action. -/
  ι₁_comm : ∀ y : M₁, ι₁ (t₁ y) = tN.inv (ι₁ y)
  /-- Denominator clearing at chart 0: every overlap element comes from the chart-0
  lattice after clearing by a power of the coordinate. -/
  denom₀ : ∀ n : N, ∃ (m : ℕ) (x : M₀), (tN.val ^ m) n = ι₀ x
  /-- Denominator clearing at chart 1. -/
  denom₁ : ∀ n : N, ∃ (m : ℕ) (y : M₁), (tN.inv ^ m) n = ι₁ y
  /-- Defect annihilation at chart 0: a chart-0 section vanishing on the overlap is
  killed by a power of the coordinate. -/
  ann₀ : ∀ x : M₀, ι₀ x = 0 → ∃ m : ℕ, (t₀ ^ m) x = 0
  /-- Defect annihilation at chart 1. -/
  ann₁ : ∀ y : M₁, ι₁ y = 0 → ∃ m : ℕ, (t₁ ^ m) y = 0

namespace TwoLatticePair

variable {R M₀ M₁ N}
variable (P : TwoLatticePair R M₀ M₁ N)

/-! ### The invertible overlap action -/

@[simp]
lemma tN_inv_val_apply (n : N) : P.tN.inv (P.tN.val n) = n := by
  have h := congrArg (fun e : Module.End R N => e n) P.tN.inv_val
  simpa only [Module.End.mul_apply, Module.End.one_apply] using h

@[simp]
lemma tN_val_inv_apply (n : N) : P.tN.val (P.tN.inv n) = n := by
  have h := congrArg (fun e : Module.End R N => e n) P.tN.val_inv
  simpa only [Module.End.mul_apply, Module.End.one_apply] using h

lemma tN_inv_pow_val_pow_apply (m : ℕ) (n : N) :
    (P.tN.inv ^ m) ((P.tN.val ^ m) n) = n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ']
    simp only [Module.End.mul_apply, tN_inv_val_apply]
    exact ih

lemma tN_val_pow_inv_pow_apply (m : ℕ) (n : N) :
    (P.tN.val ^ m) ((P.tN.inv ^ m) n) = n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ']
    simp only [Module.End.mul_apply, tN_val_inv_apply]
    exact ih

/-! ### Iterated equivariance -/

lemma ι₀_pow_comm (m : ℕ) (x : M₀) :
    P.ι₀ ((P.t₀ ^ m) x) = (P.tN.val ^ m) (P.ι₀ x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ']
    simp only [Module.End.mul_apply]
    rw [P.ι₀_comm, ih]

lemma ι₁_pow_comm (m : ℕ) (y : M₁) :
    P.ι₁ ((P.t₁ ^ m) y) = (P.tN.inv ^ m) (P.ι₁ y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ']
    simp only [Module.End.mul_apply]
    rw [P.ι₁_comm, ih]

/-! ### The two-term complex and its cohomology -/

/-- The Čech differential of the pair: `(x, y) ↦ ι₀ x - ι₁ y`. -/
def diff : (M₀ × M₁) →ₗ[R] N :=
  P.ι₀ ∘ₗ LinearMap.fst R M₀ M₁ - P.ι₁ ∘ₗ LinearMap.snd R M₀ M₁

@[simp]
lemma diff_apply (z : M₀ × M₁) : P.diff z = P.ι₀ z.1 - P.ι₁ z.2 := rfl

/-- The image lattice `range ι₀ ⊔ range ι₁ ⊆ N`: the denominator of `H¹`. -/
def imageLattice : Submodule R N :=
  LinearMap.range P.ι₀ ⊔ LinearMap.range P.ι₁

/-- The range of the Čech differential is the image lattice. -/
theorem range_diff_eq : LinearMap.range P.diff = P.imageLattice := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro n ⟨z, rfl⟩
    rw [diff_apply]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨z.1, rfl⟩)
      (Submodule.mem_sup_right ⟨z.2, rfl⟩)
  · rintro n ⟨x, rfl⟩
    exact ⟨(x, 0), by simp⟩
  · rintro n ⟨y, rfl⟩
    exact ⟨(0, -y), by simp⟩

/-- `H⁰` of the pair: the kernel of the Čech differential, as a submodule of `M₀ × M₁`.
In the geometric application this computes the global sections of the sheaf. -/
def H0 : Submodule R (M₀ × M₁) := LinearMap.ker P.diff

lemma mem_H0 {z : M₀ × M₁} : z ∈ P.H0 ↔ P.diff z = 0 := Iff.rfl

lemma mem_H0_iff_eq {z : M₀ × M₁} : z ∈ P.H0 ↔ P.ι₀ z.1 = P.ι₁ z.2 := by
  rw [mem_H0, diff_apply, sub_eq_zero]

/-- `H¹` of the pair: the cokernel `N ⧸ (range ι₀ ⊔ range ι₁)` of the Čech differential
(`range_diff_eq`). In the geometric application this computes `H¹` of the sheaf on the
two-cover (the `TwoCover.H1Cok` mechanism). -/
abbrev H1 := N ⧸ P.imageLattice

/-- The quotient projection onto `H¹`. -/
def h1Mk : N →ₗ[R] P.H1 := P.imageLattice.mkQ

@[simp]
lemma h1Mk_apply (n : N) : P.h1Mk n = Submodule.Quotient.mk n := rfl

lemma h1Mk_surjective : Function.Surjective P.h1Mk :=
  Submodule.Quotient.mk_surjective _

@[simp]
lemma h1Mk_ι₀ (x : M₀) : P.h1Mk (P.ι₀ x) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_left ⟨x, rfl⟩)

@[simp]
lemma h1Mk_ι₁ (y : M₁) : P.h1Mk (P.ι₁ y) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_right ⟨y, rfl⟩)

/-- The class of an element of the image lattice vanishes in `H¹`; stated for the range
of the differential. -/
lemma h1Mk_diff (z : M₀ × M₁) : P.h1Mk (P.diff z) = 0 := by
  rw [diff_apply, map_sub, h1Mk_ι₀, h1Mk_ι₁, sub_zero]

/-! ### Maps of pairs -/

variable {M₀' M₁' N' : Type*}
variable [AddCommGroup M₀'] [AddCommGroup M₁'] [AddCommGroup N']
variable [Module R M₀'] [Module R M₁'] [Module R N']
variable {M₀'' M₁'' N'' : Type*}
variable [AddCommGroup M₀''] [AddCommGroup M₁''] [AddCommGroup N'']
variable [Module R M₀''] [Module R M₁''] [Module R N'']

/-- A **map of two-lattice pairs**: a triple of `R`-linear maps on the carriers commuting
with the coordinate actions and with the localization maps. -/
structure Hom (P : TwoLatticePair R M₀ M₁ N) (P' : TwoLatticePair R M₀' M₁' N') where
  /-- The map on chart-0 lattices. -/
  hom₀ : M₀ →ₗ[R] M₀'
  /-- The map on chart-1 lattices. -/
  hom₁ : M₁ →ₗ[R] M₁'
  /-- The map on overlap modules. -/
  homN : N →ₗ[R] N'
  /-- Compatibility with the chart-0 coordinate action. -/
  comm_t₀ : ∀ x : M₀, hom₀ (P.t₀ x) = P'.t₀ (hom₀ x)
  /-- Compatibility with the chart-1 coordinate action. -/
  comm_t₁ : ∀ y : M₁, hom₁ (P.t₁ y) = P'.t₁ (hom₁ y)
  /-- Compatibility with the overlap action. -/
  comm_tN : ∀ n : N, homN (P.tN.val n) = P'.tN.val (homN n)
  /-- Compatibility with the chart-0 localization map. -/
  comm_ι₀ : ∀ x : M₀, homN (P.ι₀ x) = P'.ι₀ (hom₀ x)
  /-- Compatibility with the chart-1 localization map. -/
  comm_ι₁ : ∀ y : M₁, homN (P.ι₁ y) = P'.ι₁ (hom₁ y)

namespace Hom

variable {P} {P' : TwoLatticePair R M₀' M₁' N'} {P'' : TwoLatticePair R M₀'' M₁'' N''}

/-- Maps of pairs are automatically compatible with the *inverse* overlap action. -/
lemma comm_tN_inv (f : P.Hom P') (n : N) :
    f.homN (P.tN.inv n) = P'.tN.inv (f.homN n) := by
  have h : f.homN n = P'.tN.val (f.homN (P.tN.inv n)) := by
    conv_lhs => rw [← P.tN_val_inv_apply n]
    exact f.comm_tN _
  rw [h, P'.tN_inv_val_apply]

lemma comm_t₀_pow (f : P.Hom P') (m : ℕ) (x : M₀) :
    f.hom₀ ((P.t₀ ^ m) x) = (P'.t₀ ^ m) (f.hom₀ x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ']
    simp only [Module.End.mul_apply]
    rw [f.comm_t₀, ih]

lemma comm_t₁_pow (f : P.Hom P') (m : ℕ) (y : M₁) :
    f.hom₁ ((P.t₁ ^ m) y) = (P'.t₁ ^ m) (f.hom₁ y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ']
    simp only [Module.End.mul_apply]
    rw [f.comm_t₁, ih]

lemma comm_tN_pow (f : P.Hom P') (m : ℕ) (n : N) :
    f.homN ((P.tN.val ^ m) n) = (P'.tN.val ^ m) (f.homN n) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ']
    simp only [Module.End.mul_apply]
    rw [f.comm_tN, ih]

lemma comm_tN_inv_pow (f : P.Hom P') (m : ℕ) (n : N) :
    f.homN ((P.tN.inv ^ m) n) = (P'.tN.inv ^ m) (f.homN n) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ']
    simp only [Module.End.mul_apply]
    rw [f.comm_tN_inv, ih]

/-- Naturality of the Čech differential in maps of pairs. -/
lemma diff_comm (f : P.Hom P') (z : M₀ × M₁) :
    P'.diff (f.hom₀ z.1, f.hom₁ z.2) = f.homN (P.diff z) := by
  simp only [diff_apply, map_sub, f.comm_ι₀, f.comm_ι₁]

/-- The induced map on `H⁰`. -/
def h0Map (f : P.Hom P') : P.H0 →ₗ[R] P'.H0 :=
  (f.hom₀.prodMap f.hom₁).restrict fun z hz => by
    rw [mem_H0, LinearMap.prodMap_apply, diff_comm, hz.out, map_zero]

@[simp]
lemma h0Map_coe (f : P.Hom P') (z : P.H0) :
    (f.h0Map z : M₀' × M₁') = (f.hom₀ (z : M₀ × M₁).1, f.hom₁ (z : M₀ × M₁).2) := rfl

/-- The induced map on `H¹`. -/
def h1Map (f : P.Hom P') : P.H1 →ₗ[R] P'.H1 :=
  Submodule.mapQ P.imageLattice P'.imageLattice f.homN <| by
    refine sup_le ?_ ?_
    · rintro n ⟨x, rfl⟩
      exact Submodule.mem_sup_left ⟨f.hom₀ x, (f.comm_ι₀ x).symm⟩
    · rintro n ⟨y, rfl⟩
      exact Submodule.mem_sup_right ⟨f.hom₁ y, (f.comm_ι₁ y).symm⟩

@[simp]
lemma h1Map_mk (f : P.Hom P') (n : N) :
    f.h1Map (Submodule.Quotient.mk n) = Submodule.Quotient.mk (f.homN n) :=
  Submodule.mapQ_apply _ _ _ n

/-- **Right exactness of `H¹` in the pair**: a map of pairs surjective on the overlap
modules is surjective on `H¹`. -/
lemma h1Map_surjective (f : P.Hom P') (hN : Function.Surjective f.homN) :
    Function.Surjective f.h1Map := by
  intro c
  obtain ⟨n', rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨n, rfl⟩ := hN n'
  exact ⟨Submodule.Quotient.mk n, f.h1Map_mk n⟩

end Hom

end TwoLatticePair
