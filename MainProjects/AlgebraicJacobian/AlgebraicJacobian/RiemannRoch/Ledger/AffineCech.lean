/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Degree-one Čech cobounding for the structure sheaf on an affine open

This file proves the algebraic core of degree-one cohomology vanishing on affine opens
(Serre): on an affine open `U` of a scheme `X`, every Čech 1-cocycle for the structure
sheaf on a finite cover of `U` by basic opens is a coboundary
(`AlgebraicGeometry.IsAffineOpen.exists_cech_cobounding`).

The proof is the classical partition-of-unity argument, carried out entirely in the
language of sections of the structure sheaf (no abstract localizations appear in the
statement): given a cocycle `a i j ∈ Γ(X, D(f i) ⊓ D(f j))` for `f : Fin n → Γ(X, U)`
with `⨆ i, D(f i) = U`,

1. *clear denominators* (`IsAffineOpen.exists_res_eq_pow_mul`): each `f j ^ N * a i j`
   extends to a section `e i j` on `D(f i)`, with one uniform exponent `N`;
2. *annihilate the defects* (`IsAffineOpen.exists_pow_mul_eq_zero_of_res_eq_zero`): the
   defect `t i j l = e i l - e j l - f l ^ N * a i j` on `D(f i) ⊓ D(f j)` restricts to
   zero on the triple intersection by the cocycle identity, so `f l ^ M * t i j l = 0`
   for one uniform `M`;
3. *partition of unity*: `1 = ∑ h l * f l ^ (N + M)` in `Γ(X, U)` since the `D(f i)`
   cover `U`, and `b i = ∑ l, h l * (f l ^ M * e i l)` is the desired cobounding.

Both helper lemmas are the `IsLocalization.Away` property of sections over basic opens of
an affine open, repackaged through `Scheme.resHom`; they are stated for a section `g`
living on any open `W ≥ U`, which is the form needed in the main argument (there `U` is a
basic open of the cover and `W` the ambient affine open).

The statements are for an arbitrary scheme `X` and an affine open `U`; the affine-scheme
case is `U = ⊤`. This file is `Ext`-free; it is consumed by
`AlgebraicJacobian.Cohomology.AffineVanishing`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u})

/-- Restriction of sections of the structure sheaf along an inclusion of opens, as a ring
homomorphism. A convenience wrapper around `X.presheaf.map` that composes cleanly
(`Scheme.resHom_resHom`); the inclusion proof argument is proof-irrelevant. -/
noncomputable def resHom {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

variable {X}

@[simp]
lemma resHom_resHom {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (t : Γ(X, U)) :
    X.resHom h₂ (X.resHom h₁ t) = X.resHom (h₂.trans h₁) t := by
  rw [resHom, resHom, resHom, ← CommRingCat.comp_apply, ← X.presheaf.map_comp,
    ← op_comp, homOfLE_comp]

lemma resHom_refl {U : X.Opens} (t : Γ(X, U)) : X.resHom le_rfl t = t := by
  have h : (homOfLE (le_refl U)).op = 𝟙 (op U) := rfl
  rw [resHom, h, X.presheaf.map_id]
  rfl

/-- Restriction along `U ≤ U` is the identity (for an arbitrary proof, which is
proof-irrelevant). -/
@[simp]
lemma resHom_self {U : X.Opens} (h : U ≤ U) (t : Γ(X, U)) : X.resHom h t = t :=
  resHom_refl t

lemma basicOpen_resHom {U W : X.Opens} (h : U ≤ W) (g : Γ(X, W)) :
    X.basicOpen (X.resHom h g) = U ⊓ X.basicOpen g :=
  X.basicOpen_res _ _

/-- The canonical algebra structure on sections over a basic open (mathlib's
`algebra_section_section_basicOpen` instance), in `resHom` normal form. -/
lemma algebraMap_basicOpen_eq_resHom {U : X.Opens} (f : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen f) = X.resHom (X.basicOpen_le f) :=
  rfl

end Scheme

namespace IsAffineOpen

open Scheme

variable {X : Scheme.{u}} {U W : X.Opens} (hU : IsAffineOpen U) (hUW : U ≤ W)
  (g : Γ(X, W))

include hU in
/-- Denominator clearing on an affine open: a section `c` of the structure sheaf on
`U ⊓ D(g)` becomes the restriction of a section on `U` after multiplication by a power
of `g` (a section on any open `W ≥ U`). -/
theorem exists_res_eq_pow_mul (c : Γ(X, U ⊓ X.basicOpen g)) :
    ∃ (N : ℕ) (e : Γ(X, U)),
      X.resHom inf_le_left e = X.resHom (inf_le_left.trans hUW) g ^ N * c := by
  have hb : X.basicOpen (X.resHom hUW g) = U ⊓ X.basicOpen g :=
    basicOpen_resHom hUW g
  haveI := hU.isLocalization_basicOpen (X.resHom hUW g)
  obtain ⟨⟨y, m⟩, hy⟩ := IsLocalization.surj
    (M := Submonoid.powers (X.resHom hUW g)) (X.resHom hb.le c)
  dsimp only at hy
  obtain ⟨Nm, hNm⟩ := (Submonoid.mem_powers_iff (m : Γ(X, U))
    (X.resHom hUW g)).mp m.2
  refine ⟨Nm, y, ?_⟩
  have hy' := congrArg (X.resHom hb.ge) hy
  rw [← hNm] at hy'
  simp only [Scheme.algebraMap_basicOpen_eq_resHom, map_mul, map_pow, resHom_resHom,
    resHom_self] at hy'
  linear_combination -hy'

include hU in
/-- Annihilation on an affine open: a section of the structure sheaf on `U` restricting to
zero on `U ⊓ D(g)` is killed by a power of `g`. -/
theorem exists_pow_mul_eq_zero_of_res_eq_zero (t : Γ(X, U))
    (ht : X.resHom (inf_le_left : U ⊓ X.basicOpen g ≤ U) t = 0) :
    ∃ M : ℕ, X.resHom hUW g ^ M * t = 0 := by
  have hb : X.basicOpen (X.resHom hUW g) = U ⊓ X.basicOpen g :=
    basicOpen_resHom hUW g
  haveI := hU.isLocalization_basicOpen (X.resHom hUW g)
  have h0 : algebraMap Γ(X, U) Γ(X, X.basicOpen (X.resHom hUW g)) t = 0 := by
    rw [Scheme.algebraMap_basicOpen_eq_resHom]
    have hcomp : X.resHom (X.basicOpen_le (X.resHom hUW g)) t =
        X.resHom hb.le (X.resHom inf_le_left t) := by
      rw [Scheme.resHom_resHom]
    rw [hcomp, ht, map_zero]
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (X.resHom hUW g)) _ t).mp h0
  obtain ⟨M, hM⟩ := (Submonoid.mem_powers_iff (m : Γ(X, U))
    (X.resHom hUW g)).mp m.2
  refine ⟨M, ?_⟩
  calc X.resHom hUW g ^ M * t = ↑m * t := by rw [← hM]
    _ = 0 := hm

variable {hU hUW g}

/-- **Degree-one Čech cobounding on an affine open.** Let `U` be an affine open of a
scheme `X`, covered by finitely many basic opens `D(f i)` of sections `f i ∈ Γ(X, U)`.
Every 1-cocycle `a i j` of sections of the structure sheaf on the pairwise intersections
(with the cocycle identity on triple intersections) is a coboundary: there are sections
`b i` on `D(f i)` with `a i j = b i - b j` on `D(f i) ⊓ D(f j)`.

This is the algebraic heart of `H¹(U, 𝒪_X) = 0` for affine `U` (Serre). -/
theorem exists_cech_cobounding (hU : IsAffineOpen U) {n : ℕ} (f : Fin n → Γ(X, U))
    (hcov : ⨆ i, X.basicOpen (f i) = U)
    (a : ∀ i j, Γ(X, X.basicOpen (f i) ⊓ X.basicOpen (f j)))
    (hc : ∀ i j l,
      X.resHom (inf_le_inf_right (X.basicOpen (f l)) inf_le_left) (a i l) =
        X.resHom inf_le_left (a i j) +
          X.resHom (inf_le_inf_right (X.basicOpen (f l)) inf_le_right) (a j l)) :
    ∃ b : ∀ i, Γ(X, X.basicOpen (f i)),
      ∀ i j, a i j = X.resHom inf_le_left (b i) - X.resHom inf_le_right (b j) := by
  classical
  have haff : ∀ i : Fin n, IsAffineOpen (X.basicOpen (f i)) := fun i ↦ hU.basicOpen (f i)
  have haff2 : ∀ i j : Fin n, IsAffineOpen (X.basicOpen (f i) ⊓ X.basicOpen (f j)) := by
    intro i j
    rw [← X.basicOpen_mul]
    exact hU.basicOpen _
  -- Step 1: clear denominators, with a uniform exponent `N`.
  choose N₀ e₀ he₀ using fun i j ↦
    (haff i).exists_res_eq_pow_mul (X.basicOpen_le (f i)) (f j) (a i j)
  obtain ⟨N, hN⟩ : ∃ N, ∀ i j, N₀ i j ≤ N :=
    ⟨Finset.univ.sup fun p : Fin n × Fin n ↦ N₀ p.1 p.2,
      fun i j ↦ Finset.le_sup (f := fun p : Fin n × Fin n ↦ N₀ p.1 p.2)
        (Finset.mem_univ (i, j))⟩
  obtain ⟨e, he⟩ : ∃ e : ∀ i : Fin n, Fin n → Γ(X, X.basicOpen (f i)),
      ∀ i j, X.resHom inf_le_left (e i j) =
        X.resHom (inf_le_left.trans (X.basicOpen_le (f i))) (f j) ^ N * a i j := by
    refine ⟨fun i j ↦ X.resHom (X.basicOpen_le (f i)) (f j) ^ (N - N₀ i j) * e₀ i j,
      fun i j ↦ ?_⟩
    calc X.resHom inf_le_left
          (X.resHom (X.basicOpen_le (f i)) (f j) ^ (N - N₀ i j) * e₀ i j)
        = X.resHom inf_le_left (X.resHom (X.basicOpen_le (f i)) (f j)) ^ (N - N₀ i j) *
            X.resHom inf_le_left (e₀ i j) := by rw [map_mul, map_pow]
      _ = X.resHom (inf_le_left.trans (X.basicOpen_le (f i))) (f j) ^ (N - N₀ i j) *
            (X.resHom (inf_le_left.trans (X.basicOpen_le (f i))) (f j) ^ N₀ i j *
              a i j) := by rw [resHom_resHom, he₀ i j]
      _ = X.resHom (inf_le_left.trans (X.basicOpen_le (f i))) (f j) ^ N * a i j := by
            rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hN i j)]
  -- Step 2: the defects vanish on triple intersections, hence are killed by powers.
  obtain ⟨t, ht_def⟩ : ∃ t : ∀ i j : Fin n, Fin n →
        Γ(X, X.basicOpen (f i) ⊓ X.basicOpen (f j)),
      ∀ i j l, t i j l =
        X.resHom inf_le_left (e i l) - X.resHom inf_le_right (e j l) -
          X.resHom (inf_le_left.trans (X.basicOpen_le (f i))) (f l) ^ N * a i j :=
    ⟨_, fun _ _ _ ↦ rfl⟩
  have ht0 : ∀ i j l, X.resHom
      (inf_le_left : (X.basicOpen (f i) ⊓ X.basicOpen (f j)) ⊓ X.basicOpen (f l) ≤ _)
      (t i j l) = 0 := by
    intro i j l
    have hil := congrArg
      (X.resHom (inf_le_inf_right (X.basicOpen (f l)) inf_le_left :
        X.basicOpen (f i) ⊓ X.basicOpen (f j) ⊓ X.basicOpen (f l) ≤
          X.basicOpen (f i) ⊓ X.basicOpen (f l))) (he i l)
    have hjl := congrArg
      (X.resHom (inf_le_inf_right (X.basicOpen (f l)) inf_le_right :
        X.basicOpen (f i) ⊓ X.basicOpen (f j) ⊓ X.basicOpen (f l) ≤
          X.basicOpen (f j) ⊓ X.basicOpen (f l))) (he j l)
    rw [map_mul, map_pow, resHom_resHom, resHom_resHom] at hil hjl
    rw [ht_def i j l, map_sub, map_sub, map_mul, map_pow, resHom_resHom, resHom_resHom,
      resHom_resHom, hil, hjl, hc i j l]
    ring
  choose M₀ hM₀ using fun i j l ↦
    (haff2 i j).exists_pow_mul_eq_zero_of_res_eq_zero
      ((inf_le_left.trans (X.basicOpen_le (f i))) :
        X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ U)
      (f l) (t i j l) (ht0 i j l)
  obtain ⟨M, hM⟩ : ∃ M, ∀ i j l, M₀ i j l ≤ M :=
    ⟨Finset.univ.sup fun p : Fin n × Fin n × Fin n ↦ M₀ p.1 p.2.1 p.2.2,
      fun i j l ↦ Finset.le_sup (f := fun p : Fin n × Fin n × Fin n ↦ M₀ p.1 p.2.1 p.2.2)
        (Finset.mem_univ (i, j, l))⟩
  have hMt : ∀ i j l, X.resHom
      ((inf_le_left.trans (X.basicOpen_le (f i))) :
        X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ U) (f l) ^ M * t i j l = 0 := by
    intro i j l
    have h0 : X.resHom (inf_le_left.trans (X.basicOpen_le (f i))) (f l) ^ (M - M₀ i j l) *
        (X.resHom (inf_le_left.trans (X.basicOpen_le (f i))) (f l) ^ M₀ i j l *
          t i j l) = 0 := by
      rw [hM₀ i j l, mul_zero]
    rwa [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hM i j l)] at h0
  -- Step 3: partition of unity for the exponent `N + M`.
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    rw [← hU.iSup_basicOpen_eq_self_iff]
    rw [iSup_range' (fun g ↦ X.basicOpen g) f]
    exact hcov
  have hspanK : Ideal.span (Set.range fun i ↦ f i ^ (N + M)) = ⊤ := by
    have hpow := Ideal.span_pow_eq_top (Set.range f) hspan (N + M)
    rwa [← Set.range_comp] at hpow
  have hone : (1 : Γ(X, U)) ∈ Ideal.span (Set.range fun i ↦ f i ^ (N + M)) := by
    rw [hspanK]; trivial
  rw [Ideal.mem_span_range_iff_exists_fun] at hone
  obtain ⟨h, hh⟩ := hone
  -- Step 4: assemble the cobounding.
  refine ⟨fun i ↦ ∑ l, X.resHom (X.basicOpen_le (f i)) (h l) *
    (X.resHom (X.basicOpen_le (f i)) (f l) ^ M * e i l), fun i j ↦ ?_⟩
  have key : ∀ l : Fin n,
      X.resHom (inf_le_left : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ _)
          (X.resHom (X.basicOpen_le (f i)) (h l) *
            (X.resHom (X.basicOpen_le (f i)) (f l) ^ M * e i l)) -
        X.resHom (inf_le_right : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ _)
          (X.resHom (X.basicOpen_le (f j)) (h l) *
            (X.resHom (X.basicOpen_le (f j)) (f l) ^ M * e j l)) =
      X.resHom (inf_le_left.trans (X.basicOpen_le (f i))) (h l * f l ^ (N + M)) *
        a i j := by
    intro l
    have hkill := hMt i j l
    rw [ht_def i j l] at hkill
    simp only [map_mul, map_pow, resHom_resHom]
    linear_combination (X.resHom (inf_le_left.trans (X.basicOpen_le (f i)) :
      X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ U) (h l)) * hkill
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun l _ ↦ key l]
  rw [← Finset.sum_mul, ← map_sum, hh, map_one, one_mul]

end IsAffineOpen

namespace Scheme

variable (X : Scheme.{u}) [IsAffine X]

/-- **Degree-one Čech cobounding on an affine scheme**: the special case `U = ⊤` of
`IsAffineOpen.exists_cech_cobounding`. -/
theorem exists_cech_cobounding {n : ℕ} (f : Fin n → Γ(X, ⊤))
    (hcov : ⨆ i, X.basicOpen (f i) = ⊤)
    (a : ∀ i j, Γ(X, X.basicOpen (f i) ⊓ X.basicOpen (f j)))
    (hc : ∀ i j l,
      X.resHom (inf_le_inf_right (X.basicOpen (f l)) inf_le_left) (a i l) =
        X.resHom inf_le_left (a i j) +
          X.resHom (inf_le_inf_right (X.basicOpen (f l)) inf_le_right) (a j l)) :
    ∃ b : ∀ i, Γ(X, X.basicOpen (f i)),
      ∀ i j, a i j = X.resHom inf_le_left (b i) - X.resHom inf_le_right (b j) :=
  (isAffineOpen_top X).exists_cech_cobounding f hcov a hc

end Scheme

end AlgebraicGeometry
