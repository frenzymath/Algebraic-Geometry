/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechAcyclic

/-!
# Čech 1-coboundary splitting over an affine open

This file packages the degree-1 instance of the positive-degree exactness of the
section Čech module complex (`SectionCechModule.dDiff_exact`, the module core of
Stacks 01EW) in the form the degree-1 affine vanishing `H¹(U affine, 𝒪_X) = 0`
consumes: for an affine open `U` of a scheme `X`, a finite family
`g : ι → Γ(X, U)` whose basic opens `D(gᵢ)` cover `U`, and an arbitrary
`Γ(X, U)`-module `M`, every Čech 1-cocycle `u : Π (σ : Fin 2 → ι), M_{g_σ}`
(`dDiff g M 2 u = 0`) splits as a 1-coboundary `u = dDiff g M 1 t`.

Alongside the splitting we provide the *section identification kit* that lets a
consumer read the abstract localised Čech coefficients
`SectionCechModule.dCoeff g Γ(X, U) σ = Γ(X, U)_{g_σ}` as honest section modules
of the structure sheaf over the multi-index basic opens
`D(g_σ) = D(g_{σ 0}) ⊓ … ⊓ D(g_{σ m})`, with the Čech coface identified with the
presheaf restriction.

## Main results

* `SectionCechModule.exists_dDiff_eq_of_dDiff_eq_zero`: the ring-level splitting
  brick — over a finite family `s : ι → R` spanning the unit ideal, every
  1-cocycle of `∏_σ M_{s_σ}` is a 1-coboundary (the `m = 0` instance of
  `SectionCechModule.dDiff_exact`).
* `IsAffineOpen.exists_dDiff_eq_of_dDiff_eq_zero`: the geometric consumable —
  the same splitting with the spanning hypothesis replaced by the covering
  hypothesis `⨆ i, D(gᵢ) = U` for an affine open `U ⊆ X`.
* `SectionCechModule.dDiff_one_apply` (with `comp_succAbove_zero/one`): the
  degree-1 differential in its classical two-term form
  `(d t)_σ = t_{σ 1}|_{D(g_σ)} - t_{σ 0}|_{D(g_σ)}`.
* `Scheme.basicOpen_sprod`: `D(g_σ) = ⨅ k, D(g_{σ k})` for a nonempty Čech
  multi-index `σ`, at arbitrary-scheme generality.
* `IsAffineOpen.dCoeffSectionsLinearEquiv`: the structure-sheaf Čech coefficient
  `Γ(X, U)_{g_σ}` is `Γ(X, U)`-linearly the section module `Γ(X, D(g_σ))`.
* `IsAffineOpen.dCoeffSectionsLinearEquiv_dCoface`: under this identification the
  Čech coface `dCoface` is the presheaf restriction along `D(g_σ) ⊆ D(g_{σ∘dⱼ})`.

Nothing here is re-proved: the exactness input is the kernel-verified
`SectionCechModule.dDiff_exact` chain of `AlgebraicJacobian.Cohomology.CechAcyclic`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-! ## Ring-level degree-1 splitting -/

namespace SectionCechModule

open CechLocalized

variable {ι : Type*}

/-- Deleting the index `0` from a pair multi-index `σ : Fin 2 → α` leaves the
singleton multi-index at its second entry `σ 1`. -/
lemma comp_succAbove_zero {α : Type*} (σ : Fin 2 → α) :
    σ ∘ (0 : Fin 2).succAbove = fun _ : Fin 1 => σ 1 := by
  funext k
  have hk : k = 0 := Subsingleton.elim k 0
  subst hk
  rfl

/-- Deleting the index `1` from a pair multi-index `σ : Fin 2 → α` leaves the
singleton multi-index at its first entry `σ 0`. -/
lemma comp_succAbove_one {α : Type*} (σ : Fin 2 → α) :
    σ ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 => σ 0 := by
  funext k
  have hk : k = 0 := Subsingleton.elim k 0
  subst hk
  rfl

variable {R : Type u} [CommRing R] (s : ι → R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- **Degree-1 Čech differential, classical two-term form**: on a pair
multi-index `σ : Fin 2 → ι`,
`(d t)_σ = t_{σ 1}|_{D(s_σ)} - t_{σ 0}|_{D(s_σ)}`, the restrictions being the
canonical localisation comparisons `dCoface` (and the deleted-face multi-indices
being the singletons of `comp_succAbove_zero`/`comp_succAbove_one`). -/
lemma dDiff_one_apply (t : ∀ σ : Fin 1 → ι, dCoeff s M σ) (σ : Fin 2 → ι) :
    dDiff s M 1 t σ
      = dCoface s M 1 σ 0 (t (σ ∘ (0 : Fin 2).succAbove))
        - dCoface s M 1 σ 1 (t (σ ∘ (1 : Fin 2).succAbove)) := by
  rw [dDiff_apply, Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_one_zsmul, ← sub_eq_add_neg]

/-- **Čech 1-coboundary splitting, module form** (the `m = 0` instance of the
positive-degree exactness `SectionCechModule.dDiff_exact`, Stacks 01EW): for a
finite family `s : ι → R` spanning the unit ideal and any `R`-module `M`, every
1-cocycle `u` of the section Čech module complex `∏_σ M_{s_σ}` — i.e. `u` with
`dDiff s M 2 u = 0`, the cocycle identity in the triple localisations — is a
1-coboundary `u = dDiff s M 1 t`.  Unfolded via `dDiff_one_apply`, `t` is the
classical family with `u σ = t_{σ 1} - t_{σ 0}` in `M_{s_{σ 0} · s_{σ 1}}`. -/
theorem exists_dDiff_eq_of_dDiff_eq_zero [Finite ι] (hs : Ideal.span (Set.range s) = ⊤)
    (u : ∀ σ : Fin 2 → ι, dCoeff s M σ) (hu : dDiff s M 2 u = 0) :
    ∃ t : ∀ σ : Fin 1 → ι, dCoeff s M σ, dDiff s M 1 t = u :=
  (dDiff_exact s M hs 0 u).mp hu

end SectionCechModule

/-! ## Geometric form: basic-open covers of an affine open

The consumable hypotheses for the degree-1 vanishing: an affine open `U` in an
arbitrary scheme `X` and a finite family `g : ι → Γ(X, U)` with
`⨆ i, D(gᵢ) = U`.  Covering is equivalent to spanning the unit ideal of
`Γ(X, U)` (`IsAffineOpen.iSup_basicOpen_eq_self_iff`), so the ring-level brick
applies with `R = Γ(X, U)` directly — no change of base ring is needed. -/

variable {X : Scheme.{u}} {U : X.Opens}

/-- If `a ∣ b` in `Γ(X, U)` then `D(b) ⊆ D(a)`: a basic open shrinks along
divisibility.  This is the inclusion along which the Čech cofaces restrict. -/
lemma Scheme.basicOpen_le_basicOpen_of_dvd {a b : Γ(X, U)} (h : a ∣ b) :
    X.basicOpen b ≤ X.basicOpen a := by
  obtain ⟨c, rfl⟩ := h
  rw [X.basicOpen_mul]
  exact inf_le_left

/-- Splitting an indexed infimum over `Fin (n + 1)` into the `0`-th term and the
infimum over the tail.  (Public copy of the lattice helper behind
`AlgebraicGeometry.basicOpen_sprod`.) -/
lemma iInf_fin_succ {α : Type*} [CompleteLattice α] {n : ℕ} (f : Fin (n + 1) → α) :
    (⨅ i, f i) = f 0 ⊓ ⨅ i : Fin n, f i.succ := by
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (le_iInf fun i => iInf_le _ i.succ)
  · refine le_iInf fun i => ?_
    refine Fin.cases inf_le_left (fun j => le_trans inf_le_right (iInf_le _ j)) i

/-- **Multi-index basic open** at arbitrary-scheme generality: for a nonempty
Čech multi-index `σ : Fin (m + 1) → ι`, the basic open of the product
`g_σ = ∏ k, g (σ k)` is the intersection of the basic opens,
`D(g_σ) = ⨅ k, D(g_{σ k})`.  Generalises `AlgebraicGeometry.basicOpen_sprod`
(the `Spec R` case) and identifies the section module of `𝒪_X` over a Čech
intersection with the localisation carrier `dCoeff`
(via `IsAffineOpen.dCoeffSectionsLinearEquiv` below). -/
lemma Scheme.basicOpen_sprod {ι : Type*} (g : ι → Γ(X, U)) {m : ℕ} (σ : Fin (m + 1) → ι) :
    X.basicOpen (CechLocalized.sprod g σ) = ⨅ k, X.basicOpen (g (σ k)) := by
  induction m with
  | zero =>
      have h1 : CechLocalized.sprod g σ = g (σ 0) := by
        simp [CechLocalized.sprod]
      rw [h1]
      refine le_antisymm (le_iInf fun k => ?_) (iInf_le _ 0)
      rw [Fin.eq_zero k]
  | succ n ih =>
      have h1 : CechLocalized.sprod g σ
          = g (σ 0) * CechLocalized.sprod g (fun i : Fin (n + 1) => σ i.succ) := by
        rw [CechLocalized.sprod, Fin.prod_univ_succ]; rfl
      rw [h1, X.basicOpen_mul, ih (fun i => σ i.succ), iInf_fin_succ fun k => X.basicOpen (g (σ k))]

/-- **Covering ↔ spanning** for an indexed family of basic opens of an affine
open: `⨆ i, D(gᵢ) = U` iff `g` spans the unit ideal of `Γ(X, U)`.  Range form of
Mathlib's `IsAffineOpen.iSup_basicOpen_eq_self_iff`. -/
theorem IsAffineOpen.iSup_basicOpen_range_eq_self_iff (hU : IsAffineOpen U)
    {ι : Type*} (g : ι → Γ(X, U)) :
    (⨆ i, X.basicOpen (g i)) = U ↔ Ideal.span (Set.range g) = ⊤ := by
  rw [← iSup_range' (fun a => X.basicOpen a) g]
  exact hU.iSup_basicOpen_eq_self_iff

/-- **Čech 1-coboundary splitting over an affine open** (the geometric
consumable of the degree-1 affine vanishing): let `U` be an affine open of a
scheme `X`, `g : ι → Γ(X, U)` a finite family of sections whose basic opens
cover `U`, and `M` an arbitrary `Γ(X, U)`-module.  Then every 1-cocycle
`u : Π (σ : Fin 2 → ι), M_{g_σ}` of the section Čech module complex is a
1-coboundary.  For `M = Γ(X, U)` the carriers are the section modules
`Γ(X, D(g_σ))` of the structure sheaf via
`IsAffineOpen.dCoeffSectionsLinearEquiv`, and `dDiff g M 1` unfolds through
`SectionCechModule.dDiff_one_apply` to the classical difference-of-restrictions
form. -/
theorem IsAffineOpen.exists_dDiff_eq_of_dDiff_eq_zero (hU : IsAffineOpen U)
    {ι : Type*} [Finite ι] (g : ι → Γ(X, U)) (hcov : (⨆ i, X.basicOpen (g i)) = U)
    (M : Type u) [AddCommGroup M] [Module ↥Γ(X, U) M]
    (u : ∀ σ : Fin 2 → ι, SectionCechModule.dCoeff g M σ)
    (hu : SectionCechModule.dDiff g M 2 u = 0) :
    ∃ t : ∀ σ : Fin 1 → ι, SectionCechModule.dCoeff g M σ,
      SectionCechModule.dDiff g M 1 t = u :=
  SectionCechModule.exists_dDiff_eq_of_dDiff_eq_zero g M
    ((hU.iSup_basicOpen_range_eq_self_iff g).mp hcov) u hu

/-! ## Section identification kit

Reading the abstract localised Čech coefficients as honest section modules of
the structure sheaf.  The algebra structure on `Γ(X, D(f))` over `Γ(X, U)` is
Mathlib's `algebra_section_section_basicOpen`, i.e. the presheaf restriction
(`Scheme.algebraMap_section_basicOpen`). -/

/-- The algebra structure map `Γ(X, U) → Γ(X, D(f))` (from Mathlib's
`algebra_section_section_basicOpen` instance) is the presheaf restriction. -/
lemma Scheme.algebraMap_section_basicOpen (f : Γ(X, U)) :
    algebraMap ↥Γ(X, U) ↥Γ(X, X.basicOpen f)
      = (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom :=
  rfl

/-- Over an affine open `U`, the restriction `Γ(X, U) →ₗ[Γ(X, U)] Γ(X, D(f))` is
a localisation of modules away from `f` — the module-theoretic form of
`IsAffineOpen.isLocalization_basicOpen`. -/
theorem IsAffineOpen.isLocalizedModule_linearMap_basicOpen (hU : IsAffineOpen U)
    (f : Γ(X, U)) :
    IsLocalizedModule (Submonoid.powers f)
      (Algebra.linearMap ↥Γ(X, U) ↥Γ(X, X.basicOpen f)) :=
  haveI := hU.isLocalization_basicOpen f
  inferInstance

/-- **Čech coefficients are section modules**: over an affine open `U`, the
abstract structure-sheaf Čech coefficient
`SectionCechModule.dCoeff g Γ(X, U) σ = Γ(X, U)_{g_σ}` is `Γ(X, U)`-linearly the
honest section module `Γ(X, D(g_σ))` — which is `Γ(X, ⨅ k, D(g_{σ k}))` by
`Scheme.basicOpen_sprod`.  Sends `x/1` to the restriction of `x`
(`dCoeffSectionsLinearEquiv_mk_one`) and intertwines the Čech coface with the
presheaf restriction (`dCoeffSectionsLinearEquiv_dCoface`). -/
noncomputable def IsAffineOpen.dCoeffSectionsLinearEquiv (hU : IsAffineOpen U)
    {ι : Type*} (g : ι → Γ(X, U)) {m : ℕ} (σ : Fin m → ι) :
    SectionCechModule.dCoeff g (↥Γ(X, U)) σ
      ≃ₗ[↥Γ(X, U)] ↥Γ(X, X.basicOpen (CechLocalized.sprod g σ)) :=
  haveI := hU.isLocalizedModule_linearMap_basicOpen (CechLocalized.sprod g σ)
  IsLocalizedModule.iso (Submonoid.powers (CechLocalized.sprod g σ))
    (Algebra.linearMap ↥Γ(X, U) ↥Γ(X, X.basicOpen (CechLocalized.sprod g σ)))

/-- The section identification sends the localisation structure map `x ↦ x/1` to
the presheaf restriction `Γ(X, U) → Γ(X, D(g_σ))` (which is the `algebraMap` by
`Scheme.algebraMap_section_basicOpen`). -/
@[simp] lemma IsAffineOpen.dCoeffSectionsLinearEquiv_mk_one (hU : IsAffineOpen U)
    {ι : Type*} (g : ι → Γ(X, U)) {m : ℕ} (σ : Fin m → ι) (x : Γ(X, U)) :
    hU.dCoeffSectionsLinearEquiv g σ (LocalizedModule.mk x 1)
      = algebraMap ↥Γ(X, U) ↥Γ(X, X.basicOpen (CechLocalized.sprod g σ)) x := by
  haveI := hU.isLocalizedModule_linearMap_basicOpen (CechLocalized.sprod g σ)
  exact IsLocalizedModule.iso_mk_one _ _ x

/-- The presheaf restriction between basic-open section rings (nested basic
opens of sections over a common `U`) as a `Γ(X, U)`-algebra homomorphism. -/
def Scheme.basicOpenResAlgHom {f₁ f₂ : Γ(X, U)} (h : X.basicOpen f₂ ≤ X.basicOpen f₁) :
    ↥Γ(X, X.basicOpen f₁) →ₐ[↥Γ(X, U)] ↥Γ(X, X.basicOpen f₂) where
  toRingHom := (X.presheaf.map (homOfLE h).op).hom
  commutes' r := by
    change (X.presheaf.map (homOfLE h).op).hom
        ((X.presheaf.map (homOfLE (X.basicOpen_le f₁)).op).hom r)
      = (X.presheaf.map (homOfLE (X.basicOpen_le f₂)).op).hom r
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp, ← op_comp, homOfLE_comp]

@[simp] lemma Scheme.basicOpenResAlgHom_apply {f₁ f₂ : Γ(X, U)}
    (h : X.basicOpen f₂ ≤ X.basicOpen f₁) (x : Γ(X, X.basicOpen f₁)) :
    Scheme.basicOpenResAlgHom h x = (X.presheaf.map (homOfLE h).op).hom x :=
  rfl

/-- **Coface = restriction**: under the section identification
`IsAffineOpen.dCoeffSectionsLinearEquiv`, the Čech coface
`dCoface : M_{g_{σ∘dⱼ}} → M_{g_σ}` (the canonical localisation comparison for
the index deletion `dⱼ`) is the presheaf restriction
`Γ(X, D(g_{σ∘dⱼ})) → Γ(X, D(g_σ))` along `D(g_σ) ⊆ D(g_{σ∘dⱼ})`.  Summed over
the alternating signs (`dDiff_apply`/`dDiff_one_apply`), this reads the whole
abstract differential `dDiff` as the alternating difference of restrictions of
honest sections. -/
lemma IsAffineOpen.dCoeffSectionsLinearEquiv_dCoface (hU : IsAffineOpen U)
    {ι : Type*} (g : ι → Γ(X, U)) {m : ℕ} (σ : Fin (m + 1) → ι) (j : Fin (m + 1))
    (x : SectionCechModule.dCoeff g (↥Γ(X, U)) (σ ∘ j.succAbove)) :
    hU.dCoeffSectionsLinearEquiv g σ (SectionCechModule.dCoface g (↥Γ(X, U)) m σ j x)
      = (X.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
            (CechLocalized.sprod_succAbove_dvd g σ j))).op).hom
          (hU.dCoeffSectionsLinearEquiv g (σ ∘ j.succAbove) x) := by
  haveI instσ := hU.isLocalizedModule_linearMap_basicOpen (CechLocalized.sprod g σ)
  haveI instτ :=
    hU.isLocalizedModule_linearMap_basicOpen (CechLocalized.sprod g (σ ∘ j.succAbove))
  have hdvd := CechLocalized.sprod_succAbove_dvd g σ j
  have key : (hU.dCoeffSectionsLinearEquiv g σ).toLinearMap
        ∘ₗ SectionCechModule.dCoface g (↥Γ(X, U)) m σ j
      = (Scheme.basicOpenResAlgHom (Scheme.basicOpen_le_basicOpen_of_dvd hdvd)).toLinearMap
        ∘ₗ (hU.dCoeffSectionsLinearEquiv g (σ ∘ j.succAbove)).toLinearMap := by
    apply IsLocalizedModule.ext (Submonoid.powers (CechLocalized.sprod g (σ ∘ j.succAbove)))
      (LocalizedModule.mkLinearMap _ _)
      ((AwayComparison.Inverts.of_dvd hdvd
        (Algebra.linearMap ↥Γ(X, U)
          ↥Γ(X, X.basicOpen (CechLocalized.sprod g σ)))).isUnit_powers)
    ext
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      AlgHom.toLinearMap_apply]
    rw [show (LocalizedModule.mkLinearMap
          (Submonoid.powers (CechLocalized.sprod g (σ ∘ j.succAbove))) (↥Γ(X, U))) 1
        = LocalizedModule.mk 1 1 from rfl]
    rw [show SectionCechModule.dCoface g (↥Γ(X, U)) m σ j (LocalizedModule.mk 1 1)
        = LocalizedModule.mk 1 1 from
      AwayComparison.comparison_apply
        (LocalizedModule.mkLinearMap
          (Submonoid.powers (CechLocalized.sprod g (σ ∘ j.succAbove))) (↥Γ(X, U)))
        (LocalizedModule.mkLinearMap (Submonoid.powers (CechLocalized.sprod g σ)) (↥Γ(X, U)))
        (AwayComparison.Inverts.of_dvd (CechLocalized.sprod_succAbove_dvd g σ j)
          (LocalizedModule.mkLinearMap (Submonoid.powers (CechLocalized.sprod g σ)) (↥Γ(X, U))))
        1]
    rw [hU.dCoeffSectionsLinearEquiv_mk_one g σ 1,
      hU.dCoeffSectionsLinearEquiv_mk_one g (σ ∘ j.succAbove) 1]
    exact (Scheme.basicOpenResAlgHom _).commutes 1 |>.symm
  exact DFunLike.congr_fun key x

end AlgebraicGeometry
