/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Equalizer
import Std.Tactic.BVDecide.LRAT.Internal.Clause

/-!
# Abstract flat-base-change ladder for glued module sections (Stacks 02KE, `i = 0`)

This file contains the *pure module-theoretic* half of the Stacks 02KE argument
("cohomology and base change in degree zero for quasi-compact quasi-separated
morphisms"), abstracted away from schemes.  The geometric application (in
`AlgebraicJacobian.Picard.QuotScheme`, theorem
`pullback_baseMap_sectionLinearEquiv_of_quasiCompact`) instantiates the data
below with:

* `A = Γ(S, V)`, `B = Γ(S', U)` a flat `A`-algebra,
* `M = Γ(F, f ⁻¹ᵁ V)` and its restrictions `Mi i = Γ(F, V i)`,
  `Mk (i,j) = Γ(F, V i ⊓ V j)` to a finite affine cover `{V i}` of `f ⁻¹ᵁ V`,
* `P = Γ(g'^* F, f' ⁻¹ᵁ U)` and its restrictions to the primed cover
  `W i = g' ⁻¹ᵁ V i ⊓ f' ⁻¹ᵁ U`,
* `ε i` the per-piece affine base-change comparison (bijective on affine
  pieces), `μ k` the overlap comparison (injective by one further descent).

The main results:

* `SectionBaseChange.linearMap_ext_one_tmul`: `B`-linear maps out of
  `B ⊗[A] M` are determined on the generators `1 ⊗ₜ m`.
* `SectionBaseChange.injective_of_injective_cover`: if a comparison map is,
  componentwise on a finite cover, intertwined with injective comparisons,
  and the source restriction is jointly injective (sheaf separatedness), then
  flatness of `B` makes the comparison injective.
* `SectionBaseChange.isPushout_of_ringEquiv`: recognize `Algebra.IsPushout`
  from an explicit ring isomorphism `C ⊗[A] B ≃+* D`.
* `SectionBaseChange.bijective_addHom_of_isPushout`: for a pushout square of
  rings `A → B, A → C, C → D, B → D` and a `C`-module `M`, the canonical map
  `B ⊗[A] M → D ⊗[C] M`, `b ⊗ m ↦ (algebraMap B D b) ⊗ m` is bijective
  (associativity of scalar extension along a pushout).
* `SectionBaseChange.exists_linearEquiv_of_gluing`: the **equalizer ladder**:
  given sheaf-style gluing data for `M` over `A` and for `P` over a flat
  `A`-algebra `B`, bijective comparisons on the cover pieces and injective
  comparisons on the overlaps (all intertwining the restrictions), there is a
  `B`-linear equivalence `B ⊗[A] M ≃ₗ[B] P` compatible with all restrictions.
  This is the module dialect of Mathlib's
  `AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq` ladder.

Source: Stacks Project, Tags 02KE and 02KH (`i = 0`).
-/

universe u

open TensorProduct

namespace AlgebraicGeometry

namespace SectionBaseChange

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

section Ext

variable {M P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup P] [Module B P]

/-- Two `B`-linear maps out of `B ⊗[A] M` agreeing on the generators `1 ⊗ₜ m`
agree everywhere (`b ⊗ₜ m = b • (1 ⊗ₜ m)`). -/
theorem linearMap_ext_one_tmul {f g : B ⊗[A] M →ₗ[B] P}
    (h : ∀ m : M, f ((1 : B) ⊗ₜ[A] m) = g ((1 : B) ⊗ₜ[A] m)) : f = g := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
      have hb : (b ⊗ₜ[A] m : B ⊗[A] M) = b • ((1 : B) ⊗ₜ[A] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hb, map_smul, map_smul, h]
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

/-- Pointwise form of `linearMap_ext_one_tmul`. -/
theorem linearMap_congr_one_tmul {f g : B ⊗[A] M →ₗ[B] P}
    (h : ∀ m : M, f ((1 : B) ⊗ₜ[A] m) = g ((1 : B) ⊗ₜ[A] m)) (z : B ⊗[A] M) :
    f z = g z :=
  DFunLike.congr_fun (linearMap_ext_one_tmul h) z

end Ext

section LTensor

variable {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [Module A N₁]
  [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃]

/-- Composition collapse for `AlgebraTensorModule.lTensor` (pointwise). -/
theorem lTensor_lTensor_apply (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃) (z : B ⊗[A] N₁) :
    TensorProduct.AlgebraTensorModule.lTensor B B g
        (TensorProduct.AlgebraTensorModule.lTensor B B f z) =
      TensorProduct.AlgebraTensorModule.lTensor B B (g ∘ₗ f) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => rfl
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]

end LTensor

section Injective

variable {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module A M]
variable {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module A (Mi i)]
variable {P : Type*} [AddCommGroup P] [Module B P]
variable {Pi : ι → Type*} [∀ i, AddCommGroup (Pi i)] [∀ i, Module B (Pi i)]

omit [Finite ι] in
/-- The tensored restriction to a cover piece is the corresponding component of
the tensored restriction to the whole (finite) cover. -/
theorem lTensor_pi_apply (res : ∀ i, M →ₗ[A] Mi i) (z : B ⊗[A] M) (i : ι) :
    TensorProduct.piRightHom A B B Mi
        (TensorProduct.AlgebraTensorModule.lTensor B B (LinearMap.pi res) z) i =
      TensorProduct.AlgebraTensorModule.lTensor B B (res i) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => rfl
  | add z₁ z₂ h₁ h₂ => simp only [map_add, Pi.add_apply, h₁, h₂]

/-- **Injectivity along a finite cover by flat base change** (the
separatedness half of the 02KE ladder).  If restriction of `M` to a finite
cover is jointly injective, `B` is flat over `A`, and a comparison map `s`
is intertwined (on tensor generators) with injective per-piece comparisons
`ε i`, then `s` is injective. -/
theorem injective_of_injective_cover [Module.Flat A B]
    (res : ∀ i, M →ₗ[A] Mi i)
    (hres : ∀ m : M, (∀ i, res i m = 0) → m = 0)
    (res' : ∀ i, P →ₗ[B] Pi i)
    (ε : ∀ i, B ⊗[A] Mi i →ₗ[B] Pi i) (hε : ∀ i, Function.Injective (ε i))
    (s : B ⊗[A] M →ₗ[B] P)
    (hsq : ∀ (i : ι) (m : M),
      res' i (s ((1 : B) ⊗ₜ[A] m)) = ε i ((1 : B) ⊗ₜ[A] res i m)) :
    Function.Injective s := by
  classical
  cases nonempty_fintype ι
  -- Full-`z` intertwining squares from the generator squares.
  have hsq' : ∀ (i : ι) (z : B ⊗[A] M),
      res' i (s z) =
        ε i (TensorProduct.AlgebraTensorModule.lTensor B B (res i) z) := by
    intro i z
    refine linearMap_congr_one_tmul (f := (res' i).comp s)
      (g := (ε i).comp (TensorProduct.AlgebraTensorModule.lTensor B B (res i)))
      (fun m => ?_) z
    simpa using hsq i m
  -- Restriction to the cover is injective, hence so is its flat base change.
  have hT : Function.Injective (LinearMap.pi res : M →ₗ[A] ∀ i, Mi i) := by
    intro x y hxy
    rw [← sub_eq_zero]
    refine hres _ fun i => ?_
    have h := congrFun hxy i
    simp only [LinearMap.pi_apply] at h
    rw [map_sub, h, sub_self]
  have hTB : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor B B (LinearMap.pi res)) := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := B)
      (LinearMap.pi res) hT
    rwa [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := B)] at h
  have hpiInj : Function.Injective (TensorProduct.piRightHom A B B Mi) := by
    have h := (TensorProduct.piRight A B B Mi).injective
    have hcoe : ⇑(TensorProduct.piRight A B B Mi) =
        ⇑(TensorProduct.piRightHom A B B Mi) :=
      funext fun z => TensorProduct.piRight_apply A B B Mi z
    rwa [hcoe] at h
  refine (injective_iff_map_eq_zero s).mpr fun z hz => ?_
  have hzi : ∀ i, TensorProduct.AlgebraTensorModule.lTensor B B (res i) z = 0 := by
    intro i
    refine hε i ?_
    rw [map_zero, ← hsq' i z, hz, map_zero]
  have hz0 : TensorProduct.AlgebraTensorModule.lTensor B B (LinearMap.pi res) z = 0 := by
    refine hpiInj ?_
    rw [map_zero]
    funext i
    rw [lTensor_pi_apply res z i, hzi i]
    simp
  have := hTB (by rw [hz0, map_zero] : TensorProduct.AlgebraTensorModule.lTensor B B
    (LinearMap.pi res) z = TensorProduct.AlgebraTensorModule.lTensor B B
    (LinearMap.pi res) 0)
  exact this

end Injective

section Pushout

variable {C D : Type*} [CommRing C] [CommRing D]
variable [Algebra A C] [Algebra C D] [Algebra B D] [Algebra A D]
variable [IsScalarTower A C D] [IsScalarTower A B D]

/-- Recognize `Algebra.IsPushout A C B D` from an explicit ring isomorphism
`C ⊗[A] B ≃+* D` matching the two structure maps on pure tensors. -/
theorem isPushout_of_ringEquiv (E : C ⊗[A] B ≃+* D)
    (hE : ∀ (c : C) (b : B), E (c ⊗ₜ[A] b) = algebraMap C D c * algebraMap B D b) :
    Algebra.IsPushout A C B D := by
  constructor
  have hsmul : ∀ (c : C) (x : C ⊗[A] B), E (c • x) = c • E x := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c' b =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, hE, hE, map_mul,
          Algebra.smul_def, mul_assoc]
    | add x₁ x₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂, map_add, smul_add]
  refine IsBaseChange.of_equiv
    ({ toFun := E
       map_add' := map_add E
       map_smul' := fun c x => hsmul c x
       invFun := E.symm
       left_inv := E.left_inv
       right_inv := E.right_inv } : C ⊗[A] B ≃ₗ[C] D) fun b => ?_
  change E ((1 : C) ⊗ₜ[A] b) = _
  rw [hE, map_one, one_mul]
  rfl

/-- **Associativity of scalar extension along a pushout square**: for rings
`A → B`, `A → C` with pushout `D` and a `C`-module `M`, the canonical
additive map `B ⊗[A] M → D ⊗[C] M`, `b ⊗ₜ m ↦ (algebraMap B D b) ⊗ₜ m`,
is bijective (`D ⊗[C] M = (B ⊗[A] C) ⊗[C] M = B ⊗[A] M`). -/
theorem bijective_addHom_of_isPushout [h : Algebra.IsPushout A C B D]
    {M : Type*} [AddCommGroup M] [Module A M] [Module C M] [IsScalarTower A C M]
    (s : B ⊗[A] M →+ D ⊗[C] M)
    (hs : ∀ (b : B) (m : M), s (b ⊗ₜ[A] m) = algebraMap B D b ⊗ₜ[C] m) :
    Function.Bijective s := by
  have hbc : IsBaseChange C (IsScalarTower.toAlgHom A B D).toLinearMap := h.out
  let e₁ : B ⊗[A] M ≃ₗ[A] M ⊗[A] B := TensorProduct.comm A B M
  let e₂ : M ⊗[A] B ≃ₗ[C] M ⊗[C] D := (hbc.tensorEquiv M).symm
  let e₃ : M ⊗[C] D ≃ₗ[C] D ⊗[C] M := TensorProduct.comm C M D
  have he₂ : ∀ (m : M) (b : B), e₂ (m ⊗ₜ[A] b) = m ⊗ₜ[C] algebraMap B D b := by
    intro m b
    rw [LinearEquiv.symm_apply_eq]
    symm
    change hbc.tensorEquiv M (m ⊗ₜ[C] algebraMap B D b) = m ⊗ₜ[A] b
    have hsymm : hbc.equiv.symm (algebraMap B D b) = (1 : C) ⊗ₜ[A] b := by
      have h1 := hbc.equiv_symm_apply b
      simpa using h1
    rw [IsBaseChange.tensorEquiv]
    rw [LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul, hsymm]
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  have key : ∀ z : B ⊗[A] M, s z = e₃ (e₂ (e₁ z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
        rw [hs]
        have h1 : e₁ (b ⊗ₜ[A] m) = m ⊗ₜ[A] b := rfl
        rw [h1, he₂]
        rfl
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
  rw [show ⇑s = ⇑e₃ ∘ ⇑e₂ ∘ ⇑e₁ from funext key]
  exact e₃.bijective.comp (e₂.bijective.comp e₁.bijective)

end Pushout

section Glue

variable {ι κ : Type*} [Finite ι] [Finite κ]
variable {M : Type*} [AddCommGroup M] [Module A M]
variable {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module A (Mi i)]
variable {Mk : κ → Type*} [∀ k, AddCommGroup (Mk k)] [∀ k, Module A (Mk k)]
variable {P : Type*} [AddCommGroup P] [Module B P]
variable {Pi : ι → Type*} [∀ i, AddCommGroup (Pi i)] [∀ i, Module B (Pi i)]
variable {Pk : κ → Type*} [∀ k, AddCommGroup (Pk k)] [∀ k, Module B (Pk k)]

/-- **The 02KE equalizer ladder, abstract form.**  Let `M` be an `A`-module
presented by a finite "sheaf-style" gluing datum (`res`: restriction to the
cover, jointly injective and with image exactly the compatible families for
the overlap maps `l, r`), and let `P` be a `B`-module (`B` a flat
`A`-algebra) presented by an analogous datum (`res'`, `l'`, `r'`).  Given
bijective comparison maps `ε i : B ⊗[A] Mi i → Pi i` on the pieces,
injective comparison maps `μ k : B ⊗[A] Mk k → Pk k` on the overlaps, all
intertwining the two restriction legs on tensor generators, there is a
`B`-linear equivalence `Φ : B ⊗[A] M ≃ₗ[B] P` compatible with all
restrictions to the cover.

This is the module version of Mathlib's
`AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq` chase; the compatibility
output pins `Φ` on the generators `1 ⊗ₜ m` (via injectivity of `res'`). -/
theorem exists_linearEquiv_of_gluing [Module.Flat A B]
    (res : ∀ i, M →ₗ[A] Mi i) (l r : ∀ k, (∀ i, Mi i) →ₗ[A] Mk k)
    (res' : ∀ i, P →ₗ[B] Pi i) (l' r' : ∀ k, (∀ i, Pi i) →ₗ[B] Pk k)
    (hMinj : ∀ m : M, (∀ i, res i m = 0) → m = 0)
    (hMglue : ∀ sf : ∀ i, Mi i, (∀ k, l k sf = r k sf) →
      ∃ m : M, ∀ i, res i m = sf i)
    (hMcpt : ∀ (m : M) (k : κ), l k (fun i => res i m) = r k (fun i => res i m))
    (hPinj : ∀ p : P, (∀ i, res' i p = 0) → p = 0)
    (hPglue : ∀ sf : ∀ i, Pi i, (∀ k, l' k sf = r' k sf) →
      ∃ p : P, ∀ i, res' i p = sf i)
    (hPcpt : ∀ (p : P) (k : κ), l' k (fun i => res' i p) = r' k (fun i => res' i p))
    (ε : ∀ i, B ⊗[A] Mi i →ₗ[B] Pi i) (hε : ∀ i, Function.Bijective (ε i))
    (μ : ∀ k, B ⊗[A] Mk k →ₗ[B] Pk k) (hμ : ∀ k, Function.Injective (μ k))
    (hl : ∀ (k : κ) (sf : ∀ i, Mi i),
      μ k ((1 : B) ⊗ₜ[A] l k sf) = l' k (fun i => ε i ((1 : B) ⊗ₜ[A] sf i)))
    (hr : ∀ (k : κ) (sf : ∀ i, Mi i),
      μ k ((1 : B) ⊗ₜ[A] r k sf) = r' k (fun i => ε i ((1 : B) ⊗ₜ[A] sf i))) :
    ∃ Φ : (B ⊗[A] M) ≃ₗ[B] P, ∀ (z : B ⊗[A] M) (i : ι),
      res' i (Φ z) = ε i (TensorProduct.AlgebraTensorModule.lTensor B B (res i) z) := by
  classical
  cases nonempty_fintype ι
  -- Abbreviations for the assembled cover maps.
  set T : M →ₗ[A] ∀ i, Mi i := LinearMap.pi res with hT
  set L : (∀ i, Mi i) →ₗ[A] ∀ k, Mk k := LinearMap.pi l with hL
  set R : (∀ i, Mi i) →ₗ[A] ∀ k, Mk k := LinearMap.pi r with hR
  -- The candidate family map and the restriction embedding of `P`.
  set Fam : B ⊗[A] M →ₗ[B] ∀ i, Pi i := LinearMap.pi
    (fun i => (ε i).comp (TensorProduct.AlgebraTensorModule.lTensor B B (res i)))
    with hFam
  set νP : P →ₗ[B] ∀ i, Pi i := LinearMap.pi res' with hνP
  -- The per-piece comparisons as equivalences, and the product comparison.
  let εe : ∀ i, (B ⊗[A] Mi i) ≃ₗ[B] Pi i := fun i => LinearEquiv.ofBijective (ε i) (hε i)
  set Epi : B ⊗[A] (∀ i, Mi i) →ₗ[B] ∀ i, Pi i := LinearMap.pi
    (fun i => (ε i).comp
      (TensorProduct.AlgebraTensorModule.lTensor B B (LinearMap.proj i)))
    with hEpi
  -- Full-`z` intertwining squares for the two legs.
  have hlz : ∀ (k : κ) (w : B ⊗[A] (∀ i, Mi i)),
      μ k (TensorProduct.AlgebraTensorModule.lTensor B B (l k) w) = l' k (Epi w) := by
    intro k w
    refine linearMap_congr_one_tmul
      (f := (μ k).comp (TensorProduct.AlgebraTensorModule.lTensor B B (l k)))
      (g := (l' k).comp Epi) (fun sf => ?_) w
    exact hl k sf
  have hrz : ∀ (k : κ) (w : B ⊗[A] (∀ i, Mi i)),
      μ k (TensorProduct.AlgebraTensorModule.lTensor B B (r k) w) = r' k (Epi w) := by
    intro k w
    refine linearMap_congr_one_tmul
      (f := (μ k).comp (TensorProduct.AlgebraTensorModule.lTensor B B (r k)))
      (g := (r' k).comp Epi) (fun sf => ?_) w
    exact hr k sf
  -- `Fam` factors through the tensored total restriction.
  have hFamT : ∀ (z : B ⊗[A] M) (i : ι),
      Fam z i = ε i (TensorProduct.AlgebraTensorModule.lTensor B B (LinearMap.proj i)
        (TensorProduct.AlgebraTensorModule.lTensor B B T z)) := by
    intro z i
    rw [lTensor_lTensor_apply]
    have hproj : (LinearMap.proj i) ∘ₗ T = res i := by
      refine LinearMap.ext fun m => ?_
      simp [hT]
    rw [hproj]
    simp [hFam, LinearMap.pi_apply]
  -- `Fam` is injective (separatedness + flatness).
  have hFamInj : Function.Injective Fam := by
    refine injective_of_injective_cover res hMinj
      (fun i => (LinearMap.proj i : (∀ j, Pi j) →ₗ[B] Pi i)) ε
      (fun i => (hε i).injective) Fam (fun i m => ?_)
    simp [hFam, LinearMap.pi_apply]
  -- `νP` is injective (separatedness of `P`).
  have hνPInj : Function.Injective νP := by
    intro x y hxy
    rw [← sub_eq_zero]
    refine hPinj _ fun i => ?_
    have h := congrFun hxy i
    simp only [hνP, LinearMap.pi_apply] at h
    rw [map_sub, h, sub_self]
  -- The two legs agree after composing with the tensored total restriction.
  have hLRT : ∀ k, (l k) ∘ₗ T = (r k) ∘ₗ T := by
    intro k
    refine LinearMap.ext fun m => ?_
    exact hMcpt m k
  -- Range inclusion 1: `Fam` lands in the glued sections.
  have hsub₁ : LinearMap.range Fam ≤ LinearMap.range νP := by
    rintro _ ⟨z, rfl⟩
    have hcpt : ∀ k, l' k (Fam z) = r' k (Fam z) := by
      intro k
      have hFamE : Fam z = Epi (TensorProduct.AlgebraTensorModule.lTensor B B T z) := by
        funext i
        rw [hFamT z i]
        simp [hEpi, LinearMap.pi_apply]
      rw [hFamE, ← hlz k, ← hrz k, lTensor_lTensor_apply, lTensor_lTensor_apply,
        hLRT k]
    obtain ⟨p, hp⟩ := hPglue (Fam z) hcpt
    exact ⟨p, funext fun i => by simp [hνP, LinearMap.pi_apply, hp i]⟩
  -- The `M`-side equalizer presentation and its flat base change.
  have hmemT : ∀ m : M, T m ∈ LinearMap.eqLocus L R := by
    intro m
    rw [LinearMap.mem_eqLocus]
    funext k
    exact hMcpt m k
  -- Range inclusion 2: every glued section is hit.
  have hsub₂ : LinearMap.range νP ≤ LinearMap.range Fam := by
    rintro _ ⟨p, rfl⟩
    -- The compatible family of preimages under the piece comparisons.
    set q : ∀ i, B ⊗[A] Mi i := fun i => (εe i).symm (res' i p) with hq
    set Y : B ⊗[A] (∀ i, Mi i) := (TensorProduct.piRight A B B Mi).symm q with hY
    have hYq : ∀ i, TensorProduct.AlgebraTensorModule.lTensor B B (LinearMap.proj i) Y
        = q i := by
      intro i
      have hcomp : ∀ w : B ⊗[A] (∀ i, Mi i),
          TensorProduct.AlgebraTensorModule.lTensor B B (LinearMap.proj i) w =
            TensorProduct.piRightHom A B B Mi w i := by
        intro w
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul b sf => rfl
        | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂, _root_.Pi.add_apply]
      rw [hcomp Y, ← TensorProduct.piRight_apply, hY,
        LinearEquiv.apply_symm_apply]
    have hEpiY : Epi Y = fun i => res' i p := by
      funext i
      have hεq : ε i (q i) = res' i p := by
        rw [hq]
        exact (εe i).apply_symm_apply (res' i p)
      calc Epi Y i
          = ε i (TensorProduct.AlgebraTensorModule.lTensor B B (LinearMap.proj i) Y) := rfl
        _ = ε i (q i) := by rw [hYq i]
        _ = res' i p := hεq
    -- `Y` lies in the base-changed equalizer.
    have hprojL : ∀ (k : κ) (w : B ⊗[A] (∀ i, Mi i)),
        TensorProduct.piRightHom A B B Mk
          (TensorProduct.AlgebraTensorModule.lTensor B B L w) k =
          TensorProduct.AlgebraTensorModule.lTensor B B (l k) w := by
      intro k w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul b sf => rfl
      | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂, _root_.Pi.add_apply]
    have hprojR : ∀ (k : κ) (w : B ⊗[A] (∀ i, Mi i)),
        TensorProduct.piRightHom A B B Mk
          (TensorProduct.AlgebraTensorModule.lTensor B B R w) k =
          TensorProduct.AlgebraTensorModule.lTensor B B (r k) w := by
      intro k w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul b sf => rfl
      | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂, _root_.Pi.add_apply]
    have hYmem : TensorProduct.AlgebraTensorModule.lTensor B B L Y =
        TensorProduct.AlgebraTensorModule.lTensor B B R Y := by
      have hpiInj : Function.Injective (TensorProduct.piRightHom A B B Mk) := by
        cases nonempty_fintype κ
        have h := (TensorProduct.piRight A B B Mk).injective
        have hcoe : ⇑(TensorProduct.piRight A B B Mk) =
            ⇑(TensorProduct.piRightHom A B B Mk) :=
          funext fun z => TensorProduct.piRight_apply A B B Mk z
        rwa [hcoe] at h
      refine hpiInj ?_
      funext k
      rw [hprojL k Y, hprojR k Y]
      refine hμ k ?_
      rw [hlz k Y, hrz k Y, hEpiY]
      exact hPcpt p k
    -- Transport through the equalizer presentation of `M` and its base change.
    set Tc : M →ₗ[A] LinearMap.eqLocus L R := T.codRestrict _ hmemT with hTc
    have hTcbij : Function.Bijective Tc := by
      constructor
      · intro x y hxy
        rw [← sub_eq_zero]
        refine hMinj _ fun i => ?_
        have h := congrFun (congrArg (Subtype.val) hxy) i
        simp only [hTc, LinearMap.codRestrict_apply, hT, LinearMap.pi_apply] at h
        rw [map_sub, h, sub_self]
      · rintro ⟨sf, hsf⟩
        rw [LinearMap.mem_eqLocus] at hsf
        obtain ⟨m, hm⟩ := hMglue sf (fun k => by
          have h := congrFun hsf k
          simpa [hL, hR, LinearMap.pi_apply] using h)
        refine ⟨m, Subtype.ext ?_⟩
        funext i
        simpa [hTc, LinearMap.codRestrict_apply, hT, LinearMap.pi_apply] using hm i
    let eM : M ≃ₗ[A] LinearMap.eqLocus L R := LinearEquiv.ofBijective Tc hTcbij
    let tEq := LinearMap.tensorEqLocusEquiv B B L R
    have hYmem' : Y ∈ LinearMap.eqLocus
        (TensorProduct.AlgebraTensorModule.lTensor B B L)
        (TensorProduct.AlgebraTensorModule.lTensor B B R) := by
      rw [LinearMap.mem_eqLocus]; exact hYmem
    set z : B ⊗[A] M := (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl B B) eM).symm (tEq.symm ⟨Y, hYmem'⟩) with hz
    refine ⟨z, ?_⟩
    -- `lTensor eM z` is the transported element of the base-changed equalizer.
    have hcongr : ∀ w : B ⊗[A] M,
        TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) eM w =
          TensorProduct.AlgebraTensorModule.lTensor B B (eM : M →ₗ[A] _) w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul b m => rfl
      | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    have heMz : TensorProduct.AlgebraTensorModule.lTensor B B (eM : M →ₗ[A] _) z =
        tEq.symm ⟨Y, hYmem'⟩ := by
      rw [← hcongr z, hz, LinearEquiv.apply_symm_apply]
    -- Hence the tensored total restriction of `z` is `Y`.
    have hTz : TensorProduct.AlgebraTensorModule.lTensor B B T z = Y := by
      have hT2 : T = (LinearMap.eqLocus L R).subtype ∘ₗ (eM : M →ₗ[A] _) := by
        refine LinearMap.ext fun m => ?_
        rfl
      rw [hT2, ← lTensor_lTensor_apply ((eM : M →ₗ[A] _))
        (LinearMap.eqLocus L R).subtype z, heMz]
      have hcoe : TensorProduct.AlgebraTensorModule.lTensor B B
          (LinearMap.eqLocus L R).subtype (tEq.symm ⟨Y, hYmem'⟩) =
          LinearMap.lTensor B (LinearMap.eqLocus L R).subtype (tEq.symm ⟨Y, hYmem'⟩) := by
        rw [TensorProduct.AlgebraTensorModule.coe_lTensor (A := B)]
      rw [hcoe]
      exact LinearMap.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm B B L R ⟨Y, hYmem'⟩
    -- Conclude: `Fam z` is the family of restrictions of `p`.
    refine funext fun i => ?_
    rw [hFamT z i, hTz, hYq i, hq]
    exact (εe i).apply_symm_apply (res' i p)
  -- Assemble the equivalence from the two range inclusions.
  have hrange : LinearMap.range Fam = LinearMap.range νP := le_antisymm hsub₁ hsub₂
  let Φ : (B ⊗[A] M) ≃ₗ[B] P :=
    (LinearEquiv.ofInjective Fam hFamInj) ≪≫ₗ (LinearEquiv.ofEq _ _ hrange) ≪≫ₗ
      (LinearEquiv.ofInjective νP hνPInj).symm
  refine ⟨Φ, fun z i => ?_⟩
  have hν : νP (Φ z) = Fam z := by
    have h1 : (LinearEquiv.ofInjective νP hνPInj) (Φ z) =
        LinearEquiv.ofEq _ _ hrange ((LinearEquiv.ofInjective Fam hFamInj) z) := by
      change (LinearEquiv.ofInjective νP hνPInj)
        ((LinearEquiv.ofInjective νP hνPInj).symm _) = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    have h2 : ((LinearEquiv.ofInjective νP hνPInj) (Φ z) : ∀ i, Pi i) = νP (Φ z) :=
      LinearEquiv.ofInjective_apply νP (Φ z)
    have h3 : ((LinearEquiv.ofEq _ _ hrange
        ((LinearEquiv.ofInjective Fam hFamInj) z) : LinearMap.range νP) : ∀ i, Pi i) =
        (((LinearEquiv.ofInjective Fam hFamInj) z : LinearMap.range Fam) : ∀ i, Pi i) :=
      rfl
    have h4 : (((LinearEquiv.ofInjective Fam hFamInj) z : LinearMap.range Fam) :
        ∀ i, Pi i) = Fam z := LinearEquiv.ofInjective_apply Fam z
    rw [← h2, h1, h3, h4]
  have h5 := congrFun hν i
  simpa [hνP, hFam, LinearMap.pi_apply] using h5

end Glue

end SectionBaseChange

end AlgebraicGeometry
