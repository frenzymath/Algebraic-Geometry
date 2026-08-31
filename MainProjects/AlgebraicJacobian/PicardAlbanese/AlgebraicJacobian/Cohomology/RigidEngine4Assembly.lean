/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RigidEngineLatticeCoherence
import AlgebraicJacobian.Cohomology.RigidEngine2Nakayama
import AlgebraicJacobian.Cohomology.RigidEngine3Rigidity
import AlgebraicJacobian.Cohomology.AffineVanishingQcoh
import AlgebraicJacobian.Cohomology.TwoCover

/-!
# RE-4 — the sheaf-level assembly of the rigid engine (Layer 1, abstract)

This file assembles the module-algebra rigid engine (RE-1/2/3,
`informal/w4-rigid-engine-worksheet.md` §1.2 Level 2) at the sheaf level: for a sheaf `F`
of `R`-modules on the small Zariski site of a scheme `X`, packaged quasi-coherently on an
affine two-chart cover `U₀, U₁` (`Scheme.QcohOn`, w4-1), it constructs **the two-lattice
pair of `F`** and fires the engine on it.

* `Scheme.TwoCoverPairData` — the coordinate data of the cover: chart coordinates
  `g₀ ∈ Γ(X, U₀)`, `g₁ ∈ Γ(X, U₁)` with the overlap-as-basic-open identifications
  `U₀ ⊓ U₁ = D(g₀) = D(g₁)`, the `R`-linearity of their packaged actions, and the
  mutual-inverse law `g₀·g₁ = 1` on the overlap (expressed on the packaged actions:
  the two `qsmul` compositions are the identity of `F(U₀ ⊓ U₁)`).
* `Scheme.TwoCoverPairData.pair` — the two-lattice pair with carriers
  `Γ(U₀, F) × Γ(U₁, F) → Γ(U₀ ⊓ U₁, F)`. The localization axioms `denom/ann` are
  discharged **term-for-term from the (P2) axioms of the packaging** — the same three-axiom
  match that RE-0's bridge (`Scheme.QcohOn.isLocalizedModule_secResₗ`,
  `IsLocalizedModule.surj`/`exists_of_eq`) certifies, applied here directly to avoid
  carrying the `moduleOfLE` instance tower (worksheet risk 3); the overlap transport is
  along the `inf_eq_basicOpen` identifications through `secRes_secRes`/`secRes_self`.
* `MayerVietorisSquare.sectionsKerEquiv` / `Scheme.twoCoverH0LinearEquiv` — **the H⁰-kernel
  bridge** (worksheet risk 4, the kernel twin of the landed cokernel bridge
  `TwoCover.h1CokEquiv`): degree-zero cohomology of the site is the kernel of the
  Mayer–Vietoris restriction-difference map, from the landed degree-0 exactness
  (`sections_ext`, `moduleDiff_restriction`, `exists_glue_of_moduleDiff_eq_zero`).
* `Scheme.TwoCoverPairData.h0Equiv` / `h1Equiv` — the cohomology carriers of the pair:
  `Sheaf.HModule F 0 ≃ₗ[R] H⁰(pair)` and `Sheaf.HModule F 1 ≃ₗ[R] H¹(pair)` (the latter
  through the landed `Scheme.twoCoverH1LinearEquiv` and the twisted affine vanishing
  `IsAffineOpen.subsingleton_hModule'_one_of_qcoh`).
* **The engine** (Kleiman 3.10 (v)⟹(i)+(iii), curve-lite):
  `Scheme.TwoCoverPairData.rigidEngine` — under COH finiteness of the chart lattices
  (the pinned `Module.Finite R[X] (Module.AEval' _)` spelling) and flatness/projectivity
  of the section modules (discharged in Layer 2, where they are free), fibrewise vanishing
  of `H¹` in **complex form** forces `H¹(X, F) = 0` and makes `H⁰(X, F)` finite projective;
  `rigidEngine_isOpen_vanishing` — the openness export (COH-1 + RE-2);
  `h0TensorEquiv` — the module-coefficient clause `H⁰(X, F) ⊗ P ≃ ker (δ ⊗ P)` (Kleiman
  `eq:Q`); `h0BaseChangeEquiv` — the `R'`-linear ring-map clause onto
  `ker (δ.baseChange R')`, which Layer 2 (`RigidEngine4Relative`) threads through CBC-1 to
  the base-changed sheaf.

**The fibre hypothesis is pinned in complex form** (`hfib : ∀ p, Subsingleton
(H¹(pair) ⊗ κ(p))`, worksheet §3.2): the sheaf-level discharge (glued fibre sheaf ≅ divisor
sheaf of a witness, FLV class form) gates on the W6-full seam and is deliberately NOT
attempted here — the consumer supplies `hfib` once that seam lands.

The Layer-2 instantiation on the relative twisted sheaf is in
`AlgebraicJacobian.Cohomology.RigidEngine4Twist` / `…4Relative`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace Polynomial

open scoped TensorProduct

/-! ## The kernel-transport toolkit (module algebra) -/

namespace AlgebraicJacobian.RigidEngine

variable {S : Type*} [CommRing S]
variable {A B A' B' : Type*}
variable [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
variable [AddCommGroup A'] [Module S A'] [AddCommGroup B'] [Module S B']
variable (δ : A →ₗ[S] B) (δ' : A' →ₗ[S] B')
variable (e₁ : A ≃ₗ[S] A') (e₂ : B ≃ₗ[S] B')

/-- **Kernel transport along a commuting square of equivalences.** If
`e₂ ∘ δ = δ' ∘ e₁` then `ker δ ≃ₗ[S] ker δ'`. Layer 2 uses this to thread the ring-map
base-change clause through the CBC-1 term identifications. 
 * Provenance: CUSTOM.
-/
noncomputable def kerCongr (h : ∀ a : A, e₂ (δ a) = δ' (e₁ a)) :
    ↥(LinearMap.ker δ) ≃ₗ[S] ↥(LinearMap.ker δ') where
  toFun x := ⟨e₁ x, by
    have hx : δ (x : A) = 0 := x.2
    rw [LinearMap.mem_ker, ← h, hx, map_zero]⟩
  invFun y := ⟨e₁.symm y, by
    have hy : δ' (y : A') = 0 := y.2
    have h' := h (e₁.symm (y : A'))
    rw [e₁.apply_symm_apply, hy] at h'
    rw [LinearMap.mem_ker, ← e₂.map_eq_zero_iff, h']⟩
  left_inv x := Subtype.ext (e₁.symm_apply_apply (x : A))
  right_inv y := Subtype.ext (e₁.apply_symm_apply (y : A'))
  map_add' x y := Subtype.ext (map_add e₁ (x : A) (y : A))
  map_smul' c x := Subtype.ext (map_smul e₁ c (x : A))

/-- Provenance: CUSTOM. -/
@[simp]
lemma kerCongr_apply_coe (h : ∀ a : A, e₂ (δ a) = δ' (e₁ a)) (x : LinearMap.ker δ) :
    (kerCongr δ δ' e₁ e₂ h x : A') = e₁ (x : A) := rfl

/-- **Surjectivity transport along a commuting square of equivalences.** 
 * Provenance: CUSTOM.
-/
theorem surjective_congr (h : ∀ a : A, e₂ (δ a) = δ' (e₁ a))
    (hδ : Function.Surjective δ) : Function.Surjective δ' := by
  intro b
  obtain ⟨a, ha⟩ := hδ (e₂.symm b)
  refine ⟨e₁ a, ?_⟩
  rw [← h a, ha, e₂.apply_symm_apply]

end AlgebraicJacobian.RigidEngine

/-! ## The Mayer–Vietoris degree-zero kernel bridge -/

namespace CategoryTheory.GrothendieckTopology.MayerVietorisSquare

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable {R : Type u} [CommRing R]
variable [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} R)]
variable {S : J.MayerVietorisSquare} (F : Sheaf J (ModuleCat.{u} R))

variable (S) in
/-- The restriction pair `F(X₄) → F(X₂) × F(X₃)`, corestricted to the kernel of the
Mayer–Vietoris restriction-difference map (`moduleDiff_restriction`). -/
noncomputable def sectionsToKerModuleDiff :
    F.obj.obj (op S.X₄) →ₗ[R] ↥(LinearMap.ker (S.moduleDiff F)) :=
  LinearMap.codRestrict _
    (((F.obj.map S.f₂₄.op).hom).prod ((F.obj.map S.f₃₄.op).hom))
    fun x => LinearMap.mem_ker.mpr (S.moduleDiff_restriction F x)

omit [HasSheafify J (ModuleCat.{u} R)] in
@[simp]
lemma sectionsToKerModuleDiff_coe (x : F.obj.obj (op S.X₄)) :
    (S.sectionsToKerModuleDiff F x : F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃)) =
      ((F.obj.map S.f₂₄.op).hom x, (F.obj.map S.f₃₄.op).hom x) := rfl

variable (S) in
/-- **The Mayer–Vietoris degree-zero kernel bridge** (the kernel twin of
`MayerVietorisSquare.h1LinearEquiv`): sections over `X₄` are exactly the kernel of the
restriction-difference map `F(X₂) × F(X₃) → F(X₁)` — injectivity is the separation half
of the sheaf condition (`sections_ext`), surjectivity is the gluing half
(`exists_glue_of_moduleDiff_eq_zero`). -/
noncomputable def sectionsKerEquiv :
    F.obj.obj (op S.X₄) ≃ₗ[R] ↥(LinearMap.ker (S.moduleDiff F)) := by
  refine LinearEquiv.ofBijective (S.sectionsToKerModuleDiff F) ⟨?_, ?_⟩
  · intro x y hxy
    have hval : ((F.obj.map S.f₂₄.op).hom x, (F.obj.map S.f₃₄.op).hom x)
        = ((F.obj.map S.f₂₄.op).hom y, (F.obj.map S.f₃₄.op).hom y) := by
      rw [← S.sectionsToKerModuleDiff_coe F x, ← S.sectionsToKerModuleDiff_coe F y, hxy]
    exact S.sections_ext F x y (Prod.ext_iff.mp hval).1 (Prod.ext_iff.mp hval).2
  · rintro ⟨t, ht⟩
    obtain ⟨x, hx₁, hx₂⟩ :=
      S.exists_glue_of_moduleDiff_eq_zero F t (LinearMap.mem_ker.mp ht)
    exact ⟨x, Subtype.ext (Prod.ext hx₁ hx₂)⟩

omit [HasSheafify J (ModuleCat.{u} R)] in
@[simp]
lemma sectionsKerEquiv_apply_coe (x : F.obj.obj (op S.X₄)) :
    (S.sectionsKerEquiv F x : F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃)) =
      ((F.obj.map S.f₂₄.op).hom x, (F.obj.map S.f₃₄.op).hom x) := rfl

end CategoryTheory.GrothendieckTopology.MayerVietorisSquare

namespace AlgebraicGeometry

open CategoryTheory.GrothendieckTopology

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-! ## The scheme-level H⁰-kernel bridge -/

section H0Bridge

variable (U₀ U₁ : X.Opens)
variable (F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} R))

/-- **The two-cover H⁰ kernel bridge** (general coefficients): for any sheaf `F` of
`R`-modules on the small Zariski site and any two-cover `U₀ ⊔ U₁ = ⊤`, the degree-zero
cohomology of the site is the kernel of the Mayer–Vietoris restriction-difference map.
No affineness is needed — degree-0 exactness is the sheaf condition of the square. -/
noncomputable def Scheme.twoCoverH0LinearEquiv (hcov : U₀ ⊔ U₁ = ⊤) :
    Sheaf.HModule F 0 ≃ₗ[R]
      ↥(LinearMap.ker ((X.twoCoverSquare U₀ U₁ hcov).moduleDiff F)) :=
  (Sheaf.HModule.linearEquivHModule' (isTerminalTop : IsTerminal (⊤ : X.Opens)) F 0).trans
    ((Sheaf.HModule'.linearEquiv₀ F (X.twoCoverSquare U₀ U₁ hcov).X₄).trans
      ((X.twoCoverSquare U₀ U₁ hcov).sectionsKerEquiv F))

end H0Bridge

/-! ## The two-lattice pair of a packaged sheaf on a two-chart cover -/

/-- **The two-cover pair data** for a sheaf `F` of `R`-modules packaged quasi-coherently
(`Scheme.QcohOn`) on both charts of a two-chart cover `U₀, U₁` of `X`: the two chart
coordinates `g₀, g₁` with

* the overlap-as-basic-open identifications `U₀ ⊓ U₁ = D(g₀) = D(g₁)` (on the pinned
  relative cover these come from `Scheme.preimage_basicOpen` and the `ℙ¹` chart geometry);
* the `R`-linearity of the packaged coordinate actions (making them `Module.End R`);
* the mutual-inverse law `g₀ · g₁ = 1` on the overlap, expressed directly on the packaged
  actions: the two `qsmul` compositions are the identity of `F(U₀ ⊓ U₁)` (this is the
  pulled-back `P1.chartCoord` relation `t₀t₁ = 1`, and is what makes the overlap action of
  the two-lattice pair invertible).

From this data `Scheme.TwoCoverPairData.pair` builds the `TwoLatticePair` of `F`, whose
localization axioms are the (P2) axioms of the packaging (term-for-term the
`IsLocalizedModule` axioms of RE-0's bridge, worksheet §2.3). -/
structure Scheme.TwoCoverPairData
    (F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} R))
    (U₀ U₁ : X.Opens) [Scheme.QcohOn F U₀] [Scheme.QcohOn F U₁] : Type u where
  /-- The chart-0 coordinate. -/
  g₀ : Γ(X, U₀)
  /-- The (inverse) chart-1 coordinate. -/
  g₁ : Γ(X, U₁)
  /-- The overlap is the basic open of the chart-0 coordinate. -/
  inf_eq_basicOpen₀ : U₀ ⊓ U₁ = X.basicOpen g₀
  /-- The overlap is the basic open of the chart-1 coordinate. -/
  inf_eq_basicOpen₁ : U₀ ⊓ U₁ = X.basicOpen g₁
  /-- The packaged chart-0 coordinate action is `R`-linear. -/
  smul_qsmul₀ : ∀ {W : X.Opens} (hW : W ≤ U₀) (c : R) (m : F.obj.obj (op W)),
    Scheme.QcohOn.qsmul hW g₀ (c • m) = c • Scheme.QcohOn.qsmul hW g₀ m
  /-- The packaged chart-1 coordinate action is `R`-linear. -/
  smul_qsmul₁ : ∀ {W : X.Opens} (hW : W ≤ U₁) (c : R) (m : F.obj.obj (op W)),
    Scheme.QcohOn.qsmul hW g₁ (c • m) = c • Scheme.QcohOn.qsmul hW g₁ m
  /-- On the overlap the two coordinate actions are mutually inverse (`g₀ g₁ = 1`). -/
  qsmul₀_qsmul₁ : ∀ m : F.obj.obj (op (U₀ ⊓ U₁)),
    Scheme.QcohOn.qsmul (inf_le_left : U₀ ⊓ U₁ ≤ U₀) g₀
      (Scheme.QcohOn.qsmul (inf_le_right : U₀ ⊓ U₁ ≤ U₁) g₁ m) = m
  /-- On the overlap the two coordinate actions are mutually inverse (`g₁ g₀ = 1`). -/
  qsmul₁_qsmul₀ : ∀ m : F.obj.obj (op (U₀ ⊓ U₁)),
    Scheme.QcohOn.qsmul (inf_le_right : U₀ ⊓ U₁ ≤ U₁) g₁
      (Scheme.QcohOn.qsmul (inf_le_left : U₀ ⊓ U₁ ≤ U₀) g₀ m) = m

namespace Scheme.TwoCoverPairData

variable {F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} R)}
variable {U₀ U₁ : X.Opens} [Scheme.QcohOn F U₀] [Scheme.QcohOn F U₁]
variable (dat : Scheme.TwoCoverPairData F U₀ U₁)

/-! ### The coordinate actions as `R`-linear endomorphisms -/

/-- The chart-0 coordinate action on `F`-sections over `W ≤ U₀`, as an `R`-linear
endomorphism. -/
noncomputable def end₀ {W : X.Opens} (hW : W ≤ U₀) :
    Module.End R (F.obj.obj (op W)) where
  toFun := Scheme.QcohOn.qsmul hW dat.g₀
  map_add' m n := Scheme.QcohOn.qsmul_add hW dat.g₀ m n
  map_smul' c m := dat.smul_qsmul₀ hW c m

/-- The chart-1 coordinate action on `F`-sections over `W ≤ U₁`, as an `R`-linear
endomorphism. -/
noncomputable def end₁ {W : X.Opens} (hW : W ≤ U₁) :
    Module.End R (F.obj.obj (op W)) where
  toFun := Scheme.QcohOn.qsmul hW dat.g₁
  map_add' m n := Scheme.QcohOn.qsmul_add hW dat.g₁ m n
  map_smul' c m := dat.smul_qsmul₁ hW c m

@[simp]
lemma end₀_apply {W : X.Opens} (hW : W ≤ U₀) (m : F.obj.obj (op W)) :
    dat.end₀ hW m = Scheme.QcohOn.qsmul hW dat.g₀ m := rfl

@[simp]
lemma end₁_apply {W : X.Opens} (hW : W ≤ U₁) (m : F.obj.obj (op W)) :
    dat.end₁ hW m = Scheme.QcohOn.qsmul hW dat.g₁ m := rfl

lemma end₀_pow_apply {W : X.Opens} (hW : W ≤ U₀) (n : ℕ) (m : F.obj.obj (op W)) :
    (dat.end₀ hW ^ n) m = Scheme.QcohOn.qsmul hW (dat.g₀ ^ n) m := by
  induction n generalizing m with
  | zero => rw [pow_zero, Module.End.one_apply, pow_zero, Scheme.QcohOn.one_qsmul]
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, end₀_apply, ← Scheme.QcohOn.mul_qsmul,
      ← pow_succ]

lemma end₁_pow_apply {W : X.Opens} (hW : W ≤ U₁) (n : ℕ) (m : F.obj.obj (op W)) :
    (dat.end₁ hW ^ n) m = Scheme.QcohOn.qsmul hW (dat.g₁ ^ n) m := by
  induction n generalizing m with
  | zero => rw [pow_zero, Module.End.one_apply, pow_zero, Scheme.QcohOn.one_qsmul]
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, end₁_apply, ← Scheme.QcohOn.mul_qsmul,
      ← pow_succ]

/-! ### The pair -/

/-- **The two-lattice pair of a packaged sheaf on an affine two-chart cover** (RE-4,
Layer 1). Carriers `Γ(U₀, F) × Γ(U₁, F) → Γ(U₀ ⊓ U₁, F)`; coordinate actions the packaged
`qsmul` at the pinned chart coordinates; `ι₀, ι₁` the chart-to-overlap section
restrictions; localization axioms `denom/ann` from the (P2) axioms of the packaging —
term-for-term the `IsLocalizedModule.surj`/`exists_of_eq` axioms of RE-0's bridge
(`Scheme.QcohOn.isLocalizedModule_secResₗ`), transported to the overlap along the
`inf_eq_basicOpen` identifications. -/
noncomputable def pair (hU₀ : IsAffineOpen U₀) (hU₁ : IsAffineOpen U₁) :
    TwoLatticePair R (F.obj.obj (op U₀)) (F.obj.obj (op U₁))
      (F.obj.obj (op (U₀ ⊓ U₁))) where
  t₀ := dat.end₀ (le_refl U₀)
  t₁ := dat.end₁ (le_refl U₁)
  tN :=
    { val := dat.end₀ (inf_le_left : U₀ ⊓ U₁ ≤ U₀)
      inv := dat.end₁ (inf_le_right : U₀ ⊓ U₁ ≤ U₁)
      val_inv := LinearMap.ext fun m => dat.qsmul₀_qsmul₁ m
      inv_val := LinearMap.ext fun m => dat.qsmul₁_qsmul₀ m }
  ι₀ := secRes F (inf_le_left : U₀ ⊓ U₁ ≤ U₀)
  ι₁ := secRes F (inf_le_right : U₀ ⊓ U₁ ≤ U₁)
  ι₀_comm x := Scheme.QcohOn.secRes_qsmul inf_le_left (le_refl U₀) dat.g₀ x
  ι₁_comm y := Scheme.QcohOn.secRes_qsmul inf_le_right (le_refl U₁) dat.g₁ y
  denom₀ := fun n => by
    have hb : U₀ ⊓ X.basicOpen dat.g₀ ≤ U₀ ⊓ U₁ :=
      inf_le_right.trans dat.inf_eq_basicOpen₀.ge
    have hb' : U₀ ⊓ U₁ ≤ U₀ ⊓ X.basicOpen dat.g₀ :=
      le_inf inf_le_left dat.inf_eq_basicOpen₀.le
    obtain ⟨M, e, he⟩ := Scheme.QcohOn.exists_secRes_eq_qsmul_pow (F := F) hU₀
      (le_refl U₀) dat.g₀ (secRes F hb n)
    refine ⟨M, e, ?_⟩
    have h2 := congrArg (secRes F hb') he
    rw [Scheme.QcohOn.secRes_qsmul] at h2
    simp only [secRes_secRes, secRes_self] at h2
    rw [dat.end₀_pow_apply]
    exact h2.symm
  denom₁ := fun n => by
    have hb : U₁ ⊓ X.basicOpen dat.g₁ ≤ U₀ ⊓ U₁ :=
      inf_le_right.trans dat.inf_eq_basicOpen₁.ge
    have hb' : U₀ ⊓ U₁ ≤ U₁ ⊓ X.basicOpen dat.g₁ :=
      le_inf inf_le_right dat.inf_eq_basicOpen₁.le
    obtain ⟨M, e, he⟩ := Scheme.QcohOn.exists_secRes_eq_qsmul_pow (F := F) hU₁
      (le_refl U₁) dat.g₁ (secRes F hb n)
    refine ⟨M, e, ?_⟩
    have h2 := congrArg (secRes F hb') he
    rw [Scheme.QcohOn.secRes_qsmul] at h2
    simp only [secRes_secRes, secRes_self] at h2
    rw [dat.end₁_pow_apply]
    exact h2.symm
  ann₀ := fun x hx => by
    have hb : U₀ ⊓ X.basicOpen dat.g₀ ≤ U₀ ⊓ U₁ :=
      inf_le_right.trans dat.inf_eq_basicOpen₀.ge
    have h0 : secRes F (inf_le_left : U₀ ⊓ X.basicOpen dat.g₀ ≤ U₀) x = 0 := by
      have h := congrArg (secRes F hb) hx
      rw [map_zero, secRes_secRes] at h
      exact h
    obtain ⟨M, hM⟩ := Scheme.QcohOn.exists_qsmul_pow_eq_zero (F := F) hU₀
      (le_refl U₀) dat.g₀ x h0
    refine ⟨M, ?_⟩
    rw [dat.end₀_pow_apply]
    exact hM
  ann₁ := fun y hy => by
    have hb : U₁ ⊓ X.basicOpen dat.g₁ ≤ U₀ ⊓ U₁ :=
      inf_le_right.trans dat.inf_eq_basicOpen₁.ge
    have h0 : secRes F (inf_le_left : U₁ ⊓ X.basicOpen dat.g₁ ≤ U₁) y = 0 := by
      have h := congrArg (secRes F hb) hy
      rw [map_zero, secRes_secRes] at h
      exact h
    obtain ⟨M, hM⟩ := Scheme.QcohOn.exists_qsmul_pow_eq_zero (F := F) hU₁
      (le_refl U₁) dat.g₁ y h0
    refine ⟨M, ?_⟩
    rw [dat.end₁_pow_apply]
    exact hM

variable (hU₀ : IsAffineOpen U₀) (hU₁ : IsAffineOpen U₁)

/-- The differential of the pair is the Mayer–Vietoris restriction-difference map of the
two-cover square. -/
lemma pair_diff (hcov : U₀ ⊔ U₁ = ⊤) :
    (dat.pair hU₀ hU₁).diff = (X.twoCoverSquare U₀ U₁ hcov).moduleDiff F := rfl

@[simp]
lemma pair_t₀ : (dat.pair hU₀ hU₁).t₀ = dat.end₀ (le_refl U₀) := rfl

@[simp]
lemma pair_t₁ : (dat.pair hU₀ hU₁).t₁ = dat.end₁ (le_refl U₁) := rfl

/-! ### The cohomology carriers of the pair -/

variable (hcov : U₀ ⊔ U₁ = ⊤)

/-- **The H⁰ carrier**: degree-zero cohomology of the site with coefficients in `F` is
`H⁰` of the two-lattice pair. -/
noncomputable def h0Equiv :
    Sheaf.HModule F 0 ≃ₗ[R] ↥((dat.pair hU₀ hU₁).H0) :=
  (Scheme.twoCoverH0LinearEquiv U₀ U₁ F hcov).trans
    (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker (dat.pair_diff hU₀ hU₁ hcov)).symm)

/-- **The H¹ carrier**: degree-one cohomology of the site with coefficients in `F` is
`H¹` of the two-lattice pair (through the landed two-cover computation and the twisted
affine vanishing on the two charts). -/
noncomputable def h1Equiv :
    Sheaf.HModule F 1 ≃ₗ[R] (dat.pair hU₀ hU₁).H1 :=
  letI := hU₀.subsingleton_hModule'_one_of_qcoh F
  letI := hU₁.subsingleton_hModule'_one_of_qcoh F
  (Scheme.twoCoverH1LinearEquiv R X U₀ U₁ F hcov).trans
    (Submodule.quotEquivOfEq _ _
      ((congrArg LinearMap.range (dat.pair_diff hU₀ hU₁ hcov)).symm.trans
        (dat.pair hU₀ hU₁).range_diff_eq))

/-! ### The engine -/

open AlgebraicJacobian

/-- Vanishing of `H¹` of the pair makes the Čech differential surjective. -/
theorem surjective_diff (hH1 : Subsingleton (dat.pair hU₀ hU₁).H1) :
    Function.Surjective (dat.pair hU₀ hU₁).diff := by
  haveI := hH1
  exact RigidEngine.surjective_of_subsingleton_quotient _
    ((Submodule.quotEquivOfEq _ _
      (dat.pair hU₀ hU₁).range_diff_eq).toEquiv.subsingleton)

include hcov in
/-- **The rigid engine, sheaf level** (Kleiman 3.10 (v)⟹(i)+(iii), curve-lite; worksheet
§1.2 Level 2): for a packaged sheaf on an affine two-chart cover with COH-finite chart
lattices, if every residue-field fibre of `H¹` of the pair vanishes (the **complex-form**
hypothesis; its sheaf-level discharge is the W6-full seam), then `H¹(X, F) = 0` and
`H⁰(X, F)` is a finite projective `R`-module.

Flatness/projectivity hypotheses are carried on the section modules (they are free in the
Layer-2 instantiation): flatness of the Čech domain feeds `RigidEngine.flat_ker`,
projectivity of the overlap module splits the surjective differential. `IsNoetherianRing`
is spent exactly on COH-0 and on `finite ⟹ finitely presented` (worksheet discipline 4). -/
theorem rigidEngine [IsNoetherianRing R]
    [Module.Finite R[X] (Module.AEval' (dat.pair hU₀ hU₁).t₀)]
    [Module.Finite R[X] (Module.AEval' (dat.pair hU₀ hU₁).t₁)]
    [Module.Flat R ((F.obj.obj (op U₀)) × (F.obj.obj (op U₁)))]
    [Module.Projective R (F.obj.obj (op (U₀ ⊓ U₁)))]
    (hfib : ∀ p : PrimeSpectrum R,
      Subsingleton ((dat.pair hU₀ hU₁).H1 ⊗[R] p.asIdeal.ResidueField)) :
    Subsingleton (Sheaf.HModule F 1) ∧ Module.Finite R (Sheaf.HModule F 0) ∧
      Module.Projective R (Sheaf.HModule F 0) := by
  haveI hH1fin : Module.Finite R (dat.pair hU₀ hU₁).H1 :=
    (dat.pair hU₀ hU₁).moduleFinite_h1
  haveI hH1 : Subsingleton (dat.pair hU₀ hU₁).H1 :=
    RigidEngine.subsingleton_of_forall_subsingleton_residueField_tensor hfib
  have hsurj : Function.Surjective (dat.pair hU₀ hU₁).diff :=
    dat.surjective_diff hU₀ hU₁ hH1
  haveI hH0fin : Module.Finite R ↥((dat.pair hU₀ hU₁).H0) :=
    (dat.pair hU₀ hU₁).moduleFinite_h0
  refine ⟨(dat.h1Equiv hU₀ hU₁ hcov).toEquiv.subsingleton, ?_, ?_⟩
  · exact Module.Finite.equiv (dat.h0Equiv hU₀ hU₁ hcov).symm
  · haveI : Module.Finite R ↥(LinearMap.ker (dat.pair hU₀ hU₁).diff) := hH0fin
    haveI : Module.Projective R ↥((dat.pair hU₀ hU₁).H0) :=
      RigidEngine.projective_ker (dat.pair hU₀ hU₁).diff hsurj
    exact Module.Projective.of_equiv' (dat.h0Equiv hU₀ hU₁ hcov).symm

/-- **The openness export** (the strata gift, worksheet §3.3): the fibrewise-vanishing
locus of `H¹` of the pair is open in `Spec R` — COH-1 (Noetherian-free) plus RE-2's
support argument.

* Provenance: ADAPTED.
* TO CHECK: Kleiman's cited openness argument assumes a Noetherian base, while
  this export claims the same result over an arbitrary commutative ring;
  verify the source-to-blueprint hypothesis change. -/
theorem rigidEngine_isOpen_vanishing
    [Module.Finite R[X] (Module.AEval' (dat.pair hU₀ hU₁).t₀)]
    [Module.Finite R[X] (Module.AEval' (dat.pair hU₀ hU₁).t₁)] :
    IsOpen {p : PrimeSpectrum R |
      Subsingleton ((dat.pair hU₀ hU₁).H1 ⊗[R] p.asIdeal.ResidueField)} := by
  haveI : Module.Finite R (dat.pair hU₀ hU₁).H1 := (dat.pair hU₀ hU₁).moduleFinite_h1
  exact RigidEngine.isOpen_setOf_subsingleton_residueField_tensor

/-- **The module-coefficient clause** (Kleiman `eq:Q`, worksheet §1.2): on the vanishing
locus, formation of `H⁰(X, F)` commutes with `⊗_R P` for **every** `R`-module `P` — the
sheaf-level form of `RigidEngine.kerRTensorEquiv` through the H⁰ carrier. -/
noncomputable def h0TensorEquiv (hH1 : Subsingleton (dat.pair hU₀ hU₁).H1)
    [Module.Flat R (F.obj.obj (op (U₀ ⊓ U₁)))]
    (P : Type u) [AddCommGroup P] [Module R P] :
    (Sheaf.HModule F 0) ⊗[R] P ≃ₗ[R]
      ↥(LinearMap.ker ((dat.pair hU₀ hU₁).diff.rTensor P)) :=
  (LinearEquiv.rTensor P (dat.h0Equiv hU₀ hU₁ hcov)).trans
    (RigidEngine.kerRTensorEquiv (dat.pair hU₀ hU₁).diff
      (dat.surjective_diff hU₀ hU₁ hH1) P)

/-- **The ring-map base-change clause, abstract half** (worksheet §1.2
`rigidEngine_baseChange`): on the vanishing locus, `R' ⊗[R] H⁰(X, F)` is `R'`-linearly the
kernel of the base-changed Čech differential, for **every** `R`-algebra `R'`. Layer 2
threads this through the CBC-1 term identifications (`RigidEngine.kerCongr`) to reach
`H⁰` of the base-changed sheaf on the nose. -/
noncomputable def h0BaseChangeEquiv (hH1 : Subsingleton (dat.pair hU₀ hU₁).H1)
    [Module.Flat R (F.obj.obj (op (U₀ ⊓ U₁)))]
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    R' ⊗[R] (Sheaf.HModule F 0) ≃ₗ[R']
      ↥(LinearMap.ker ((dat.pair hU₀ hU₁).diff.baseChange R')) :=
  (LinearEquiv.baseChange R R' _ _ (dat.h0Equiv hU₀ hU₁ hcov)).trans
    (RigidEngine.kerBaseChangeEquiv (dat.pair hU₀ hU₁).diff R'
      (dat.surjective_diff hU₀ hU₁ hH1))

end Scheme.TwoCoverPairData

end AlgebraicGeometry
