/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SectionsDescent
import AlgebraicJacobian.Algebra.BaseChangeTrivialization

/-!
# Evaluation of a descended submodule into base-changed sections (ζ3 brick M, part 1)

For a tower of `k`-algebras `k → A → B` and an `A`-submodule `Mod ⊆ B` (in practice the
descended module of a descent unit `W ∈ (B ⊗[A] B)ˣ`), this file constructs the
**evaluation maps**

`evalT Mod V U e : Γ(Spec A, V) ⊗[A] Mod →ₗ[A] Γ(Spec B, U)`,   `e : U ≤ g_S ⁻¹ᵁ V`,

sending `s ⊗ m` to the product of the `g_S`-pullback of `s` with the restriction of the
`ΓSpecIso`-avatar of `m ∈ B`, together with their calculus:

* `evalT_smul`: `Γ(Spec A, V)`-semilinearity — scalars cross as `g_S`-pullbacks;
* `evalT_res`: compatibility with restriction in both opens;
* `evalT_ratio`: the two coprojection pullbacks of an evaluation differ exactly by the
  restriction of the global unit `w` whenever every element of `Mod` satisfies the
  descent equation `1 ⊗ m = W ⋅ (m ⊗ 1)` — the heart of the `μ`-correction of the ζ3
  kernel lemma.

The trivialization-side algebra (pushforward of a trivialization applied to `rTensor`,
the generator of a pushed trivialization, and the transition-unit action on generators)
is developed first, in the generality of `Module.trivializationPush`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

/-! ## Trivialization generators and transition units -/

namespace Module

variable {A : Type u} [CommRing A] {N : Type u} [AddCommGroup N] [Module A N]
variable {C : Type u} [CommRing C] [Algebra A C]
variable {C' : Type u} [CommRing C'] [Algebra A C']

/-- The pushforward of a trivialization computes `h ∘ t` on `rTensor h`-images. -/
lemma trivializationPush_rTensor (h : C →ₐ[A] C') (t : C ⊗[A] N ≃ₗ[C] C)
    (x : C ⊗[A] N) :
    trivializationPush h t (LinearMap.rTensor N h.toLinearMap x) = h (t x) := by
  induction x with
  | zero => simp
  | tmul c n =>
      rw [LinearMap.rTensor_tmul,
        show (h.toLinearMap c ⊗ₜ[A] n : C' ⊗[A] N) = h c • ((1 : C') ⊗ₜ[A] n) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl,
        map_smul, trivializationPush_one_tmul,
        show (c ⊗ₜ[A] n : C ⊗[A] N) = c • ((1 : C) ⊗ₜ[A] n) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul]
      rw [smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- The generator of a pushed trivialization is the `rTensor`-image of the generator. -/
lemma trivializationPush_symm_one (h : C →ₐ[A] C') (t : C ⊗[A] N ≃ₗ[C] C) :
    (trivializationPush h t).symm 1
      = LinearMap.rTensor N h.toLinearMap (t.symm 1) := by
  apply (trivializationPush h t).injective
  rw [LinearEquiv.apply_symm_apply, trivializationPush_rTensor,
    LinearEquiv.apply_symm_apply, map_one]

/-- The transition unit carries the generator of the second identification onto the
generator of the first. -/
lemma transitionUnit_smul_symm_one {M : Type u} [AddCommGroup M] [Module C M]
    (t₁ t₂ : M ≃ₗ[C] C) :
    t₁.symm 1 = (transitionUnit t₁ t₂).val • t₂.symm 1 := by
  apply t₂.injective
  rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  exact (transitionUnit_val t₁ t₂).symm

end Module

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

set_option quotPrecheck false in
local notation "SA" => (overSpec k A).left
set_option quotPrecheck false in
local notation "SB" => (overSpec k B).left
set_option quotPrecheck false in
local notation "Sq" => (overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "gS" => (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "gS₂" =>
  (Over.overSpecMap ((Algebra.ofId A (B ⊗[A] B)).restrictScalars k)).left
set_option quotPrecheck false in
local notation "q₁" => (Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "q₂" => (Over.overSpecMap (tensorInr (A := A) (B := B))).left

-- Reactivate the section-ring algebra structures of
-- `AlgebraicJacobian.Picard.WitnessAway`.
attribute [local instance] specSectionsAlgebra overSpecSectionsAlgebra
  overSpecSectionsAlgebraSq algebraA_sections isScalarTower_sections
  isScalarTower_sections_basicOpen

namespace Over

/-- `specSectionsAlgebra`, re-keyed on the `overSpec`-spelling of `Spec A` (scoped). -/
@[reducible] noncomputable def overSpecSectionsAlgebraA (U : (SA).Opens) :
    Algebra A Γ(SA, U) :=
  specSectionsAlgebra A U

attribute [local instance] overSpecSectionsAlgebraA

/-- Congruence in the morphism for `appLE` (local copy). -/
private lemma appLE_congr_hom' {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (V : Y.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    f.appLE V U e = g.appLE V U (h ▸ e) := by
  subst h; rfl

/-! ## Spec-level coprojection composites -/

/-- `Spec` level: `q₁ ≫ g_S = g_{S₂}`. -/
lemma overSpecMap_inl_comp_ofId : (q₁) ≫ (gS) = (gS₂) := by
  rw [← Over.comp_left, ← Over.overSpecMap_comp, Over.tensorInl_comp_ofId_eq_ofId]

/-- `Spec` level: `q₂ ≫ g_S = g_{S₂}`. -/
lemma overSpecMap_inr_comp_ofId : (q₂) ≫ (gS) = (gS₂) := by
  rw [← Over.comp_left, ← Over.overSpecMap_comp, Over.tensorInr_comp_ofId_eq_ofId]

/-! ## The evaluation maps -/

variable (Mod : Submodule A B)

/-- The two-variable core of the evaluation: the `g_S`-pullback of the section times the
restricted `ΓSpecIso`-avatar of the submodule element. -/
private noncomputable def evalAux (V : (SA).Opens) (U : (SB).Opens)
    (e : U ≤ (gS) ⁻¹ᵁ V) (s : Γ(SA, V)) (m : Mod) : Γ(SB, U) :=
  ((gS).appLE V U e).hom s
    * ((SB).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (.of B)).inv.hom (m : B))

/-- The `g_S`-pullback intertwines the canonical `A`-algebra structures on sections. -/
private lemma appLE_algebraMap (V : (SA).Opens) (U : (SB).Opens)
    (e : U ≤ (gS) ⁻¹ᵁ V) (a : A) :
    ((gS).appLE V U e).hom (algebraMap A Γ(SA, V) a) = algebraMap A Γ(SB, U) a := by
  change ((gS).appLE V U e).hom
      (((SA).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (.of A)).inv.hom a))
    = ((SB).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (.of B)).inv.hom (algebraMap A B a))
  rw [appLE_restrict_top]
  exact congrArg _ (ΓSpecIso_inv_appTop (CommRingCat.ofHom (algebraMap A B)) a)

/-- Distributivity of the restricted `ΓSpecIso`-avatar over addition. -/
lemma resInv_add (U : (SB).Opens) (b b' : B) :
    ((SB).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (.of B)).inv.hom (b + b'))
      = ((SB).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          ((Scheme.ΓSpecIso (.of B)).inv.hom b)
        + ((SB).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          ((Scheme.ΓSpecIso (.of B)).inv.hom b') := by
  rw [map_add]
  exact map_add _ _ _

/-- Multiplicativity of the restricted `ΓSpecIso`-avatar. -/
lemma resInv_mul (U : (SB).Opens) (b b' : B) :
    ((SB).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (.of B)).inv.hom (b * b'))
      = ((SB).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          ((Scheme.ΓSpecIso (.of B)).inv.hom b)
        * ((SB).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          ((Scheme.ΓSpecIso (.of B)).inv.hom b') := by
  rw [map_mul]
  exact map_mul _ _ _

/-- The evaluation of a section–submodule tensor into base-changed sections:
`s ⊗ m ↦ g_S^♯ s ⋅ (ΓSpecIso⁻¹ m)|_U`. -/
noncomputable def evalT (V : (SA).Opens) (U : (SB).Opens) (e : U ≤ (gS) ⁻¹ᵁ V) :
    Γ(SA, V) ⊗[A] Mod →ₗ[A] Γ(SB, U) :=
  TensorProduct.lift (LinearMap.mk₂ A (evalAux Mod V U e)
    (fun s s' m => by
      simp only [evalAux, map_add, add_mul])
    (fun a s m => by
      simp only [evalAux, Algebra.smul_def, map_mul, appLE_algebraMap, mul_assoc])
    (fun s m m' => by
      simp only [evalAux, Submodule.coe_add]
      rw [resInv_add, mul_add])
    (fun a s m => by
      simp only [evalAux, SetLike.val_smul, Algebra.smul_def]
      rw [resInv_mul]
      change _ = ((SB).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          ((Scheme.ΓSpecIso (.of B)).inv.hom (algebraMap A B a)) * _
      exact mul_left_comm _ _ _))

@[simp]
lemma evalT_tmul (V : (SA).Opens) (U : (SB).Opens) (e : U ≤ (gS) ⁻¹ᵁ V)
    (s : Γ(SA, V)) (m : Mod) :
    evalT Mod V U e (s ⊗ₜ m)
      = ((gS).appLE V U e).hom s
        * ((SB).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
            ((Scheme.ΓSpecIso (.of B)).inv.hom (m : B)) :=
  rfl

/-- Scalars of the section ring cross the evaluation as `g_S`-pullbacks. -/
lemma evalT_smul (V : (SA).Opens) (U : (SB).Opens) (e : U ≤ (gS) ⁻¹ᵁ V)
    (c : Γ(SA, V)) (x : Γ(SA, V) ⊗[A] Mod) :
    evalT Mod V U e (c • x) = ((gS).appLE V U e).hom c * evalT Mod V U e x := by
  induction x with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | tmul s m =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, evalT_tmul, evalT_tmul, map_mul,
        mul_assoc]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]

/-- The evaluation is compatible with restriction in both opens: restricting the value
is evaluating the restricted tensor. -/
lemma evalT_res {V V' : (SA).Opens} {U U' : (SB).Opens}
    (e : U ≤ (gS) ⁻¹ᵁ V) (e' : U' ≤ (gS) ⁻¹ᵁ V') (hV : V' ≤ V) (hU : U' ≤ U)
    (resA : Γ(SA, V) →ₗ[A] Γ(SA, V'))
    (hresA : ∀ s, resA s = ((SA).presheaf.map (homOfLE hV).op).hom s)
    (x : Γ(SA, V) ⊗[A] Mod) :
    ((SB).presheaf.map (homOfLE hU).op).hom (evalT Mod V U e x)
      = evalT Mod V' U' e' (LinearMap.rTensor Mod resA x) := by
  induction x with
  | zero => simp only [map_zero]
  | tmul s m =>
      rw [evalT_tmul, LinearMap.rTensor_tmul, evalT_tmul, hresA, map_mul]
      congr 1
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The coprojection ratio of an evaluation** (the `μ`-correction identity): if every
element of `Mod` satisfies the descent equation of the global unit `w` — `1 ⊗ m =
ΓSpecIso(w) ⋅ (m ⊗ 1)` in `B ⊗[A] B` — then the two coprojection pullbacks of any
evaluation differ by the restriction of `w`. -/
lemma evalT_ratio (w : Γ(Sq, ⊤)ˣ)
    (hmod : ∀ m : Mod, tensorInr (k := k) (A := A) (B := B) (m : B)
      = (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom w.val
        * tensorInl (k := k) (A := A) (B := B) (m : B))
    (V : (SA).Opens) (U : (SB).Opens) (e : U ≤ (gS) ⁻¹ᵁ V)
    {O : (Sq).Opens} (e₁ : O ≤ (q₁) ⁻¹ᵁ U) (e₂ : O ≤ (q₂) ⁻¹ᵁ U)
    (x : Γ(SA, V) ⊗[A] Mod) :
    ((q₂).appLE U O e₂).hom (evalT Mod V U e x)
      = ((Sq).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom w.val
        * ((q₁).appLE U O e₁).hom (evalT Mod V U e x) := by
  induction x with
  | zero => simp only [map_zero, mul_zero]
  | tmul s m =>
      rw [evalT_tmul, map_mul, map_mul]
      have hle₂ : O ≤ (gS₂) ⁻¹ᵁ V :=
        (overSpecMap_inl_comp_ofId (k := k) (A := A) (B := B)) ▸
          (e₁.trans ((q₁).preimage_mono e))
      -- the section parts collapse onto the common composite
      have hs₁ : ((q₁).appLE U O e₁).hom (((gS).appLE V U e).hom s)
          = (((gS₂)).appLE V O hle₂).hom s := by
        rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
        exact congr($(appLE_congr_hom'
          (overSpecMap_inl_comp_ofId (k := k) (A := A) (B := B)) V O
          (e₁.trans ((q₁).preimage_mono e))).hom s)
      have hs₂ : ((q₂).appLE U O e₂).hom (((gS).appLE V U e).hom s)
          = (((gS₂)).appLE V O hle₂).hom s := by
        rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
        exact congr($(appLE_congr_hom'
          (overSpecMap_inr_comp_ofId (k := k) (A := A) (B := B)) V O
          (e₂.trans ((q₂).preimage_mono e))).hom s)
      -- the module parts are the two coprojections of the avatar
      have hm : ∀ (σ : B →ₐ[k] B ⊗[A] B)
          (eφ : O ≤ (Over.overSpecMap σ).left ⁻¹ᵁ U),
          (((Over.overSpecMap σ).left).appLE U O eφ).hom
              (((SB).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
                ((Scheme.ΓSpecIso (.of B)).inv.hom (m : B)))
            = ((Sq).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom
                ((Scheme.ΓSpecIso (.of (B ⊗[A] B))).inv.hom (σ (m : B))) := by
        intro σ eφ
        rw [appLE_restrict_top]
        exact congrArg _ (ΓSpecIso_inv_appTop (CommRingCat.ofHom σ.toRingHom) (m : B))
      rw [hs₁, hs₂, hm (tensorInl (k := k) (A := A) (B := B)) e₁,
        hm (tensorInr (k := k) (A := A) (B := B)) e₂]
      -- the descent equation of `w`
      have h3 : ((Sq).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom
            ((Scheme.ΓSpecIso (.of (B ⊗[A] B))).inv.hom
              (tensorInr (k := k) (A := A) (B := B) (m : B)))
          = ((Sq).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom w.val
            * ((Sq).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom
              ((Scheme.ΓSpecIso (.of (B ⊗[A] B))).inv.hom
                (tensorInl (k := k) (A := A) (B := B) (m : B))) := by
        refine (congrArg (fun b => ((Sq).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom
            ((Scheme.ΓSpecIso (.of (B ⊗[A] B))).inv.hom b)) (hmod m)).trans ?_
        refine (congrArg ((Sq).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom
            (map_mul (Scheme.ΓSpecIso (.of (B ⊗[A] B))).inv.hom _ _)).trans ?_
        refine (map_mul _ _ _).trans ?_
        exact congrArg (fun z => z * ((Sq).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom
            ((Scheme.ΓSpecIso (.of (B ⊗[A] B))).inv.hom
              (tensorInl (k := k) (A := A) (B := B) (m : B))))
          (congrArg ((Sq).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom
            (ΓSpecIso_inv_hom (CommRingCat.of (B ⊗[A] B)) w.val))
      rw [h3]
      exact mul_left_comm _ _ _
  | add x y hx hy =>
      simp only [map_add, hx, hy, mul_add]

end Over

end AlgebraicGeometry
