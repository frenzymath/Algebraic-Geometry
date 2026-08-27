/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Presheaf internal hom sub-module of `TensorObjSubstrate`

This file provides the foundational presheaf-level algebra that the C-bridge
`dual_isLocallyTrivial` (and thereby `exists_tensorObj_inverse`) consumes:

- `RestrictScalarsRingIsoTensor`: the strong-monoidal upgrade of `restrictScalars`
  along a ring iso (H2 of `tensorObj_restrict_iso`); includes `restrictScalarsRingIsoDualEquiv`.
- Lax-monoidal `PresheafOfModules.restrictScalars` (H2 presheaf lift).
- Presheaf-level pushforward adjunction `pushforwardPushforwardAdj`
  (H1 of `tensorObj_restrict_iso`).
- `StrongMonoidalRestrictScalars`: `restrictScalarsMonoidalOfBijective`.
- `InternalHom` namespace: slice internal hom, homModule, internalHom, internalHomEval.
- `Dual` section: presheaf dual, evalLin, dualIsoOfIso.

Imported by `AlgebraicJacobian.Picard.TensorObjSubstrate` (the public API file).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

/-! ## Project-local Mathlib supplement — base change along a ring iso commutes
with `⊗` (the H2 "bottom gap" of `tensorObj_restrict_iso`)

For a *ring isomorphism* `e : R ≃+* S` and `S`-modules `A`, `B`, base change along
`e` (giving each `S`-module its `R`-module structure via `Module.compHom _ e.toRingHom`)
commutes with the tensor product: the canonical map `a ⊗ₜ[R] b ↦ a ⊗ₜ[S] b` is an
`R`-linear equivalence `A ⊗[R] B ≃ₗ[R] A ⊗[S] B`. Equivalently, `restrictScalars`
along a ring iso is *strong* monoidal — the lax tensorator is invertible. Mathlib
has `ModuleCat.extendScalars` strong monoidal but `restrictScalars` only
`LaxMonoidal`; this ring-iso strong upgrade is absent and is the documented "REAL
bottom gap" (H2) of `tensorObj_restrict_iso`. -/

section RestrictScalarsRingIsoTensor

open TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The `R`-linear equivalence `A ⊗[R] B ≃ₗ[R] A ⊗[S] B` (`a ⊗ₜ b ↦ a ⊗ₜ b`),
where the `R`-module structures are base-changed along the ring iso `e : R ≃+* S`.
Base change along a ring iso commutes with `⊗`. -/
noncomputable def restrictScalarsRingIsoTensorEquiv (e : R ≃+* S)
    (A B : Type u) [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B] :
    letI _iA : Module R A := Module.compHom A e.toRingHom
    letI _iB : Module R B := Module.compHom B e.toRingHom
    letI _iT : Module R (TensorProduct S A B) := Module.compHom _ e.toRingHom
    TensorProduct R A B ≃ₗ[R] TensorProduct S A B := by
  letI _iA : Module R A := Module.compHom A e.toRingHom
  letI _iB : Module R B := Module.compHom B e.toRingHom
  letI _iT : Module R (TensorProduct S A B) := Module.compHom _ e.toRingHom
  -- Forward: `a ⊗ₜ[R] b ↦ a ⊗ₜ[S] b`, an `R`-bilinear-to-linear lift.
  let fwd : TensorProduct R A B →ₗ[R] TensorProduct S A B :=
    TensorProduct.lift
      { toFun := fun a =>
          { toFun := fun b => a ⊗ₜ[S] b
            map_add' := fun b b' => by rw [TensorProduct.tmul_add]
            map_smul' := fun r b => by
              simp only [RingHom.id_apply]
              change a ⊗ₜ[S] (e r • b) = e r • (a ⊗ₜ[S] b)
              rw [TensorProduct.tmul_smul] }
        map_add' := fun a a' => by ext b; simp [TensorProduct.add_tmul]
        map_smul' := fun r a => by
          ext b
          simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk,
            AddHom.coe_mk]
          change (e r • a) ⊗ₜ[S] b = e r • (a ⊗ₜ[S] b)
          rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul] }
  -- Inverse: `a ⊗ₜ[S] b ↦ a ⊗ₜ[R] b`. Built as an additive lift out of the
  -- `S`-tensor (scalar-swap compatibility uses `s • a = e.symm s •ᵣ a`), then
  -- shown `R`-linear (`R` acting on the `S`-tensor via `e`).
  let bwdAdd : TensorProduct S A B →+ TensorProduct R A B :=
    TensorProduct.liftAddHom
      { toFun := fun a =>
          { toFun := fun b => a ⊗ₜ[R] b
            map_zero' := by rw [TensorProduct.tmul_zero]
            map_add' := fun b b' => by rw [TensorProduct.tmul_add] }
        map_zero' := by ext b; simp [TensorProduct.zero_tmul]
        map_add' := fun a a' => by ext b; simp [TensorProduct.add_tmul] }
      (fun s a b => by
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        -- `(s • a) ⊗ₜ[R] b = a ⊗ₜ[R] (s • b)`; move the `S`-scalar through `e.symm`.
        have hsa : (s • a) = (e.symm s : R) • a := by
          change s • a = e (e.symm s) • a; rw [e.apply_symm_apply]
        have hsb : (s • b) = (e.symm s : R) • b := by
          change s • b = e (e.symm s) • b; rw [e.apply_symm_apply]
        rw [hsa, hsb]; exact TensorProduct.smul_tmul _ _ _ )
  let bwd : TensorProduct S A B →ₗ[R] TensorProduct R A B :=
    { toFun := bwdAdd
      map_add' := bwdAdd.map_add
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        -- `R` acts on the `S`-tensor via `e`; reduce to additive `S`-scalar action.
        change bwdAdd (e r • x) = r • bwdAdd x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b =>
            rw [TensorProduct.smul_tmul']
            change (e r • a) ⊗ₜ[R] b = r • (a ⊗ₜ[R] b)
            rw [TensorProduct.smul_tmul']
            rfl
        | add x y hx hy =>
            rw [smul_add, map_add, map_add, hx, hy, smul_add] }
  refine LinearEquiv.ofLinear fwd bwd ?_ ?_
  · -- right inverse `fwd ∘ bwd = id`. The composite is `R`-linear over the
    -- `S`-tensor, so check on additive generators by induction.
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        change fwd (bwdAdd (a ⊗ₜ[S] b)) = a ⊗ₜ[S] b
        change fwd (a ⊗ₜ[R] b) = a ⊗ₜ[S] b
        simp only [fwd, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
    | add x y hx hy => rw [map_add bwd, map_add fwd, hx, hy]
  · -- left inverse `bwd ∘ fwd = id` on `a ⊗ₜ[R] b` (composite `R`-linear over the
    -- `R`-tensor, so `TensorProduct.ext'` applies).
    refine TensorProduct.ext' fun a b => ?_
    change bwdAdd (fwd (a ⊗ₜ[R] b)) = a ⊗ₜ[R] b
    change bwdAdd (a ⊗ₜ[S] b) = a ⊗ₜ[R] b
    rfl

/-- The forward map of `restrictScalarsRingIsoTensorEquiv` on a simple tensor:
`a ⊗ₜ[R] b ↦ a ⊗ₜ[S] b`. -/
@[simp] lemma restrictScalarsRingIsoTensorEquiv_apply_tmul (e : R ≃+* S)
    (A B : Type u) [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B] (a : A) (b : B) :
    letI _iA : Module R A := Module.compHom A e.toRingHom
    letI _iB : Module R B := Module.compHom B e.toRingHom
    letI _iT : Module R (TensorProduct S A B) := Module.compHom _ e.toRingHom
    restrictScalarsRingIsoTensorEquiv e A B (a ⊗ₜ[R] b) = a ⊗ₜ[S] b := by
  letI _iA : Module R A := Module.compHom A e.toRingHom
  letI _iB : Module R B := Module.compHom B e.toRingHom
  letI _iT : Module R (TensorProduct S A B) := Module.compHom _ e.toRingHom
  simp only [restrictScalarsRingIsoTensorEquiv, LinearEquiv.ofLinear_apply,
    TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]

/-- **`ModuleCat.restrictScalars` along a ring isomorphism is strong monoidal: the
lax tensorator `μ` is an isomorphism.** This is the "REAL bottom gap" (H2) of
`tensorObj_restrict_iso`. For a ring iso `e : R ≃+* S` and `S`-modules `M₁, M₂`,
the underlying map of the lax tensorator
`μ : restrictScalars(M₁) ⊗_R restrictScalars(M₂) ⟶ restrictScalars(M₁ ⊗_S M₂)`
sends `m₁ ⊗ₜ m₂ ↦ m₁ ⊗ₜ m₂` (`ModuleCat.restrictScalars_μ_tmul`), which is exactly
the forward `R`-linear equivalence `restrictScalarsRingIsoTensorEquiv e`, hence is
bijective, hence an isomorphism. Mathlib has `extendScalars` strong monoidal but
only `restrictScalars` lax; this ring-iso strong upgrade is the documented absent
ingredient. -/
lemma restrictScalars_isIso_μ (e : R ≃+* S) (M₁ M₂ : ModuleCat.{u} S) :
    IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M₁ M₂) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfun : ⇑(Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M₁ M₂)
      = ⇑(restrictScalarsRingIsoTensorEquiv e M₁ M₂) := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact (map_zero _).symm
    | tmul a b =>
        erw [ModuleCat.restrictScalars_μ_tmul]
        exact (restrictScalarsRingIsoTensorEquiv_apply_tmul e M₁ M₂ a b).symm
    | add x y hx hy => rw [map_add, hx, hy]; exact (map_add _ x y).symm
  rw [hfun]
  exact (restrictScalarsRingIsoTensorEquiv e M₁ M₂).bijective

/-- **The lax-monoidal unit `ε` of `restrictScalars` along a ring iso is an
isomorphism.** Its underlying map is the ring map `e` (`ModuleCat.restrictScalars_η`),
which is bijective since `e` is a ring equivalence. -/
lemma restrictScalars_isIso_ε (e : R ≃+* S) :
    IsIso (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars e.toRingHom)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfun : ⇑(Functor.LaxMonoidal.ε (ModuleCat.restrictScalars e.toRingHom)) = ⇑e := by
    ext r
    exact ModuleCat.restrictScalars_η (f := e.toRingHom) r
  rw [hfun]
  exact e.bijective

/-- **`ModuleCat.restrictScalars` along a ring isomorphism is (strong) monoidal.**
The packaged `Functor.Monoidal` structure obtained from the lax structure by
inverting `ε` (`restrictScalars_isIso_ε`) and `μ` (`restrictScalars_isIso_μ`). This
is the clean, reusable strong-monoidal upgrade that Mathlib provides for
`extendScalars` but not `restrictScalars`; it is the ModuleCat-level core of the H2
ingredient of `tensorObj_restrict_iso`. -/
@[implicit_reducible]
noncomputable def restrictScalarsMonoidalOfRingEquiv (e : R ≃+* S) :
    (ModuleCat.restrictScalars e.toRingHom).Monoidal := by
  haveI : IsIso (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars e.toRingHom)) :=
    restrictScalars_isIso_ε e
  haveI : ∀ M₁ M₂, IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M₁ M₂) :=
    fun M₁ M₂ => restrictScalars_isIso_μ e M₁ M₂
  exact Functor.Monoidal.ofLaxMonoidal _

/-- **Bijective-ring-hom form of the strong-monoidal tensorator.** For an arbitrary
*bijective* ring hom `f : R →+* S`, the lax tensorator of `ModuleCat.restrictScalars f`
is an isomorphism. This is the form consumed by the presheaf-level lift, where the
componentwise ring map `(α.app X).hom` of a `NatIso` of ring presheaves is bijective
but not literally presented as `(_ : R ≃+* S).toRingHom`. -/
lemma restrictScalars_isIso_μ_of_bijective (f : R →+* S) (hf : Function.Bijective f)
    (M₁ M₂ : ModuleCat.{u} S) :
    IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars f) M₁ M₂) := by
  have hfe : f = (RingEquiv.ofBijective f hf).toRingHom := RingHom.ext fun _ => rfl
  rw [hfe]
  exact restrictScalars_isIso_μ (RingEquiv.ofBijective f hf) M₁ M₂

/-- **Bijective-ring-hom form of the strong-monoidal unit.** Companion of
`restrictScalars_isIso_μ_of_bijective` for the lax unit `ε`. -/
lemma restrictScalars_isIso_ε_of_bijective (f : R →+* S) (hf : Function.Bijective f) :
    IsIso (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars f)) := by
  have hfe : f = (RingEquiv.ofBijective f hf).toRingHom := RingHom.ext fun _ => rfl
  rw [hfe]
  exact restrictScalars_isIso_ε (RingEquiv.ofBijective f hf)

/-- **Base change along a ring iso commutes with the linear dual** (the `Hom`-analogue
of `restrictScalarsRingIsoTensorEquiv`). For a ring isomorphism `e : R ≃+* S` and an
`S`-module `M`, the `R`-linear equivalence
`restrictScalars_e (M →ₗ[S] S) ≃ₗ[R] (restrictScalars_e M →ₗ[R] R)`, `φ ↦ e.symm ∘ φ`.

This is the ModuleCat-level **H2′ ingredient** of the (still-open, d.2-FREE) C-bridge
`(dual M).restrict f ≅ dual (M.restrict f)` along an open immersion `f`: the C-bridge
mirrors `tensorObj_restrict_iso` exactly (Step 1 `restrictFunctorIsoPullback`, Step 2
`sheafificationCompPullback`, Step 3 strip sheafification, Step 4 H1
`pushforwardPushforwardAdj`∘`leftAdjointUniq` ∘ this H2′), with `⊗` replaced by `dual`
and `restrictScalarsRingIsoTensorEquiv` replaced by this equivalence. Like its tensor
counterpart it is **pure algebra over a ring iso — no stalk, no filtered-colimit, no
whiskering of the sheafification unit (no d.2)**: a map `M → S` is `R`-linear (via `e`)
iff it is `S`-linear, and `e.symm` carries the codomain `S` to `R`. The forward map is
`R`-linear; the inverse `ψ ↦ e ∘ ψ` is its two-sided inverse. The `iMS` `Module R`
instance on `M →ₗ[S] S` is base change along `e`. -/
noncomputable def restrictScalarsRingIsoDualEquiv (e : R ≃+* S)
    (M : Type u) [AddCommGroup M] [Module S M] :
    letI _iM : Module R M := Module.compHom M e.toRingHom
    letI _iMS : Module R (M →ₗ[S] S) := Module.compHom _ e.toRingHom
    (M →ₗ[S] S) ≃ₗ[R] (M →ₗ[R] R) := by
  letI _iM : Module R M := Module.compHom M e.toRingHom
  letI _iMS : Module R (M →ₗ[S] S) := Module.compHom _ e.toRingHom
  have hsmulM : ∀ (r : R) (m : M), r • m = e r • m := fun _ _ => rfl
  refine
    { toFun := fun φ =>
        { toFun := fun m => e.symm (φ m)
          map_add' := fun m m' => by simp [map_add]
          map_smul' := fun r m => by
            simp only [RingHom.id_apply, smul_eq_mul]
            rw [hsmulM, map_smul, smul_eq_mul, map_mul, e.symm_apply_apply] }
      invFun := fun ψ =>
        { toFun := fun m => e (ψ m)
          map_add' := fun m m' => by simp [map_add]
          map_smul' := fun s m => by
            simp only [RingHom.id_apply, smul_eq_mul]
            have hsm : s • m = (e.symm s) • m := by rw [hsmulM, e.apply_symm_apply]
            rw [hsm, map_smul, smul_eq_mul, map_mul, e.apply_symm_apply] }
      left_inv := fun φ => by ext m; exact e.apply_symm_apply _
      right_inv := fun ψ => by ext m; exact e.symm_apply_apply _
      map_add' := fun φ φ' => by
        ext m
        simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk, map_add]
      map_smul' := fun r φ => by
        ext m
        simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk,
          smul_eq_mul]
        change e.symm ((e r • φ) m) = r * e.symm (φ m)
        rw [LinearMap.smul_apply, smul_eq_mul, map_mul, e.symm_apply_apply] }

end RestrictScalarsRingIsoTensor

/-! ## Project-local Mathlib supplement — `restrictScalars` is lax monoidal

The presheaf-of-modules restriction-of-scalars functor along a morphism of
presheaves of *commutative* rings is lax monoidal. Mathlib ships the sectionwise
fact `ModuleCat.restrictScalars f` is `LaxMonoidal`
(`Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction`); here we lift it to
the presheaf level through the sectionwise presheaf monoidal structure
(`PresheafOfModules.Monoidal`). This is the sole project-side ingredient feeding
the oplax comparison `δ` of `pullback φ` (the mate of `pushforward φ`) used to
close `tensorObj_restrict_iso`. Per blueprint `lem:restrictscalars_laxmonoidal`. -/

namespace PresheafOfModules

universe v'

variable {C : Type u} [Category.{v'} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The lax-monoidal unit `ε` of `restrictScalars α`, assembled sectionwise from
`ModuleCat.restrictScalars (α.app X)`'s lax-monoidal unit. -/
noncomputable def restrictScalarsLaxε
    (α : R ⋙ forget₂ CommRingCat RingCat ⟶ S ⋙ forget₂ CommRingCat RingCat) :
    (𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ _ _))) ⟶
      (restrictScalars α).obj (𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ _ _))) where
  app X := Functor.LaxMonoidal.ε (ModuleCat.restrictScalars (α.app X).hom)
  naturality {X Y} f := by
    ext
    dsimp
    erw [PresheafOfModules.unit_map_one, ModuleCat.restrictScalars_η,
      ModuleCat.restrictScalars_η]
    simp only [map_one]
    erw [PresheafOfModules.unit_map_one]

set_option backward.isDefEq.respectTransparency false in
/-- The lax-monoidal tensorator `μ` of `restrictScalars α`, assembled sectionwise
from `ModuleCat.restrictScalars (α.app X)`'s lax-monoidal tensorator. -/
noncomputable def restrictScalarsLaxμ
    (α : R ⋙ forget₂ CommRingCat RingCat ⟶ S ⋙ forget₂ CommRingCat RingCat)
    (M₁ M₂ : PresheafOfModules.{u} (S ⋙ forget₂ _ _)) :
    (restrictScalars α).obj M₁ ⊗ (restrictScalars α).obj M₂ ⟶
      (restrictScalars α).obj (M₁ ⊗ M₂) where
  app X := by
    exact Functor.LaxMonoidal.μ (ModuleCat.restrictScalars (α.app X).hom) (M₁.obj X) (M₂.obj X)
  naturality {X Y} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₂ ↦ ?_)
    dsimp
    erw [PresheafOfModules.Monoidal.tensorObj_map_tmul, ModuleCat.restrictScalars_μ_tmul,
      ModuleCat.restrictScalars_μ_tmul, PresheafOfModules.Monoidal.tensorObj_map_tmul]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- **`restrictScalars α` is lax monoidal** for a morphism `α` of presheaves of
commutative rings. Project-local lift of `ModuleCat.instLaxMonoidalRestrictScalars`. -/
noncomputable instance restrictScalarsLaxMonoidal
    (α : R ⋙ forget₂ CommRingCat RingCat ⟶ S ⋙ forget₂ CommRingCat RingCat) :
    (PresheafOfModules.restrictScalars α).LaxMonoidal where
  ε := restrictScalarsLaxε α
  μ M₁ M₂ := restrictScalarsLaxμ α M₁ M₂
  μ_natural_left := by
    intro X Y f X'
    ext1 Z
    exact Functor.LaxMonoidal.μ_natural_left (F := ModuleCat.restrictScalars (α.app Z).hom)
      (f.app Z) (X'.obj Z)
  μ_natural_right := by
    intro X Y X' f
    ext1 Z
    exact Functor.LaxMonoidal.μ_natural_right (F := ModuleCat.restrictScalars (α.app Z).hom)
      (X'.obj Z) (f.app Z)
  associativity := by
    intro M N P
    ext1 Z
    exact Functor.LaxMonoidal.associativity (F := ModuleCat.restrictScalars (α.app Z).hom)
      (M.obj Z) (N.obj Z) (P.obj Z)
  left_unitality := by
    intro M
    ext1 Z
    exact Functor.LaxMonoidal.left_unitality (F := ModuleCat.restrictScalars (α.app Z).hom)
      (M.obj Z)
  right_unitality := by
    intro M
    ext1 Z
    exact Functor.LaxMonoidal.right_unitality (F := ModuleCat.restrictScalars (α.app Z).hom)
      (M.obj Z)

end PresheafOfModules

/-! ## Project-local Mathlib supplement — the presheaf-level pushforward adjunction (H1)

De-sheafification of `SheafOfModules.{pushforwardNatTrans, pushforwardCongr,
pushforwardPushforwardAdj}`
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`, L154/L73/L226) to the
`PresheafOfModules` level. Every line of the sheaf template already manipulates
`.val`/`.val.presheaf` presheaf data, so the de-sheafification is mechanical (drop the `Sheaf`
wrapper and the sheaf-only `IsContinuous` `letI`s). These are the **H1** linchpin of
`tensorObj_restrict_iso`: from a pair `adj : F ⊣ G` one obtains a presheaf-level adjunction
`pushforward φ ⊣ pushforward ψ`, hence — against the existing
`PresheafOfModules.pullbackPushforwardAdjunction` and via `Adjunction.leftAdjointUniq` —
the iso `pushforward β ≅ pullback φ` that moves the abstract presheaf pullback onto the concrete
restriction pushforward. Per blueprint `lem:tensorobj_restrict_iso`, Step 3 (the H1 residual). -/

namespace PresheafOfModules

open CategoryTheory Functor

section PushforwardNatTrans

universe v₁ v₂ uC uD

variable {C : Type uC} [Category.{v₁} C] {D : Type uD} [Category.{v₂} D]
  {F G : C ⥤ D} {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
  (φ : S ⟶ G.op ⋙ R)

/-- **Presheaf-level `pushforwardNatTrans`.** A natural transformation `α : F ⟶ G` of functors
`C ⥤ D` induces a natural transformation between the pushforward functors along `F` and `G`.
De-sheafification of `SheafOfModules.pushforwardNatTrans`
(`Sheaf/PushforwardContinuous.lean:154`), dropping the `.val` wrapper. -/
noncomputable def pushforwardNatTrans (α : F ⟶ G) :
    pushforward.{u} φ ⟶ pushforward.{u} (φ ≫ Functor.whiskerRight (NatTrans.op α) R) where
  app M :=
    { app := fun U => (ModuleCat.restrictScalars (φ.app U).hom).map (M.map (α.app U.unop).op)
      naturality := fun {U V} i => by
        ext x
        dsimp
        change (M.presheaf.map (G.map i.unop).op ≫ M.presheaf.map (α.app V.unop).op) _ =
          (M.presheaf.map (α.app U.unop).op ≫ M.presheaf.map (F.map i.unop).op) _
        simp only [← CategoryTheory.Functor.map_comp, ← op_comp, α.naturality] }
  naturality := fun {M N} f => by
    ext U x
    exact congr($(f.naturality (α.app U.unop).op) x).symm

@[simp] lemma pushforwardNatTrans_app_app_apply (α : F ⟶ G) (M : PresheafOfModules.{u} R)
    (U : Cᵒᵖ) (x) :
    ((pushforwardNatTrans φ α).app M).app U x = M.map (α.app U.unop).op x := rfl

end PushforwardNatTrans

section PushforwardCongr

universe v₁ v₂ uC uD

variable {C : Type uC} [Category.{v₁} C] {D : Type uD} [Category.{v₂} D]
  {F : C ⥤ D} {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}

/-- **Presheaf-level `pushforwardCongr`.** Pushforwards along equal morphisms of presheaves of
rings are isomorphic. De-sheafification of `SheafOfModules.pushforwardCongr`
(`Sheaf/PushforwardContinuous.lean:73`), dropping the `fullyFaithfulForget` preimage (the
presheaf-level `pushforward` lands in `PresheafOfModules` directly). -/
noncomputable def pushforwardCongr {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) :
    pushforward.{u} φ ≅ pushforward.{u} ψ :=
  NatIso.ofComponents (fun M ↦
    PresheafOfModules.isoMk
      (fun U ↦ (ModuleCat.restrictScalarsCongr (R := S.obj U) (S := R.obj _)
        (f := (φ.app U).hom) (g := (ψ.app U).hom) (by subst e; rfl)).app _)
      (fun _ _ _ ↦ by subst e; rfl)) (fun _ ↦ by subst e; rfl)

@[simp] lemma pushforwardCongr_hom_app_app {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ)
    (M : PresheafOfModules.{u} R) (U x) :
    ((pushforwardCongr e).hom.app M).app U x = x := by subst e; rfl

@[simp] lemma pushforwardCongr_inv_app_app {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ)
    (M : PresheafOfModules.{u} R) (U x) :
    ((pushforwardCongr e).inv.app M).app U x = x := by subst e; rfl

end PushforwardCongr

section PushforwardAdj

universe v₁ v₂ uC uD

variable {C : Type uC} [Category.{v₁} C] {D : Type uD} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
  (adj : F ⊣ G)
  (φ : S ⟶ F.op ⋙ R)
  (ψ : R ⟶ G.op ⋙ S)
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R = ψ ≫ G.op.whiskerLeft φ)
  (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ Functor.whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)

set_option backward.isDefEq.respectTransparency false in
/-- **Presheaf-level `pushforwardPushforwardAdj`.** If `F ⊣ G`, then the presheaf-of-modules
pushforwards along `F` and `G` are also adjoint. De-sheafification of
`SheafOfModules.pushforwardPushforwardAdj` (`Sheaf/PushforwardContinuous.lean:226`), dropping the
sheaf-only `IsContinuous` `letI`s and the `.val`/`.hom` wrappers. This is the H1 linchpin: applied
to the open-immersion adjunction `f.opensFunctor ⊣ Opens.map f.base` it gives
`pushforward β ⊣ pushforward φ`. -/
noncomputable def pushforwardPushforwardAdj : pushforward.{u} φ ⊣ pushforward.{u} ψ where
  unit :=
    (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
      (pushforwardCongr (by simpa using H₁)).hom ≫ (pushforwardComp _ _).inv
  counit :=
    (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
      (pushforwardCongr (by simpa using H₂)).hom ≫ (pushforwardId _).hom
  left_triangle_components X := by
    ext U x
    change (X.presheaf.map (adj.counit.app (F.obj U.unop)).op ≫
      X.presheaf.map (F.map (adj.unit.app U.unop)).op) _ = _
    dsimp only [id_obj]
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components]
    simp
  right_triangle_components X := by
    ext U x
    change (X.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
      X.presheaf.map (adj.unit.app (G.obj U.unop)).op) _ = _
    rw [← Functor.map_comp, ← op_comp, adj.right_triangle_components]
    simp

end PushforwardAdj

section StrongMonoidalRestrictScalars

universe v'

variable {C : Type u} [Category.{v'} C]

/-- **A sectionwise-isomorphism morphism of presheaves of modules is an isomorphism.**
The inverse is assembled sectionwise via `isoMk` (whose forward naturality is exactly the
naturality of the given morphism). -/
lemma isIso_of_isIso_app {𝓡 : Cᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{u} 𝓡}
    (g : M ⟶ N) (h : ∀ U, IsIso (g.app U)) : IsIso g := by
  haveI := h
  have hg : g = (PresheafOfModules.isoMk (fun U => asIso (g.app U))
      (fun _ _ φ => g.naturality φ)).hom :=
    PresheafOfModules.hom_ext (fun _ => rfl)
  rw [hg]; infer_instance

variable {R S : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- **`PresheafOfModules.restrictScalars α` is strong monoidal when `α` is sectionwise
bijective.** The lax tensorator `μ` and unit `ε` (`restrictScalarsLaxMonoidal`) are assembled
sectionwise from the `ModuleCat`-level ones, which are isomorphisms for a bijective ground-ring
map (`restrictScalars_isIso_μ_of_bijective`, `restrictScalars_isIso_ε_of_bijective`); hence the
presheaf `μ`/`ε` are sectionwise isos, hence isos (`isIso_of_isIso_app`), and the lax structure
upgrades to strong via `Functor.Monoidal.ofLaxMonoidal`. This is the **H2** presheaf lift of
`tensorObj_restrict_iso`. -/
@[implicit_reducible]
noncomputable def restrictScalarsMonoidalOfBijective
    (α : R ⋙ forget₂ CommRingCat RingCat ⟶ S ⋙ forget₂ CommRingCat RingCat)
    (hα : ∀ U, Function.Bijective (α.app U).hom) :
    (PresheafOfModules.restrictScalars α).Monoidal := by
  haveI hε : IsIso (Functor.LaxMonoidal.ε (PresheafOfModules.restrictScalars α)) :=
    isIso_of_isIso_app _ (fun U => restrictScalars_isIso_ε_of_bijective (α.app U).hom (hα U))
  haveI hμ : ∀ M₁ M₂, IsIso (Functor.LaxMonoidal.μ (PresheafOfModules.restrictScalars α) M₁ M₂) :=
    fun M₁ M₂ => isIso_of_isIso_app _
      (fun U => restrictScalars_isIso_μ_of_bijective (α.app U).hom (hα U) (M₁.obj U) (M₂.obj U))
  exact Functor.Monoidal.ofLaxMonoidal _

end StrongMonoidalRestrictScalars

/-! ## Project-local Mathlib supplement — the internal hom of presheaves of modules
(slice formula): the `R(T)`-module structure on `Hom(M, N)`

This section builds the FIRST primitive of the sheaf internal-hom / dual block
(blueprint `sec:tensorobj_dual_infra`, the `⊗`-inverse's missing ingredient): the
`R(T)`-module structure on the morphism abelian group `M ⟶ N` of presheaves of
modules over a base category `C` with a **terminal object** `T`, where the scalar
ring is the global ring `R(T)`.

This is exactly the module attached to each value of the slice internal hom
`ℋom(M, N)(U) := ModuleCat.of (R(U)) (M|_U ⟶ N|_U)` of
blueprint `def:presheaf_internal_hom`: over the restricted site (terminal `U`),
the section module over `U` is `Hom(M|_U, N|_U)` with its `R(U)`-action. The slice
formula is forced by contravariance of the naive pointwise rule
`U ↦ Hom_{R(U)}(M(U), N(U))`; the module of morphisms of *restricted* objects is
the covariant remedy, and its `R(U)`-module structure is the content here.

The action is `f • φ := φ ≫ globalSMul f`, where `globalSMul f : N ⟶ N` is the
"multiply by the global scalar `f ∈ R(T)`" endomorphism: at an object `Y`, with
`R(T) → R(Y)` the canonical map `termRingMap` induced by the unique `Y → T`, it is
scalar multiplication by the image of `f`. Mathlib has the fixed-ring internal hom
`ihom M N = (M ⟶ N)` (`Mathlib/Algebra/Category/ModuleCat/Monoidal/Closed.lean`) but
nothing for the varying structure sheaf at the `PresheafOfModules` level; this is the
project-local supplement. -/

namespace InternalHom

open CategoryTheory Limits

universe vC uC

variable {C : Type uC} [Category.{vC} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {T : C} (hT : IsTerminal T)

/-- **The canonical ring map `R(T) → R(Y)` from a terminal object `T`.** For each
object `Y`, the unique morphism `Y.unop → T` (terminality) induces, after `op` and
applying `R`, the ring map `R(T) → R(Y)` along which a global scalar `f ∈ R(T)` acts
on `R(Y)`-modules. Project-local: the `R(T)`-module structure on `Hom(M, N)` (the slice
internal-hom value) is defined through this map. -/
noncomputable def termRingMap (Y : Cᵒᵖ) : R.obj (Opposite.op T) ⟶ R.obj Y :=
  R.map (hT.from Y.unop).op

/-- **Naturality of `termRingMap`.** The restriction map `R(g) : R(X) → R(Y)` of `R`
along `g : X ⟶ Y` carries `termRingMap X f` to `termRingMap Y f`; equivalently the
images of a global scalar `f ∈ R(T)` are compatible with restriction. This is the
sole ingredient making `globalSMul f` a genuine morphism of presheaves of modules. -/
lemma termRingMap_naturality {X Y : Cᵒᵖ} (g : X ⟶ Y) (f) :
    (ConcreteCategory.hom ((R ⋙ forget₂ CommRingCat RingCat).map g))
        ((ConcreteCategory.hom (termRingMap hT X)) f)
      = (ConcreteCategory.hom (termRingMap hT Y)) f := by
  have h : (hT.from X.unop).op ≫ g = (hT.from Y.unop).op := by
    apply Quiver.Hom.unop_inj; apply hT.hom_ext
  change (ConcreteCategory.hom (R.map g)) ((ConcreteCategory.hom (R.map (hT.from X.unop).op)) f) = _
  rw [show termRingMap hT Y = R.map (hT.from Y.unop).op from rfl, ← h, Functor.map_comp]; rfl

/-- **Multiplication by a global scalar `f ∈ R(T)` as an endomorphism of `N`.** At an
object `Y`, it is scalar multiplication by `termRingMap Y f ∈ R(Y)` on `N(Y)`; the
naturality square commutes by `termRingMap_naturality` and the semilinearity of the
restriction maps of `N` (`PresheafOfModules.map_smul`). This is the central object: it
gives the `R(T)`-action on `Hom(M, N)` by post-composition (`homModule`). -/
noncomputable def globalSMul (N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (f : (R.obj (Opposite.op T) : Type u)) : N ⟶ N :=
  PresheafOfModules.Hom.mk
    (fun Y => ModuleCat.ofHom
      (LinearMap.lsmul (R.obj Y : Type u) (N.obj Y) ((ConcreteCategory.hom (termRingMap hT Y)) f)))
    (by
      intro X Y g; ext m
      change (LinearMap.lsmul (R.obj Y : Type u) (N.obj Y)
            ((ConcreteCategory.hom (termRingMap hT Y)) f)) ((ConcreteCategory.hom (N.map g)) m)
          = (ConcreteCategory.hom (N.map g)) ((LinearMap.lsmul (R.obj X : Type u) (N.obj X)
            ((ConcreteCategory.hom (termRingMap hT X)) f)) m)
      rw [LinearMap.lsmul_apply, LinearMap.lsmul_apply]; erw [PresheafOfModules.map_smul]
      rw [termRingMap_naturality]; rfl)

variable {N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- The section-wise action of `globalSMul f`: at `Y`, it is scalar multiplication by
`termRingMap Y f`. -/
lemma globalSMul_hom_apply (f : (R.obj (Opposite.op T) : Type u)) (Y : Cᵒᵖ) (m : N.obj Y) :
    ((globalSMul hT N f).app Y).hom m = ((ConcreteCategory.hom (termRingMap hT Y)) f) • m := rfl

/-- `globalSMul 1 = 𝟙`. -/
lemma globalSMul_one : globalSMul hT N 1 = 𝟙 N := by
  ext Y m; rw [globalSMul_hom_apply, map_one, one_smul]; rfl

/-- `globalSMul 0 = 0`. -/
lemma globalSMul_zero : globalSMul hT N 0 = 0 := by
  ext Y m; rw [globalSMul_hom_apply, map_zero, zero_smul]; rfl

/-- `globalSMul` is additive in the scalar. -/
lemma globalSMul_add (f g : (R.obj (Opposite.op T) : Type u)) :
    globalSMul hT N (f + g) = globalSMul hT N f + globalSMul hT N g := by
  ext Y m; rw [add_app, globalSMul_hom_apply, _root_.map_add, add_smul]; rfl

/-- `globalSMul` turns ring multiplication into composition (the scalar endomorphisms
commute, so the order is immaterial). -/
lemma globalSMul_mul (f g : (R.obj (Opposite.op T) : Type u)) :
    globalSMul hT N (f * g) = globalSMul hT N g ≫ globalSMul hT N f := by
  ext Y m; rw [comp_app, globalSMul_hom_apply, map_mul, mul_smul, ModuleCat.hom_comp,
    LinearMap.comp_apply, globalSMul_hom_apply, globalSMul_hom_apply]

/-- **The `R(T)`-module structure on `Hom(M, N)` of presheaves of modules over a base
category `C` with a terminal object `T`.** The action `f • φ := φ ≫ globalSMul f` scales
a morphism by post-composing with multiplication by the global scalar `f ∈ R(T)`; the
module axioms reduce to the `globalSMul_{one,zero,add,mul}` ring-homomorphism facts and
the bilinearity of composition (`Preadditive`). This is the module carried by each value
of the slice internal hom `ℋom(M, N)(U)` of blueprint `def:presheaf_internal_hom`
(take `C =` the restricted site over `U`, with terminal `U`, so `R(T) = R(U)`).
Project-local: Mathlib has the fixed-ring internal hom but no `PresheafOfModules`-level
internal hom for the varying structure sheaf. -/
@[implicit_reducible]
noncomputable def homModule (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    Module (R.obj (Opposite.op T) : Type u) (M ⟶ N) where
  smul f φ := φ ≫ globalSMul hT N f
  one_smul φ := by change φ ≫ globalSMul hT N 1 = φ; rw [globalSMul_one, Category.comp_id]
  mul_smul f g φ := by
    change φ ≫ globalSMul hT N (f * g) = (φ ≫ globalSMul hT N g) ≫ globalSMul hT N f
    rw [globalSMul_mul, Category.assoc]
  smul_zero f := by change (0 : M ⟶ N) ≫ globalSMul hT N f = 0; rw [Limits.zero_comp]
  zero_smul φ := by change φ ≫ globalSMul hT N 0 = 0; rw [globalSMul_zero, Limits.comp_zero]
  smul_add f φ ψ := by
    change (φ + ψ) ≫ globalSMul hT N f = φ ≫ globalSMul hT N f + ψ ≫ globalSMul hT N f
    rw [Preadditive.add_comp]
  add_smul f g φ := by
    change φ ≫ globalSMul hT N (f + g) = φ ≫ globalSMul hT N f + φ ≫ globalSMul hT N g
    rw [globalSMul_add, Preadditive.comp_add]

/-! ### The slice value at an object `U` via the over-category `Over U`

The slice internal hom `ℋom(M, N)(U) := ModuleCat.of (R(U)) (M|_U ⟶ N|_U)` of
blueprint `def:presheaf_internal_hom` is realized object-by-object here. The
restriction `M|_U` is `PresheafOfModules.pushforward₀` along the over-category
projection `Over.forget U : Over U ⥤ C`; the over-category has terminal object
`Over.mk (𝟙 U)` (`Over.mkIdTerminal`), at which the restricted ring is `R(U)`
(by `rfl`), so the `R(U)`-module structure on `M|_U ⟶ N|_U` is exactly `homModule`
applied to that terminal. -/

/-- **Restriction of a presheaf of modules to the over-category `Over U`.** This is
the `M|_U` of the slice internal-hom formula: `PresheafOfModules.pushforward₀` along
the over-category projection `Over.forget U`. The new base presheaf of rings is
`(Over.forget U).op ⋙ R`, whose value at the terminal `Over.mk (𝟙 U)` is `R(U)`. -/
noncomputable def restr (U : C)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u} (((Over.forget U).op ⋙ R) ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.pushforward₀ (Over.forget U) (R ⋙ forget₂ CommRingCat RingCat)).obj M

/-- **The slice internal-hom value at `U`: `Hom(M|_U, N|_U)` as an `R(U)`-module.**
This is the `R(U)`-module underlying `ℋom(M, N)(U)` of blueprint
`def:presheaf_internal_hom`: the morphism group of the over-category restrictions
`M|_U ⟶ N|_U`, equipped with the `homModule` action for the terminal object
`Over.mk (𝟙 U)` of `Over U`. The full presheaf `internalHom` (the assembly of these
values over the restriction maps `V ⟶ U`) was assembled iter-220 (`internalHom`). -/
@[implicit_reducible]
noncomputable def internalHomObjModule (U : C)
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    Module (R.obj (Opposite.op U) : Type u) (restr U M ⟶ restr U N) :=
  homModule (R := (Over.forget U).op ⋙ R) (T := Over.mk (𝟙 U)) Over.mkIdTerminal
    (restr U M) (restr U N)

/-- **The restriction map of the presheaf internal hom.** For a morphism `g : V ⟶ U`
of `C`, restricting a morphism `φ : M|_U ⟶ N|_U` of restricted presheaves of modules
along `Over.map g : Over V ⥤ Over U` yields a morphism `M|_V ⟶ N|_V`. Realised as
`(pushforward₀ (Over.map g) …).map φ`; the target base ring presheaf
`(Over.map g).op ⋙ (Over.forget U).op ⋙ R` is definitionally `(Over.forget V).op ⋙ R`,
so the result has the expected type `restr V M ⟶ restr V N`. This is the
further-restriction map `φ ↦ φ|_V` of blueprint `lem:presheaf_internal_hom_restriction`. -/
noncomputable def restrictionMap {U V : C} (g : V ⟶ U)
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : restr U M ⟶ restr U N) : restr V M ⟶ restr V N :=
  (PresheafOfModules.pushforward₀ (Over.map g)
    ((Over.forget U).op ⋙ (R ⋙ forget₂ CommRingCat RingCat))).map φ

/-- **`restrictionMap` is additive.** Part of the additivity assertion of blueprint
`lem:presheaf_internal_hom_restriction`. -/
lemma restrictionMap_add {U V : C} (g : V ⟶ U)
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ ψ : restr U M ⟶ restr U N) :
    restrictionMap g (φ + ψ) = restrictionMap g φ + restrictionMap g ψ := by
  ext1 X; rfl

/-- **`restrictionMap` preserves zero.** -/
lemma restrictionMap_zero {U V : C} (g : V ⟶ U)
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} :
    restrictionMap g (0 : restr U M ⟶ restr U N) = 0 := by
  ext1 X; rfl

/-- Helper: the component of a morphism of presheaves of modules at two *equal*
objects agrees up to `HEq`. Proven by `subst`. Used to discharge the
pseudofunctoriality coherence of `restrictionMap` (`Over.map` is only functorial in
its argument up to `Over.mapId_eq` / `Over.mapComp_eq`). -/
private lemma hom_app_heq {B : Cᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{u} B}
    (φ : M ⟶ N) {X Y : Cᵒᵖ} (h : X = Y) : HEq (φ.app X) (φ.app Y) := by
  subst h; rfl

/-- **Functoriality of `restrictionMap`: identity.** -/
lemma restrictionMap_id {U : C}
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : restr U M ⟶ restr U N) :
    restrictionMap (𝟙 U) φ = φ := by
  ext1 X
  exact eq_of_heq (hom_app_heq φ (by rw [Over.mapId_eq]; rfl))

/-- **Functoriality of `restrictionMap`: composition.** For `g : V ⟶ U`, `h : W ⟶ V`,
restricting along `h ≫ g` is restricting along `g` then along `h`. -/
lemma restrictionMap_comp {U V W : C} (g : V ⟶ U) (h : W ⟶ V)
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : restr U M ⟶ restr U N) :
    restrictionMap (h ≫ g) φ = restrictionMap h (restrictionMap g φ) := by
  ext1 X
  exact eq_of_heq (hom_app_heq φ (by rw [Over.mapComp_eq]; rfl))

/-- **`restrictionMap` respects composition of morphisms** (functoriality of
`pushforward₀.map`). -/
lemma restrictionMap_comp_hom {U V : C} (g : V ⟶ U)
    {M N P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : restr U M ⟶ restr U N) (ψ : restr U N ⟶ restr U P) :
    restrictionMap g (φ ≫ ψ) = restrictionMap g φ ≫ restrictionMap g ψ :=
  Functor.map_comp _ _ _

/-- **Restriction commutes with the global-scalar endomorphism.** For `g : V ⟶ U`
and a global scalar `r ∈ R(U)`, restricting the multiplication-by-`r` endomorphism of
`N|_U` yields the multiplication-by-`R(g)(r)` endomorphism of `N|_V`. This is the heart
of the semilinearity of `restrictionMap` (blueprint `lem:presheaf_internal_hom_restriction`):
both sides act on each section by scalar multiplication, and the scalars agree by
functoriality of `R` (`termRingMap_naturality`). -/
lemma restrictionMap_globalSMul {U V : C} (g : V ⟶ U)
    {N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (r : (R.obj (Opposite.op U) : Type u)) :
    restrictionMap g (globalSMul (R := (Over.forget U).op ⋙ R) (T := Over.mk (𝟙 U))
        Over.mkIdTerminal (restr U N) r)
      = globalSMul (R := (Over.forget V).op ⋙ R) (T := Over.mk (𝟙 V))
        Over.mkIdTerminal (restr V N) ((ConcreteCategory.hom (R.map g.op)) r) := by
  ext1 Y
  ext m
  rw [globalSMul_hom_apply]
  erw [globalSMul_hom_apply]
  congr 1
  simp only [termRingMap, Functor.comp_map]
  have hmor : (Over.forget U).op.map
        (Over.mkIdTerminal.from ((Over.map g).op.obj Y).unop).op
      = g.op ≫ (Over.forget V).op.map (Over.mkIdTerminal.from Y.unop).op := by
    apply Quiver.Hom.unop_inj
    change Over.Hom.left (Over.mkIdTerminal.from ((Over.map g).obj Y.unop))
      = Over.Hom.left (Over.mkIdTerminal.from Y.unop) ≫ g
    have e1 : Over.Hom.left (Over.mkIdTerminal.from ((Over.map g).obj Y.unop))
        = ((Over.map g).obj Y.unop).hom := by simp
    have e2 : Over.Hom.left (Over.mkIdTerminal.from Y.unop) = Y.unop.hom := by simp
    rw [e1, e2]
    exact Over.map_obj_hom
  rw [hmor]
  erw [← CommRingCat.comp_apply, ← R.map_comp]
  rfl

/-- **`restrictionMap` packaged as an additive group homomorphism** on the morphism
groups, using `restrictionMap_zero` and `restrictionMap_add`. This is the value of the
underlying `Ab`-presheaf morphism of `internalHom`. -/
noncomputable def restrictionMapAddHom {U V : C} (g : V ⟶ U)
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (restr U M ⟶ restr U N) →+ (restr V M ⟶ restr V N) where
  toFun := restrictionMap g
  map_zero' := restrictionMap_zero g
  map_add' := restrictionMap_add g

/-- **The underlying `Ab`-valued presheaf of `internalHom M N`**: `U ↦ (M|_U ⟶ N|_U)`
with the further-restriction maps. Functoriality is `restrictionMap_id` /
`restrictionMap_comp`. This is piece (a)+(b)+(c) of blueprint `def:presheaf_internal_hom`
at the abelian-group level; the `R(U)`-module refinement is added by `internalHom`. -/
noncomputable def internalHomPresheaf
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max u uC vC} where
  obj X := AddCommGrpCat.of (restr X.unop M ⟶ restr X.unop N)
  map {X Y} f := AddCommGrpCat.ofHom (restrictionMapAddHom f.unop M N)
  map_id X := by
    apply AddCommGrpCat.hom_ext
    refine AddMonoidHom.ext fun φ => ?_
    exact restrictionMap_id φ
  map_comp {X Y Z} f f' := by
    apply AddCommGrpCat.hom_ext
    refine AddMonoidHom.ext fun φ => ?_
    exact restrictionMap_comp f.unop f'.unop φ

/-- **Semilinearity of `restrictionMap`** in the form consumed by
`PresheafOfModules.ofPresheaf`: for `f : X ⟶ Y` in `Cᵒᵖ`, a global scalar
`r ∈ R(X)` and `m : M|_{X} ⟶ N|_{X}`, `restrictionMap f.unop (r • m) =
R(f)(r) • restrictionMap f.unop m`, where the `•`'s are the slice-value module
actions (`internalHomObjModule`). This is `lem:presheaf_internal_hom_restriction`'s
compatibility datum; it follows from `restrictionMap_comp_hom` and
`restrictionMap_globalSMul`. -/
lemma restrictionMap_smul {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (r : (R.obj X : Type u)) (m : restr X.unop M ⟶ restr X.unop N) :
    restrictionMap f.unop
        (letI := internalHomObjModule X.unop M N; r • m)
      = (letI := internalHomObjModule Y.unop M N;
          (ConcreteCategory.hom (R.map f)) r • restrictionMap f.unop m) := by
  change restrictionMap f.unop (m ≫ globalSMul Over.mkIdTerminal (restr X.unop N) r)
    = restrictionMap f.unop m
        ≫ globalSMul Over.mkIdTerminal (restr Y.unop N) ((ConcreteCategory.hom (R.map f)) r)
  rw [restrictionMap_comp_hom, restrictionMap_globalSMul, Quiver.Hom.op_unop]

end InternalHom

/-! ### Assembly of the presheaf internal hom over a single-universe base

`PresheafOfModules.ofPresheaf` ties the underlying `Ab`-presheaf to the ground ring
presheaf `R`'s universe (`Type u`), but for a general base category the morphism groups
`M|_U ⟶ N|_U` live in `Type (max u uC vC)`. The two coincide exactly when the base
category is single-universe (`Category.{u, u}`), which is the case for the topological
site `Opens X` underlying the structure sheaf of a scheme. The full presheaf internal
hom is therefore assembled in this specialised universe context. -/

namespace InternalHom

section Assembly

variable {D : Type u} [Category.{u, u} D] {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}}

/-- **The presheaf internal hom `ℋom(M, N)`** (blueprint `def:presheaf_internal_hom`):
the presheaf of `R`-modules assembled from the slice value modules
`internalHomObjModule` (a), the further-restriction maps `internalHomPresheaf` (b)(c),
and the semilinearity datum `restrictionMap_smul`, via `PresheafOfModules.ofPresheaf`.
Stated over a single-universe base (e.g. the topological site `Opens X`); see the
section note for the universe constraint. -/
noncomputable def internalHom
    (M N : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat) :=
  @PresheafOfModules.ofPresheaf D _ (R₀ ⋙ forget₂ CommRingCat RingCat)
    (internalHomPresheaf M N)
    (fun X => internalHomObjModule X.unop M N)
    (fun {_ _} f r m => restrictionMap_smul f M N r m)

end Assembly

end InternalHom

namespace InternalHom

open CategoryTheory Limits Opposite

universe vC uC

variable {C : Type uC} [Category.{vC} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {T : C} (hT : IsTerminal T)

/-- **`termRingMap` at the terminal object itself is the identity.** The unique
`T → T` is the identity, so the induced ring map `R(T) → R(T)` is `id`. This is the
fact that the global-scalar action evaluated at the terminal section is the scalar
itself, used to prove the evaluation map of `internalHomEval` is `R(U)`-bilinear. -/
lemma termRingMap_terminal (f : (R.obj (op T) : Type u)) :
    (ConcreteCategory.hom (termRingMap hT (op T))) f = f := by
  have hid : hT.from T = 𝟙 T := hT.hom_ext _ _
  simp only [termRingMap, unop_op, hid, op_id, R.map_id]
  rfl

end InternalHom

/-! ### The presheaf dual `M^∨ := ℋom(M, R)`

The presheaf dual is the internal hom into the monoidal unit (the structure presheaf
viewed as a module over itself), assembled in the same single-universe context as
`InternalHom.internalHom`. Blueprint `def:presheaf_dual`. -/

section Dual

open InternalHom Opposite

variable {D : Type u} [Category.{u, u} D] {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}}

/-- **The presheaf dual `M^∨ := ℋom(M, R)`** (blueprint `def:presheaf_dual`): the
internal hom into the monoidal unit `𝟙_` (the structure presheaf `R` viewed as a module
over itself / the regular representation). The value
`M^∨(U) = ModuleCat.of (R(U)) (M|_U ⟶ R|_U)` is the `R(U)`-module of `R|_U`-linear
functionals on `M|_U`, the presheaf-of-modules analogue of the fixed-ring linear dual
`Module.Dual R M = (M ⟶ R)` that serves as the `⊗`-inverse of an invertible module.
Project-local: Mathlib has the fixed-ring dual but no `PresheafOfModules`-level dual for
the varying structure sheaf. -/
noncomputable def dual
    (M : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat) :=
  InternalHom.internalHom M (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))

/-- The evaluation functional `φ ↦ (s ↦ φ(s))` of a dual section `φ`, cast to an
`R₀.obj X`-linear map `M(X) → R(X)` (the over-category ring at the terminal section is
definitionally `R₀.obj X`). Helper for `internalHomEvalApp`. -/
noncomputable def evalLin
    (M : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) (X : Dᵒᵖ)
    (φ : (dual M).obj X) :
    (M.obj X : Type u) →ₗ[(R₀.obj X : Type u)] (R₀.obj X : Type u) :=
  ((φ : restr X.unop M ⟶ restr X.unop
      (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))).app
        (op (Over.mk (𝟙 X.unop)))).hom

/-- `evalLin` is additive in the dual section `φ` (the dual-section addition is the
categorical `Hom`-addition, on which `app`/`hom`-application is definitionally additive). -/
lemma evalLin_add
    (M : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) (X : Dᵒᵖ)
    (φ φ' : (dual M).obj X) :
    evalLin M X (φ + φ') = evalLin M X φ + evalLin M X φ' :=
  LinearMap.ext fun _ => rfl

/-- `evalLin` is `R₀.obj X`-linear in the dual section `φ`, using the `homModule`
action `c • φ = φ ≫ globalSMul c` and `termRingMap_terminal`. -/
lemma evalLin_smul
    (M : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) (X : Dᵒᵖ)
    (c : (R₀.obj X : Type u)) (φ : (dual M).obj X) :
    evalLin M X (c • φ) = c • evalLin M X φ := by
  refine LinearMap.ext fun s => ?_
  rw [LinearMap.smul_apply]
  change ((ConcreteCategory.hom
      (termRingMap (R := (Over.forget X.unop).op ⋙ R₀) Over.mkIdTerminal
        (op (Over.mk (𝟙 X.unop)))) c)
    • ((φ : restr X.unop M ⟶ restr X.unop
        (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))).app
          (op (Over.mk (𝟙 X.unop)))).hom s : (R₀.obj X : Type u))
    = c • evalLin M X φ s
  rw [termRingMap_terminal]
  rfl

/-- **The open-by-open evaluation/contraction map** underlying `internalHomEval`. At an
object `X` it is the `R(X)`-bilinear contraction
`(M(X)) ⊗_{R(X)} (M|_X ⟶ R|_X) → R(X)`, `s ⊗ φ ↦ φ(s)`, where `φ(s)` evaluates the
functional `φ` (a morphism of restricted presheaves of modules over `Over X.unop`) at its
terminal section, applied to `s`. Bilinearity over `R(X)`: linearity in `s` is linearity
of `evalLin`; linearity in `φ` is `evalLin_add` / `evalLin_smul`. The codomain is cast to
`R₀.obj X` (defeq to the unit value `(𝟙_).obj X`) to pin the `CommRingCat` module. -/
noncomputable def internalHomEvalApp
    (M : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) (X : Dᵒᵖ) :
    (PresheafOfModules.Monoidal.tensorObj M (dual M)).obj X ⟶
      (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))).obj X :=
  show ModuleCat.of (R₀.obj X : Type u)
        (TensorProduct (R₀.obj X : Type u) (M.obj X) ((dual M).obj X))
      ⟶ ModuleCat.of (R₀.obj X : Type u) (R₀.obj X : Type u) from
  ModuleCat.ofHom
    (TensorProduct.lift
      (LinearMap.mk₂ (R₀.obj X : Type u)
        (fun (s : M.obj X) (φ : (dual M).obj X) => evalLin M X φ s)
        (fun s s' φ => _root_.map_add (evalLin M X φ) s s')
        (fun c s φ => _root_.map_smul (evalLin M X φ) c s)
        (fun s φ φ' => by
          change evalLin M X (φ + φ') s = evalLin M X φ s + evalLin M X φ' s
          rw [evalLin_add, LinearMap.add_apply])
        (fun c s φ => by
          change evalLin M X (c • φ) s = c • evalLin M X φ s
          rw [evalLin_smul, LinearMap.smul_apply])))

/-- Value of `internalHomEvalApp` on a simple tensor: the contraction `s ⊗ φ ↦ φ(s)`.
The eval value is kept at its NATURAL over-ring type `R₀.obj X` (not ascribed to the
unit value `(𝟙_).obj X`). Used to reduce the naturality of `internalHomEval`. -/
@[simp] lemma internalHomEvalApp_tmul
    (M : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) (X : Dᵒᵖ)
    (s : (M.obj X : Type u)) (φ : ((dual M).obj X : Type u)) :
    (internalHomEvalApp M X).hom (s ⊗ₜ[(R₀.obj X : Type u)] φ) = evalLin M X φ s :=
  rfl

/-- **Further-restriction of `M|_U` along the canonical `Over.homMk f.unop` equals `M.map f`.**
For `f : X ⟶ Y` in `Dᵒᵖ`, restricting `M|_{X.unop}` (the `pushforward₀` of `M` along
`Over.forget X.unop`) along the over-category morphism `Over.homMk f.unop : Over.mk f.unop ⟶
Over.mk (𝟙 X.unop)` is, definitionally, `M.map f`. Extracted as its own lemma so the heavy
`whnf` defeq runs once within its own heartbeat budget (the `internalHomEval` naturality proof
would otherwise time out). Used to rewrite the `naturality_apply` of a dual section into the
shape `ev_M`'s naturality needs. -/
private lemma restr_map_homMk
    (N : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) {X Y : Dᵒᵖ} (f : X ⟶ Y) :
    (restr X.unop N).map
        (Over.homMk f.unop (Category.comp_id _) : Over.mk f.unop ⟶ Over.mk (𝟙 X.unop)).op
      = N.map f := rfl

/-- **The evaluation morphism `ev_M : M ⊗_R M^∨ ⟶ R`** (blueprint `lem:internal_hom_eval`):
the natural morphism `M ⊗_R M^∨ ⟶ R`, sending `s ⊗ φ` to `φ(s)`. Its components are
`internalHomEvalApp`; naturality reduces to naturality of a dual section after rewriting restriction
along the canonical morphism with `restr_map_homMk`. -/
noncomputable def internalHomEval
    (M : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.Monoidal.tensorObj M (dual M) ⟶
      𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.Hom.mk (fun X => internalHomEvalApp M X) (by
    intro X Y f
    refine ModuleCat.MonoidalCategory.tensor_ext (fun s φ => ?_)
    -- Break the two composites on `s ⊗ₜ φ`; the tensor and evaluation lemmas then reduce the goal.
    -- (handled by `erw`'s defeq matching through `restrictScalars`):
    --   LHS ⇒ `evalLin M Y ((dual M).map f φ) ((M.map f) s)`.
    erw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      internalHomEvalApp_tmul, internalHomEvalApp_tmul]
    simp only []
    -- Reduce the RHS `(𝟙_).map f`-image of `(internalHomEvalApp M X)(s ⊗ₜ φ)` to the unit ring
    -- map applied to `evalLin M X φ s` (defeq, since `internalHomEvalApp_tmul` is `rfl`).
    change M.evalLin Y ((M.dual.map f) φ) ((M.map f) s)
      = ((𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))).map f).hom
          (M.evalLin X φ s)
    -- Step 4: naturality of the dual section `φ` (a morphism over `Over X.unop`) along the
    -- canonical `(Over.homMk f.unop).op : (terminal) ⟶ (op (Over.mk f.unop))`, applied to `s`.
    have key := PresheafOfModules.naturality_apply
      (φ : restr X.unop M ⟶ restr X.unop
        (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))))
      (Over.homMk f.unop (Category.comp_id _) : Over.mk f.unop ⟶ Over.mk (𝟙 X.unop)).op s
    -- Both further-restrictions `(restr X.unop _).map (Over.homMk f.unop).op` are definitionally
    -- the base maps `M.map f` / `(𝟙_).map f` (`restr_map_homMk`).
    rw [restr_map_homMk, restr_map_homMk] at key
    -- Step 5 (`hdt`): identify the dual section's terminal value with `φ` evaluated at
    -- `op (Over.mk f.unop)` (the over-objects `Over.mk (𝟙 Y.unop ≫ f.unop)` and `Over.mk f.unop`
    -- are equal via `Category.id_comp`, with equal source `Y.unop`, so `hom_app_heq`+`eq_of_heq`).
    have hdt : M.evalLin Y ((M.dual.map f) φ) = (φ.app (op (Over.mk f.unop))).hom :=
      congrArg ModuleCat.Hom.hom
        (eq_of_heq (hom_app_heq
          (φ : restr X.unop M ⟶ restr X.unop
            (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))))
          (congrArg op (congrArg Over.mk (Category.id_comp f.unop)))))
    -- Step 6: chain `hdt` (applied to `(M.map f) s`) into `key`.
    exact (DFunLike.congr_fun hdt _).trans key
    )

/-- **Precomposition `R(U)`-linear equivalence on dual sections induced by an iso `e : M ≅ M'`.**
At an object `U`, sends a dual section `φ : M'|_U ⟶ R|_U` to `(e.hom|_U) ≫ φ : M|_U ⟶ R|_U`, with
inverse `ψ ↦ (e.inv|_U) ≫ ψ`. The `R(U)`-action on dual sections is post-composition with
`globalSMul` (the `homModule` action), which commutes with this pre-composition, so the map is
`R(U)`-linear. This is the section-level core of `dualIsoOfIso` (the dual is contravariantly
functorial in isomorphisms). -/
noncomputable def dualPrecompEquiv
    {M M' : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)} (e : M ≅ M') (U : D) :
    letI := internalHomObjModule U M'
      (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
    letI := internalHomObjModule U M
      (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
    (restr U M' ⟶ restr U (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))))
      ≃ₗ[(R₀.obj (op U) : Type u)]
      (restr U M ⟶ restr U (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))) := by
  letI := internalHomObjModule U M'
    (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
  letI := internalHomObjModule U M
    (𝟙_ (PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
  exact
    { toFun := fun φ =>
        (PresheafOfModules.pushforward₀ (Over.forget U)
          (R₀ ⋙ forget₂ CommRingCat RingCat)).map e.hom ≫ φ
      invFun := fun ψ =>
        (PresheafOfModules.pushforward₀ (Over.forget U)
          (R₀ ⋙ forget₂ CommRingCat RingCat)).map e.inv ≫ ψ
      map_add' := fun φ ψ => Preadditive.comp_add _ _ _ _ φ ψ
      map_smul' := fun r φ => by
        simp only [RingHom.id_apply]
        exact (Category.assoc _ _ _).symm
      left_inv := fun φ => by
        change (PresheafOfModules.pushforward₀ (Over.forget U)
            (R₀ ⋙ forget₂ CommRingCat RingCat)).map e.inv
          ≫ ((PresheafOfModules.pushforward₀ (Over.forget U)
            (R₀ ⋙ forget₂ CommRingCat RingCat)).map e.hom ≫ φ) = φ
        rw [← Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
          Category.id_comp]
      right_inv := fun ψ => by
        change (PresheafOfModules.pushforward₀ (Over.forget U)
            (R₀ ⋙ forget₂ CommRingCat RingCat)).map e.hom
          ≫ ((PresheafOfModules.pushforward₀ (Over.forget U)
            (R₀ ⋙ forget₂ CommRingCat RingCat)).map e.inv ≫ ψ) = ψ
        rw [← Category.assoc, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id,
          Category.id_comp] }

/-- **The presheaf dual is contravariantly functorial in isomorphisms.** An isomorphism
`e : M ≅ M'` of presheaves of modules induces an isomorphism `dual M' ≅ dual M` of their
duals (`dual N = internalHom N (𝟙_)`), assembled sectionwise from the precomposition
equivalences `dualPrecompEquiv`. This is the `\leanok`-ready ingredient that transports a
local trivialisation `L|_U ≅ 𝒪_U` to `dual (L|_U) ≅ dual 𝒪_U` in the assembly of
`dual_isLocallyTrivial`. -/
noncomputable def dualIsoOfIso
    {M M' : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)} (e : M ≅ M') :
    dual M' ≅ dual M :=
  PresheafOfModules.isoMk
    (fun U => (dualPrecompEquiv e U.unop).toModuleIso)

end Dual

end PresheafOfModules
