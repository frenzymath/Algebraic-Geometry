/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Std.Tactic.BVDecide.LRAT.Internal.Clause

/-!
# Stalk of a tensor product of presheaves of modules (ingredient d.2)

This file constructs the *comparison map* underlying the varying-ring stalk--tensor
commutation isomorphism

  `(A ⊗ᵖ B).stalk x ≅ A.stalk x ⊗_{R.stalk x} B.stalk x`

for presheaves of modules over the structure presheaf `R` of a scheme — the single
genuinely Mathlib-absent ingredient ("d.2") on which the unconditional associator of
the relative-Picard tensor substrate rests.

This iteration builds the forward additive comparison map `stalkTensorDesc` and its
germ characterisation (the colimit-descent of the sectionwise base-change maps). The
full isomorphism `PresheafOfModules.stalkTensorIso` (blueprint `lem:stalk_tensor_commutation`)
additionally requires the `R.stalk x`-linear packaging of this map, the reverse map, and
their mutual inversion on germs — see the handoff in `task_results`.

The construction proceeds bottom-up:

* `PresheafOfModules.stalkTensorBilin` — for a neighbourhood `U ∋ x`, the `R(U)`-balanced
  bilinear map `A(U) × B(U) → A_x ⊗_{R_x} B_x`, `(a,b) ↦ germ a ⊗ germ b`.
* `PresheafOfModules.stalkTensorDescU` — its descent through `TensorProduct.liftAddHom`
  to a map `(A ⊗ᵖ B)(U) = A(U) ⊗_{R(U)} B(U) → A_x ⊗_{R_x} B_x`.
* `PresheafOfModules.stalkTensorDesc` — the colimit descent to the comparison map
  `(A ⊗ᵖ B).stalk x → A_x ⊗_{R_x} B_x`.

Source: [Stacks Project], Modules on Ringed Spaces, Lemma `lemma-stalk-tensor-product`.

Blueprint: `chapters/Picard_TensorObjSubstrate.tex`, §`sec:tensorobj_stalk_tensor`
(`lem:stalk_tensor_commutation`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory TopologicalSpace TopCat.Presheaf Opposite

namespace PresheafOfModules

open PresheafOfModules.Monoidal

/-! ## Project-local Mathlib supplement — stalk of a tensor product (d.2) -/

section StalkTensor

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (A B : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (x : X)

local notation3 "Tgt" =>
  TensorProduct ↑(R.stalk x) ↑(TopCat.Presheaf.stalk A.presheaf x)
    ↑(TopCat.Presheaf.stalk B.presheaf x)

/-- **The `R(U)`-balanced bilinear comparison map.** For a neighbourhood `U ∋ x`, the
bilinear (additive-monoid-hom) map `A(U) × B(U) → A_x ⊗_{R_x} B_x` sending
`(a, b)` to `germ a ⊗ germ b`. Project-local: the building block of the d.2 stalk--tensor
comparison; Mathlib has no varying-ring stalk--tensor commutation. -/
noncomputable def stalkTensorBilin (U : Opens X) (hx : x ∈ U) :
    (↑(A.obj (op U)) : Type u) →+ (↑(B.obj (op U)) : Type u) →+ Tgt where
  toFun m :=
    ((TensorProduct.mk ↑(R.stalk x) _ _
      ((ConcreteCategory.hom (TopCat.Presheaf.germ A.presheaf U x hx)) m)).toAddMonoidHom).comp
      (ConcreteCategory.hom (TopCat.Presheaf.germ B.presheaf U x hx))
  map_zero' := by ext n; simp
  map_add' m m' := by ext n; simp

/-- The defining balancing identity making `stalkTensorBilin` descend through the
relative tensor product `A(U) ⊗_{R(U)} B(U)`: `(r • a) ⊗ b ↦ a ⊗ (r • b)`. -/
lemma stalkTensorBilin_balanced (U : Opens X) (hx : x ∈ U) (r : ↑(R.obj (op U)))
    (m : ↑(A.obj (op U))) (n : ↑(B.obj (op U))) :
    (stalkTensorBilin A B x U hx (r • m)) n = (stalkTensorBilin A B x U hx m) (r • n) := by
  simp only [stalkTensorBilin, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_comp,
    LinearMap.toAddMonoidHom_coe, Function.comp_apply, TensorProduct.mk_apply]
  rw [PresheafOfModules.germ_smul A x U hx]
  erw [PresheafOfModules.germ_smul B x U hx]
  exact TensorProduct.smul_tmul _ _ _

/-- **The per-neighbourhood descended comparison map** `(A ⊗ᵖ B)(U) → A_x ⊗_{R_x} B_x`,
obtained from `stalkTensorBilin` via `TensorProduct.liftAddHom`. The source object is
`(A ⊗ᵖ B).presheaf.obj (op U)`, definitionally `A(U) ⊗_{R(U)} B(U)`. -/
noncomputable def stalkTensorDescU (U : Opens X) (hx : x ∈ U) :
    (Monoidal.tensorObj A B).presheaf.obj (op U) ⟶ AddCommGrpCat.of Tgt :=
  AddCommGrpCat.ofHom
    (TensorProduct.liftAddHom (stalkTensorBilin A B x U hx) (stalkTensorBilin_balanced A B x U hx))

@[simp] lemma stalkTensorDescU_tmul (U : Opens X) (hx : x ∈ U)
    (a : ↑(A.obj (op U))) (b : ↑(B.obj (op U))) :
    (stalkTensorDescU A B x U hx) (a ⊗ₜ[R.obj (op U)] b)
      = (ConcreteCategory.hom (TopCat.Presheaf.germ A.presheaf U x hx)) a ⊗ₜ[↑(R.stalk x)]
        (ConcreteCategory.hom (TopCat.Presheaf.germ B.presheaf U x hx)) b := by
  change (TensorProduct.liftAddHom (stalkTensorBilin A B x U hx)
    (stalkTensorBilin_balanced A B x U hx)) (a ⊗ₜ[R.obj (op U)] b) = _
  rw [TensorProduct.liftAddHom_tmul]
  rfl

/-- **Scalar compatibility of the per-neighbourhood descent.** For `r : R(U)` and a
section `z` of `A ⊗ᵖ B` over `U`, the descent `stalkTensorDescU` carries the `R(U)`-scalar
action over to the `R.stalk x`-action by the germ of `r`. This is stage (iii)'s
section-level core; the carrier-duality between the `CommRingCat` scalar `r : R(U)` and the
`RingCat`-carrier module structure on `A(U) ⊗ B(U)` is absorbed by `germ_smul`/`smul_tmul'`. -/
lemma stalkTensorDescU_smul (U : Opens X) (hx : x ∈ U) (r : ↑(R.obj (op U)))
    (z : ↑((Monoidal.tensorObj A B).obj (op U))) :
    (stalkTensorDescU A B x U hx) (r • z)
      = (ConcreteCategory.hom (TopCat.Presheaf.germ R U x hx)) r •
          (stalkTensorDescU A B x U hx) z := by
  -- The section tensor `A(U) ⊗ B(U)` is a module over the `RingCat` carrier
  -- `S := (R ⋙ forget₂).obj (op U)`, which is defeq to the `CommRingCat` carrier `R(U)`.
  -- We pin `smul_tmul'`/`smul_add`/`smul_zero` to that ring so the scalar `r` slots in.
  induction z using TensorProduct.induction_on with
  | zero =>
      simp only [presheaf_obj_coe]
      exact map_zero _
  | tmul a b =>
      erw [stalkTensorDescU_tmul, stalkTensorDescU_tmul, PresheafOfModules.germ_smul A x U hx]
      exact (TensorProduct.smul_tmul' _ _ _).symm
  | add p q hp hq =>
      erw [smul_add]
      refine (map_add _ _ _).trans ?_
      rw [hp, hq, ← smul_add]
      exact congrArg _ (map_add _ p q).symm

/-- **The d.2 comparison map** `(A ⊗ᵖ B).stalk x → A_x ⊗_{R_x} B_x`, obtained by descending
the per-neighbourhood maps `stalkTensorDescU` through the colimit defining the stalk. -/
noncomputable def stalkTensorDesc :
    TopCat.Presheaf.stalk (Monoidal.tensorObj A B).presheaf x ⟶ AddCommGrpCat.of Tgt :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ (Monoidal.tensorObj A B).presheaf)
    ⟨AddCommGrpCat.of Tgt,
      fun U => stalkTensorDescU A B x (unop U).1 (unop U).2,
      by
        intro U V i
        apply AddCommGrpCat.hom_ext
        ext z
        induction z using TensorProduct.induction_on with
        | zero => exact (AddMonoidHom.map_zero _).trans (AddMonoidHom.map_zero _).symm
        | tmul a b =>
            simp only [CategoryTheory.comp_apply, Functor.const_obj_map]
            erw [tensorObj_map_tmul, stalkTensorDescU_tmul, stalkTensorDescU_tmul]
            erw [germ_res_apply, germ_res_apply]
            rfl
        | add p q hp hq =>
            exact (AddMonoidHom.map_add _ p q).trans
              ((congrArg₂ HAdd.hAdd hp hq).trans (AddMonoidHom.map_add _ p q).symm)⟩

/-- The comparison map `stalkTensorDesc` factors the per-neighbourhood map
`stalkTensorDescU` through the germ, by the colimit universal property. -/
@[reassoc]
lemma germ_stalkTensorDesc (U : Opens X) (hx : x ∈ U) :
    TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf U x hx ≫ stalkTensorDesc A B x
      = stalkTensorDescU A B x U hx :=
  colimit.ι_desc _ (op (⟨U, hx⟩ : OpenNhds x))

/-- **Germ characterisation of the d.2 comparison map** on a simple tensor: the germ of
`a ⊗ b` over `U` maps to `germ a ⊗ germ b`. -/
@[simp]
lemma stalkTensorDesc_germ_tmul (U : Opens X) (hx : x ∈ U)
    (a : ↑(A.obj (op U))) (b : ↑(B.obj (op U))) :
    (stalkTensorDesc A B x)
        ((ConcreteCategory.hom (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf U x hx))
          (a ⊗ₜ[R.obj (op U)] b))
      = (ConcreteCategory.hom (TopCat.Presheaf.germ A.presheaf U x hx)) a ⊗ₜ[↑(R.stalk x)]
        (ConcreteCategory.hom (TopCat.Presheaf.germ B.presheaf U x hx)) b := by
  rw [← stalkTensorDescU_tmul, ← CategoryTheory.comp_apply, germ_stalkTensorDesc]

/-- **Element form of `germ_stalkTensorDesc`.** The comparison map sends the germ of a
section `w` over `U` to its per-neighbourhood descent `stalkTensorDescU`. -/
lemma stalkTensorDesc_germ (U : Opens X) (hx : x ∈ U)
    (w : ↑((Monoidal.tensorObj A B).presheaf.obj (op U))) :
    (stalkTensorDesc A B x)
        ((ConcreteCategory.hom (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf U x hx)) w)
      = (stalkTensorDescU A B x U hx) w := by
  rw [← CategoryTheory.comp_apply, germ_stalkTensorDesc]

/-- **The `R.stalk x`-linear d.2 comparison map** (stage (iii)). The additive comparison
map `stalkTensorDesc` is `R.stalk x`-linear for the stalk module structures of
`Mathlib.Algebra.Category.ModuleCat.Stalk`: linearity is checked on a germ `germ r` of a
scalar `r : R(U)` via the germ--scalar compatibility `germ_smul` and the section-level
scalar compatibility `stalkTensorDescU_smul`, after passing to a common neighbourhood.
This is the linear packaging the d.2 stalk--tensor isomorphism `stalkTensorIso` builds on. -/
noncomputable def stalkTensorLinearMap :
    (↑(TopCat.Presheaf.stalk (Monoidal.tensorObj A B).presheaf x) : Type u)
      →ₗ[↑(R.stalk x)] Tgt where
  toFun := ConcreteCategory.hom (stalkTensorDesc A B x)
  map_add' a b := map_add _ a b
  map_smul' r ξ := by
    dsimp only [RingHom.id_apply]
    obtain ⟨U, hxU, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
    obtain ⟨V, hxV, z, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (Monoidal.tensorObj A B).presheaf ξ
    set W : Opens X := U ⊓ V with hW
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    set iWU : W ⟶ U := homOfLE inf_le_left
    set iWV : W ⟶ V := homOfLE inf_le_right
    have hr : (ConcreteCategory.hom (R.germ U x hxU)) r₀
        = (ConcreteCategory.hom (R.germ W x hxW)) ((ConcreteCategory.hom (R.map iWU.op)) r₀) :=
      (TopCat.Presheaf.germ_res_apply R iWU x hxW r₀).symm
    have hz : (ConcreteCategory.hom
          (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf V x hxV)) z
        = (ConcreteCategory.hom
            (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf W x hxW))
            ((ConcreteCategory.hom ((Monoidal.tensorObj A B).presheaf.map iWV.op)) z) :=
      (TopCat.Presheaf.germ_res_apply (Monoidal.tensorObj A B).presheaf iWV x hxW z).symm
    rw [hr, hz, ← PresheafOfModules.germ_smul (Monoidal.tensorObj A B) x W hxW,
      stalkTensorDesc_germ, stalkTensorDescU_smul, ← stalkTensorDesc_germ]

/-- **Germ characterisation of the linear comparison map** on a simple tensor: the germ of
`a ⊗ b` over `U` maps to `germ a ⊗ germ b`. The `R.stalk x`-linear repackaging
`stalkTensorLinearMap` agrees with `stalkTensorDesc` on germs. -/
@[simp]
lemma stalkTensorLinearMap_germ_tmul (U : Opens X) (hx : x ∈ U)
    (a : ↑(A.obj (op U))) (b : ↑(B.obj (op U))) :
    stalkTensorLinearMap A B x
        ((ConcreteCategory.hom (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf U x hx))
          (a ⊗ₜ[R.obj (op U)] b))
      = (ConcreteCategory.hom (TopCat.Presheaf.germ A.presheaf U x hx)) a ⊗ₜ[↑(R.stalk x)]
        (ConcreteCategory.hom (TopCat.Presheaf.germ B.presheaf U x hx)) b :=
  stalkTensorDesc_germ_tmul A B x U hx a b

/-! ### Stage (iv): the reverse map -/

/-- **Inner cocone leg for the reverse map** (fixed `A`-section `a` over `U`). For a
`B`-neighbourhood `V ∋ x`, the additive map `B(V) → (A ⊗ᵖ B).stalk x` sending `b` to the
germ of `(a|_{U⊓V}) ⊗ (b|_{U⊓V})`. Project-local building block of the d.2 reverse map. -/
private noncomputable def revInnerLeg (U : Opens X) (hxU : x ∈ U) (a : ↑(A.obj (op U)))
    (V : Opens X) (hxV : x ∈ V) :
    B.presheaf.obj (op V) ⟶ TopCat.Presheaf.stalk (Monoidal.tensorObj A B).presheaf x :=
  AddCommGrpCat.ofHom <|
    (ConcreteCategory.hom
        (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf (U ⊓ V) x ⟨hxU, hxV⟩)).comp
      (((TensorProduct.mk ↑(R.obj (op (U ⊓ V))) ↑(A.obj (op (U ⊓ V))) ↑(B.obj (op (U ⊓ V)))
          ((ConcreteCategory.hom (A.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op)) a :
            ↑(A.obj (op (U ⊓ V))))).toAddMonoidHom).comp
        (ConcreteCategory.hom (B.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op)))

/-- Evaluation of `revInnerLeg`: it sends `b` to the germ of `(a|_{U⊓V}) ⊗ (b|_{U⊓V})`. -/
private lemma revInnerLeg_apply (U : Opens X) (hxU : x ∈ U) (a : ↑(A.obj (op U)))
    (V : Opens X) (hxV : x ∈ V) (b : ↑(B.presheaf.obj (op V))) :
    (ConcreteCategory.hom (revInnerLeg A B x U hxU a V hxV)) b
      = (ConcreteCategory.hom
          (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf (U ⊓ V) x ⟨hxU, hxV⟩))
          (((ConcreteCategory.hom (A.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op)) a :
              ↑(A.obj (op (U ⊓ V)))) ⊗ₜ[R.obj (op (U ⊓ V))]
            ((ConcreteCategory.hom (B.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op)) b :
              ↑(B.obj (op (U ⊓ V))))) :=
  rfl

/-- **Inner descent of the reverse map** (fixed `A`-section `a` over `U`): the additive
map `B.stalk x → (A ⊗ᵖ B).stalk x` descending `revInnerLeg` through the `B`-stalk colimit. -/
private noncomputable def revInner (U : Opens X) (hxU : x ∈ U) (a : ↑(A.obj (op U))) :
    TopCat.Presheaf.stalk B.presheaf x ⟶
      TopCat.Presheaf.stalk (Monoidal.tensorObj A B).presheaf x :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ B.presheaf)
    ⟨TopCat.Presheaf.stalk (Monoidal.tensorObj A B).presheaf x,
      fun W => revInnerLeg A B x U hxU a (unop W).1 (unop W).2,
      by
        intro W W' f
        apply AddCommGrpCat.hom_ext
        ext b
        simp only [CategoryTheory.comp_apply, Functor.const_obj_map]
        erw [CategoryTheory.ConcreteCategory.id_apply, revInnerLeg_apply]
        conv_rhs => erw [revInnerLeg_apply]
        have hVle : (unop W').1 ≤ (unop W).1 := leOfHom ((OpenNhds.inclusion x).map f.unop)
        have j : U ⊓ (unop W').1 ⟶ U ⊓ (unop W).1 := homOfLE (inf_le_inf_left U hVle)
        rw [← TopCat.Presheaf.germ_res_apply (Monoidal.tensorObj A B).presheaf j x
          ⟨hxU, (unop W').2⟩]
        congr 1
        erw [presheaf_map_apply_coe, PresheafOfModules.Monoidal.tensorObj_map_tmul]
        congr 1
        · rw [← presheaf_map_apply_coe, ← presheaf_map_apply_coe]
          erw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
          congr 1
        · rw [← presheaf_map_apply_coe, Functor.comp_map]
          erw [← CategoryTheory.ConcreteCategory.comp_apply,
            ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
          congr 1⟩

/-- The inner descent factors `revInnerLeg` through the `B`-germ, by the colimit
universal property. -/
private lemma germ_revInner (U : Opens X) (hxU : x ∈ U) (a : ↑(A.obj (op U)))
    (V : Opens X) (hxV : x ∈ V) :
    TopCat.Presheaf.germ B.presheaf V x hxV ≫ revInner A B x U hxU a
      = revInnerLeg A B x U hxU a V hxV :=
  colimit.ι_desc _ (op (⟨V, hxV⟩ : OpenNhds x))

/-- **Germ characterisation of the inner descent** on a section `b` over `V`: the inner
descent sends `germ b` to the germ of `(a|_{U⊓V}) ⊗ (b|_{U⊓V})`. -/
private lemma revInner_germ (U : Opens X) (hxU : x ∈ U) (a : ↑(A.obj (op U)))
    (V : Opens X) (hxV : x ∈ V) (b : ↑(B.presheaf.obj (op V))) :
    (ConcreteCategory.hom (revInner A B x U hxU a))
        ((ConcreteCategory.hom (TopCat.Presheaf.germ B.presheaf V x hxV)) b)
      = (ConcreteCategory.hom
          (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf (U ⊓ V) x ⟨hxU, hxV⟩))
          (((ConcreteCategory.hom (A.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op)) a :
              ↑(A.obj (op (U ⊓ V)))) ⊗ₜ[R.obj (op (U ⊓ V))]
            ((ConcreteCategory.hom (B.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op)) b :
              ↑(B.obj (op (U ⊓ V))))) := by
  rw [← CategoryTheory.comp_apply, germ_revInner]
  exact revInnerLeg_apply A B x U hxU a V hxV b

/-- **Outer cocone leg for the reverse map.** For a neighbourhood `U ∋ x`, the additive map
`A(U) → (B.stalk x →+ (A ⊗ᵖ B).stalk x)` sending an `A`-section `a` to the inner descent
`revInner` it determines. Additivity in `a` is checked on germ generators of `B.stalk x`
via `revInner_germ` and bilinearity of the section tensor. -/
private noncomputable def revOuterLeg (U : Opens X) (hxU : x ∈ U) :
    (↑(A.obj (op U)) : Type u) →+
      ((↑(TopCat.Presheaf.stalk B.presheaf x) : Type u) →+
        ↑(TopCat.Presheaf.stalk (Monoidal.tensorObj A B).presheaf x)) where
  toFun a := ConcreteCategory.hom (revInner A B x U hxU a)
  map_add' a a' := by
    apply AddMonoidHom.ext
    intro ξ
    obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq B.presheaf ξ
    simp only [AddMonoidHom.add_apply, revInner_germ]
    erw [_root_.map_add, TensorProduct.add_tmul, _root_.map_add]
  map_zero' := by
    apply AddMonoidHom.ext
    intro ξ
    obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq B.presheaf ξ
    simp only [AddMonoidHom.zero_apply, revInner_germ]
    erw [_root_.map_zero, TensorProduct.zero_tmul, _root_.map_zero]

/-- Evaluation of the outer leg: it is the inner descent. -/
private lemma revOuterLeg_apply (U : Opens X) (hxU : x ∈ U) (a : ↑(A.obj (op U)))
    (ξ : ↑(TopCat.Presheaf.stalk B.presheaf x)) :
    (revOuterLeg A B x U hxU a) ξ = (ConcreteCategory.hom (revInner A B x U hxU a)) ξ :=
  rfl

/-- **Outer descent of the reverse map.** The additive map
`A.stalk x → (B.stalk x →+ (A ⊗ᵖ B).stalk x)` descending `revOuterLeg` through the
`A`-stalk colimit; this is the additive bilinear comparison underlying the reverse map. -/
private noncomputable def revBihom :
    TopCat.Presheaf.stalk A.presheaf x ⟶
      AddCommGrpCat.of ((↑(TopCat.Presheaf.stalk B.presheaf x) : Type u) →+
        ↑(TopCat.Presheaf.stalk (Monoidal.tensorObj A B).presheaf x)) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ A.presheaf)
    ⟨AddCommGrpCat.of _,
      fun U => AddCommGrpCat.ofHom (revOuterLeg A B x (unop U).1 (unop U).2),
      by
        intro W W' f
        apply AddCommGrpCat.hom_ext
        ext a
        simp only [CategoryTheory.comp_apply, Functor.const_obj_map]
        erw [CategoryTheory.ConcreteCategory.id_apply]
        apply AddMonoidHom.ext
        intro ξ
        obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq B.presheaf ξ
        erw [revOuterLeg_apply, revOuterLeg_apply, revInner_germ, revInner_germ]
        have hVle : (unop W').1 ≤ (unop W).1 := leOfHom ((OpenNhds.inclusion x).map f.unop)
        have j : (unop W').1 ⊓ V ⟶ (unop W).1 ⊓ V := homOfLE (inf_le_inf_right V hVle)
        rw [← TopCat.Presheaf.germ_res_apply (Monoidal.tensorObj A B).presheaf j x
          ⟨(unop W').2, hxV⟩]
        congr 1
        erw [presheaf_map_apply_coe, PresheafOfModules.Monoidal.tensorObj_map_tmul]
        congr 1
        · rw [← presheaf_map_apply_coe, ← presheaf_map_apply_coe, Functor.comp_map]
          erw [← CategoryTheory.ConcreteCategory.comp_apply,
            ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
          congr 1
        · rw [← presheaf_map_apply_coe]
          erw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
          congr 1⟩

/-- The outer descent factors `revOuterLeg` through the `A`-germ. -/
private lemma germ_revBihom (U : Opens X) (hxU : x ∈ U) :
    TopCat.Presheaf.germ A.presheaf U x hxU ≫ revBihom A B x
      = AddCommGrpCat.ofHom (revOuterLeg A B x U hxU) :=
  colimit.ι_desc _ (op (⟨U, hxU⟩ : OpenNhds x))

/-- **Germ characterisation of the additive bilinear comparison** on germ generators:
`revBihom (germ a) (germ b)` is the germ of `(a|_{U⊓V}) ⊗ (b|_{U⊓V})`. -/
private lemma revBihom_germ_tmul (U : Opens X) (hxU : x ∈ U) (a : ↑(A.obj (op U)))
    (V : Opens X) (hxV : x ∈ V) (b : ↑(B.obj (op V))) :
    ((ConcreteCategory.hom (revBihom A B x))
        ((ConcreteCategory.hom (TopCat.Presheaf.germ A.presheaf U x hxU)) a))
        ((ConcreteCategory.hom (TopCat.Presheaf.germ B.presheaf V x hxV)) b)
      = (ConcreteCategory.hom
          (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf (U ⊓ V) x ⟨hxU, hxV⟩))
          (((ConcreteCategory.hom (A.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op)) a :
              ↑(A.obj (op (U ⊓ V)))) ⊗ₜ[R.obj (op (U ⊓ V))]
            ((ConcreteCategory.hom (B.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op)) b :
              ↑(B.obj (op (U ⊓ V))))) := by
  have hb : (ConcreteCategory.hom (revBihom A B x))
        ((ConcreteCategory.hom (TopCat.Presheaf.germ A.presheaf U x hxU)) a)
      = revOuterLeg A B x U hxU a := by
    rw [← CategoryTheory.comp_apply, germ_revBihom]
    rfl
  rw [hb, revOuterLeg_apply, revInner_germ]

/-- **The `W ⊓ W` section identity underlying the stage-(iv) balancing.** Over the
self-intersection `W ⊓ W`, restricting a scalar-twisted simple tensor commutes between the
two factors. Proved by transporting the clean `W`-level identity `(r₀ • a) ⊗ b = a ⊗ (r₀ • b)`
(`TensorProduct.smul_tmul` over the `CommRingCat` carrier `R(W)` — no carrier mixing, the
scalar never leaves `R(W)`) down through `(A ⊗ᵖ B).map` via `tensorObj_map_tmul`. This is the
project-local resolution of the `CommRingCat`-vs-`RingCat` carrier wall flagged in stage (iii). -/
private lemma revBihom_balanced_germ (W Z : Opens X) (hxZ : x ∈ Z) (j : Z ⟶ W)
    (r₀ : ↑(R.obj (op W))) (a : ↑(A.obj (op W))) (b : ↑(B.obj (op W))) :
    (ConcreteCategory.hom (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf Z x hxZ))
        (((ConcreteCategory.hom (A.presheaf.map j.op)) (r₀ • a : ↑(A.obj (op W))) :
              ↑(A.obj (op Z)))
          ⊗ₜ[R.obj (op Z)]
        ((ConcreteCategory.hom (B.presheaf.map j.op)) b : ↑(B.obj (op Z))))
      = (ConcreteCategory.hom (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf Z x hxZ))
        (((ConcreteCategory.hom (A.presheaf.map j.op)) a : ↑(A.obj (op Z)))
          ⊗ₜ[R.obj (op Z)]
        ((ConcreteCategory.hom (B.presheaf.map j.op)) (r₀ • b : ↑(B.obj (op W))) :
              ↑(B.obj (op Z)))) := by
  congr 1
  have hWsec : ((r₀ • a) ⊗ₜ[R.obj (op W)] b : ↑((Monoidal.tensorObj A B).obj (op W)))
      = a ⊗ₜ[R.obj (op W)] (r₀ • b) := TensorProduct.smul_tmul _ _ _
  have h2 := congrArg (ConcreteCategory.hom ((Monoidal.tensorObj A B).map j.op)) hWsec
  erw [tensorObj_map_tmul, tensorObj_map_tmul] at h2
  exact h2

/-- **The `R.stalk x`-balancing of the additive bilinear comparison `revBihom`** — the
condition feeding `TensorProduct.liftAddHom` to produce the reverse map. On germ
generators over a common neighbourhood `W := T ⊓ U ⊓ V` the germ–scalar compatibility
`germ_smul` keeps the scalar in `R.stalk x`, and the two `revBihom_germ_tmul` germs reduce
to the single section identity `revBihom_balanced_section` over `W ⊓ W`. -/
private lemma revBihom_balanced (r : ↑(R.stalk x))
    (m : ↑(TopCat.Presheaf.stalk A.presheaf x))
    (n : ↑(TopCat.Presheaf.stalk B.presheaf x)) :
    ((ConcreteCategory.hom (revBihom A B x)) (r • m)) n
      = ((ConcreteCategory.hom (revBihom A B x)) m) (r • n) := by
  obtain ⟨T, hxT, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
  obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq A.presheaf m
  obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq B.presheaf n
  set W : Opens X := T ⊓ U ⊓ V with hWdef
  have hxW : x ∈ W := ⟨⟨hxT, hxU⟩, hxV⟩
  rw [← TopCat.Presheaf.germ_res_apply R
        (homOfLE (le_trans inf_le_left inf_le_left) : W ⟶ T) x hxW r₀,
      ← TopCat.Presheaf.germ_res_apply A.presheaf
        (homOfLE (le_trans inf_le_left inf_le_right) : W ⟶ U) x hxW a,
      ← TopCat.Presheaf.germ_res_apply B.presheaf
        (homOfLE inf_le_right : W ⟶ V) x hxW b]
  set r₀' := (ConcreteCategory.hom
    (R.map (homOfLE (le_trans inf_le_left inf_le_left) : W ⟶ T).op)) r₀ with hr₀'
  set a' := (ConcreteCategory.hom
    (A.presheaf.map (homOfLE (le_trans inf_le_left inf_le_right) : W ⟶ U).op)) a with ha'
  set b' := (ConcreteCategory.hom
    (B.presheaf.map (homOfLE inf_le_right : W ⟶ V).op)) b with hb'
  rw [← PresheafOfModules.germ_smul A x W hxW,
      ← PresheafOfModules.germ_smul B x W hxW,
      revBihom_germ_tmul A B x W hxW _ W hxW b',
      revBihom_germ_tmul A B x W hxW a' W hxW _]
  exact revBihom_balanced_germ A B x W (W ⊓ W) ⟨hxW, hxW⟩ (homOfLE inf_le_left) r₀' a' b'

/-- **The reverse map of the d.2 stalk--tensor comparison** `A_x ⊗_{R_x} B_x → (A ⊗ᵖ B).stalk x`,
the descent of the `R.stalk x`-balanced additive bilinear map `revBihom` through the relative
tensor product over `R.stalk x` (via `TensorProduct.liftAddHom`). This is the candidate inverse
to `stalkTensorLinearMap`; mutual inversion is checked in `stalkTensorIso`. -/
noncomputable def stalkTensorRev :
    Tgt →+ ↑(TopCat.Presheaf.stalk (Monoidal.tensorObj A B).presheaf x) :=
  TensorProduct.liftAddHom (ConcreteCategory.hom (revBihom A B x)) (revBihom_balanced A B x)

/-- Germ characterisation of the reverse map on a simple tensor of germs: `germ a ⊗ germ b`
maps to the germ of `(a|_{U⊓V}) ⊗ (b|_{U⊓V})`. -/
lemma stalkTensorRev_germ_tmul (U : Opens X) (hxU : x ∈ U) (a : ↑(A.obj (op U)))
    (V : Opens X) (hxV : x ∈ V) (b : ↑(B.obj (op V))) :
    stalkTensorRev A B x
        ((ConcreteCategory.hom (TopCat.Presheaf.germ A.presheaf U x hxU)) a ⊗ₜ[↑(R.stalk x)]
          (ConcreteCategory.hom (TopCat.Presheaf.germ B.presheaf V x hxV)) b)
      = (ConcreteCategory.hom
          (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf (U ⊓ V) x ⟨hxU, hxV⟩))
          (((ConcreteCategory.hom (A.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op)) a :
              ↑(A.obj (op (U ⊓ V)))) ⊗ₜ[R.obj (op (U ⊓ V))]
            ((ConcreteCategory.hom (B.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op)) b :
              ↑(B.obj (op (U ⊓ V))))) := by
  rw [stalkTensorRev, TensorProduct.liftAddHom_tmul]
  exact revBihom_germ_tmul A B x U hxU a V hxV b

/-- **Germ of a restricted simple tensor.** The germ over `Z` of `(a|_Z) ⊗ (b|_Z)` agrees with
the germ over `W` of `a ⊗ b`, for `j : Z ⟶ W` and sections `a, b` over `W`. The reverse-map
inversion identity `germ_{U⊓U}((a|) ⊗ (b|)) = germ_U (a ⊗ b)` is the special case `Z = U ⊓ U`.
Stated with a single restriction `j` (so the `tensorObj_map_tmul` fold applies); the germ wrapper
supplies the expected module type for the relative tensor over the `CommRingCat` carrier `R(Z)`. -/
private lemma germ_tensorObj_map_tmul (W Z : Opens X) (hxZ : x ∈ Z) (hxW : x ∈ W) (j : Z ⟶ W)
    (a : ↑(A.obj (op W))) (b : ↑(B.obj (op W))) :
    (ConcreteCategory.hom
        (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf Z x hxZ))
        (((ConcreteCategory.hom (A.presheaf.map j.op)) a : ↑(A.obj (op Z))) ⊗ₜ[R.obj (op Z)]
          ((ConcreteCategory.hom (B.presheaf.map j.op)) b : ↑(B.obj (op Z))))
      = (ConcreteCategory.hom
          (TopCat.Presheaf.germ (Monoidal.tensorObj A B).presheaf W x hxW))
          ((a : ↑(A.obj (op W))) ⊗ₜ[R.obj (op W)] (b : ↑(B.obj (op W)))) := by
  erw [← PresheafOfModules.Monoidal.tensorObj_map_tmul (M₁ := A) (M₂ := B) j.op a b,
    ← presheaf_map_apply_coe (Monoidal.tensorObj A B)]
  exact TopCat.Presheaf.germ_res_apply (Monoidal.tensorObj A B).presheaf j x hxZ _

/-- **The d.2 stalk--tensor commutation isomorphism** (blueprint `lem:stalk_tensor_commutation`).
The `R.stalk x`-linear comparison map `stalkTensorLinearMap` is an isomorphism
`(A ⊗ᵖ B).stalk x ≃ A_x ⊗_{R_x} B_x`, with inverse the descended reverse map `stalkTensorRev`.
Mutual inversion is checked on germ generators (`stalkTensorLinearMap_germ_tmul`,
`stalkTensorRev_germ_tmul`) and extended by `TensorProduct.induction_on` and the joint
epimorphism of the germ maps (`TopCat.Presheaf.stalk_hom_ext`). This is the single
genuinely Mathlib-absent ingredient (d.2) underlying the unconditional associator of the
relative-Picard tensor substrate. -/
noncomputable def stalkTensorIso :
    (↑(TopCat.Presheaf.stalk (Monoidal.tensorObj A B).presheaf x) : Type u)
      ≃ₗ[↑(R.stalk x)] Tgt where
  toFun := stalkTensorLinearMap A B x
  map_add' := map_add _
  map_smul' := (stalkTensorLinearMap A B x).map_smul'
  invFun := stalkTensorRev A B x
  left_inv := by
    intro s
    obtain ⟨U, hxU, w, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (Monoidal.tensorObj A B).presheaf s
    induction w using TensorProduct.induction_on with
    | zero =>
        erw [map_zero, map_zero, map_zero]
    | tmul a b =>
        erw [stalkTensorLinearMap_germ_tmul, stalkTensorRev_germ_tmul]
        exact germ_tensorObj_map_tmul A B x U (U ⊓ U) ⟨hxU, hxU⟩ hxU (homOfLE inf_le_left) a b
    | add p q hp hq =>
        erw [map_add, map_add, map_add, hp, hq]
  right_inv := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
        simp only [map_zero]
    | tmul ξ η =>
        obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq A.presheaf ξ
        obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq B.presheaf η
        rw [stalkTensorRev_germ_tmul]
        erw [stalkTensorLinearMap_germ_tmul,
            TopCat.Presheaf.germ_res_apply A.presheaf
              (homOfLE inf_le_left : U ⊓ V ⟶ U) x ⟨hxU, hxV⟩,
            TopCat.Presheaf.germ_res_apply B.presheaf
              (homOfLE inf_le_right : U ⊓ V ⟶ V) x ⟨hxU, hxV⟩]
    | add p q hp hq =>
        simp only [map_add]
        rw [hp, hq]

end StalkTensor

end PresheafOfModules
