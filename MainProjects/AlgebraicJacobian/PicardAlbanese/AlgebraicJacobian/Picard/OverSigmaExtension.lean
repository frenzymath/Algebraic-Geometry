/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The Σ-extension of a presheaf on a slice (DAT-6, stage 2)

A presheaf `F` on the slice `Over S` extends to a presheaf on the ambient category:
`F̃(T) := Σ (a : T ⟶ S), F(Over.mk a)` — an element is a structure morphism together
with an element of `F` at the corresponding slice object.  This is the *slice trick*
of the Wave-4 datum campaign (worksheet §1.2.1): for `S = Spec k'` and `F` the
degree-zero Picard functor, `F̃` is the big-site carrier that mathlib's 01JJ
local-representability engine consumes, and a representation of `F̃` descends to a
representation of `F` on the slice with the represented object's structure morphism
the Σ-component of the universal element.

* `CategoryTheory.Over.mkCongr`: the canonical slice morphism `Over.mk a ⟶ Over.mk b`
  of an equality `a = b` — an honest `homMk (𝟙 T)`, no `eqToHom`; the whole transport
  calculus of the file is cast-free.
* `CategoryTheory.Over.sigmaExtension S F : Cᵒᵖ ⥤ Type (max v w)`: the Σ-extension,
  with restriction by composition on the Σ-component and by the canonical slice
  morphism `Over.homMk g` on the fibre component.
* `CategoryTheory.Over.sigmaExtension_ext` / `sigmaExtension_snd_eq`: the transport
  calculus of Σ-elements along equalities of structure morphisms.
* `CategoryTheory.Over.sigmaExtension_map_mk_eq_iff`: **the amalgamation seam** — a
  restriction of a Σ-element hits a prescribed Σ-element iff the fibre component of
  the source restricts to the prescribed fibre along the canonical slice morphism.
* `CategoryTheory.Over.map_eq_of_sigmaExtension_map_eq`: **the compatibility
  descent** — two Σ-elements whose restrictions along the left legs of a pair of
  slice morphisms agree have fibre components agreeing after slice restriction.
* `CategoryTheory.Functor.RepresentableBy.overSlice`: **the Σ-descent** — a
  representation `α` of `sigmaExtension S F` by `J` induces a representation of `F`
  by `Over.mk (α.homEquiv (𝟙 J)).1`; the slice `homEquiv` is plain application of
  `F.map` to the universal element's fibre component.
-/

set_option autoImplicit false

universe w v u

namespace CategoryTheory

open Opposite

namespace Over

variable {C : Type u} [Category.{v} C] {S : C}

/-! ## The cast-free transport calculus -/

/-- The canonical slice morphism between `Over.mk`s of equal structure morphisms: an
honest `homMk (𝟙 T)`, never an `eqToHom`. -/
def mkCongr {T : C} {a b : T ⟶ S} (h : a = b) : Over.mk a ⟶ Over.mk b :=
  Over.homMk (𝟙 T) (show 𝟙 T ≫ b = a by rw [Category.id_comp, h])

@[simp]
lemma mkCongr_left {T : C} {a b : T ⟶ S} (h : a = b) : (mkCongr h).left = 𝟙 T :=
  rfl

lemma mkCongr_rfl {T : C} (a : T ⟶ S) : mkCongr (rfl : a = a) = 𝟙 (Over.mk a) := by
  ext
  rfl

/-- Two consecutive canonical morphisms compose to the canonical morphism of the
transitive equality. -/
lemma mkCongr_comp_mkCongr {T : C} {a b c : T ⟶ S} (h : a = b) (h' : b = c) :
    mkCongr h ≫ mkCongr h' = mkCongr (h.trans h') := by
  ext
  change 𝟙 T ≫ 𝟙 T = 𝟙 T
  rw [Category.id_comp]

/-- Any slice morphism into an `Over.mk` factors as the canonical `mkCongr` of its
`Over.w` equation followed by the canonical `homMk` of its left leg. -/
lemma mkCongr_comp_homMk {Y : C} {c : Y ⟶ S} {X : Over S} (g : X ⟶ Over.mk c) :
    (mkCongr (Over.w g).symm : X ⟶ Over.mk (g.left ≫ c)) ≫
        (Over.homMk g.left rfl : Over.mk (g.left ≫ c) ⟶ Over.mk c) = g := by
  ext
  change 𝟙 X.left ≫ g.left = g.left
  rw [Category.id_comp]

section Transport

variable (F : (Over S)ᵒᵖ ⥤ Type w)

/-- Elements of a Σ-extension fibre agree once they agree after transport along an
equality of the structure morphisms. -/
lemma sigmaExtension_ext {T : C} {a b : T ⟶ S} (hab : a = b)
    {x : F.obj (op (Over.mk a))} {y : F.obj (op (Over.mk b))}
    (hxy : F.map (mkCongr hab).op y = x) :
    (⟨a, x⟩ : Σ c : T ⟶ S, F.obj (op (Over.mk c))) = ⟨b, y⟩ := by
  subst hab
  rw [mkCongr_rfl, op_id, F.map_id] at hxy
  exact congrArg (Sigma.mk a) hxy.symm

/-- The second components of equal Σ-elements agree after transport along the equality
of the structure morphisms. -/
lemma sigmaExtension_snd_eq {T : C} {a b : T ⟶ S} (hab : a = b)
    {x : F.obj (op (Over.mk a))} {y : F.obj (op (Over.mk b))}
    (h : (⟨a, x⟩ : Σ c : T ⟶ S, F.obj (op (Over.mk c))) = ⟨b, y⟩) :
    F.map (mkCongr hab).op y = x := by
  subst hab
  rw [mkCongr_rfl, op_id, F.map_id]
  exact (eq_of_heq (Sigma.mk.inj h).2).symm

end Transport

variable (S) (F : (Over S)ᵒᵖ ⥤ Type w)

/-! ## The Σ-extension -/

/-- The restriction map of the Σ-extension along `g : T' ⟶ T`: composition on the
structure morphism, the canonical slice morphism `Over.homMk g` on the fibre
component. -/
def sigmaExtensionMap {T' T : C} (g : T' ⟶ T) :
    (Σ a : T ⟶ S, F.obj (op (Over.mk a))) → Σ a : T' ⟶ S, F.obj (op (Over.mk a)) :=
  fun x =>
    ⟨g ≫ x.1, F.map (Over.homMk g rfl : Over.mk (g ≫ x.1) ⟶ Over.mk x.1).op x.2⟩

/-- **The Σ-extension** of a presheaf on the slice `Over S` to the ambient category:
`T ↦ Σ (a : T ⟶ S), F(Over.mk a)`. -/
def sigmaExtension : Cᵒᵖ ⥤ Type (max v w) where
  obj T := Σ a : T.unop ⟶ S, F.obj (op (Over.mk a))
  map g := TypeCat.ofHom (sigmaExtensionMap S F g.unop)
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    obtain ⟨a, ξ⟩ := x
    exact sigmaExtension_ext F (Category.id_comp a) rfl
  map_comp {T₁ T₂ T₃} g h := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    obtain ⟨a, ξ⟩ := x
    change (⟨(h.unop ≫ g.unop) ≫ a,
        F.map (Over.homMk (h.unop ≫ g.unop) rfl :
          Over.mk ((h.unop ≫ g.unop) ≫ a) ⟶ Over.mk a).op ξ⟩
        : Σ c : T₃.unop ⟶ S, F.obj (op (Over.mk c)))
      = ⟨h.unop ≫ g.unop ≫ a,
          F.map (Over.homMk h.unop rfl :
            Over.mk (h.unop ≫ g.unop ≫ a) ⟶ Over.mk (g.unop ≫ a)).op
            (F.map (Over.homMk g.unop rfl :
              Over.mk (g.unop ≫ a) ⟶ Over.mk a).op ξ)⟩
    refine sigmaExtension_ext F (Category.assoc h.unop g.unop a) ?_
    rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp]
    refine congrArg (fun φ : Over.mk ((h.unop ≫ g.unop) ≫ a) ⟶ Over.mk a =>
      F.map φ.op ξ) ?_
    ext
    change (𝟙 T₃.unop ≫ h.unop) ≫ g.unop = h.unop ≫ g.unop
    rw [Category.id_comp]

variable {S F}

@[simp]
lemma sigmaExtension_obj (T : Cᵒᵖ) :
    (sigmaExtension S F).obj T = Σ a : T.unop ⟶ S, F.obj (op (Over.mk a)) :=
  rfl

/-- The computation rule of the Σ-extension's restriction. -/
lemma sigmaExtension_map_mk {T' T : C} (g : T' ⟶ T) (a : T ⟶ S)
    (ξ : F.obj (op (Over.mk a))) :
    (sigmaExtension S F).map g.op ⟨a, ξ⟩
      = ⟨g ≫ a, F.map (Over.homMk g rfl : Over.mk (g ≫ a) ⟶ Over.mk a).op ξ⟩ :=
  rfl

@[simp]
lemma sigmaExtension_map_fst {T' T : C} (g : T' ⟶ T)
    (x : (sigmaExtension S F).obj (op T)) :
    ((sigmaExtension S F).map g.op x).1 = g ≫ x.1 :=
  rfl

/-- **The amalgamation seam**: a restriction of a Σ-element hits a prescribed
Σ-element iff the fibre component of the source restricts to the prescribed fibre
component along the canonical slice morphism over the prescribed structure
morphism. -/
lemma sigmaExtension_map_mk_eq_iff {T' T : C} (g : T' ⟶ T) {a : T ⟶ S} {b : T' ⟶ S}
    (w : g ≫ a = b) (s : F.obj (op (Over.mk a))) (y : F.obj (op (Over.mk b))) :
    (sigmaExtension S F).map g.op ⟨a, s⟩ = ⟨b, y⟩
      ↔ F.map (Over.homMk g (show g ≫ (Over.mk a).hom = (Over.mk b).hom from w) :
          Over.mk b ⟶ Over.mk a).op s = y := by
  subst w
  rw [sigmaExtension_map_mk]
  constructor
  · intro h
    have h2 := sigmaExtension_snd_eq F rfl h
    rw [mkCongr_rfl, op_id, F.map_id] at h2
    exact h2.symm
  · intro h
    refine sigmaExtension_ext F rfl ?_
    rw [mkCongr_rfl, op_id, F.map_id]
    exact h.symm

/-- The Σ-extension's restriction along the left leg of a slice morphism `g : Z ⟶
Over.mk a`, evaluated at a Σ-element over `a`: the structure morphism is `Z.hom` and
the fibre component is the honest slice restriction `F.map g.op`. -/
lemma sigmaExtension_map_left_mk {Z : Over S} {T : C} {a : T ⟶ S}
    (g : Z ⟶ Over.mk a) (x : F.obj (op (Over.mk a))) :
    (sigmaExtension S F).map g.left.op ⟨a, x⟩
      = ⟨Z.hom, F.map g.op x⟩ :=
  (sigmaExtension_map_mk_eq_iff g.left (Over.w g) x (F.map g.op x)).mpr
    (congrArg (fun φ : Z ⟶ Over.mk a => F.map φ.op x)
      (Over.OverMorphism.ext rfl :
        (Over.homMk g.left (Over.w g) : Z ⟶ Over.mk a) = g))

/-- **The compatibility descent**: two Σ-elements whose Σ-extension restrictions along
the left legs of a pair of slice morphisms with common domain agree have fibre
components agreeing after restriction along the slice morphisms themselves. -/
lemma map_eq_of_sigmaExtension_map_eq {Z : Over S} {T T' : C} {a : T ⟶ S}
    {b : T' ⟶ S} {x : F.obj (op (Over.mk a))} {y : F.obj (op (Over.mk b))}
    (gi : Z ⟶ Over.mk a) (gj : Z ⟶ Over.mk b)
    (h : (sigmaExtension S F).map gi.left.op ⟨a, x⟩
        = (sigmaExtension S F).map gj.left.op ⟨b, y⟩) :
    F.map gi.op x = F.map gj.op y := by
  have h' : (⟨Z.hom, F.map gi.op x⟩ : Σ c : Z.left ⟶ S, F.obj (op (Over.mk c)))
      = ⟨Z.hom, F.map gj.op y⟩ :=
    (sigmaExtension_map_left_mk gi x).symm.trans
      (h.trans (sigmaExtension_map_left_mk gj y))
  exact eq_of_heq (Sigma.mk.inj h').2

end Over

/-! ## The Σ-descent of a representation -/

namespace Functor.RepresentableBy

open Over

variable {C : Type u} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type w}

/-- **The Σ-descent of a representation** (the slice trick, output half): a
representation of the Σ-extension of `F` by an object `J` of the ambient category
induces a representation of `F` on the slice by `Over.mk` of the Σ-component of the
universal element; the slice `homEquiv` is plain application of `F.map` to the fibre
component of the universal element. -/
def overSlice {J : C} (α : (sigmaExtension S F).RepresentableBy J) :
    F.RepresentableBy (Over.mk (α.homEquiv (𝟙 J)).1) where
  homEquiv {X} :=
    { toFun := fun g => F.map g.op (α.homEquiv (𝟙 J)).2
      invFun := fun ξ =>
        Over.homMk (α.homEquiv.symm ⟨X.hom, ξ⟩)
          (congrArg Sigma.fst
            ((α.homEquiv_eq (α.homEquiv.symm ⟨X.hom, ξ⟩)).symm.trans
              (α.homEquiv.apply_symm_apply ⟨X.hom, ξ⟩)))
      left_inv := fun g => by
        refine Over.OverMorphism.ext ?_
        change α.homEquiv.symm ⟨X.hom, F.map g.op (α.homEquiv (𝟙 J)).2⟩ = g.left
        rw [Equiv.symm_apply_eq, α.homEquiv_eq g.left]
        exact (sigmaExtension_map_left_mk g (α.homEquiv (𝟙 J)).2).symm
      right_inv := fun ξ => by
        have h : (sigmaExtension S F).map (α.homEquiv.symm ⟨X.hom, ξ⟩).op
              (α.homEquiv (𝟙 J))
            = ⟨X.hom, ξ⟩ :=
          (α.homEquiv_eq (α.homEquiv.symm ⟨X.hom, ξ⟩)).symm.trans
            (α.homEquiv.apply_symm_apply ⟨X.hom, ξ⟩)
        have h2 : (⟨X.hom, F.map (Over.homMk (α.homEquiv.symm ⟨X.hom, ξ⟩)
              (congrArg Sigma.fst
                ((α.homEquiv_eq (α.homEquiv.symm ⟨X.hom, ξ⟩)).symm.trans
                  (α.homEquiv.apply_symm_apply ⟨X.hom, ξ⟩)))
                : X ⟶ Over.mk (α.homEquiv (𝟙 J)).1).op (α.homEquiv (𝟙 J)).2⟩
            : Σ c : X.left ⟶ S, F.obj (op (Over.mk c))) = ⟨X.hom, ξ⟩ :=
          (sigmaExtension_map_left_mk
            (Over.homMk (α.homEquiv.symm ⟨X.hom, ξ⟩)
              (congrArg Sigma.fst
                ((α.homEquiv_eq (α.homEquiv.symm ⟨X.hom, ξ⟩)).symm.trans
                  (α.homEquiv.apply_symm_apply ⟨X.hom, ξ⟩))))
            (α.homEquiv (𝟙 J)).2).symm.trans h
        exact eq_of_heq (Sigma.mk.inj h2).2 }
  homEquiv_comp {X X'} f g := by
    dsimp only [Equiv.coe_fn_mk]
    rw [op_comp, Functor.map_comp_apply]

end Functor.RepresentableBy

end CategoryTheory
