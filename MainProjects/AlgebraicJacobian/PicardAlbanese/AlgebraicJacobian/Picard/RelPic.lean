/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The relative Picard functor of a curve

For a scheme `C` over a field `k` (an object of `Over (Spec k)`) this file defines the
relative Picard functor of Grothendieck–Kleiman:
$$\operatorname{Pic}_{C/k}(T) \;=\; \operatorname{Pic}(C \times_k T)\,/\,
  \operatorname{Pic}(T),$$
line-bundle classes on `C ⊗ T` modulo classes pulled back from the test object `T`
along the second projection. The quotient — never the absolute `Pic(C ⊗ T)`, which is
not even a separated presheaf in any useful sense — is the functor that étale
sheafification and the representability theorem consume.

Products are the cartesian-monoidal product of `Over (Spec k)` (chosen pullbacks of
schemes): `C ⊗ T`, projection `snd C T`, whiskering `C ◁ g`, matching the vocabulary
of the challenge statement file.

## Main declarations

* `AlgebraicGeometry.picFromBase C T`: the subgroup of `(C ⊗ T).left.CechPic` of classes
  pulled back from `T` along the second projection.
* `AlgebraicGeometry.relPic C T`: the relative Picard group, the quotient by
  `picFromBase C T`, a `CommGroup`; `relPicMk` is the projection, with
  `relPicMk_eq_relPicMk_iff` the exact coset relation (a genuine range condition, no
  choice, no `Nonempty (≅)`).
* `AlgebraicGeometry.relPicMap C g`: restriction along `g : T' ⟶ T`, descended from
  pullback of Čech classes along `C ◁ g`.
* `AlgebraicGeometry.relPicFunctor C`: the relative Picard functor
  `(Over (Spec k))ᵒᵖ ⥤ CommGrpCat`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry.Scheme (CechPic)

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

noncomputable section

/-- The subgroup of Picard classes on `C ⊗ T` pulled back from the test object `T`
along the second projection. The relative Picard group is the quotient by it. -/
def picFromBase (T : Over (Spec (.of k))) : Subgroup ((C ⊗ T).left.CechPic) :=
  (CechPic.map (snd C T).left).range

lemma mem_picFromBase_iff {T : Over (Spec (.of k))} {L : (C ⊗ T).left.CechPic} :
    L ∈ picFromBase C T ↔ ∃ N : T.left.CechPic, CechPic.map (snd C T).left N = L :=
  Iff.rfl

/-- The relative Picard group of `C/k` at a test object `T`: Picard classes on `C ⊗ T`
modulo classes pulled back from `T`. -/
def relPic (T : Over (Spec (.of k))) : Type u :=
  (C ⊗ T).left.CechPic ⧸ picFromBase C T

noncomputable instance (T : Over (Spec (.of k))) : CommGroup (relPic C T) :=
  QuotientGroup.Quotient.commGroup (picFromBase C T)

/-- The projection from Picard classes on `C ⊗ T` to the relative Picard group. -/
noncomputable def relPicMk (T : Over (Spec (.of k))) :
    (C ⊗ T).left.CechPic →* relPic C T :=
  QuotientGroup.mk' (picFromBase C T)

lemma relPicMk_surjective (T : Over (Spec (.of k))) :
    Function.Surjective (relPicMk C T) :=
  QuotientGroup.mk'_surjective (picFromBase C T)

/-- The exact coset relation: two Picard classes on `C ⊗ T` have equal image in the
relative Picard group iff their ratio is pulled back from `T`. -/
lemma relPicMk_eq_relPicMk_iff {T : Over (Spec (.of k))}
    {L L' : (C ⊗ T).left.CechPic} :
    relPicMk C T L = relPicMk C T L' ↔ L / L' ∈ picFromBase C T :=
  QuotientGroup.eq_iff_div_mem

@[elab_as_elim]
theorem relPic.ind {T : Over (Spec (.of k))} {motive : relPic C T → Prop}
    (mk : ∀ L : (C ⊗ T).left.CechPic, motive (relPicMk C T L)) (x : relPic C T) :
    motive x :=
  QuotientGroup.induction_on x mk

variable {T T' T'' : Over (Spec (.of k))}

/-- Pullback of Čech Picard classes along `C ◁ g` sends classes from `T` to classes
from `T'`: the well-definedness of `relPicMap` on the `H_T`-cosets. -/
lemma picFromBase_le_comap (g : T' ⟶ T) :
    picFromBase C T ≤ (picFromBase C T').comap (CechPic.map (C ◁ g).left) := by
  rintro _ ⟨N, rfl⟩
  refine ⟨CechPic.map g.left N, ?_⟩
  show CechPic.map (snd C T').left (CechPic.map g.left N)
      = CechPic.map (C ◁ g).left (CechPic.map (snd C T).left N)
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
    ← Scheme.CechPic.map_comp, ← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]

/-- Restriction of relative Picard classes along `g : T' ⟶ T`: pull back along
`C ◁ g` and descend to the quotients. -/
noncomputable def relPicMap (g : T' ⟶ T) : relPic C T →* relPic C T' :=
  QuotientGroup.map (picFromBase C T) (picFromBase C T')
    (CechPic.map (C ◁ g).left) (picFromBase_le_comap C g)

@[simp]
lemma relPicMap_mk (g : T' ⟶ T) (L : (C ⊗ T).left.CechPic) :
    relPicMap C g (relPicMk C T L) = relPicMk C T' (CechPic.map (C ◁ g).left L) :=
  QuotientGroup.map_mk' _ _ _ _ L

lemma relPicMap_id (x : relPic C T) : relPicMap C (𝟙 T) x = x := by
  induction x using relPic.ind with
  | mk L =>
    rw [relPicMap_mk, MonoidalCategory.whiskerLeft_id, Over.id_left,
      Scheme.CechPic.map_id]
    rfl

lemma relPicMap_comp (g : T' ⟶ T) (h : T'' ⟶ T') (x : relPic C T) :
    relPicMap C (h ≫ g) x = relPicMap C h (relPicMap C g x) := by
  induction x using relPic.ind with
  | mk L =>
    rw [relPicMap_mk, relPicMap_mk, relPicMap_mk]
    refine congrArg (relPicMk C T'') ?_
    rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, ← Over.comp_left,
      ← MonoidalCategory.whiskerLeft_comp]

/-- The relative Picard functor `T ↦ Pic(C ⊗ T)/Pic(T)` of Grothendieck–Kleiman, as a
presheaf of commutative groups on `Over (Spec k)`. -/
noncomputable def relPicFunctor : (Over (Spec (.of k)))ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (relPic C T.unop)
  map g := CommGrpCat.ofHom (relPicMap C g.unop)
  map_id T := by
    ext x
    exact relPicMap_id C x
  map_comp g h := by
    ext x
    exact relPicMap_comp C g.unop h.unop x

@[simp]
lemma relPicFunctor_obj (T : (Over (Spec (.of k)))ᵒᵖ) :
    (relPicFunctor C).obj T = CommGrpCat.of (relPic C T.unop) :=
  rfl

@[simp]
lemma relPicFunctor_map {T T' : (Over (Spec (.of k)))ᵒᵖ} (g : T ⟶ T')
    (x : relPic C T.unop) :
    (relPicFunctor C).map g x = relPicMap C g.unop x :=
  rfl

/-! ## Naturality in the curve -/

variable {C} {C' C'' : Over (Spec (.of k))}

/-- Pullback of Čech classes along `g ▷ T` sends classes pulled back from `T` to classes
pulled back from `T`: well-definedness of the curve-direction map on the `H_T`-cosets. -/
lemma picFromBase_le_comap_whiskerRight (g : C' ⟶ C) (T : Over (Spec (.of k))) :
    picFromBase C T ≤ (picFromBase C' T).comap (CechPic.map (g ▷ T).left) := by
  rintro _ ⟨N, rfl⟩
  refine ⟨N, ?_⟩
  show CechPic.map (snd C' T).left N
      = CechPic.map (g ▷ T).left (CechPic.map (snd C T).left N)
  rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, ← Over.comp_left,
    whiskerRight_snd]

/-- Restriction of relative Picard classes along a morphism of curves `g : C' ⟶ C`,
at a fixed test object: pull back along `g ▷ T` and descend to the quotients. -/
noncomputable def relPicMapCurveApp (g : C' ⟶ C) (T : Over (Spec (.of k))) :
    relPic C T →* relPic C' T :=
  QuotientGroup.map (picFromBase C T) (picFromBase C' T)
    (CechPic.map (g ▷ T).left) (picFromBase_le_comap_whiskerRight g T)

@[simp]
lemma relPicMapCurveApp_mk (g : C' ⟶ C) (T : Over (Spec (.of k)))
    (L : (C ⊗ T).left.CechPic) :
    relPicMapCurveApp g T (relPicMk C T L)
      = relPicMk C' T (CechPic.map (g ▷ T).left L) :=
  QuotientGroup.map_mk' _ _ _ _ L

/-- Naturality of the relative Picard functor in the curve: a morphism of curves
`g : C' ⟶ C` induces a natural transformation `Pic_{C/k} ⟶ Pic_{C'/k}`. -/
noncomputable def relPicMapCurve (g : C' ⟶ C) :
    relPicFunctor C ⟶ relPicFunctor C' where
  app T := CommGrpCat.ofHom (relPicMapCurveApp g T.unop)
  naturality T T' t := by
    ext x
    induction x using relPic.ind with
    | mk L =>
      show relPicMapCurveApp g T'.unop (relPicMap C t.unop (relPicMk C T.unop L))
          = relPicMap C' t.unop (relPicMapCurveApp g T.unop (relPicMk C T.unop L))
      rw [relPicMap_mk, relPicMapCurveApp_mk, relPicMapCurveApp_mk, relPicMap_mk]
      refine congrArg (relPicMk C' T'.unop) ?_
      rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
        ← Scheme.CechPic.map_comp, ← Over.comp_left, ← Over.comp_left, whisker_exchange]

@[simp]
lemma relPicMapCurve_app_mk (g : C' ⟶ C) (T : (Over (Spec (.of k)))ᵒᵖ)
    (L : (C ⊗ T.unop).left.CechPic) :
    (relPicMapCurve g).app T (relPicMk C T.unop L)
      = relPicMk C' T.unop (CechPic.map (g ▷ T.unop).left L) :=
  relPicMapCurveApp_mk g T.unop L

/-- The curve-direction maps are strictly functorial: the identity morphism induces the
identity transformation. -/
lemma relPicMapCurve_id : relPicMapCurve (𝟙 C) = 𝟙 (relPicFunctor C) := by
  ext T x
  induction x using relPic.ind with
  | mk L =>
    show relPicMapCurveApp (𝟙 C) T.unop (relPicMk C T.unop L) = relPicMk C T.unop L
    rw [relPicMapCurveApp_mk, MonoidalCategory.id_whiskerRight, Over.id_left,
      Scheme.CechPic.map_id]
    rfl

/-- The curve-direction maps are strictly functorial: composition of curve morphisms
goes to composition of the induced transformations (contravariantly). -/
lemma relPicMapCurve_comp (g' : C'' ⟶ C') (g : C' ⟶ C) :
    relPicMapCurve (g' ≫ g) = relPicMapCurve g ≫ relPicMapCurve g' := by
  ext T x
  induction x using relPic.ind with
  | mk L =>
    show relPicMapCurveApp (g' ≫ g) T.unop (relPicMk C T.unop L)
        = relPicMapCurveApp g' T.unop (relPicMapCurveApp g T.unop (relPicMk C T.unop L))
    rw [relPicMapCurveApp_mk, relPicMapCurveApp_mk, relPicMapCurveApp_mk]
    refine congrArg (relPicMk C'' T.unop) ?_
    rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, ← Over.comp_left,
      ← MonoidalCategory.comp_whiskerRight]

end

end AlgebraicGeometry
