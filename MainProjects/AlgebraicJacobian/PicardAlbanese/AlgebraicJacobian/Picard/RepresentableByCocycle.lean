/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianData

/-!
# Canonical cocycles of representability isomorphisms

`Functor.RepresentableBy.uniqueUpToIso` is defined by Yoneda uniqueness, but mathlib does
not expose the two equations that descent data consume: its universal-element intertwining
formula and transitivity for three independently chosen representing objects.  These generic
lemmas make those equations explicit.  In particular, the transitivity theorem proves a
three-face cocycle without defining the `1,3` face as a composite.
-/

set_option autoImplicit false

universe v u u'

open CategoryTheory

namespace CategoryTheory.Functor.RepresentableBy

/-- Transport a representation through the right adjoint of an adjunction.

This is the categorical pullback step used for overlap bases: if `L ⊣ R`, then a
representation of `F` by `Y` induces one of `L.op ⋙ F` by `R.obj Y`.  The statement
requires only the adjunction; for schemes, `Over.mapPullbackAdj` supplies it whenever
the relevant pullbacks exist, including tensor-product (non-field) bases. -/
noncomputable def ofLeftAdjoint
    {C : Type u} {D : Type u'} [Category.{v, u} C] [Category.{v, u'} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {F : Dᵒᵖ ⥤ Type v} {Y : D} (e : F.RepresentableBy Y) :
    (L.op ⋙ F).RepresentableBy (R.obj Y) :=
  (adj.representableBy Y).ofIso (Functor.isoWhiskerLeft L.op e.toIso)

/-- The universal element of `ofLeftAdjoint` is obtained by applying the adjunction inverse. -/
theorem ofLeftAdjoint_homEquiv
    {C : Type u} {D : Type u'} [Category.{v, u} C] [Category.{v, u'} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {F : Dᵒᵖ ⥤ Type v} {Y : D} (e : F.RepresentableBy Y)
    {X : C} (g : X ⟶ R.obj Y) :
    (ofLeftAdjoint adj e).homEquiv g = e.homEquiv ((adj.homEquiv X Y).symm g) := by
  rfl

/-- Compare representations of two isomorphic presheaves.

The source representation is first transported along `η`; the comparison is then the ordinary
Yoneda comparison.  This is the canonical overlap isomorphism once the two pullback Picard
presheaves have been identified. -/
noncomputable def uniqueUpToIsoOfIso
    {C : Type u} [Category.{v, u} C]
    {F F' : Cᵒᵖ ⥤ Type v} {Y Y' : C}
    (e : F.RepresentableBy Y) (e' : F'.RepresentableBy Y') (η : F ≅ F') : Y ≅ Y' :=
  (e.ofIso η).uniqueUpToIso e'

/-- The comparison in `uniqueUpToIsoOfIso` intertwines the two universal elements. -/
theorem homEquiv_uniqueUpToIsoOfIso_hom
    {C : Type u} [Category.{v, u} C]
    {F F' : Cᵒᵖ ⥤ Type v} {Y Y' : C}
    (e : F.RepresentableBy Y) (e' : F'.RepresentableBy Y') (η : F ≅ F')
    {X : C} (f : X ⟶ Y) :
    e'.homEquiv (f ≫ (uniqueUpToIsoOfIso e e' η).hom) =
      η.hom.app (Opposite.op X) (e.homEquiv f) := by
  change e'.homEquiv (f ≫ ((e.ofIso η).uniqueUpToIso e').hom) =
    (e.ofIso η).homEquiv f
  have h : ((e.ofIso η).uniqueUpToIso e').hom =
      e'.homEquiv.symm ((e.ofIso η).homEquiv (𝟙 Y)) := rfl
  rw [h, comp_homEquiv_symm, Equiv.apply_symm_apply]
  rw [← (e.ofIso η).homEquiv_comp f (𝟙 Y), Category.comp_id]

/-- Transporting a representation across conjugate adjunctions produces the conjugate
right-adjoint isomorphism on the representing object. -/
theorem uniqueUpToIsoOfIso_ofLeftAdjoint_conjugate
    {C : Type u} {D : Type u'} [Category.{v, u} C] [Category.{v, u'} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ≅ L₁)
    {F : Dᵒᵖ ⥤ Type v} {Y : D} (e : F.RepresentableBy Y) :
    uniqueUpToIsoOfIso
      (ofLeftAdjoint adj₁ e)
      (ofLeftAdjoint adj₂ e)
      (Functor.isoWhiskerRight (NatIso.op α) F) =
      (conjugateIsoEquiv adj₁ adj₂ α).app Y := by
  let e₁ := ofLeftAdjoint adj₁ e
  let e₂ := ofLeftAdjoint adj₂ e
  apply Iso.ext
  apply e₂.homEquiv.injective
  have h : (adj₂.homEquiv (R₁.obj Y) Y).symm
      ((conjugateIsoEquiv adj₁ adj₂ α).app Y).hom =
      α.hom.app (R₁.obj Y) ≫ adj₁.counit.app Y := by
    apply (adj₂.homEquiv (R₁.obj Y) Y).injective
    rw [Equiv.apply_symm_apply]
    have hc := conjugateEquiv_counit adj₁ adj₂ α.hom Y
    have hn := adj₂.homEquiv_naturality_left
      (X' := R₁.obj Y) (X := R₂.obj Y) (Y := Y)
      ((conjugateEquiv adj₁ adj₂ α.hom).app Y) (adj₂.counit.app Y)
    have hunit : (adj₂.homEquiv (R₂.obj Y) Y) (adj₂.counit.app Y) =
        𝟙 (R₂.obj Y) := by
      have hh := adj₂.homEquiv_counit (R₂.obj Y) Y (𝟙 (R₂.obj Y))
      have hh' := congrArg (adj₂.homEquiv (R₂.obj Y) Y) hh
      simpa using hh'.symm
    change (conjugateEquiv adj₁ adj₂ α.hom).app Y = _
    calc
      (conjugateEquiv adj₁ adj₂ α.hom).app Y =
          (conjugateEquiv adj₁ adj₂ α.hom).app Y ≫ 𝟙 _ := by simp
      _ = (conjugateEquiv adj₁ adj₂ α.hom).app Y ≫
          (adj₂.homEquiv (R₂.obj Y) Y) (adj₂.counit.app Y) := by
        rw [hunit, Category.comp_id]
      _ = (adj₂.homEquiv (R₁.obj Y) Y)
          (L₂.map ((conjugateEquiv adj₁ adj₂ α.hom).app Y) ≫ adj₂.counit.app Y) :=
        hn.symm
      _ = (adj₂.homEquiv (R₁.obj Y) Y)
          (α.hom.app (R₁.obj Y) ≫ adj₁.counit.app Y) := by
        exact congrArg (adj₂.homEquiv (R₁.obj Y) Y) hc
  calc
    e₂.homEquiv
        (uniqueUpToIsoOfIso e₁ e₂
          (Functor.isoWhiskerRight (NatIso.op α) F)).hom =
      (Functor.isoWhiskerRight (NatIso.op α) F).hom.app
          (Opposite.op (R₁.obj Y)) (e₁.homEquiv (𝟙 _)) := by
      simpa using homEquiv_uniqueUpToIsoOfIso_hom
        e₁ e₂ (Functor.isoWhiskerRight (NatIso.op α) F) (𝟙 _)
    _ = e.homEquiv (α.hom.app (R₁.obj Y) ≫ adj₁.counit.app Y) := by
      simp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
      dsimp [e₁]
      rw [ofLeftAdjoint_homEquiv]
      have hunit : (adj₁.homEquiv (R₁.obj Y) Y).symm (𝟙 (R₁.obj Y)) =
          adj₁.counit.app Y := by
        have hh := adj₁.homEquiv_counit (R₁.obj Y) Y (𝟙 (R₁.obj Y))
        simpa using hh
      rw [hunit]
      change (ConcreteCategory.hom (F.map (α.hom.app (R₁.obj Y)).op))
          (e.homEquiv (adj₁.counit.app Y)) =
        e.homEquiv (α.hom.app (R₁.obj Y) ≫ adj₁.counit.app Y)
      exact (e.homEquiv_comp
        (α.hom.app (R₁.obj Y)) (adj₁.counit.app Y)).symm
    _ = e₂.homEquiv ((conjugateIsoEquiv adj₁ adj₂ α).app Y).hom := by
      rw [ofLeftAdjoint_homEquiv, h]
      rfl

/-- Applying one adjunction to two representations carries their canonical comparison
to the image of the original comparison under the right adjoint. -/
theorem uniqueUpToIsoOfIso_ofLeftAdjoint_mapIso
    {C : Type u} {D : Type u'} [Category.{v, u} C] [Category.{v, u'} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {F F' : Dᵒᵖ ⥤ Type v} {Y Y' : D}
    (e : F.RepresentableBy Y) (e' : F'.RepresentableBy Y') (η : F ≅ F') :
    uniqueUpToIsoOfIso
      (ofLeftAdjoint adj e)
      (ofLeftAdjoint adj e')
      (Functor.isoWhiskerLeft L.op η) =
      R.mapIso (uniqueUpToIsoOfIso e e' η) := by
  apply Iso.ext
  apply (ofLeftAdjoint adj e').homEquiv.injective
  calc
    (ofLeftAdjoint adj e').homEquiv
        ((uniqueUpToIsoOfIso
          (ofLeftAdjoint adj e)
          (ofLeftAdjoint adj e')
          (Functor.isoWhiskerLeft L.op η)).hom) =
      (Functor.isoWhiskerLeft L.op η).hom.app
        (Opposite.op (R.obj Y))
        ((ofLeftAdjoint adj e).homEquiv (𝟙 _)) := by
      simpa using homEquiv_uniqueUpToIsoOfIso_hom
        (ofLeftAdjoint adj e)
        (ofLeftAdjoint adj e')
        (Functor.isoWhiskerLeft L.op η) (𝟙 _)
    _ = (ofLeftAdjoint adj e').homEquiv
        (R.mapIso (uniqueUpToIsoOfIso e e' η)).hom := by
      change (ConcreteCategory.hom
          (η.hom.app (L.op.obj (Opposite.op (R.obj Y)))))
          (e.homEquiv ((adj.homEquiv (R.obj Y) Y).symm (𝟙 _))) =
        e'.homEquiv ((adj.homEquiv (R.obj Y) Y').symm
          (R.map (uniqueUpToIsoOfIso e e' η).hom))
      rw [show (adj.homEquiv (R.obj Y) Y').symm
          (R.map (uniqueUpToIsoOfIso e e' η).hom) =
        (adj.homEquiv (R.obj Y) Y).symm (𝟙 _) ≫
          (uniqueUpToIsoOfIso e e' η).hom by
        simpa using adj.homEquiv_naturality_right_symm
          (𝟙 (R.obj Y)) (uniqueUpToIsoOfIso e e' η).hom]
      symm
      exact homEquiv_uniqueUpToIsoOfIso_hom e e' η
        ((adj.homEquiv (R.obj Y) Y).symm (𝟙 _))

/-- The canonical comparison for the inverse presheaf isomorphism is the inverse
of the original comparison. -/
theorem uniqueUpToIsoOfIso_symm
    {C : Type u} [Category.{v, u} C]
    {F F' : Cᵒᵖ ⥤ Type v} {Y Y' : C}
    (e : F.RepresentableBy Y) (e' : F'.RepresentableBy Y') (η : F ≅ F') :
    (uniqueUpToIsoOfIso e e' η).symm =
      uniqueUpToIsoOfIso e' e η.symm := by
  let u := uniqueUpToIsoOfIso e e' η
  let v := uniqueUpToIsoOfIso e' e η.symm
  apply Iso.ext
  change u.inv = v.hom
  apply (cancel_mono u.hom).1
  have hvu : v.hom ≫ u.hom = 𝟙 _ := by
    apply e'.homEquiv.injective
    calc
      e'.homEquiv (v.hom ≫ u.hom) =
          η.hom.app (Opposite.op Y')
            (e.homEquiv v.hom) := by
        simpa [u, v] using
          homEquiv_uniqueUpToIsoOfIso_hom e e' η v.hom
      _ = η.hom.app (Opposite.op Y')
          (η.inv.app (Opposite.op Y') (e'.homEquiv (𝟙 _))) := by
        rw [show e.homEquiv v.hom =
            η.inv.app (Opposite.op Y') (e'.homEquiv (𝟙 _)) by
          simpa [v] using
            homEquiv_uniqueUpToIsoOfIso_hom e' e η.symm (𝟙 Y')]
      _ = e'.homEquiv (𝟙 _) := by
        have hh := η.inv_hom_id_app (Opposite.op Y')
        exact congrArg (fun f => f (e'.homEquiv (𝟙 _))) hh
  calc
    u.inv ≫ u.hom = 𝟙 _ := u.inv_hom_id
    _ = v.hom ≫ u.hom := hvu.symm

/-- Transport through a composite adjunction is the same representation as transport
through the two adjunctions successively. -/
theorem ofLeftAdjoint_comp
    {C : Type u} {D E : Type u'} [Category.{v, u} C]
    [Category.{v, u'} D] [Category.{v, u'} E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {F : Eᵒᵖ ⥤ Type v} {Y : E} (e : F.RepresentableBy Y) :
    ofLeftAdjoint (adj₁.comp adj₂) e =
      ofLeftAdjoint adj₁ (ofLeftAdjoint adj₂ e) := by
  apply RepresentableBy.ext
  change e.homEquiv
      (((adj₁.comp adj₂).homEquiv ((R₂ ⋙ R₁).obj Y) Y).symm (𝟙 _)) =
    e.homEquiv ((adj₂.homEquiv (L₁.obj ((R₂ ⋙ R₁).obj Y)) Y).symm
      ((adj₁.homEquiv ((R₂ ⋙ R₁).obj Y) (R₂.obj Y)).symm (𝟙 _)))
  rw [Adjunction.comp_homEquiv]
  rfl

open Limits
/-- For over-categories, the canonical comparison between direct and iterated
adjunction transport is mathlib's `Over.pullbackComp`. -/
theorem uniqueUpToIsoOfIso_pullbackComp
    {D : Type u} [Category.{v, u} D] [HasPullbacks D]
    {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    {F : (Over Z)ᵒᵖ ⥤ Type v} {J : Over Z} (e : F.RepresentableBy J) :
    uniqueUpToIsoOfIso
      (ofLeftAdjoint (Over.mapPullbackAdj (f ≫ g)) e)
      (ofLeftAdjoint (Over.mapPullbackAdj f)
        (ofLeftAdjoint (Over.mapPullbackAdj g) e))
      (Functor.isoWhiskerRight
        (NatIso.op (Over.mapComp f g).symm) F) =
      (Over.pullbackComp f g).app J := by
  rw [← ofLeftAdjoint_comp]
  exact uniqueUpToIsoOfIso_ofLeftAdjoint_conjugate
    (Over.mapPullbackAdj (f ≫ g))
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapComp f g).symm e

/-- The presheaf-level composite comparison with an explicit equality of base maps. -/
noncomputable def Over.mapCompPresheafOfEq
    {D : Type u} [Category.{v, u} D]
    {X Y Z : D} (r : X ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : r = f ≫ g) (F : (Over Z)ᵒᵖ ⥤ Type v) :
    (Over.map r).op ⋙ F ≅
      (Over.map f).op ⋙ ((Over.map g).op ⋙ F) :=
  eqToIso (congrArg (fun m => (Over.map m).op ⋙ F) h) ≪≫
    Functor.isoWhiskerRight (NatIso.op (Over.mapComp f g)).symm F

/-- The scheme-level composite pullback comparison with an explicit equality of base maps. -/
noncomputable def Over.pullbackCompOfEq
    {D : Type u} [Category.{v, u} D] [HasPullbacks D]
    {X Y Z : D} (r : X ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : r = f ≫ g) (J : Over Z) :
    (Over.pullback r).obj J ≅
      (Over.pullback f).obj ((Over.pullback g).obj J) :=
  eqToIso (congrArg (fun m => (Over.pullback m).obj J) h) ≪≫
    (Over.pullbackComp f g).app J

/-- The canonical representation comparison remains `pullbackComp` after an explicit
proof-bearing equality identifies the direct map with a composite. -/
theorem uniqueUpToIsoOfIso_pullbackComp_of_eq
    {D : Type u} [Category.{v, u} D] [HasPullbacks D]
    {X Y Z : D} (r : X ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : r = f ≫ g) {F : (Over Z)ᵒᵖ ⥤ Type v} {J : Over Z}
    (e : F.RepresentableBy J) :
    uniqueUpToIsoOfIso
      (ofLeftAdjoint (Over.mapPullbackAdj r) e)
      (ofLeftAdjoint (Over.mapPullbackAdj f)
        (ofLeftAdjoint (Over.mapPullbackAdj g) e))
      (Over.mapCompPresheafOfEq r f g h F) =
      Over.pullbackCompOfEq r f g h J := by
  subst r
  simpa [Over.mapCompPresheafOfEq, Over.pullbackCompOfEq] using
    (uniqueUpToIsoOfIso_pullbackComp f g e)

/-- Three canonical comparisons satisfy the cocycle law when the presheaf isomorphisms do. -/
theorem uniqueUpToIsoOfIso_trans
    {C : Type u} [Category.{v, u} C]
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ Type v} {Y₁ Y₂ Y₃ : C}
    (e₁ : F₁.RepresentableBy Y₁) (e₂ : F₂.RepresentableBy Y₂)
    (e₃ : F₃.RepresentableBy Y₃)
    (η₁₂ : F₁ ≅ F₂) (η₂₃ : F₂ ≅ F₃) (η₁₃ : F₁ ≅ F₃)
    (hη : η₁₃ = η₁₂ ≪≫ η₂₃) :
    uniqueUpToIsoOfIso e₁ e₃ η₁₃ =
      uniqueUpToIsoOfIso e₁ e₂ η₁₂ ≪≫ uniqueUpToIsoOfIso e₂ e₃ η₂₃ := by
  apply Iso.ext
  apply e₃.homEquiv.injective
  calc
    e₃.homEquiv (uniqueUpToIsoOfIso e₁ e₃ η₁₃).hom =
        η₁₃.hom.app (Opposite.op Y₁) (e₁.homEquiv (𝟙 Y₁)) := by
      simpa using homEquiv_uniqueUpToIsoOfIso_hom e₁ e₃ η₁₃ (𝟙 Y₁)
    _ = η₂₃.hom.app (Opposite.op Y₁)
        (η₁₂.hom.app (Opposite.op Y₁) (e₁.homEquiv (𝟙 Y₁))) := by
      rw [hη]
      rfl
    _ = e₃.homEquiv ((uniqueUpToIsoOfIso e₁ e₂ η₁₂).hom ≫
        (uniqueUpToIsoOfIso e₂ e₃ η₂₃).hom) := by
      rw [homEquiv_uniqueUpToIsoOfIso_hom e₂ e₃ η₂₃]
      rw [← Category.id_comp (uniqueUpToIsoOfIso e₁ e₂ η₁₂).hom,
        homEquiv_uniqueUpToIsoOfIso_hom e₁ e₂ η₁₂]

/-- Assemble a direct presheaf comparison from a common outer pullback and an inner
presheaf comparison. -/
noncomputable def Over.mapCompPresheafFace
    {D : Type u} [Category.{v, u} D]
    {X Y Z : D} (r₀ r₁ : X ⟶ Z) (q : X ⟶ Y)
    (p₀ p₁ : Y ⟶ Z) (h₀ : r₀ = q ≫ p₀) (h₁ : r₁ = q ≫ p₁)
    {F : (Over Z)ᵒᵖ ⥤ Type v}
    (θ : (Over.map p₀).op ⋙ F ≅ (Over.map p₁).op ⋙ F) :
    (Over.map r₀).op ⋙ F ≅ (Over.map r₁).op ⋙ F :=
  Over.mapCompPresheafOfEq r₀ q p₀ h₀ F ≪≫
    Functor.isoWhiskerLeft (Over.map q).op θ ≪≫
    (Over.mapCompPresheafOfEq r₁ q p₁ h₁ F).symm

/-- Assemble the corresponding scheme comparison from an inner scheme isomorphism. -/
noncomputable def Over.pullbackFaceIsoOfEq
    {D : Type u} [Category.{v, u} D] [HasPullbacks D]
    {X Y Z : D} (r₀ r₁ : X ⟶ Z) (q : X ⟶ Y)
    (p₀ p₁ : Y ⟶ Z) (h₀ : r₀ = q ≫ p₀) (h₁ : r₁ = q ≫ p₁)
    {J : Over Z} (i : (Over.pullback p₀).obj J ≅ (Over.pullback p₁).obj J) :
    (Over.pullback r₀).obj J ≅ (Over.pullback r₁).obj J :=
  Over.pullbackCompOfEq r₀ q p₀ h₀ J ≪≫
    Functor.mapIso (Over.pullback q) i ≪≫
    (Over.pullbackCompOfEq r₁ q p₁ h₁ J).symm

/-- The Yoneda comparison for a direct face is exactly the raw pullback comparison
through the common outer map. -/
theorem uniqueUpToIsoOfIso_pullbackFace
    {D : Type u} [Category.{v, u} D] [HasPullbacks D]
    {X Y Z : D} (r₀ r₁ : X ⟶ Z) (q : X ⟶ Y)
    (p₀ p₁ : Y ⟶ Z) (h₀ : r₀ = q ≫ p₀) (h₁ : r₁ = q ≫ p₁)
    {F : (Over Z)ᵒᵖ ⥤ Type v} {J : Over Z} (e : F.RepresentableBy J)
    (θ : (Over.map p₀).op ⋙ F ≅ (Over.map p₁).op ⋙ F) :
    uniqueUpToIsoOfIso
      (ofLeftAdjoint (Over.mapPullbackAdj r₀) e)
      (ofLeftAdjoint (Over.mapPullbackAdj r₁) e)
      (Over.mapCompPresheafFace r₀ r₁ q p₀ p₁ h₀ h₁ θ) =
      Over.pullbackFaceIsoOfEq r₀ r₁ q p₀ p₁ h₀ h₁
        (uniqueUpToIsoOfIso
          (ofLeftAdjoint (Over.mapPullbackAdj p₀) e)
          (ofLeftAdjoint (Over.mapPullbackAdj p₁) e) θ) := by
  let e₀ := ofLeftAdjoint (Over.mapPullbackAdj p₀) e
  let e₁ := ofLeftAdjoint (Over.mapPullbackAdj p₁) e
  let d₀ := ofLeftAdjoint (Over.mapPullbackAdj r₀) e
  let d₁ := ofLeftAdjoint (Over.mapPullbackAdj r₁) e
  let i₀ := ofLeftAdjoint (Over.mapPullbackAdj q) e₀
  let i₁ := ofLeftAdjoint (Over.mapPullbackAdj q) e₁
  have h₀' :
      uniqueUpToIsoOfIso d₀ i₀
          (Over.mapCompPresheafOfEq r₀ q p₀ h₀ F) =
        Over.pullbackCompOfEq r₀ q p₀ h₀ J := by
    simpa [d₀, i₀] using
      (uniqueUpToIsoOfIso_pullbackComp_of_eq r₀ q p₀ h₀ e)
  have h₁' :
      uniqueUpToIsoOfIso i₁ d₁
          (Over.mapCompPresheafOfEq r₁ q p₁ h₁ F).symm =
        (Over.pullbackCompOfEq r₁ q p₁ h₁ J).symm := by
    have hh := uniqueUpToIsoOfIso_pullbackComp_of_eq r₁ q p₁ h₁ e
    calc
      uniqueUpToIsoOfIso i₁ d₁
          (Over.mapCompPresheafOfEq r₁ q p₁ h₁ F).symm =
          (uniqueUpToIsoOfIso d₁ i₁
            (Over.mapCompPresheafOfEq r₁ q p₁ h₁ F)).symm := by
        exact (uniqueUpToIsoOfIso_symm d₁ i₁
          (Over.mapCompPresheafOfEq r₁ q p₁ h₁ F)).symm
      _ = (Over.pullbackCompOfEq r₁ q p₁ h₁ J).symm :=
        congrArg Iso.symm hh
  have hm :
      uniqueUpToIsoOfIso i₀ i₁ (Functor.isoWhiskerLeft (Over.map q).op θ) =
        Functor.mapIso (Over.pullback q)
          (uniqueUpToIsoOfIso e₀ e₁ θ) := by
    simpa [i₀, i₁] using
      (uniqueUpToIsoOfIso_ofLeftAdjoint_mapIso
        (Over.mapPullbackAdj q) e₀ e₁ θ)
  have hleft :
      uniqueUpToIsoOfIso d₀ i₁
          (Over.mapCompPresheafOfEq r₀ q p₀ h₀ F ≪≫
            Functor.isoWhiskerLeft (Over.map q).op θ) =
        Over.pullbackCompOfEq r₀ q p₀ h₀ J ≪≫
          Functor.mapIso (Over.pullback q)
            (uniqueUpToIsoOfIso e₀ e₁ θ) := by
    calc
      uniqueUpToIsoOfIso d₀ i₁
          (Over.mapCompPresheafOfEq r₀ q p₀ h₀ F ≪≫
            Functor.isoWhiskerLeft (Over.map q).op θ) =
          uniqueUpToIsoOfIso d₀ i₀
            (Over.mapCompPresheafOfEq r₀ q p₀ h₀ F) ≪≫
          uniqueUpToIsoOfIso i₀ i₁
            (Functor.isoWhiskerLeft (Over.map q).op θ) :=
        uniqueUpToIsoOfIso_trans d₀ i₀ i₁
          (Over.mapCompPresheafOfEq r₀ q p₀ h₀ F)
          (Functor.isoWhiskerLeft (Over.map q).op θ)
          (Over.mapCompPresheafOfEq r₀ q p₀ h₀ F ≪≫
            Functor.isoWhiskerLeft (Over.map q).op θ) rfl
      _ = _ := by rw [h₀', hm]
  calc
    uniqueUpToIsoOfIso d₀ d₁
        (Over.mapCompPresheafFace r₀ r₁ q p₀ p₁ h₀ h₁ θ) =
        uniqueUpToIsoOfIso d₀ i₁
          (Over.mapCompPresheafOfEq r₀ q p₀ h₀ F ≪≫
            Functor.isoWhiskerLeft (Over.map q).op θ) ≪≫
        uniqueUpToIsoOfIso i₁ d₁
          (Over.mapCompPresheafOfEq r₁ q p₁ h₁ F).symm :=
      uniqueUpToIsoOfIso_trans d₀ i₁ d₁
        (Over.mapCompPresheafOfEq r₀ q p₀ h₀ F ≪≫
          Functor.isoWhiskerLeft (Over.map q).op θ)
        (Over.mapCompPresheafOfEq r₁ q p₁ h₁ F).symm
        (Over.mapCompPresheafFace r₀ r₁ q p₀ p₁ h₀ h₁ θ) rfl
    _ = Over.pullbackFaceIsoOfEq r₀ r₁ q p₀ p₁ h₀ h₁
        (uniqueUpToIsoOfIso e₀ e₁ θ) := by
      rw [hleft, h₁']
      simp only [Over.pullbackFaceIsoOfEq, Iso.trans_assoc]

/-- Composition with the canonical representing-object isomorphism transports the universal
element unchanged. -/
theorem homEquiv_uniqueUpToIso_hom {C : Type u} [Category.{v, u} C]
    {F : Cᵒᵖ ⥤ Type v} {Y Y' : C} (e : F.RepresentableBy Y)
    (e' : F.RepresentableBy Y') {X : C} (f : X ⟶ Y) :
    e'.homEquiv (f ≫ (e.uniqueUpToIso e').hom) = e.homEquiv f := by
  have h : (e.uniqueUpToIso e').hom =
      e'.homEquiv.symm (e.homEquiv (𝟙 Y)) := rfl
  rw [h, comp_homEquiv_symm, Equiv.apply_symm_apply]
  rw [← e.homEquiv_comp f (𝟙 Y), Category.comp_id]

/-- The canonical isomorphisms between three representations satisfy the cocycle law.  The
`1,3` comparison is the independently defined `uniqueUpToIso e₁ e₃`, not a composite alias. -/
theorem uniqueUpToIso_trans {C : Type u} [Category.{v, u} C]
    {F : Cᵒᵖ ⥤ Type v} {Y₁ Y₂ Y₃ : C}
    (e₁ : F.RepresentableBy Y₁) (e₂ : F.RepresentableBy Y₂)
    (e₃ : F.RepresentableBy Y₃) :
    e₁.uniqueUpToIso e₃ = e₁.uniqueUpToIso e₂ ≪≫ e₂.uniqueUpToIso e₃ := by
  apply Iso.ext
  apply e₃.homEquiv.injective
  calc
    e₃.homEquiv (e₁.uniqueUpToIso e₃).hom = e₁.homEquiv (𝟙 Y₁) := by
      simpa using homEquiv_uniqueUpToIso_hom e₁ e₃ (𝟙 Y₁)
    _ = e₂.homEquiv (e₁.uniqueUpToIso e₂).hom := by
      symm
      simpa using homEquiv_uniqueUpToIso_hom e₁ e₂ (𝟙 Y₁)
    _ = e₃.homEquiv
        ((e₁.uniqueUpToIso e₂).hom ≫ (e₂.uniqueUpToIso e₃).hom) := by
      symm
      exact homEquiv_uniqueUpToIso_hom e₂ e₃ (e₁.uniqueUpToIso e₂).hom

end CategoryTheory.Functor.RepresentableBy
