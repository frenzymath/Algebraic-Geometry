/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Group.Smooth

/-!
# Group schemes and translations

This file records the group-object part of Mumford's definition of an abelian
variety.  A section of a group scheme can be moved to any other section by a
canonical right translation.  The construction is completely categorical, so
the same lemmas are available for group objects in any cartesian monoidal
category.

The final predicate keeps the geometric hypotheses used by the standard
commutativity theorem visible: a proper geometrically integral group scheme
over a field is commutative.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace Mumford

namespace GroupScheme

section Categorical

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G] {X : C}

/-- The cartesian identity underlying the rigidity lemma: collapsing the first
variable to a chosen point can be written using either projection. -/
theorem rigidity_snd_lift
    {X Y : C} (x₀ : 𝟙_ C ⟶ X) :
    snd X Y ≫ lift (toUnit Y ≫ x₀) (𝟙 Y) =
      lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) := by
  ext1 <;> simp

/- A categorical factorization form of the rigidity step.  Invariance under
   replacing the first coordinate by `x₀` is equivalent to factoring through
   the second projection. -/
theorem factors_through_snd_iff
    {X Y Z : C} (x₀ : 𝟙_ C ⟶ X) (f : X ⊗ Y ⟶ Z) :
    (∃ g : Y ⟶ Z, f = snd X Y ≫ g) ↔
      lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) ≫ f = f := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [← rigidity_snd_lift x₀]
    simp
  · intro h
    refine ⟨lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f, ?_⟩
    calc
      f = lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) ≫ f := h.symm
      _ = (snd X Y ≫ lift (toUnit Y ≫ x₀) (𝟙 Y)) ≫ f := by
        rw [rigidity_snd_lift x₀]
      _ = snd X Y ≫ (lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f) :=
        Category.assoc _ _ _

/-- The factor through the second projection is unique. -/
theorem factor_through_snd_unique
    {X Y Z : C} (x₀ : 𝟙_ C ⟶ X) (f : X ⊗ Y ⟶ Z)
    {g₁ g₂ : Y ⟶ Z} (h₁ : f = snd X Y ≫ g₁)
    (h₂ : f = snd X Y ≫ g₂) : g₁ = g₂ := by
  have h := congrArg (fun q => lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ q)
    (h₁.symm.trans h₂)
  simpa using h

/-- The rigidity factorization can be stated with a unique factor. -/
theorem existsUnique_factor_through_snd_iff
    {X Y Z : C} (x₀ : 𝟙_ C ⟶ X) (f : X ⊗ Y ⟶ Z) :
    (∃! g : Y ⟶ Z, f = snd X Y ≫ g) ↔
      lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) ≫ f = f := by
  constructor
  · rintro ⟨g, hg, _⟩
    exact (factors_through_snd_iff x₀ f).mp ⟨g, hg⟩
  · intro h
    have hex : ∃ g : Y ⟶ Z, f = snd X Y ≫ g :=
      (factors_through_snd_iff x₀ f).mpr h
    obtain ⟨g, hg⟩ := hex
    refine ⟨g, hg, ?_⟩
    intro g' hg'
    exact factor_through_snd_unique x₀ f hg' hg

/-- The group-valued functor of points of a group object. -/
abbrev pointsFunctor (G : C) [GrpObj G] : Cᵒᵖ ⥤ GrpCat :=
  CategoryTheory.yonedaGrpObj G

/-- The functor of points is represented by the underlying group object. -/
def pointsFunctor_representable (G : C) [GrpObj G] :
    (pointsFunctor G ⋙ CategoryTheory.forget GrpCat).RepresentableBy G :=
  CategoryTheory.yonedaGrpObjRepresentableBy G

/-- The Yoneda functor from group objects to group-valued functors is fully faithful. -/
def pointsYoneda : Grp C ⥤ Cᵒᵖ ⥤ GrpCat :=
  CategoryTheory.yonedaGrp

def pointsYoneda_fullyFaithful : (pointsYoneda (C := C)).FullyFaithful :=
  CategoryTheory.yonedaGrpFullyFaithful

/-- Composition with a right translation is multiplication in the Hom-group. -/
theorem comp_mulRight_hom (f : X ⟶ G) (g : 𝟙_ C ⟶ G) :
    f ≫ (GrpObj.mulRight g).hom = f * (toUnit X ≫ g) := by
  rw [GrpObj.mulRight_hom, comp_lift_assoc, Category.comp_id,
    comp_toUnit_assoc, CategoryTheory.Hom.mul_def]

/-- Composition with the inverse right translation is multiplication by the inverse. -/
theorem comp_mulRight_inv (f : X ⟶ G) (g : 𝟙_ C ⟶ G) :
    f ≫ (GrpObj.mulRight g).inv = f * (toUnit X ≫ g)⁻¹ := by
  rw [GrpObj.mulRight_inv, comp_lift_assoc, Category.comp_id,
    ← Category.assoc, comp_toUnit, CategoryTheory.Hom.mul_def,
    CategoryTheory.Hom.inv_def, Category.assoc]

/-- The translation carrying the section `x` to the section `y`. -/
def pointTranslation (G : C) [GrpObj G] (x y : 𝟙_ C ⟶ G) : G ≅ G :=
  (GrpObj.mulRight x).symm ≪≫ GrpObj.mulRight y

@[simp]
theorem pointTranslation_self (x : 𝟙_ C ⟶ G) :
    pointTranslation G x x = Iso.refl G := by
  simp [pointTranslation]

@[simp]
theorem pointTranslation_symm (x y : 𝟙_ C ⟶ G) :
    (pointTranslation G x y).symm = pointTranslation G y x := by
  simp [pointTranslation]

@[simp]
theorem pointTranslation_trans (x y z : 𝟙_ C ⟶ G) :
    pointTranslation G x y ≪≫ pointTranslation G y z = pointTranslation G x z := by
  simp [pointTranslation, Iso.trans_assoc]

@[reassoc (attr := simp)]
theorem comp_pointTranslation_hom (x y : 𝟙_ C ⟶ G) :
    x ≫ (pointTranslation G x y).hom = y := by
  rw [pointTranslation, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    comp_mulRight_inv, comp_mulRight_hom, toUnit_unit,
    Category.id_comp, Category.id_comp, mul_inv_cancel, _root_.one_mul]

/- The inverse translation carries `y` back to `x`; keeping this as a named
   simp lemma avoids repeating the symmetry rewrite at geometric use sites. -/
@[reassoc (attr := simp)]
theorem comp_pointTranslation_inv (x y : 𝟙_ C ⟶ G) :
    y ≫ (pointTranslation G x y).inv = x := by
  exact comp_pointTranslation_hom (G := G) y x

end Categorical

section RigidityGeometry

open AlgebraicGeometry

variable {kbar : Type u} [Field kbar]

/- Geometric integrality of both factors gives the integral source needed by
   the rigidity argument.  The tensor object is definitionally the scheme
   pullback, so the standard pullback instance applies once the first factor's
   integrality and local noetherianity have been exposed. -/
theorem isIntegral_tensorObj_left_of_geometricallyIntegral
    {X Y : Over (Spec (.of kbar))}
    [GeometricallyIntegral X.hom] [GeometricallyIntegral Y.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    IsIntegral (X ⊗ Y).left := by
  have hX : IsIntegral X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  have hNoeth : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact inferInstanceAs (IsIntegral (pullback X.hom Y.hom))

/-- Properness of the first factor makes the second projection a closed map.

The underlying scheme morphism is the pullback of `X.hom` along `Y.hom`; this
is the geometric input used in the closed-map proof of Mumford's rigidity
lemma. -/
theorem snd_left_isClosedMap
    {X Y : Over (Spec (.of kbar))} [IsProper X.hom] :
    IsClosedMap (snd X Y).left.base := by
  haveI hp : UniversallyClosed X.hom := IsProper.toUniversallyClosed
  haveI : UniversallyClosed (snd X Y).left := by
    rw [Over.snd_left]
    exact universallyClosed_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback X.hom Y.hom) hp
  exact Scheme.Hom.isClosedMap _

end RigidityGeometry

section ClosedPointExtensionality

open AlgebraicGeometry

variable {W Z : Scheme.{u}} [IsReduced W] [JacobsonSpace W] [Z.IsSeparated]

/-- Two morphisms from a reduced Jacobson scheme into a separated scheme are
equal when their residue-field probes agree at every closed point. -/
theorem morphism_eq_of_eqAt_closedPoints
    {g₁ g₂ : W ⟶ Z}
    (h : ∀ x ∈ closedPoints W,
      W.fromSpecResidueField x ≫ g₁ = W.fromSpecResidueField x ≫ g₂) :
    g₁ = g₂ := by
  let F : closedPoints W → Scheme.{u} := fun x => Spec (W.residueField x.1)
  let probe : (∐ F) ⟶ W := Sigma.desc fun x => W.fromSpecResidueField x.1
  haveI : IsDominant probe := by
    refine ⟨(dense_iff_closure_eq.mpr (closure_closedPoints (X := W))).mono ?_⟩
    intro x hx
    obtain ⟨pt⟩ : Nonempty (Spec (W.residueField x)) := inferInstance
    refine ⟨(Sigma.ι F ⟨x, hx⟩).base pt, ?_⟩
    have hcomp : Sigma.ι F ⟨x, hx⟩ ≫ probe = W.fromSpecResidueField x :=
      Sigma.ι_desc _ _
    have e1 : probe.base ((Sigma.ι F ⟨x, hx⟩).base pt) =
        (W.fromSpecResidueField x).base pt := by
      rw [← Scheme.Hom.comp_apply, hcomp]
    rw [e1]
    exact Set.eq_of_mem_singleton
      (Scheme.range_fromSpecResidueField x ▸ Set.mem_range_self pt)
  refine ext_of_isDominant probe (Sigma.hom_ext _ _ fun x => ?_)
  rw [← Category.assoc, ← Category.assoc, Sigma.ι_desc]
  exact h x.1 x.2

end ClosedPointExtensionality

section ProperAffineConstancy

open AlgebraicGeometry

variable {kbar : Type u} [Field kbar]

/-! A proper integral scheme over an algebraically closed field has no
nonconstant maps to an affine scheme.  This is the slice-constancy bridge in
Form I of the rigidity lemma. -/

theorem eq_comp_of_isAffine_of_properIntegral
    [IsAlgClosed kbar]
    {W : Scheme.{u}} [IsIntegral W] (wk : W ⟶ Spec (CommRingCat.of kbar))
    [UniversallyClosed wk] [LocallyOfFiniteType wk]
    {V : Scheme.{u}} [IsAffine V] (g : W ⟶ V)
    (a b : Spec (CommRingCat.of kbar) ⟶ W)
    (ha : a ≫ wk = 𝟙 _) (hb : b ≫ wk = 𝟙 _) :
    a ≫ g = b ≫ g := by
  letI : Field Γ(W, ⊤) :=
    (isField_of_universallyClosed (CommRingCat.of kbar) wk).toField
  set F : CommRingCat.of kbar ⟶ Γ(W, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of kbar)).inv ≫ wk.appTop with hF
  have hint : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed wk
  haveI : IsIso F := (ConcreteCategory.isIso_iff_bijective F).mpr
    (IsAlgClosed.ringHom_bijective_of_isIntegral F.hom hint)
  haveI : IsIso wk.appTop := by
    have heq : wk.appTop = (Scheme.ΓSpecIso (CommRingCat.of kbar)).hom ≫ F := by
      rw [hF]
      simp
    rw [heq]
    infer_instance
  have haa : wk.appTop ≫ a.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, ha]
    simp
  have hbb : wk.appTop ≫ b.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hb]
    simp
  have hab : a.appTop = b.appTop := by
    rw [← cancel_epi wk.appTop, haa, hbb]
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, hab]

/-! Integrality descends along a scheme-theoretic retract.  The section makes
the retraction surjective on points, while the stalk map of the retraction is
injective because it is a factor of an isomorphism. -/

theorem isIntegral_of_retract {S T : Scheme.{u}} [IsIntegral T]
    (r : S ⟶ T) (pr : T ⟶ S) (hrp : r ≫ pr = 𝟙 S) : IsIntegral S := by
  have hsurj : Function.Surjective pr.base := by
    intro x
    refine ⟨r.base x, ?_⟩
    have h := congrArg (fun m => m.base x) hrp
    simpa using h
  haveI : IrreducibleSpace S := by
    rw [irreducibleSpace_def]
    have h := (IrreducibleSpace.isIrreducible_univ T).image pr.base
      pr.base.hom.continuous.continuousOn
    rwa [Set.image_univ, hsurj.range_eq] at h
  haveI hstalk : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := by
    intro x
    haveI hiso : IsIso ((r ≫ pr).stalkMap x) := by
      rw [Scheme.Hom.stalkMap_congr_hom (r ≫ pr) (𝟙 S) hrp x,
        Scheme.Hom.stalkMap_id]
      exact inferInstanceAs (IsIso ((S.presheaf.stalkCongr _).hom ≫ 𝟙 _))
    rw [Scheme.Hom.stalkMap_comp] at hiso
    have hbij := (ConcreteCategory.isIso_iff_bijective
      (pr.stalkMap (r.base x) ≫ r.stalkMap x)).1 hiso
    have hinj : Function.Injective (pr.stalkMap (r.base x)).hom := by
      intro a b hab
      apply hbij.injective
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      exact congrArg (r.stalkMap x) hab
    have hb : pr.base (r.base x) = x := by
      have h := congrArg (fun m => m.base x) hrp
      simpa using h
    have hred : _root_.IsReduced (S.presheaf.stalk (pr.base (r.base x))) :=
      isReduced_of_injective (pr.stalkMap (r.base x)).hom hinj
    rwa [hb] at hred
  haveI : IsReduced S := isReduced_of_isReduced_stalk S
  exact isIntegral_of_irreducibleSpace_of_isReduced S

end ProperAffineConstancy

section Scheme

open AlgebraicGeometry

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- The underlying-scheme isomorphism induced by a translation of sections. -/
noncomputable def pointTranslationIso (x y : 𝟙_ (Over S) ⟶ G) : G.left ≅ G.left :=
  (Over.forget S).mapIso (pointTranslation G x y)

@[simp]
theorem pointTranslationIso_hom (x y : 𝟙_ (Over S) ⟶ G) :
    (pointTranslationIso G x y).hom = (pointTranslation G x y).hom.left :=
  rfl

@[simp]
theorem pointTranslationIso_inv (x y : 𝟙_ (Over S) ⟶ G) :
    (pointTranslationIso G x y).inv = (pointTranslation G x y).inv.left :=
  rfl

@[simp]
theorem pointTranslationIso_self (x : 𝟙_ (Over S) ⟶ G) :
    pointTranslationIso G x x = Iso.refl G.left := by
  apply Iso.ext
  simp [pointTranslationIso]

@[simp]
theorem pointTranslationIso_symm (x y : 𝟙_ (Over S) ⟶ G) :
    (pointTranslationIso G x y).symm = pointTranslationIso G y x := by
  apply Iso.ext
  simp [pointTranslationIso, pointTranslation]

@[simp]
theorem pointTranslationIso_trans (x y z : 𝟙_ (Over S) ⟶ G) :
    pointTranslationIso G x y ≪≫ pointTranslationIso G y z =
      pointTranslationIso G x z := by
  apply Iso.ext
  simp [pointTranslationIso, pointTranslation, Iso.trans_assoc]

@[reassoc (attr := simp)]
theorem pointTranslationIso_hom_comp (x y : 𝟙_ (Over S) ⟶ G) :
    (pointTranslationIso G x y).hom ≫ G.hom = G.hom :=
  Over.w _

@[simp]
theorem pointTranslationIso_hom_apply (x y : 𝟙_ (Over S) ⟶ G) (s : S) :
    (pointTranslationIso G x y).hom (x.left s) = y.left s := by
  rw [pointTranslationIso_hom, ← Scheme.Hom.comp_apply, ← Over.comp_left,
    comp_pointTranslation_hom]

end Scheme

section Transport

open AlgebraicGeometry

/-- Smooth-locus membership is invariant under an automorphism over the base. -/
theorem mem_smoothLocus_iff_of_comp_eq {X S : Scheme.{u}} (e : X ⟶ X) [IsOpenImmersion e]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (he : e ≫ f = f) (z : X) :
    e z ∈ f.smoothLocus ↔ z ∈ f.smoothLocus := by
  conv_lhs => rw [← Scheme.Hom.mem_preimage]
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  simp only [he]

/-- Reducedness of a stalk is invariant under an open immersion. -/
theorem isReduced_stalk_iff_of_isOpenImmersion {X Y : Scheme.{u}} (e : X ⟶ Y)
    [IsOpenImmersion e] (z : X) :
    _root_.IsReduced (X.presheaf.stalk z) ↔ _root_.IsReduced (Y.presheaf.stalk (e z)) := by
  constructor
  · intro h
    exact isReduced_of_injective (asIso (e.stalkMap z)).commRingCatIsoToRingEquiv
      (asIso (e.stalkMap z)).commRingCatIsoToRingEquiv.injective
  · intro h
    exact isReduced_of_injective (asIso (e.stalkMap z)).commRingCatIsoToRingEquiv.symm
      (asIso (e.stalkMap z)).commRingCatIsoToRingEquiv.symm.injective

/-- Irreducibility of a subset is invariant under an isomorphism (preimage form). -/
theorem isIrreducible_preimage_iff_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e]
    (t : Set Y) : IsIrreducible (e ⁻¹' t) ↔ IsIrreducible t := by
  have hcoe : ⇑(Scheme.homeoOfIso (asIso e)) = ⇑e := by
    rw [Scheme.coe_homeoOfIso, asIso_hom]
  constructor
  · intro hi
    have hsurj : Function.Surjective ⇑e := by
      rw [← hcoe]
      exact (Scheme.homeoOfIso (asIso e)).surjective
    have h2 := hi.image ⇑e e.continuous.continuousOn
    rwa [Set.image_preimage_eq t hsurj] at h2
  · intro ht
    refine ht.preimage ?_ ?_
    · rw [← hcoe]
      exact (Scheme.homeoOfIso (asIso e)).isOpenEmbedding
    · have hr : Set.range ⇑e = Set.univ := by
        rw [← hcoe]
        exact (Scheme.homeoOfIso (asIso e)).surjective.range_eq
      rw [hr, Set.inter_univ]
      exact ht.nonempty

/-- Translation preserves membership in the smooth locus of a group scheme. -/
theorem pointTranslationIso_mem_smoothLocus_iff {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [LocallyOfFinitePresentation G.hom] (x y : 𝟙_ (Over S) ⟶ G) (z : G.left) :
    (pointTranslationIso G x y).hom z ∈ G.hom.smoothLocus ↔ z ∈ G.hom.smoothLocus :=
  mem_smoothLocus_iff_of_comp_eq _ G.hom (pointTranslationIso_hom_comp G x y) z

/-- Translation preserves reducedness of the local ring at a point. -/
theorem isReduced_stalk_pointTranslationIso_iff {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (x y : 𝟙_ (Over S) ⟶ G) (z : G.left) :
    _root_.IsReduced (G.left.presheaf.stalk z) ↔
      _root_.IsReduced (G.left.presheaf.stalk ((pointTranslationIso G x y).hom z)) :=
  isReduced_stalk_iff_of_isOpenImmersion _ z

/-- Irreducibility of subsets is preserved by translation. -/
theorem isIrreducible_pointTranslationIso_preimage_iff {S : Scheme.{u}} (G : Over S)
    [GrpObj G] (x y : 𝟙_ (Over S) ⟶ G) (t : Set G.left) :
    IsIrreducible ((pointTranslationIso G x y).hom ⁻¹' t) ↔ IsIrreducible t :=
  isIrreducible_preimage_iff_of_isIso _ t

end Transport

end GroupScheme

section AbelianVariety

open AlgebraicGeometry

variable {K : Type u} [Field K]

/-- The geometric part of Mumford's abelian-variety condition for a group scheme.

The group-object structure is supplied as a typeclass; the predicate records
completeness (properness) and geometric integrality separately. -/
def IsAbelianVariety (G : Over (Spec (.of K))) [GrpObj G] : Prop :=
  IsProper G.hom ∧ GeometricallyIntegral G.hom

theorem isCommMonObj_of_isAbelianVariety
    (G : Over (Spec (.of K))) [GrpObj G] (hG : IsAbelianVariety G) :
    IsCommMonObj G := by
  letI : IsProper G.hom := hG.1
  letI : GeometricallyIntegral G.hom := hG.2
  exact AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral G

/-- An abelian variety is smooth over its base field. -/
theorem smooth_of_isAbelianVariety
    (G : Over (Spec (.of K))) [GrpObj G] (hG : IsAbelianVariety G) :
    Smooth G.hom := by
  letI : IsProper G.hom := hG.1
  letI : GeometricallyIntegral G.hom := hG.2
  letI : LocallyOfFiniteType G.hom := IsProper.toLocallyOfFiniteType
  letI : GrpObj (Over.mk G.hom) := ‹GrpObj G›
  exact smooth_of_grpObj G.hom

end AbelianVariety

end Mumford
