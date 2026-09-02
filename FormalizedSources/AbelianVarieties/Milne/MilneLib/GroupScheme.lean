/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Group.Smooth

/-!
# Group varieties

The group-object interface for schemes supplies canonical translations between
sections.  Proper geometrically integral group schemes over a field are
commutative, giving the categorical core of Milne's abelian-variety language.
-/

set_option autoImplicit false

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace MilneLib

namespace GroupVariety

section Categorical

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G] {X : C}

/- The cartesian identity used when reducing the geometric rigidity lemma to
   its projection/slice equation. -/
theorem rigidity_snd_lift
    {X Y : C} (x₀ : 𝟙_ C ⟶ X) :
    snd X Y ≫ lift (toUnit Y ≫ x₀) (𝟙 Y) =
      lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) := by
  ext1 <;> simp

/- Invariance under replacing the first coordinate by `x₀` is equivalent to
   factoring through the second projection. -/
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

/- The factor through the second projection is unique.  This is the
   categorical cancellation step used when the rigidity slice is evaluated
   at the distinguished first-coordinate section. -/
theorem factor_through_snd_unique
    {X Y Z : C} (x₀ : 𝟙_ C ⟶ X) (f : X ⊗ Y ⟶ Z)
    {g₁ g₂ : Y ⟶ Z} (h₁ : f = snd X Y ≫ g₁)
    (h₂ : f = snd X Y ≫ g₂) : g₁ = g₂ := by
  have h := congrArg (fun q => lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ q)
    (h₁.symm.trans h₂)
  simpa using h

/- The rigidity factorization can be stated with a unique factor. -/
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

/- The Yoneda functor from group objects to group-valued functors is fully
   faithful.  Keeping this bundled form avoids repeatedly unpacking the
   representability witness in later morphism arguments. -/
def pointsYoneda : Grp C ⥤ Cᵒᵖ ⥤ GrpCat :=
  CategoryTheory.yonedaGrp

def pointsYoneda_fullyFaithful : (pointsYoneda (C := C)).FullyFaithful :=
  CategoryTheory.yonedaGrpFullyFaithful

theorem comp_mulRight_hom (f : X ⟶ G) (g : 𝟙_ C ⟶ G) :
    f ≫ (GrpObj.mulRight g).hom = f * (toUnit X ≫ g) := by
  rw [GrpObj.mulRight_hom, comp_lift_assoc, Category.comp_id,
    comp_toUnit_assoc, CategoryTheory.Hom.mul_def]

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

/- Translation is natural for homomorphisms of group objects.  This is the
   categorical transport used when moving a local fibre calculation to a
   different section. -/
theorem pointTranslation_hom_naturality
    {G H : C} [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom f]
    (x y : 𝟙_ C ⟶ G) :
    (pointTranslation G x y).hom ≫ f =
      f ≫ (pointTranslation H (x ≫ f) (y ≫ f)).hom := by
  have hhom (g : 𝟙_ C ⟶ G) :
      (GrpObj.mulRight g).hom ≫ f =
        f ≫ (GrpObj.mulRight (g ≫ f)).hom := by
    rw [GrpObj.mulRight_hom, Category.assoc, IsMonHom.mul_hom,
      ← Category.assoc, CartesianMonoidalCategory.lift_map]
    rw [GrpObj.mulRight_hom, comp_lift_assoc]
    simp
  have hinv (g : 𝟙_ C ⟶ G) :
      (GrpObj.mulRight g).inv ≫ f =
        f ≫ (GrpObj.mulRight (g ≫ f)).inv := by
    rw [GrpObj.mulRight_inv, Category.assoc, IsMonHom.mul_hom,
      ← Category.assoc, CartesianMonoidalCategory.lift_map]
    rw [GrpObj.mulRight_inv, comp_lift_assoc]
    simp
  simp only [pointTranslation, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, hhom y]
  conv_lhs => rw [← Category.assoc]
  rw [hinv x]
  simp only [Category.assoc]

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
is the geometric input used in the closed-map proof of the rigidity lemma. -/
theorem snd_left_isClosedMap
    {X Y : Over (Spec (.of kbar))} [IsProper X.hom] :
    IsClosedMap (snd X Y).left.base := by
  haveI hp : UniversallyClosed X.hom := IsProper.toUniversallyClosed
  haveI : UniversallyClosed (snd X Y).left := by
    rw [Over.snd_left]
    exact universallyClosed_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback X.hom Y.hom) hp
  exact Scheme.Hom.isClosedMap _

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

end RigidityGeometry

section ProperAffineConstancy

open AlgebraicGeometry

variable {kbar : Type u} [Field kbar]

/- A proper integral scheme over an algebraically closed field has no
nonconstant maps to an affine scheme. -/
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

/- Integrality descends along a scheme-theoretic retract.  The section makes
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

section RigidityChain

open AlgebraicGeometry

variable {kbar : Type u} [Field kbar]

/-!
The geometric rigidity chain is kept in this file so the Milne project can use
the same scheme-level API as the Jacobian formalization without importing that
project.  The first step is the pointwise slice-constancy statement.
-/

theorem rigidity_eqAt_closedPoint_of_proper_into_affine
    [IsAlgClosed kbar]
    {X Y Z : Over (Spec (.of kbar))}
    [IsProper X.hom]
    [GeometricallyIrreducible (X ⊗ Y).hom]
    [LocallyOfFiniteType (X ⊗ Y).hom]
    [IsReduced (X ⊗ Y).left]
    [IsSeparated Z.hom]
    (f : (X ⊗ Y) ⟶ Z)
    (x₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ X)
    (U : (X ⊗ Y).left.Opens)
    (Vset : Set Y.left)
    (_hUV : (U : Set (X ⊗ Y).left) = (snd X Y).left.base ⁻¹' Vset)
    (U₀ : Z.left.Opens) (_hU₀ : IsAffineOpen U₀)
    (_hfU : ∀ u ∈ (U : Set (X ⊗ Y).left), f.left.base u ∈ U₀)
    (x : (U : (X ⊗ Y).left.Opens).toScheme)
    (_hx : x ∈ closedPoints (U : (X ⊗ Y).left.Opens).toScheme) :
    (U : (X ⊗ Y).left.Opens).toScheme.fromSpecResidueField x ≫
        ((U.ι : (U : (X ⊗ Y).left.Opens).toScheme ⟶ (X ⊗ Y).left) ≫ f.left) =
      (U : (X ⊗ Y).left.Opens).toScheme.fromSpecResidueField x ≫
        ((U.ι : (U : (X ⊗ Y).left.Opens).toScheme ⟶ (X ⊗ Y).left) ≫
          (lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) ≫ f).left) := by
  have hxc : IsClosed {x} := _hx
  set wU : (U : (X ⊗ Y).left.Opens).toScheme ⟶ Spec (CommRingCat.of kbar) :=
    U.ι ≫ (X ⊗ Y).hom with hwU
  set px : Spec (CommRingCat.of kbar) ⟶ (U : (X ⊗ Y).left.Opens).toScheme :=
    pointOfClosedPoint wU x hxc with hpx
  rw [← cancel_epi (Spec.map (residueFieldIsoBase wU x hxc).hom)]
  suffices h : px ≫ U.ι ≫ Over.Hom.left f =
      px ≫ U.ι ≫ Over.Hom.left (lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) ≫ f) by
    rw [hpx] at h
    simpa only [pointOfClosedPoint, Category.assoc] using h
  set q : Spec (CommRingCat.of kbar) ⟶ (X ⊗ Y).left := px ≫ U.ι with hq
  have hqsec : q ≫ (X ⊗ Y).hom = 𝟙 _ := by
    rw [hq, Category.assoc]
    exact pointOfClosedPoint_comp wU x hxc
  rw [Over.comp_left]
  set retract : X ⊗ Y ⟶ X ⊗ Y := lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) with hretract
  have htoUnit : (toUnit X).left = X.hom := by simp
  set qhat : 𝟙_ (Over (Spec (CommRingCat.of kbar))) ⟶ X ⊗ Y :=
    Over.homMk q hqsec with hqhat
  have hqhatL : qhat.left = q := rfl
  set yhat : 𝟙_ (Over (Spec (CommRingCat.of kbar))) ⟶ Y := qhat ≫ snd X Y with hyhat
  set xq : 𝟙_ (Over (Spec (CommRingCat.of kbar))) ⟶ X := qhat ≫ fst X Y with hxq
  set sec : X ⟶ X ⊗ Y := lift (𝟙 X) (toUnit X ≫ yhat) with hsecdef
  clear_value qhat xq yhat
  have hIover : qhat = xq ≫ sec := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, hsecdef, lift_fst, Category.comp_id]
      exact hxq.symm
    · rw [Category.assoc, hsecdef, lift_snd, ← Category.assoc,
        toUnit_unique (xq ≫ toUnit X) (𝟙 _), Category.id_comp]
      exact hyhat.symm
  have hIIover : qhat ≫ retract = x₀ ≫ sec := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [hretract, hsecdef, Category.assoc, lift_fst, ← Category.assoc,
        toUnit_unique (qhat ≫ toUnit (X ⊗ Y)) (𝟙 _), Category.id_comp, Category.assoc,
        lift_fst, Category.comp_id]
    · rw [hretract, hsecdef, Category.assoc, lift_snd, Category.assoc, lift_snd,
        ← Category.assoc, toUnit_unique (x₀ ≫ toUnit X) (𝟙 _), Category.id_comp, hyhat]
  have hsecLfst : sec.left ≫ (fst X Y).left = 𝟙 X.left := by
    rw [← Over.comp_left, hsecdef, lift_fst, Over.id_left]
  have hyhatL : yhat.left = q ≫ (snd X Y).left := by
    rw [hyhat, Over.comp_left]
    exact congrArg (· ≫ Over.Hom.left (snd X Y)) hqhatL
  have hsecLsnd : sec.left ≫ (snd X Y).left = X.hom ≫ q ≫ (snd X Y).left := by
    rw [← Over.comp_left, hsecdef, lift_snd, ← hyhatL]
    simp [htoUnit]
  haveI : IsIntegral (X ⊗ Y).left := by
    haveI : IrreducibleSpace (X ⊗ Y).left :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton (X ⊗ Y).hom
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : IsIntegral X.left := isIntegral_of_retract sec.left (fst X Y).left hsecLfst
  haveI : IsAffine U₀.toScheme := _hU₀
  have hsecU : ∀ t : X.left, sec.left.base t ∈ (↑U : Set (X ⊗ Y).left) := by
    intro t
    rw [_hUV, Set.mem_preimage]
    have e1 : (snd X Y).left.base (sec.left.base t) =
        (snd X Y).left.base (q.base (X.hom.base t)) := by
      have h2 := congrArg (fun m : X.left ⟶ Y.left => m.base t) hsecLsnd
      simpa only [Scheme.Hom.comp_apply] using h2
    rw [e1]
    have hqmem : q.base (X.hom.base t) ∈ (↑U : Set (X ⊗ Y).left) := by
      rw [hq, Scheme.Hom.comp_apply, pointOfClosedPoint_apply, ← Scheme.Opens.range_ι]
      exact Set.mem_range_self x
    rw [_hUV, Set.mem_preimage] at hqmem
    exact hqmem
  have hrange : Set.range ((sec ≫ f).left).base ⊆ Set.range U₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    have hfin := _hfU (sec.left.base t) (hsecU t)
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hfin
  set g : X.left ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (sec ≫ f).left hrange with hgdef
  have hgfac : g ≫ U₀.ι = (sec ≫ f).left := IsOpenImmersion.lift_fac _ _ hrange
  have key : xq.left ≫ g = x₀.left ≫ g :=
    eq_comp_of_isAffine_of_properIntegral X.hom g xq.left x₀.left (Over.w xq) (Over.w x₀)
  have hqf : qhat ≫ f = xq ≫ sec ≫ f := by
    rw [← Category.assoc, ← hIover]
  have hqrf : qhat ≫ retract ≫ f = x₀ ≫ sec ≫ f := by
    rw [← Category.assoc, hIIover, Category.assoc]
  have hxqf : q ≫ f.left = xq.left ≫ (sec ≫ f).left := by
    have h := congrArg Over.Hom.left hqf
    simp only [Over.comp_left, hqhatL] at h
    exact h
  have hx₀f : q ≫ retract.left ≫ f.left = x₀.left ≫ (sec ≫ f).left := by
    have h := congrArg Over.Hom.left hqrf
    simp only [Over.comp_left, hqhatL] at h
    exact h
  have hbridge : xq.left ≫ (sec ≫ f).left = x₀.left ≫ (sec ≫ f).left := by
    rw [← hgfac, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ U₀.ι) key
  have hgoalq : q ≫ f.left = q ≫ retract.left ≫ f.left :=
    hxqf.trans (hbridge.trans hx₀f.symm)
  rw [hq] at hgoalq
  simpa only [Category.assoc] using hgoalq

/- The pointwise slice equality globalizes over the dense closed points of a
   saturated open. -/
theorem rigidity_eqOn_saturated_open_to_affine
    [IsAlgClosed kbar]
    {X Y Z : Over (Spec (.of kbar))}
    [IsProper X.hom]
    [GeometricallyIrreducible (X ⊗ Y).hom]
    [LocallyOfFiniteType (X ⊗ Y).hom]
    [IsReduced (X ⊗ Y).left]
    [IsSeparated Z.hom]
    (f : (X ⊗ Y) ⟶ Z)
    (x₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ X)
    (U : (X ⊗ Y).left.Opens)
    (Vset : Set Y.left)
    (_hUV : (U : Set (X ⊗ Y).left) = (snd X Y).left.base ⁻¹' Vset)
    (U₀ : Z.left.Opens) (_hU₀ : IsAffineOpen U₀)
    (_hfU : ∀ u ∈ (U : Set (X ⊗ Y).left), f.left.base u ∈ U₀) :
    (U.ι : (U : (X ⊗ Y).left.Opens).toScheme ⟶ (X ⊗ Y).left) ≫ f.left =
      (U.ι : (U : (X ⊗ Y).left.Opens).toScheme ⟶ (X ⊗ Y).left) ≫
        (lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) ≫ f).left := by
  haveI : Z.left.IsSeparated := by
    rw [Scheme.isSeparated_iff]
    have heq : terminal.from Z.left = Z.hom ≫ terminal.from (Spec (CommRingCat.of kbar)) :=
      terminal.hom_ext _ _
    rw [heq]
    infer_instance
  haveI : JacobsonSpace ((U : (X ⊗ Y).left.Opens).toScheme) := by
    haveI : JacobsonSpace (X ⊗ Y).left :=
      LocallyOfFiniteType.jacobsonSpace (X ⊗ Y).hom
    exact JacobsonSpace.of_isOpenEmbedding U.ι.isOpenEmbedding
  exact morphism_eq_of_eqAt_closedPoints fun x hx =>
    rigidity_eqAt_closedPoint_of_proper_into_affine f x₀ U Vset _hUV U₀ _hU₀ _hfU x hx

/- The dense open used in the global rigidity step.  The complement of an
   affine chart is pushed forward along the proper projection. -/
theorem rigidity_eqOn_dense_open
    [IsAlgClosed kbar]
    {X Y Z : Over (Spec (.of kbar))}
    [IsProper X.hom]
    [GeometricallyIrreducible (X ⊗ Y).hom]
    [LocallyOfFiniteType (X ⊗ Y).hom]
    [IsReduced (X ⊗ Y).left]
    [IsSeparated Z.hom]
    (f : (X ⊗ Y) ⟶ Z)
    (x₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ X)
    (y₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ Z)
    (_hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    ∃ U : (X ⊗ Y).left.Opens, (U : Set (X ⊗ Y).left).Nonempty ∧
      (U.ι : (U : (X ⊗ Y).left.Opens).toScheme ⟶ (X ⊗ Y).left) ≫ f.left =
        (U.ι : (U : (X ⊗ Y).left.Opens).toScheme ⟶ (X ⊗ Y).left) ≫
          (lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) ≫ f).left := by
  have hclosed : IsClosedMap (snd X Y).left.base := snd_left_isClosedMap
  haveI hsub : Subsingleton (↥(𝟙_ (Over (Spec (CommRingCat.of kbar)))).left) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of kbar)))
  have ptk : (𝟙_ (Over (Spec (CommRingCat.of kbar)))).left :=
    (inferInstance : Inhabited (Spec (CommRingCat.of kbar))).default
  let z₀pt : Z.left := z₀.left.base ptk
  obtain ⟨U₀, _hU₀aff, hz₀U₀, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z.left)
    (x := z₀pt) (U := ⊤) trivial
  set Gset := (snd X Y).left.base '' (f.left.base ⁻¹' (U₀ : Set Z.left)ᶜ) with hGdef
  have hG : IsClosed Gset := hclosed _ (U₀.isOpen.isClosed_compl.preimage f.left.base.hom.2)
  have hUopen : IsOpen ((snd X Y).left.base ⁻¹' Gsetᶜ) :=
    (hG.isOpen_compl).preimage (snd X Y).left.base.hom.2
  let s := (lift (𝟙 X) (toUnit X ≫ y₀)).left
  let y₀pt : Y.left := y₀.left.base ptk
  let x₀pt : X.left := x₀.left.base ptk
  have hfib : (snd X Y).left.base ⁻¹' {y₀pt} ⊆ Set.range s.base := by
    set p₁ := pullback.fst X.hom Y.hom with hp₁def
    set p₂ := pullback.snd X.hom Y.hom with hp₂def
    have htoUnit : (toUnit X).left = X.hom := by simp
    have hsp1 : s ≫ p₁ = 𝟙 X.left := by
      rw [hp₁def, ← Over.fst_left, ← Over.comp_left, lift_fst, Over.id_left]
    have hsp2 : s ≫ p₂ = X.hom ≫ y₀.left := by
      rw [hp₂def, ← Over.snd_left, ← Over.comp_left, lift_snd, Over.comp_left]
      exact congrArg (· ≫ y₀.left) htoUnit
    have hsec : y₀.left ≫ Y.hom = 𝟙 (Spec (.of kbar)) := by simpa using Over.w y₀
    have houter : IsPullback (s ≫ p₁) X.hom X.hom (y₀.left ≫ Y.hom) := by
      have hiso : IsPullback (𝟙 X.left) X.hom X.hom (𝟙 (Spec (.of kbar))) :=
        IsPullback.of_horiz_isIso ⟨by simp⟩
      rwa [← hsp1, ← hsec] at hiso
    have hL : IsPullback s X.hom p₂ y₀.left :=
      IsPullback.of_right houter hsp2 (IsPullback.of_hasPullback X.hom Y.hom)
    have hrange : Set.range s.base = p₂.base ⁻¹' Set.range y₀.left.base := by
      have h := AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback hL.flip Set.univ
      simp only [Set.image_univ, Set.preimage_univ] at h
      exact h
    rw [Over.snd_left, ← hp₂def, hrange]
    exact Set.preimage_mono (Set.singleton_subset_iff.mpr ⟨ptk, rfl⟩)
  have hy₀ : y₀pt ∉ Gset := by
    rintro ⟨q, hq, hsndq⟩
    obtain ⟨x, rfl⟩ := hfib hsndq
    apply hq
    have hcomp : s ≫ f.left = (toUnit X ≫ z₀).left := by
      rw [← Over.comp_left]
      exact congrArg Over.Hom.left _hf
    have hfx : f.left.base (s.base x) = z₀pt := by
      rw [← Scheme.Hom.comp_apply, hcomp, Over.comp_left, Scheme.Hom.comp_apply]
      change z₀.left.base ((toUnit X).left.base x) = z₀.left.base ptk
      congr 1
      exact Subsingleton.elim _ _
    rw [hfx]
    exact hz₀U₀
  refine ⟨⟨_, hUopen⟩, ⟨s.base x₀pt, ?_⟩, ?_⟩
  · change (snd X Y).left.base (s.base x₀pt) ∈ Gsetᶜ
    have hsnd : (snd X Y).left.base (s.base x₀pt) = y₀pt := by
      have hcomp : s ≫ (snd X Y).left = (toUnit X ≫ y₀).left := by
        rw [← Over.comp_left]
        exact congrArg Over.Hom.left (lift_snd (𝟙 X) (toUnit X ≫ y₀))
      rw [← Scheme.Hom.comp_apply, hcomp, Over.comp_left, Scheme.Hom.comp_apply]
      change y₀.left.base ((toUnit X).left.base x₀pt) = y₀.left.base ptk
      congr 1
      exact Subsingleton.elim _ _
    rw [Set.mem_compl_iff, hsnd]
    exact hy₀
  · have hfU : ∀ u ∈ ((⟨_, hUopen⟩ : (X ⊗ Y).left.Opens) : Set (X ⊗ Y).left),
        f.left.base u ∈ U₀ := by
      intro u hu
      by_contra hcon
      exact hu ⟨u, hcon, rfl⟩
    exact rigidity_eqOn_saturated_open_to_affine f x₀ ⟨_, hUopen⟩ Gsetᶜ rfl U₀ _hU₀aff hfU

/- The nonempty-open equality extends across the geometrically irreducible
   reduced source by dominant-open extensionality. -/
theorem rigidity_core
    [IsAlgClosed kbar]
    {X Y Z : Over (Spec (.of kbar))}
    [IsProper X.hom]
    [GeometricallyIrreducible (X ⊗ Y).hom]
    [LocallyOfFiniteType (X ⊗ Y).hom]
    [IsReduced (X ⊗ Y).left]
    [IsSeparated Z.hom]
    (f : (X ⊗ Y) ⟶ Z)
    (x₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ X)
    (y₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ Z)
    (_hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    f = lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) ≫ f := by
  obtain ⟨U, hU, h⟩ := rigidity_eqOn_dense_open f x₀ y₀ z₀ _hf
  haveI : IrreducibleSpace (X ⊗ Y).left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (X ⊗ Y).hom
  haveI : IsDominant (U.ι : (U : (X ⊗ Y).left.Opens).toScheme ⟶ (X ⊗ Y).left) := by
    rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
    exact IsOpen.dense U.isOpen hU
  haveI : IsSeparated (Z.left ↘ Spec (CommRingCat.of kbar)) := ‹IsSeparated Z.hom›
  refine Over.OverMorphism.ext ?_
  exact ext_of_isDominant_of_isSeparated' (S := Spec (.of kbar))
    (X := (X ⊗ Y).left) (Y := Z.left) (f := f.left)
    (g := (lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) ≫ f).left) U.ι h

/- The categorical reduction turns the core equality into factorization through
   the second projection, with the witness given by the distinguished slice. -/
theorem rigidity_lemma
    [IsAlgClosed kbar]
    {X Y Z : Over (Spec (.of kbar))}
    [IsProper X.hom]
    [GeometricallyIrreducible (X ⊗ Y).hom]
    [LocallyOfFiniteType (X ⊗ Y).hom]
    [IsReduced (X ⊗ Y).left]
    [IsSeparated Z.hom]
    (f : (X ⊗ Y) ⟶ Z)
    (x₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ X)
    (y₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ Z)
    (_hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    ∃ g : Y ⟶ Z, f = snd X Y ≫ g := by
  refine ⟨lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f, ?_⟩
  rw [← Category.assoc, rigidity_snd_lift]
  exact rigidity_core f x₀ y₀ z₀ _hf

/- The two-axis form in Milne's statement: once the first-axis collapse gives
   factorisation through the second projection, the second-axis collapse makes
   that factor constant. -/
theorem rigidity_constant_of_two_axes
    [IsAlgClosed kbar]
    {X Y Z : Over (Spec (.of kbar))}
    [IsProper X.hom]
    [GeometricallyIrreducible (X ⊗ Y).hom]
    [LocallyOfFiniteType (X ⊗ Y).hom]
    [IsReduced (X ⊗ Y).left]
    [IsSeparated Z.hom]
    (f : (X ⊗ Y) ⟶ Z)
    (x₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ X)
    (y₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ Z)
    (h₁ : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀)
    (h₂ : lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f = toUnit Y ≫ z₀) :
    f = toUnit (X ⊗ Y) ≫ z₀ := by
  obtain ⟨g, hg⟩ := rigidity_lemma f x₀ y₀ z₀ h₁
  have hsg : g = toUnit Y ≫ z₀ := by
    calc
      g = (lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ snd X Y) ≫ g := by
        rw [lift_snd]
        simp
      _ = lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ (snd X Y ≫ g) := by
        rw [Category.assoc]
      _ = lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f := by rw [hg]
      _ = toUnit Y ≫ z₀ := h₂
  calc
    f = snd X Y ≫ g := hg
    _ = snd X Y ≫ (toUnit Y ≫ z₀) := by rw [hsg]
    _ = toUnit (X ⊗ Y) ≫ z₀ := by
      rw [← Category.assoc]
      rw [toUnit_unique (snd X Y ≫ toUnit Y) (toUnit (X ⊗ Y))]

/- The two-axis rigidity statement descends from an algebraic closure.  The
   hypotheses are deliberately stated on the original factors: properness of
   `X` supplies its finite-type instance, while geometric integrality of both
   factors gives the integral/reduced product after scalar extension. -/
theorem rigidity_constant_of_two_axes_arbitraryField
    {K : Type u} [Field K]
    {X Y Z : Over (Spec (.of K))}
    [IsProper X.hom]
    [GeometricallyIntegral X.hom]
    [GeometricallyIntegral Y.hom]
    [LocallyOfFiniteType Y.hom]
    [IsSeparated Z.hom]
    (f : (X ⊗ Y) ⟶ Z)
    (x₀ : 𝟙_ (Over (Spec (.of K))) ⟶ X)
    (y₀ : 𝟙_ (Over (Spec (.of K))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (.of K))) ⟶ Z)
    (h₁ : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀)
    (h₂ : lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f = toUnit Y ≫ z₀) :
    f = toUnit (X ⊗ Y) ≫ z₀ := by
  letI : LocallyOfFiniteType X.hom := IsProper.toLocallyOfFiniteType
  let b := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback b
  let X' := F.obj X
  let Y' := F.obj Y
  let Z' := F.obj Z
  let x₀' := Functor.LaxMonoidal.ε F ≫ F.map x₀
  let y₀' := Functor.LaxMonoidal.ε F ≫ F.map y₀
  let z₀' := Functor.LaxMonoidal.ε F ≫ F.map z₀
  let fmap' := Functor.LaxMonoidal.μ F X Y ≫ F.map f
  let s₁ := lift (𝟙 X) (toUnit X ≫ y₀)
  let s₂ := lift (toUnit Y ≫ x₀) (𝟙 Y)
  let s₁' := lift (𝟙 X') (toUnit X' ≫ y₀')
  let s₂' := lift (toUnit Y' ≫ x₀') (𝟙 Y')
  letI : IsProper X'.hom := by
    change IsProper (Limits.pullback.snd X.hom b)
    infer_instance
  letI : GeometricallyIntegral X'.hom := by
    change GeometricallyIntegral (Limits.pullback.snd X.hom b)
    infer_instance
  letI : GeometricallyIntegral Y'.hom := by
    change GeometricallyIntegral (Limits.pullback.snd Y.hom b)
    infer_instance
  letI : LocallyOfFiniteType X'.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd X.hom b)
    infer_instance
  letI : LocallyOfFiniteType Y'.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd Y.hom b)
    infer_instance
  letI : IsSeparated Z'.hom := by
    change IsSeparated (Limits.pullback.snd Z.hom b)
    infer_instance
  haveI : GeometricallyIrreducible (X' ⊗ Y').hom := by
    rw [Over.tensorObj_hom]
    exact GeometricallyIrreducible.comp (pullback.fst X'.hom Y'.hom) X'.hom
  haveI : LocallyOfFiniteType (X' ⊗ Y').hom := by
    rw [Over.tensorObj_hom]
    exact AlgebraicGeometry.locallyOfFiniteType_comp
      (pullback.fst X'.hom Y'.hom) X'.hom
  letI : IsIntegral (X' ⊗ Y').left :=
    isIntegral_tensorObj_left_of_geometricallyIntegral (X := X') (Y := Y')
  haveI : IsReduced (X' ⊗ Y').left := inferInstance
  have hy : toUnit X' ≫ y₀' = F.map (toUnit X ≫ y₀) := by
    dsimp [X', y₀']
    rw [Functor.Monoidal.toUnit_ε_assoc]
    simp [← Functor.map_comp]
  have hx : toUnit Y' ≫ x₀' = F.map (toUnit Y ≫ x₀) := by
    dsimp [Y', x₀']
    rw [Functor.Monoidal.toUnit_ε_assoc]
    simp [← Functor.map_comp]
  have hs₁ : s₁' ≫ Functor.LaxMonoidal.μ F X Y = F.map s₁ := by
    dsimp [s₁', s₁, X', Y']
    rw [show (𝟙 (F.obj X)) = F.map (𝟙 X) by simp, hy]
    exact Functor.Monoidal.lift_μ F (𝟙 X) (toUnit X ≫ y₀)
  have hs₂ : s₂' ≫ Functor.LaxMonoidal.μ F X Y = F.map s₂ := by
    dsimp [s₂', s₂, X', Y']
    rw [hx, show (𝟙 (F.obj Y)) = F.map (𝟙 Y) by simp]
    exact Functor.Monoidal.lift_μ F (toUnit Y ≫ x₀) (𝟙 Y)
  have h₁' : s₁' ≫ fmap' = toUnit X' ≫ z₀' := by
    dsimp [fmap']
    rw [← Category.assoc, hs₁, ← Functor.map_comp, h₁]
    rw [Functor.map_comp]
    dsimp [z₀', Z']
    rw [Functor.Monoidal.toUnit_ε_assoc]
  have h₂' : s₂' ≫ fmap' = toUnit Y' ≫ z₀' := by
    dsimp [fmap']
    rw [← Category.assoc, hs₂, ← Functor.map_comp, h₂]
    rw [Functor.map_comp]
    dsimp [z₀', Z']
    rw [Functor.Monoidal.toUnit_ε_assoc]
  have hu := rigidity_constant_of_two_axes fmap' x₀' y₀' z₀' h₁' h₂'
  apply F.map_injective
  apply (cancel_epi (Functor.LaxMonoidal.μ F X Y)).mp
  dsimp [fmap'] at hu
  rw [hu]
  dsimp [z₀', X', Y']
  rw [Functor.map_comp]
  have hμunit :
      Functor.LaxMonoidal.μ F X Y ≫ toUnit (F.obj (X ⊗ Y)) =
        toUnit (F.obj X ⊗ F.obj Y) := by
    exact toUnit_unique _ _
  have hunit :
      toUnit (F.obj X ⊗ F.obj Y) ≫ Functor.LaxMonoidal.ε F =
        Functor.LaxMonoidal.μ F X Y ≫ F.map (toUnit (X ⊗ Y)) := by
    rw [← hμunit]
    simp only [Category.assoc, Functor.Monoidal.toUnit_ε]
  simpa only [Category.assoc] using congrArg (fun q => q ≫ F.map z₀) hunit

end RigidityChain

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
theorem pointTranslationIso_hom_apply (x y : 𝟙_ (Over S) ⟶ G) (s : S) :
    (pointTranslationIso G x y).hom (x.left s) = y.left s := by
  rw [pointTranslationIso_hom, ← Scheme.Hom.comp_apply, ← Over.comp_left,
    comp_pointTranslation_hom]

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

end Scheme

section Transport

open AlgebraicGeometry

/- Point-local geometric properties are invariant under the translation
   isomorphisms above.  These general scheme lemmas keep later abelian-variety
   arguments independent of a chosen point. -/

theorem mem_smoothLocus_iff_of_comp_eq
    {X S : Scheme.{u}} (e : X ⟶ X) [IsOpenImmersion e]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (he : e ≫ f = f) (z : X) :
    e z ∈ f.smoothLocus ↔ z ∈ f.smoothLocus := by
  conv_lhs => rw [← Scheme.Hom.mem_preimage]
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  simp only [he]

theorem isReduced_stalk_iff_of_isOpenImmersion
    {X Y : Scheme.{u}} (e : X ⟶ Y) [IsOpenImmersion e] (z : X) :
    _root_.IsReduced (X.presheaf.stalk z) ↔
      _root_.IsReduced (Y.presheaf.stalk (e z)) := by
  constructor
  · intro h
    exact isReduced_of_injective (asIso (e.stalkMap z)).commRingCatIsoToRingEquiv
      (asIso (e.stalkMap z)).commRingCatIsoToRingEquiv.injective
  · intro h
    exact isReduced_of_injective (asIso (e.stalkMap z)).commRingCatIsoToRingEquiv.symm
      (asIso (e.stalkMap z)).commRingCatIsoToRingEquiv.symm.injective

theorem isIrreducible_preimage_iff_of_isIso
    {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (t : Set Y) :
    IsIrreducible (e ⁻¹' t) ↔ IsIrreducible t := by
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

theorem pointTranslationIso_mem_smoothLocus_iff
    {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [LocallyOfFinitePresentation G.hom]
    (x y : 𝟙_ (Over S) ⟶ G) (z : G.left) :
    (pointTranslationIso G x y).hom z ∈ G.hom.smoothLocus ↔
      z ∈ G.hom.smoothLocus :=
  mem_smoothLocus_iff_of_comp_eq _ G.hom
    (pointTranslationIso_hom_comp G x y) z

theorem isReduced_stalk_pointTranslationIso_iff
    {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (x y : 𝟙_ (Over S) ⟶ G) (z : G.left) :
    _root_.IsReduced (G.left.presheaf.stalk z) ↔
      _root_.IsReduced (G.left.presheaf.stalk
        ((pointTranslationIso G x y).hom z)) :=
  isReduced_stalk_iff_of_isOpenImmersion _ z

theorem isIrreducible_pointTranslationIso_preimage_iff
    {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (x y : 𝟙_ (Over S) ⟶ G) (t : Set G.left) :
    IsIrreducible ((pointTranslationIso G x y).hom ⁻¹' t) ↔
      IsIrreducible t :=
  isIrreducible_preimage_iff_of_isIso _ t

end Transport

end GroupVariety

open AlgebraicGeometry

variable {K : Type u} [Field K]

/-- The geometric hypotheses used for an abelian group scheme over a field. -/
def IsAbelianVariety (G : Over (Spec (.of K))) [GrpObj G] : Prop :=
  IsProper G.hom ∧ GeometricallyIntegral G.hom

/- The defining geometric hypotheses expose the standard source properties
   needed by dimension and residue-fibre arguments. -/
theorem isIntegral_left_of_isAbelianVariety
    (G : Over (Spec (.of K))) [GrpObj G] (hG : IsAbelianVariety G) :
    IsIntegral G.left := by
  letI : GeometricallyIntegral G.hom := hG.2
  exact GeometricallyIntegral.isIntegral_of_subsingleton G.hom

theorem isReduced_left_of_isAbelianVariety
    (G : Over (Spec (.of K))) [GrpObj G] (hG : IsAbelianVariety G) :
    IsReduced G.left := by
  letI : IsIntegral G.left := isIntegral_left_of_isAbelianVariety G hG
  infer_instance

theorem locallyOfFiniteType_of_isAbelianVariety
    (G : Over (Spec (.of K))) [GrpObj G] (hG : IsAbelianVariety G) :
    LocallyOfFiniteType G.hom := by
  letI : IsProper G.hom := hG.1
  exact IsProper.toLocallyOfFiniteType

/-- The underlying scheme of an abelian variety over a field is Jacobson.

The properness hypothesis supplies local finite type, and the spectrum of a
field is Jacobson; Mathlib's finite-type descent then transfers the property
to the total space. -/
theorem jacobsonSpace_left_of_isAbelianVariety
    (G : Over (Spec (.of K))) [GrpObj G] (hG : IsAbelianVariety G) :
    JacobsonSpace G.left := by
  letI : LocallyOfFiniteType G.hom :=
    locallyOfFiniteType_of_isAbelianVariety G hG
  exact LocallyOfFiniteType.jacobsonSpace G.hom

theorem isLocallyNoetherian_left_of_isAbelianVariety
    (G : Over (Spec (.of K))) [GrpObj G] (hG : IsAbelianVariety G) :
    IsLocallyNoetherian G.left := by
  letI : LocallyOfFiniteType G.hom :=
    locallyOfFiniteType_of_isAbelianVariety G hG
  exact LocallyOfFiniteType.isLocallyNoetherian G.hom

/-- The underlying scheme of an abelian variety over a field is Noetherian. -/
theorem isNoetherian_left_of_isAbelianVariety
    (G : Over (Spec (.of K))) [GrpObj G] (hG : IsAbelianVariety G) :
    IsNoetherian G.left := by
  letI : IsProper G.hom := hG.1
  letI : IsLocallyNoetherian G.left :=
    isLocallyNoetherian_left_of_isAbelianVariety G hG
  letI : CompactSpace G.left := compactSpace_of_universallyClosed G.hom
  exact {}

/-- An abelian variety remains an abelian variety after base change along a
morphism of field spectra.  The group structure on the pullback is the one
transported by the pullback functor. -/
theorem IsAbelianVariety.baseChange
    {L : Type u} [Field L]
    {G : Over (Spec (.of K))} [GrpObj G]
    (hG : IsAbelianVariety G)
    (f : Spec (.of L) ⟶ Spec (.of K)) :
    letI : GrpObj ((Over.pullback f).obj G) := Functor.grpObjObj
    IsAbelianVariety ((Over.pullback f).obj G) := by
  letI : IsProper G.hom := hG.1
  letI : GeometricallyIntegral G.hom := hG.2
  constructor
  · change IsProper (pullback.snd G.hom f)
    infer_instance
  · change GeometricallyIntegral (pullback.snd G.hom f)
    infer_instance

/- A morphism between abelian varieties is proper: its underlying map is
   proper after cancelling the separated target structure morphism. -/
theorem isProper_left_of_isAbelianVariety
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) : IsProper f.left := by
  letI : IsSeparated B.hom := hB.1.toIsSeparated
  haveI : IsProper (f.left ≫ B.hom) := by
    rw [Over.w f]
    exact hA.1
  exact IsProper.of_comp f.left B.hom

/-- Proper geometrically integral group schemes over a field are commutative. -/
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
  letI : LocallyOfFiniteType G.hom :=
    locallyOfFiniteType_of_isAbelianVariety G hG
  letI : GrpObj (Over.mk G.hom) := ‹GrpObj G›
  exact smooth_of_grpObj G.hom

/-- Abelian varieties are flat over their ground field. -/
theorem flat_of_isAbelianVariety
    (G : Over (Spec (.of K))) [GrpObj G] (hG : IsAbelianVariety G) :
    Flat G.hom := by
  letI : Smooth G.hom := smooth_of_isAbelianVariety G hG
  infer_instance

end MilneLib
