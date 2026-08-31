/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.RigidityPointwise

/-!
# Dense-open assembly for Form-I rigidity

This module completes the geometric assembly after the closed-point slice step
in the Mumford pointwise rigidity module.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace Mumford
namespace GroupScheme

section RigidityChain

open AlgebraicGeometry

variable {kbar : Type u} [Field kbar]

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

/- The factor in Form I is unique; this packages the existential theorem with
   the categorical uniqueness lemma for downstream uses. -/
theorem rigidity_lemma_unique
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
    ∃! g : Y ⟶ Z, f = snd X Y ≫ g := by
  obtain ⟨g, hg⟩ := rigidity_lemma f x₀ y₀ z₀ _hf
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  exact factor_through_snd_unique x₀ f hg' hg

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


end GroupScheme
end Mumford
