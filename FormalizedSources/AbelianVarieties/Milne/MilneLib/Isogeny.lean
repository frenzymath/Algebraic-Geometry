/-
Copyright (c) 2026 The Milne Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Milne Contributors
-/

import Mathlib.AlgebraicGeometry.Group.Abelian
import MilneLib.GroupScheme
import MilneLib.LocalProperties

/-!
# Isogenies

For a homomorphism of group schemes over a field, the kernel is the fibre over
the identity section.  The predicate below records the source-faithful
surjective-and-finite-kernel condition using Mathlib's scheme morphism
properties.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MorphismProperty
open AlgebraicGeometry

namespace MilneLib

open GroupVariety

variable {K : Type u} [Field K]
variable {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]

/-- The kernel scheme of a group-scheme homomorphism, as the fibre over the identity. -/
noncomputable def isogenyKernel (f : A ⟶ B) : Scheme :=
  pullback f.left (η[B].left)

/-- The structure morphism of the kernel scheme over the base field. -/
noncomputable def isogenyKernelToBase (f : A ⟶ B) :
    isogenyKernel f ⟶ Spec (.of K) :=
  pullback.snd f.left (η[B].left)

omit [GrpObj A] in
/-- A point of the kernel projects to the fibre of `f.left` over the identity
section at the same base point. -/
theorem isogenyKernel_fst_mem_preimage
    (f : A ⟶ B) (x : isogenyKernel f) :
    (pullback.fst f.left (η[B].left)).base x ∈
      f.left ⁻¹' {(η[B].left).base ((pullback.snd f.left (η[B].left)).base x)} := by
  change f.left.base ((pullback.fst f.left (η[B].left)).base x) =
    (η[B].left).base ((pullback.snd f.left (η[B].left)).base x)
  have h := pullback.condition (f := f.left) (g := η[B].left)
  exact congrArg (fun q => q.base x) h

omit [GrpObj A] in
/-- The range of the kernel projection is the set-theoretic fibre over the
identity point of `Spec K`. -/
theorem isogenyKernel_range_fst (f : A ⟶ B) :
    Set.range
        (CategoryTheory.Limits.pullback.fst (C := Scheme) f.left (η[B].left)) =
      f.left ⁻¹' {(η[B].left).base (IsLocalRing.closedPoint K)} := by
  letI : Nonempty ((𝟙_ (Over (Spec (.of K)))).left) :=
    ⟨IsLocalRing.closedPoint K⟩
  letI : Subsingleton ((𝟙_ (Over (Spec (.of K)))).left) := by
    rw [Over.tensorUnit_left]
    infer_instance
  rw [Scheme.Pullback.range_fst, Set.range_eq_singleton]
  intro x
  exact congrArg (η[B].left)
    (Subsingleton.elim x (IsLocalRing.closedPoint K))

/-- The underlying topological space of the kernel is homeomorphic to its
set-theoretic identity fibre. -/
noncomputable def isogenyKernelHomeo (f : A ⟶ B) :
    isogenyKernel f ≃ₜ
      f.left ⁻¹' {(η[B].left).base (IsLocalRing.closedPoint K)} := by
  change (CategoryTheory.Limits.pullback (C := Scheme) f.left (η[B].left)) ≃ₜ
    f.left ⁻¹' {(η[B].left).base (IsLocalRing.closedPoint K)}
  let hE :=
    ((CategoryTheory.Limits.pullback.fst (C := Scheme) f.left (η[B].left)).isEmbedding).toHomeomorph
  exact hE.trans (Homeomorph.setCongr (isogenyKernel_range_fst f))

/-- A surjective group-scheme homomorphism with finite kernel. -/
def Isogeny (f : A ⟶ B) [IsMonHom f] : Prop :=
  Surjective f.left ∧ IsFinite (isogenyKernelToBase f)

/-- The homomorphism on global sections induced by a homomorphism of group schemes. -/
noncomputable def homSectionMap (f : A ⟶ B) [IsMonHom f] :
    (𝟙_ (Over (Spec (.of K))) ⟶ A) →*
      (𝟙_ (Over (Spec (.of K))) ⟶ B) :=
  { toFun := fun a => a ≫ f
    map_one' := by
      rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, Hom.one_def]
    map_mul' := by
      intro a b
      rw [Hom.mul_def, Category.assoc, IsMonHom.mul_hom, Hom.mul_def]
      simp }

/-- Postcomposition by a group-scheme homomorphism on generalized points.

Unlike `homSectionMap`, this keeps the test object explicit.  It is the
group-theoretic interface used when a fibre is tested after an arbitrary base
change (or by an arbitrary scheme in the slice). -/
noncomputable def homMap (X : Over (Spec (.of K))) (f : A ⟶ B) [IsMonHom f] :
    (X ⟶ A) →* (X ⟶ B) :=
  { toFun := fun a => a ≫ f
    map_one' := by
      rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, Hom.one_def]
    map_mul' := by
      intro a b
      rw [Hom.mul_def, Category.assoc, IsMonHom.mul_hom, Hom.mul_def]
      simp }

@[simp]
theorem homMap_apply (X : Over (Spec (.of K))) (f : A ⟶ B) [IsMonHom f]
    (a : X ⟶ A) : homMap X f a = a ≫ f :=
  rfl

@[simp]
theorem homSectionMap_eq_homMap (f : A ⟶ B) [IsMonHom f] :
    homSectionMap f = homMap (𝟙_ (Over (Spec (.of K)))) f :=
  rfl

/- The next declarations package the fibre/kernel translation for arbitrary
   generalized points.  They are deliberately stated for section fibres of
   `homMap`; no set-theoretic identification with the points of the kernel
   scheme is assumed here. -/
noncomputable def homFiberEquivKernel
    (X : Over (Spec (.of K))) (f : A ⟶ B) [IsMonHom f]
    (a₀ : X ⟶ A) :
    (homMap X f ⁻¹' {homMap X f a₀}) ≃ (homMap X f).ker :=
  MonoidHom.fiberEquivKer (homMap X f) a₀

theorem homFiber_finite_iff_kernel_finite
    (X : Over (Spec (.of K))) (f : A ⟶ B) [IsMonHom f]
    (a₀ : X ⟶ A) :
    Finite (homMap X f ⁻¹' {homMap X f a₀}) ↔
      Finite (homMap X f).ker := by
  exact (homFiberEquivKernel X f a₀).finite_iff

theorem homFiber_finite_of_kernel_finite
    (X : Over (Spec (.of K))) (f : A ⟶ B) [IsMonHom f]
    (a₀ : X ⟶ A) [Finite (homMap X f).ker] :
    Finite (homMap X f ⁻¹' {homMap X f a₀}) := by
  exact Finite.of_equiv _ (homFiberEquivKernel X f a₀).symm

/-- Any two nonempty generalized-point fibres are equivalent. -/
noncomputable def homFiberEquiv
    (X : Over (Spec (.of K))) (f : A ⟶ B) [IsMonHom f]
    (a₀ a₁ : X ⟶ A) :
    (homMap X f ⁻¹' {homMap X f a₀}) ≃
      (homMap X f ⁻¹' {homMap X f a₁}) :=
  MonoidHom.fiberEquiv (homMap X f) a₀ a₁

@[simp]
theorem homFiberEquiv_apply
    (X : Over (Spec (.of K))) (f : A ⟶ B) [IsMonHom f]
    (a₀ a₁ : X ⟶ A)
    (a : homMap X f ⁻¹' {homMap X f a₀}) :
    homFiberEquiv X f a₀ a₁ a = a₁ * (a₀⁻¹ * a) :=
  rfl

/-- Every section fibre of a group-scheme homomorphism is equivalent to its kernel. -/
noncomputable def homSectionFiberEquivKernel
    (f : A ⟶ B) [IsMonHom f]
    (a₀ : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    (homSectionMap f ⁻¹' {homSectionMap f a₀}) ≃ (homSectionMap f).ker :=
  MonoidHom.fiberEquivKer (homSectionMap f) a₀

/-- Finiteness of a section fibre is equivalent to finiteness of the section kernel. -/
theorem homSectionFiber_finite_iff_kernel_finite
    (f : A ⟶ B) [IsMonHom f]
    (a₀ : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    Finite (homSectionMap f ⁻¹' {homSectionMap f a₀}) ↔
      Finite (homSectionMap f).ker := by
  exact (homSectionFiberEquivKernel f a₀).finite_iff

/-- A finite section kernel gives finite section fibres at every chosen section. -/
theorem homSectionFiber_finite_of_kernel_finite
    (f : A ⟶ B) [IsMonHom f]
    (a₀ : 𝟙_ (Over (Spec (.of K))) ⟶ A)
    [Finite (homSectionMap f).ker] :
    Finite (homSectionMap f ⁻¹' {homSectionMap f a₀}) := by
  exact Finite.of_equiv _ (homSectionFiberEquivKernel f a₀).symm

/-- The identity homomorphism is an isogeny. -/
@[simp]
theorem Isogeny.id (A : Over (Spec (.of K))) [GrpObj A] :
    Isogeny (𝟙 A) := by
  constructor
  · infer_instance
  · dsimp [isogenyKernelToBase, isogenyKernel]
    infer_instance

/- An isomorphism of group schemes has trivial (hence finite) kernel.  The
   explicit forgetful transport is needed because the slice-category `IsIso`
   instance is not reducible through `Over.Hom.left` during synthesis. -/
theorem Isogeny.of_isIso (f : A ⟶ B) [IsMonHom f] [IsIso f] :
    Isogeny f := by
  letI : IsIso f.left := (Over.forget (Spec (CommRingCat.of K))).map_isIso f
  constructor
  · infer_instance
  · dsimp [isogenyKernelToBase, isogenyKernel]
    infer_instance

/- When the underlying homomorphisms are finite, the usual closure of finite
   and surjective morphisms under composition gives the corresponding
   isogeny.  The finite-map hypotheses are explicit until the full
   finite-kernel-to-finite-map theorem is available in Mathlib. -/
theorem Isogeny.comp_of_finite
    {C : Over (Spec (.of K))} [GrpObj C]
    (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g]
    [IsFinite f.left] [IsFinite g.left]
    (hf : Isogeny f) (hg : Isogeny g) :
    Isogeny (f ≫ g) := by
  letI : Surjective f.left := hf.1
  letI : Surjective g.left := hg.1
  constructor
  · rw [Over.comp_left]
    infer_instance
  · dsimp [isogenyKernelToBase, isogenyKernel]
    haveI : IsFinite ((f ≫ g).left) := by
      rw [Over.comp_left]
      infer_instance
    infer_instance

/- Composition with an isomorphism is a useful specialization of the finite
   composition lemma: the underlying map of the isomorphism is finite after
   transporting its `IsIso` instance through the slice forgetful functor. -/
theorem Isogeny.comp_of_isIso_left
    {C : Over (Spec (.of K))} [GrpObj C]
    (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g]
    [IsIso f] [IsFinite g.left] (hg : Isogeny g) :
    Isogeny (f ≫ g) := by
  letI : IsIso f.left := (Over.forget (Spec (CommRingCat.of K))).map_isIso f
  letI : IsFinite f.left := inferInstance
  exact Isogeny.comp_of_finite f g (Isogeny.of_isIso f) hg

theorem Isogeny.comp_of_isIso_right
    {C : Over (Spec (.of K))} [GrpObj C]
    (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g]
    [IsFinite f.left] [IsIso g] (hf : Isogeny f) :
    Isogeny (f ≫ g) := by
  letI : IsIso g.left := (Over.forget (Spec (CommRingCat.of K))).map_isIso g
  letI : IsFinite g.left := inferInstance
  exact Isogeny.comp_of_finite f g hf (Isogeny.of_isIso g)

omit [GrpObj A] in
/-- Finiteness of the underlying map makes the kernel finite by base change. -/
theorem isogenyKernelToBase_isFinite_of_finite
    (f : A ⟶ B) [IsFinite f.left] :
    IsFinite (isogenyKernelToBase f) := by
  change IsFinite (pullback.snd f.left (η[B].left))
  exact CategoryTheory.MorphismProperty.pullback_snd _ _
    (inferInstance : IsFinite f.left)

omit [GrpObj A] in
/-- Flatness of a homomorphism is inherited by its kernel over the identity. -/
theorem isogenyKernelToBase_flat_of_flat
    (f : A ⟶ B) [Flat f.left] :
    Flat (isogenyKernelToBase f) := by
  change Flat (pullback.snd f.left (η[B].left))
  exact CategoryTheory.MorphismProperty.pullback_snd _ _
    (inferInstance : Flat f.left)

omit [GrpObj A] in
/-- Surjectivity of a homomorphism is inherited by its kernel over the identity. -/
theorem isogenyKernelToBase_surjective_of_surjective
    (f : A ⟶ B) [Surjective f.left] :
    Surjective (isogenyKernelToBase f) := by
  change Surjective (pullback.snd f.left (η[B].left))
  exact CategoryTheory.MorphismProperty.pullback_snd _ _
    (inferInstance : Surjective f.left)

/- A proper morphism with finite set-theoretic fibres is finite.  This is the
   geometric bridge used in the finite-kernel direction of Milne's
   characterization; the separate group-theoretic argument identifying all
   fibres with translates of the kernel is intentionally left explicit. -/
theorem IsFinite.of_isProper_of_finite_preimage_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hfib : ∀ y : Y, (f ⁻¹' {y}).Finite) : IsFinite f := by
  letI : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f hfib
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/- Properness and a finite faithfully-flat base change also suffice for
   finiteness.  This is the scheme-level descent step used when passing an
   abelian-variety morphism to an algebraic closure. -/
theorem IsFinite.of_isProper_of_faithfullyFlat_baseChange
    {X Y Z : Scheme.{u}} (p : Y ⟶ Z) (f : X ⟶ Z)
    [Surjective p] [Flat p] [QuasiCompact p] [IsProper f]
    (hf : IsFinite (pullback.fst p f)) : IsFinite f := by
  letI : DescendsAlong @LocallyQuasiFinite
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    locallyQuasiFinite_descendsAlong_faithfullyFlat
  letI : IsFinite (pullback.fst p f) := hf
  letI : LocallyQuasiFinite (pullback.fst p f) := inferInstance
  letI : LocallyQuasiFinite f :=
    MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @LocallyQuasiFinite)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := p) (g := f)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

omit [GrpObj A] in
/-- For a proper morphism into a group scheme, a finite set-theoretic identity
fibre makes the scheme-theoretic kernel finite over the field. -/
theorem isogenyKernelToBase_isFinite_of_proper_of_finite_identity_fibre
    (f : A ⟶ B) [IsProper f.left]
    (h : (f.left ⁻¹' {(η[B].left).base (IsLocalRing.closedPoint K)}).Finite) :
    IsFinite (isogenyKernelToBase f) := by
  letI : IsProper (isogenyKernelToBase f) := by
    change IsProper (pullback.snd f.left (η[B].left))
    infer_instance
  letI : Finite (f.left ⁻¹' {(η[B].left).base (IsLocalRing.closedPoint K)}) :=
    h.to_subtype
  letI : Finite (isogenyKernel f) :=
    Finite.of_equiv _ (isogenyKernelHomeo f).symm.toEquiv
  apply IsFinite.of_isProper_of_finite_preimage_singleton _
  intro y
  have hy : y = (default : Spec (.of K)) := Subsingleton.elim _ _
  subst y
  have hpre :
      (isogenyKernelToBase f ⁻¹' {(default : Spec (.of K))}) =
        (Set.univ : Set (isogenyKernel f)) := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simp only [Set.mem_preimage]
      exact Subsingleton.elim _ _
  rw [hpre]
  exact Set.finite_univ

omit [GrpObj A] in
/-- A finite kernel morphism has a finite set-theoretic identity fibre. -/
theorem isogenyKernel_identity_fibre_finite_of_isFinite
    (f : A ⟶ B) [IsFinite (isogenyKernelToBase f)] :
    (f.left ⁻¹' {(η[B].left).base (IsLocalRing.closedPoint K)}).Finite := by
  have hpre :=
    Scheme.Hom.finite_preimage_singleton (isogenyKernelToBase f)
      (IsLocalRing.closedPoint K)
  have hEq :
      (isogenyKernelToBase f ⁻¹' {IsLocalRing.closedPoint K}) =
        (Set.univ : Set (isogenyKernel f)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hPset : (Set.univ : Set (isogenyKernel f)).Finite := by
    rw [← hEq]
    exact hpre
  letI : Finite (isogenyKernel f) :=
    Set.finite_univ_iff.mp hPset
  haveI : Finite (f.left ⁻¹' {(η[B].left).base (IsLocalRing.closedPoint K)}) := by
    exact (Equiv.finite_iff (isogenyKernelHomeo f).toEquiv).mp inferInstance
  exact Set.toFinite _

omit [GrpObj A] in
/-- Under properness of the underlying map, finite kernel and finite identity
fibre are equivalent as set-theoretic conditions. -/
theorem isogenyKernelToBase_isFinite_iff_identity_fibre_finite
    (f : A ⟶ B) [IsProper f.left] :
    IsFinite (isogenyKernelToBase f) ↔
      (f.left ⁻¹' {(η[B].left).base (IsLocalRing.closedPoint K)}).Finite := by
  constructor
  · intro h
    letI : IsFinite (isogenyKernelToBase f) := h
    exact isogenyKernel_identity_fibre_finite_of_isFinite f
  · intro h
    exact isogenyKernelToBase_isFinite_of_proper_of_finite_identity_fibre f h

/- For a proper scheme morphism, the residue-field fibres are the precise
   local quasi-finiteness input needed for finiteness.  This formulation is
   valid over arbitrary base fields and records the descent boundary used by
   the isogeny characterization below. -/
theorem isFinite_iff_finite_residue_fibres_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    IsFinite f ↔ ∀ y : Y, IsFinite (f.fiberToSpecResidueField y) := by
  constructor
  · intro hf y
    letI : IsFinite f := hf
    infer_instance
  · intro hf
    letI : QuasiCompact f := inferInstance
    letI : LocallyQuasiFinite f :=
      (locallyQuasiFinite_iff_isFinite_fiber).2 hf
    exact IsFinite.of_isProper_of_locallyQuasiFinite f

/- For a proper morphism, finiteness of a residue-field fibre is equivalent to
   finiteness of the corresponding underlying preimage.  The forward direction
   uses the fibre homeomorphism; the reverse direction packages the finite
   topological fibre with properness and the standard quasi-finite criterion. -/
theorem isFinite_fiberToSpecResidueField_iff_finite_preimage_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) :
    IsFinite (f.fiberToSpecResidueField y) ↔
      (f ⁻¹' {y}).Finite := by
  constructor
  · intro hf
    letI : IsFinite (f.fiberToSpecResidueField y) := hf
    have hpre :=
      Scheme.Hom.finite_preimage_singleton (f.fiberToSpecResidueField y)
        (IsLocalRing.closedPoint (Y.residueField y))
    have hEq :
        (f.fiberToSpecResidueField y ⁻¹'
          {IsLocalRing.closedPoint (Y.residueField y)}) =
          (Set.univ : Set (f.fiber y)) := by
      ext x
      constructor
      · intro _
        trivial
      · intro _
        exact f.fiberToSpecResidueField_apply y x
    have hPset : (Set.univ : Set (f.fiber y)).Finite := by
      rw [← hEq]
      exact hpre
    letI : Finite (f.fiber y) :=
      Set.finite_univ_iff.mp hPset
    haveI : Finite (f ⁻¹' {y}) := by
      exact (Equiv.finite_iff (f.fiberHomeo y).toEquiv).mp inferInstance
    exact Set.toFinite _
  · intro h
    letI : IsProper (f.fiberToSpecResidueField y) := by
      change IsProper (pullback.snd f (Y.fromSpecResidueField y))
      infer_instance
    letI : Finite (f ⁻¹' {y}) := h.to_subtype
    letI : Finite (f.fiber y) :=
      Finite.of_equiv _ (f.fiberHomeo y).symm.toEquiv
    apply IsFinite.of_isProper_of_finite_preimage_singleton _
    intro z
    have hpre :
        (f.fiberToSpecResidueField y ⁻¹' {z}) =
          (Set.univ : Set (f.fiber y)) := by
      ext x
      constructor
      · intro _
        trivial
      · intro _
        change f.fiberToSpecResidueField y x = z
        exact Subsingleton.elim _ _
    rw [hpre]
    exact Set.finite_univ

/- A homeomorphism square transports finiteness of a singleton fibre.  This
   set-theoretic form is useful because scheme fibres are represented by the
   underlying preimage sets in the current Mathlib API. -/
theorem finite_preimage_singleton_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (eX : X ≃ₜ X) (eY : Y ≃ₜ Y)
    (hcomm : ∀ z, f (eX z) = eY (f z)) {y : Y}
    (h : (f ⁻¹' {y}).Finite) : (f ⁻¹' {eY y}).Finite := by
  have hset : f ⁻¹' {eY y} = eX '' (f ⁻¹' {y}) := by
    ext z
    constructor
    · intro hz
      have hz' : f z = eY y := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
      let w := eX.symm z
      refine ⟨w, ?_, ?_⟩
      · change f w = y
        apply eY.injective
        calc
          eY (f w) = f (eX w) := (hcomm w).symm
          _ = f z := by rw [eX.apply_symm_apply]
          _ = eY y := hz'
      · exact eX.apply_symm_apply z
    · rintro ⟨w, hw, rfl⟩
      have hw' : f w = y := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hw
      change f (eX w) = eY y
      rw [hcomm]
      exact congrArg eY hw'
  rw [hset]
  exact h.image eX

/- Translation by a rational section identifies its target fibre with the
   identity fibre.  The statement is deliberately phrased for sections: the
   global residue-field consequence is derived below from finiteness of the
   entire underlying morphism. -/
theorem isogeny_fibre_finite_of_section
    (f : A ⟶ B) [IsMonHom f]
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A)
    (h : (f.left ⁻¹' {(η[B].left).base (IsLocalRing.closedPoint K)}).Finite) :
    (f.left ⁻¹' {((x ≫ f).left).base (IsLocalRing.closedPoint K)}).Finite := by
  let eX := pointTranslationIso A (η[A]) x
  let eY := pointTranslationIso B (η[B]) (x ≫ f)
  have hnat := pointTranslation_hom_naturality f (η[A]) x
  have hnat' : eX.hom ≫ f.left = f.left ≫ eY.hom := by
    change (pointTranslation A (η[A]) x).hom.left ≫ f.left =
      f.left ≫ (pointTranslation B (η[B]) (x ≫ f)).hom.left
    simpa using congrArg Over.Hom.left hnat
  have htransport :
      (f.left ⁻¹' {(Scheme.homeoOfIso eY)
        ((η[B].left).base (IsLocalRing.closedPoint K))}).Finite := by
    apply finite_preimage_singleton_of_homeomorph f.left
      (Scheme.homeoOfIso eX) (Scheme.homeoOfIso eY) (y :=
        (η[B].left).base (IsLocalRing.closedPoint K)) ?_ h
    intro z
    have hz := congrArg (fun q => q z) hnat'
    simpa [Scheme.Hom.comp_apply, Scheme.coe_homeoOfIso, eX, eY] using hz
  have hpoint :
      (Scheme.homeoOfIso eY) ((η[B].left).base (IsLocalRing.closedPoint K)) =
        ((x ≫ f).left).base (IsLocalRing.closedPoint K) := by
    change eY.hom ((η[B].left).base (IsLocalRing.closedPoint K)) = _
    simpa [eY] using
      (pointTranslationIso_hom_apply B (η[B]) (x ≫ f)
        (IsLocalRing.closedPoint K))
  rw [hpoint] at htransport
  exact htransport

/- The preceding transport is immediately available from the isogeny kernel
   condition, without asking callers to unpack its identity-fibre consequence. -/
theorem Isogeny.finite_fibre_of_section
    (f : A ⟶ B) [IsMonHom f] (hf : Isogeny f)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    (f.left ⁻¹' {((x ≫ f).left).base (IsLocalRing.closedPoint K)}).Finite := by
  letI : IsFinite (isogenyKernelToBase f) := hf.2
  exact isogeny_fibre_finite_of_section f x
    (isogenyKernel_identity_fibre_finite_of_isFinite f)

/- Over an algebraically closed field, a closed fibre with a chosen closed
   source point is finite.  The chosen point is the only geometric input here;
   selecting one in every fibre is the separate Jacobson-space step. -/
theorem Isogeny.finite_preimage_singleton_of_closed_point
    {K : Type u} [Field K] [IsAlgClosed K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f] (h : Isogeny f)
    {y : B.left} (hy : IsClosed {y})
    {x : A.left} (hx : IsClosed {x}) (hxy : f.left x = y) :
    (f.left ⁻¹' {y}).Finite := by
  letI : IsProper A.hom := hA.1
  letI : IsProper B.hom := hB.1
  letI : LocallyOfFiniteType A.hom := inferInstance
  letI : LocallyOfFiniteType B.hom := inferInstance
  letI : IsProper f.left := isProper_left_of_isAbelianVariety hA hB f
  letI : Surjective f.left := h.1
  letI : IsFinite (isogenyKernelToBase f) := h.2
  let py : Spec (.of K) ⟶ B.left := pointOfClosedPoint B.hom y hy
  have hpy : py ≫ B.hom = 𝟙 _ := pointOfClosedPoint_comp B.hom y hy
  let yhat : 𝟙_ (Over (Spec (.of K))) ⟶ B := Over.homMk py hpy
  have hyhat : yhat.left (IsLocalRing.closedPoint K) = y := by
    exact pointOfClosedPoint_apply B.hom y hy _
  let px : Spec (.of K) ⟶ A.left := pointOfClosedPoint A.hom x hx
  have hpx : px ≫ A.hom = 𝟙 _ := pointOfClosedPoint_comp A.hom x hx
  let xhat : 𝟙_ (Over (Spec (.of K))) ⟶ A := Over.homMk px hpx
  have hxhat : xhat.left (IsLocalRing.closedPoint K) = x := by
    exact pointOfClosedPoint_apply A.hom x hx _
  have hcomp : xhat ≫ f = yhat := by
    apply Over.OverMorphism.ext
    apply ext_of_apply_closedPoint_eq B.hom
    · exact Over.w _
    · exact Over.w _
    · change f.left (xhat.left (IsLocalRing.closedPoint K)) =
        yhat.left (IsLocalRing.closedPoint K)
      rw [hxhat, hxy, hyhat]
  have hn := pointTranslation_hom_naturality f (η[A]) xhat
  have hnL := congrArg Over.Hom.left hn
  have hnL2 :
      (pointTranslationIso A (η[A]) xhat).hom ≫ f.left =
        f.left ≫ (pointTranslationIso B (η[B]) yhat).hom := by
    simpa [pointTranslationIso_hom, hcomp] using hnL
  let e : B.left := (η[B].left).base (IsLocalRing.closedPoint K)
  let tauA := pointTranslationIso A (η[A]) xhat
  let tauB := pointTranslationIso B (η[B]) yhat
  let k : A.left → A.left := tauA.inv
  have htauB : tauB.hom e = y := by
    change (pointTranslationIso B (η[B]) yhat).hom
      ((η[B].left) (IsLocalRing.closedPoint K)) = y
    rw [pointTranslationIso_hom_apply]
    exact hyhat
  have htauBinv : tauB.inv y = e := by
    have hi := congrArg (fun g : B.left ⟶ B.left => g e) tauB.hom_inv_id
    have hi' : tauB.inv (tauB.hom e) = e := by
      change tauB.inv (tauB.hom e) = e at hi
      exact hi
    rw [htauB] at hi'
    exact hi'
  have hker : (f.left ⁻¹' {e}).Finite := by
    dsimp [e]
    exact isogenyKernel_identity_fibre_finite_of_isFinite f
  have hmap : Set.MapsTo k (f.left ⁻¹' {y}) (f.left ⁻¹' {e}) := by
    intro z hz
    change f.left (k z) = e
    have hval := congrArg (fun g : A.left ⟶ B.left => g (k z)) hnL2
    change f.left (tauA.hom (tauA.inv z)) =
      tauB.hom (f.left (tauA.inv z)) at hval
    have hi := congrArg (fun g : A.left ⟶ A.left => g z) tauA.inv_hom_id
    have hi' : tauA.hom (tauA.inv z) = z := by
      change tauA.hom (tauA.inv z) = z at hi
      exact hi
    rw [hi'] at hval
    have hval' := congrArg tauB.inv hval
    have hi2 := congrArg (fun g : B.left ⟶ B.left =>
      g (f.left (tauA.inv z))) tauB.hom_inv_id
    have hi2' : tauB.inv (tauB.hom (f.left (tauA.inv z))) =
        f.left (tauA.inv z) := by
      change tauB.inv (tauB.hom (f.left (tauA.inv z))) =
        f.left (tauA.inv z) at hi2
      exact hi2
    rw [hi2'] at hval'
    rw [hz, htauBinv] at hval'
    exact hval'.symm
  have hinj : Set.InjOn k (f.left ⁻¹' {y}) := by
    intro z₁ hz₁ z₂ hz₂ heq
    have heq' := congrArg (fun q : A.left => tauA.hom q) heq
    have hi₁ := congrArg (fun g : A.left ⟶ A.left => g z₁) tauA.inv_hom_id
    have hi₁' : tauA.hom (tauA.inv z₁) = z₁ := by
      change tauA.hom (tauA.inv z₁) = z₁ at hi₁
      exact hi₁
    have hi₂ := congrArg (fun g : A.left ⟶ A.left => g z₂) tauA.inv_hom_id
    have hi₂' : tauA.hom (tauA.inv z₂) = z₂ := by
      change tauA.hom (tauA.inv z₂) = z₂ at hi₂
      exact hi₂
    rw [hi₁', hi₂'] at heq'
    exact heq'
  exact Set.Finite.of_injOn hmap hinj hker

/- Surjectivity makes every closed target fibre nonempty.  Since the source is
   locally of finite type over the field, its Jacobson property supplies a
   closed source point in that fibre and discharges the preceding hypothesis. -/
theorem Isogeny.finite_preimage_singleton_of_closed_target
    {K : Type u} [Field K] [IsAlgClosed K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f] (h : Isogeny f)
    {y : B.left} (hy : IsClosed {y}) :
    (f.left ⁻¹' {y}).Finite := by
  letI : IsProper A.hom := hA.1
  letI : IsProper B.hom := hB.1
  letI : LocallyOfFiniteType A.hom := inferInstance
  letI : LocallyOfFiniteType B.hom := inferInstance
  letI : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  letI : Surjective f.left := h.1
  have hpre : (f.left ⁻¹' {y}).Nonempty := by
    obtain ⟨x, hx⟩ := f.left.surjective y
    exact ⟨x, hx⟩
  have hloc : IsLocallyClosed (f.left ⁻¹' {y}) :=
    (hy.preimage f.left.continuous).isLocallyClosed
  obtain ⟨x, hxpre, hxclosed⟩ :=
    nonempty_inter_closedPoints hpre hloc
  have hxy : f.left x = y := hxpre
  exact Isogeny.finite_preimage_singleton_of_closed_point hA hB f h hy
    (mem_closedPoints_iff.mp hxclosed) hxy

/- Zariski's main theorem turns the finite fibre above a closed point into a
   finite restriction on a target neighbourhood.  This is the local input used
   below to show that the entire morphism is finite. -/
theorem Isogeny.exists_isFinite_morphismRestrict_of_closed_target
    {K : Type u} [Field K] [IsAlgClosed K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f] (h : Isogeny f)
    {y : B.left} (hy : IsClosed {y}) :
    ∃ V : B.left.Opens, y ∈ V ∧ IsFinite (f.left ∣_ V) := by
  letI : IsProper f.left := isProper_left_of_isAbelianVariety hA hB f
  exact exists_isFinite_morphismRestrict_of_finite_preimage_singleton f.left y
    (Isogeny.finite_preimage_singleton_of_closed_target hA hB f h hy)

/- The finite neighbourhoods at closed points cover the quasi-finite locus.
   Jacobson density therefore upgrades closed-target fibre finiteness to global
   local quasi-finiteness; properness then gives a finite underlying map. -/
theorem Isogeny.isFinite_of_isAbelianVariety
    {K : Type u} [Field K] [IsAlgClosed K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f] (h : Isogeny f) : IsFinite f.left := by
  letI : IsProper A.hom := hA.1
  letI : IsProper B.hom := hB.1
  letI : LocallyOfFiniteType A.hom := inferInstance
  letI : LocallyOfFiniteType B.hom := inferInstance
  letI : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  letI : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  letI : LocallyOfFiniteType (f.left ≫ B.hom) := by
    rw [Over.w f]
    infer_instance
  letI : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left B.hom
  letI : IsProper f.left := isProper_left_of_isAbelianVariety hA hB f
  have htop : f.left.quasiFiniteLocus = ⊤ := by
    apply top_unique
    intro z hz
    by_contra hznot
    have hcomp : ((f.left.quasiFiniteLocus : Set A.left)ᶜ).Nonempty :=
      ⟨z, hznot⟩
    obtain ⟨x, hxcomp, hxclosed⟩ := nonempty_inter_closedPoints hcomp
      f.left.quasiFiniteLocus.isOpen.isClosed_compl.isLocallyClosed
    have hxclosed' : IsClosed {x} := mem_closedPoints_iff.mp hxclosed
    have hmap := Scheme.Hom.closePoints_subset_preimage_closedPoints f.left hxclosed'
    have hy : IsClosed {f.left x} := mem_closedPoints_iff.mp hmap
    obtain ⟨V, hyV, hfin⟩ :=
      Isogeny.exists_isFinite_morphismRestrict_of_closed_target hA hB f h hy
    letI : IsFinite (f.left ∣_ V) := hfin
    let xV : (f.left ⁻¹ᵁ V).toScheme := ⟨x, hyV⟩
    have hxV : (f.left ∣_ V).QuasiFiniteAt xV := by
      letI : LocallyQuasiFinite (f.left ∣_ V) := by infer_instance
      exact (f.left ∣_ V).quasiFiniteAt xV
    have hcompV : ((f.left ∣_ V) ≫ V.ι).QuasiFiniteAt xV := by
      rw [Scheme.Hom.quasiFiniteAt_comp_iff]
      exact hxV
    have hcompV' : ((f.left ⁻¹ᵁ V).ι ≫ f.left).QuasiFiniteAt xV := by
      simpa only [morphismRestrict_ι] using hcompV
    have hxq : f.left.QuasiFiniteAt ((f.left ⁻¹ᵁ V).ι xV) :=
      (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion).mp hcompV'
    have hxq' : f.left.QuasiFiniteAt x := by
      simpa [xV] using hxq
    have hxmem : x ∈ f.left.quasiFiniteLocus := by
      exact hxq'
    exact hxcomp hxmem
  have hLQF : LocallyQuasiFinite f.left :=
    (Scheme.Hom.quasiFiniteLocus_eq_top_iff (f := f.left)).mp htop
  letI : LocallyQuasiFinite f.left := hLQF
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

/- Once the source and intermediate abelian varieties are known to be
   proper over an algebraically closed field, the preceding theorem supplies
   the finite-map instances needed by the general composition result.  This
   is the usual closure of isogenies under composition, exposed without
   making callers repeat those implementation-level instances. -/
theorem Isogeny.comp_of_isAbelianVariety
    {K : Type u} [Field K] [IsAlgClosed K]
    {A B C : Over (Spec (.of K))} [GrpObj A] [GrpObj B] [GrpObj C]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (hC : IsAbelianVariety C)
    (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g]
    (hf : Isogeny f) (hg : Isogeny g) :
    Isogeny (f ≫ g) := by
  letI : IsFinite f.left := Isogeny.isFinite_of_isAbelianVariety hA hB f hf
  letI : IsFinite g.left := Isogeny.isFinite_of_isAbelianVariety hB hC g hg
  exact Isogeny.comp_of_finite f g hf hg

/- The same composition closure can be used over an arbitrary field once the
   residue-field finiteness input has been established for the two factors.
   Keeping that input explicit makes this a faithful adapter around the
   algebraic-closure descent theorem above. -/
theorem Isogeny.comp_of_finite_residue_fibres
    {K : Type u} [Field K]
    {A B C : Over (Spec (.of K))} [GrpObj A] [GrpObj B] [GrpObj C]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (hC : IsAbelianVariety C)
    (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g]
    (hf : Isogeny f) (hg : Isogeny g)
    (hff : ∀ y : B.left,
      IsFinite (f.left.fiberToSpecResidueField y))
    (hgf : ∀ z : C.left,
      IsFinite (g.left.fiberToSpecResidueField z)) :
    Isogeny (f ≫ g) := by
  letI : IsProper f.left := isProper_left_of_isAbelianVariety hA hB f
  letI : IsProper g.left := isProper_left_of_isAbelianVariety hB hC g
  letI : IsFinite f.left :=
    (isFinite_iff_finite_residue_fibres_of_isProper f.left).2 hff
  letI : IsFinite g.left :=
    (isFinite_iff_finite_residue_fibres_of_isProper g.left).2 hgf
  exact Isogeny.comp_of_finite f g hf hg

/- Once the underlying map is finite, every scheme-theoretic fibre obtained by
   pulling back the target point to its residue field is finite as well. -/
theorem Isogeny.isFinite_fiberToSpecResidueField
    {K : Type u} [Field K] [IsAlgClosed K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f] (h : Isogeny f) (y : B.left) :
    IsFinite (f.left.fiberToSpecResidueField y) := by
  letI : IsFinite f.left := Isogeny.isFinite_of_isAbelianVariety hA hB f h
  change IsFinite (pullback.snd f.left (B.left.fromSpecResidueField y))
  exact CategoryTheory.MorphismProperty.pullback_snd _ _
    (inferInstance : IsFinite f.left)

/- In the algebraically closed setting, the geometric isogeny condition now
   admits the expected finite-and-surjective reformulation. -/
theorem Isogeny.iff_isFinite_and_surjective_of_isAbelianVariety
    {K : Type u} [Field K] [IsAlgClosed K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f] :
    Isogeny f ↔ IsFinite f.left ∧ Surjective f.left := by
  constructor
  · intro h
    exact ⟨Isogeny.isFinite_of_isAbelianVariety hA hB f h, h.1⟩
  · rintro ⟨hf, hs⟩
    letI : IsFinite f.left := hf
    exact ⟨hs, isogenyKernelToBase_isFinite_of_finite f⟩

/- Over an arbitrary field, the same finite-and-surjective reformulation
   follows once the residue-field fibres have been descended.  The explicit
   hypothesis isolates that remaining geometric input without asserting the
   stronger blueprint characterization prematurely. -/
theorem Isogeny.iff_isFinite_and_surjective_of_isAbelianVariety_of_finite_residue_fibres
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f]
    (hfib : ∀ y : B.left, IsFinite (f.left.fiberToSpecResidueField y)) :
    Isogeny f ↔ IsFinite f.left ∧ Surjective f.left := by
  letI : IsProper f.left := isProper_left_of_isAbelianVariety hA hB f
  constructor
  · intro h
    exact ⟨(isFinite_iff_finite_residue_fibres_of_isProper f.left).2 hfib, h.1⟩
  · rintro ⟨hf, hs⟩
    letI : IsFinite f.left := hf
    exact ⟨hs, isogenyKernelToBase_isFinite_of_finite f⟩

/- The same criterion can be fed directly with finite underlying fibres.  This
   is the form produced by translation and geometric-point arguments; the
   residue-field scheme finiteness is supplied by the proper-fibre bridge
   above. -/
theorem Isogeny.iff_isFinite_and_surjective_of_isAbelianVariety_of_finite_set_fibres
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f]
    (hfib : ∀ y : B.left, (f.left ⁻¹' {y}).Finite) :
    Isogeny f ↔ IsFinite f.left ∧ Surjective f.left := by
  letI : IsProper f.left := isProper_left_of_isAbelianVariety hA hB f
  apply Isogeny.iff_isFinite_and_surjective_of_isAbelianVariety_of_finite_residue_fibres
    hA hB f
  intro y
  exact (isFinite_fiberToSpecResidueField_iff_finite_preimage_singleton f.left y).2
    (hfib y)

/- A finite underlying morphism has finite kernel, so in this common case the
   isogeny predicate is exactly surjectivity.  This generic interface keeps the
   finite-map hypothesis explicit; the abelian-variety specialization above
   supplies it over an algebraically closed field. -/
theorem Isogeny.of_surjective_of_finite
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left]
    (hf : Surjective f.left) : Isogeny f := by
  exact ⟨hf, isogenyKernelToBase_isFinite_of_finite f⟩

theorem Isogeny.iff_surjective_of_finite
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] :
    Isogeny f ↔ Surjective f.left := by
  constructor
  · intro h
    exact h.1
  · exact Isogeny.of_surjective_of_finite f

theorem Isogeny.surjective (f : A ⟶ B) [IsMonHom f] (h : Isogeny f) :
    Surjective f.left :=
  h.1

theorem Isogeny.finite_kernel (f : A ⟶ B) [IsMonHom f] (h : Isogeny f) :
    IsFinite (isogenyKernelToBase f) :=
  h.2

/- The finite kernel of an isogeny remains finite after arbitrary base change.
   In particular, specializing `Z` to a field spectrum supplies the finite
   geometric-kernel morphism used by residue-field fibre arguments. -/
theorem Isogeny.kernel_baseChange_isFinite
    (f : A ⟶ B) [IsMonHom f] (h : Isogeny f)
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) :
    IsFinite (pullback.snd (isogenyKernelToBase f) g) := by
  letI : IsFinite (isogenyKernelToBase f) := h.2
  exact MorphismProperty.pullback_snd _ _ inferInstance

/- The finite-flat-surjective condition from Milne's characterization implies
   the source-faithful isogeny predicate.  The flatness hypothesis is retained
   in the interface because it is part of the geometric characterization and
   is used by the companion kernel lemma below. -/
theorem Isogeny.of_finite_flat_surjective
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left]
    (hf : Surjective f.left) : Isogeny f := by
  exact Isogeny.of_surjective_of_finite f hf

/- A flat isogeny has a finite, flat, and surjective kernel over the base. -/
theorem Isogeny.kernel_isFinite_flat_surjective
    (f : A ⟶ B) [IsMonHom f] [Flat f.left] (h : Isogeny f) :
    IsFinite (isogenyKernelToBase f) ∧
      Flat (isogenyKernelToBase f) ∧ Surjective (isogenyKernelToBase f) := by
  letI : Surjective f.left := h.1
  exact ⟨h.2, isogenyKernelToBase_flat_of_flat f,
    isogenyKernelToBase_surjective_of_surjective f⟩

/- A flat isogeny's kernel is finite, flat, and surjective over the base.  These
   three properties are stable under pulling the kernel back along any scheme
   over the base, which packages the geometric-fibre transport needed in the
   finite-flat characterization. -/
theorem Isogeny.kernel_baseChange_isFinite_flat_surjective
    (f : A ⟶ B) [IsMonHom f] [Flat f.left] (h : Isogeny f)
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) :
    IsFinite (pullback.snd (isogenyKernelToBase f) g) ∧
      Flat (pullback.snd (isogenyKernelToBase f) g) ∧
      Surjective (pullback.snd (isogenyKernelToBase f) g) := by
  letI : IsFinite (isogenyKernelToBase f) := h.2
  letI : Flat (isogenyKernelToBase f) := isogenyKernelToBase_flat_of_flat f
  letI : Surjective (isogenyKernelToBase f) := by
    letI : Surjective f.left := h.1
    exact isogenyKernelToBase_surjective_of_surjective f
  exact ⟨MorphismProperty.pullback_snd _ _ inferInstance,
    MorphismProperty.pullback_snd _ _ inferInstance,
    MorphismProperty.pullback_snd _ _ inferInstance⟩

/- The base change of the kernel is the iterated pullback obtained by first
   taking the identity fibre and then changing the ground field.  This
   associativity iso is the concrete scheme-level comparison used below. -/
noncomputable def isogenyKernel_baseChange_assocIso
    {L : Type u} [Field L]
    (f : A ⟶ B) (b : Spec (.of L) ⟶ Spec (.of K)) :
    pullback (isogenyKernelToBase f) b ≅
      pullback f.left (b ≫ (η[B]).left) :=
  pullbackLeftPullbackSndIso f.left (η[B]).left b

omit [GrpObj A] in
@[reassoc (attr := simp)]
theorem isogenyKernel_baseChange_assocIso_hom_fst
    {L : Type u} [Field L]
    (f : A ⟶ B) (b : Spec (.of L) ⟶ Spec (.of K)) :
    (isogenyKernel_baseChange_assocIso f b).hom ≫
        pullback.fst f.left (b ≫ (η[B]).left) =
      pullback.fst (isogenyKernelToBase f) b ≫
        pullback.fst f.left (η[B]).left := by
  exact pullbackLeftPullbackSndIso_hom_fst f.left (η[B]).left b

omit [GrpObj A] in
@[reassoc (attr := simp)]
theorem isogenyKernel_baseChange_assocIso_hom_snd
    {L : Type u} [Field L]
    (f : A ⟶ B) (b : Spec (.of L) ⟶ Spec (.of K)) :
    (isogenyKernel_baseChange_assocIso f b).hom ≫
        pullback.snd f.left (b ≫ (η[B]).left) =
      pullback.snd (isogenyKernelToBase f) b := by
  exact pullbackLeftPullbackSndIso_hom_snd f.left (η[B]).left b

/- The same comparison in the slice category retains the structure morphism
   over the base.  In particular, it exposes the map on the identity section
   after applying the `Over.pullback` functor, without choosing a presentation
   of that section on underlying schemes. -/
noncomputable def isogenyKernelOver (f : A ⟶ B) : Over (Spec (.of K)) :=
  Limits.pullback f (η[B])

noncomputable def isogenyKernelOver_baseChangeIso
    {L : Type u} [Field L]
    (f : A ⟶ B) (b : Spec (.of L) ⟶ Spec (.of K)) :
    (Over.pullback b).obj (isogenyKernelOver f) ≅
      Limits.pullback ((Over.pullback b).map f)
        ((Over.pullback b).map (η[B])) :=
  PreservesPullback.iso (Over.pullback b) f (η[B])

omit [GrpObj A] in
@[reassoc (attr := simp)]
theorem isogenyKernelOver_baseChangeIso_hom_fst
    {L : Type u} [Field L]
    (f : A ⟶ B) (b : Spec (.of L) ⟶ Spec (.of K)) :
    (isogenyKernelOver_baseChangeIso f b).hom ≫
        pullback.fst ((Over.pullback b).map f)
          ((Over.pullback b).map (η[B])) =
      (Over.pullback b).map (pullback.fst f (η[B])) := by
  exact pullbackComparison_comp_fst (Over.pullback b) f (η[B])

omit [GrpObj A] in
@[reassoc (attr := simp)]
theorem isogenyKernelOver_baseChangeIso_hom_snd
    {L : Type u} [Field L]
    (f : A ⟶ B) (b : Spec (.of L) ⟶ Spec (.of K)) :
    (isogenyKernelOver_baseChangeIso f b).hom ≫
        pullback.snd ((Over.pullback b).map f)
          ((Over.pullback b).map (η[B])) =
      (Over.pullback b).map (pullback.snd f (η[B])) := by
  exact pullbackComparison_comp_snd (Over.pullback b) f (η[B])

/- An isogeny whose underlying morphism is already known to be finite remains
   an isogeny after arbitrary base change of the field.  The finite and
   surjective hypotheses are transported by the `Over` pullback functor. -/
theorem Isogeny.baseChange_of_finite
    {L : Type u} [Field L]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left]
    (h : Isogeny f) (b : Spec (.of L) ⟶ Spec (.of K)) :
    let F := Over.pullback b
    letI : GrpObj (F.obj A) := Functor.grpObjObj
    letI : GrpObj (F.obj B) := Functor.grpObjObj
    Isogeny (F.map f) := by
  let F := Over.pullback b
  letI : GrpObj (F.obj A) := Functor.grpObjObj
  letI : GrpObj (F.obj B) := Functor.grpObjObj
  letI : IsFinite (F.map f).left :=
    MorphismProperty.overPullbackMap b f (inferInstance : IsFinite f.left)
  letI : Surjective (F.map f).left :=
    MorphismProperty.overPullbackMap b f h.1
  change Isogeny (F.map f)
  exact Isogeny.of_surjective_of_finite (F.map f) inferInstance

/- Over an algebraically closed base, the established finite-map theorem
   supplies the hypothesis required by `baseChange_of_finite`. -/
theorem Isogeny.baseChange_of_isAbelianVariety
    {K L : Type u} [Field K] [IsAlgClosed K] [Field L]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f] (h : Isogeny f)
    (b : Spec (.of L) ⟶ Spec (.of K)) :
    let F := Over.pullback b
    letI : GrpObj (F.obj A) := Functor.grpObjObj
    letI : GrpObj (F.obj B) := Functor.grpObjObj
    Isogeny (F.map f) := by
  letI : IsFinite f.left := Isogeny.isFinite_of_isAbelianVariety hA hB f h
  exact Isogeny.baseChange_of_finite f h b

/- The finite-map converse can be descended from the algebraic closure.  The
   explicit pullback fibre is the map obtained by pulling `f.left` back along
   the faithfully flat cover of `B` induced by
   `Spec (AlgebraicClosure K) → Spec K`. -/
theorem Isogeny.of_surjective_of_algebraicClosure_baseChange
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f]
    (hs : Surjective f.left)
    (hf : IsFinite
      (pullback.fst
        (pullback.fst B.hom
          (Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))))
        f.left)) :
    Isogeny f := by
  let b : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let p : pullback B.hom b ⟶ B.left := pullback.fst B.hom b
  have hff : (algebraMap K (AlgebraicClosure K)).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  have hp : Flat b ∧ Surjective b := by
    change Flat (Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))) ∧
      Surjective (Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K)))
    rwa [flat_and_surjective_SpecMap_iff]
  letI : Flat b := hp.1
  letI : Surjective b := hp.2
  letI : QuasiCompact b := inferInstance
  letI : Flat p := by
    dsimp [p]
    infer_instance
  letI : Surjective p := by
    dsimp [p]
    infer_instance
  letI : QuasiCompact p := by
    dsimp [p]
    infer_instance
  letI : IsProper f.left := isProper_left_of_isAbelianVariety hA hB f
  letI : IsFinite f.left :=
    IsFinite.of_isProper_of_faithfullyFlat_baseChange p f.left hf
  exact Isogeny.of_surjective_of_finite f hs

/- Pullback-pasting transports finiteness of the map produced by the `Over`
   pullback functor to the iterated pullback fibre used by the descent
   criterion.  The explicit isomorphism keeps the categorical identifications
   transparent to elaboration. -/
theorem isFinite_overPullbackMap_to_fibre
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (f : A ⟶ B) [IsMonHom f]
    {L : Type u} [Field L]
    (b : Spec (.of L) ⟶ Spec (.of K)) :
    IsFinite ((Over.pullback b).map f).left →
      IsFinite (pullback.fst (pullback.fst B.hom b) f.left) := by
  intro hq
  have hcond :
      (pullback.fst A.hom b ≫ f.left) ≫ B.hom =
        pullback.snd A.hom b ≫ b := by
    rw [Category.assoc, CategoryTheory.Over.w f]
    exact pullback.condition
  let q : pullback A.hom b ⟶ pullback B.hom b :=
    pullback.lift (pullback.fst A.hom b ≫ f.left) (pullback.snd A.hom b)
      hcond
  have hq' : IsFinite q := by
    change IsFinite q at hq
    exact hq
  let p : pullback B.hom b ⟶ B.left := pullback.fst B.hom b
  let e1 := pullbackRightPullbackFstIso B.hom b f.left
  let e2 := pullbackSymmetry f.left p
  let c : pullback A.hom b ≅ pullback (f.left ≫ B.hom) b :=
    pullback.congrHom (Over.w f).symm rfl
  let d := c ≪≫ e1.symm ≪≫ e2
  have he2_fst : e2.hom ≫ pullback.fst p f.left = pullback.snd f.left p := by
    simp [e2, p]
  have he1_inv_snd_fst :
      e1.inv ≫ pullback.snd f.left p ≫ pullback.fst B.hom b =
        pullback.fst (f.left ≫ B.hom) b ≫ f.left := by
    simp [e1, p]
  have he1_inv_snd_snd :
      e1.inv ≫ pullback.snd f.left p ≫ pullback.snd B.hom b =
        pullback.snd (f.left ≫ B.hom) b := by
    simp [e1, p]
  have hc_fst :
      c.hom ≫ pullback.fst (f.left ≫ B.hom) b = pullback.fst A.hom b := by
    rw [pullback.congrHom_hom]
    change pullback.lift (pullback.fst A.hom b) (pullback.snd A.hom b) _ ≫
      pullback.fst (f.left ≫ B.hom) b = _
    exact pullback.lift_fst _ _ _
  have hc_snd :
      c.hom ≫ pullback.snd (f.left ≫ B.hom) b = pullback.snd A.hom b := by
    rw [pullback.congrHom_hom]
    change pullback.lift (pullback.fst A.hom b) (pullback.snd A.hom b) _ ≫
      pullback.snd (f.left ≫ B.hom) b = _
    exact pullback.lift_snd _ _ _
  have hm_fst :
      q ≫ pullback.fst B.hom b = pullback.fst A.hom b ≫ f.left := by
    dsimp [q]
    exact pullback.lift_fst _ _ _
  have hm_snd :
      q ≫ pullback.snd B.hom b = pullback.snd A.hom b := by
    dsimp [q]
    exact pullback.lift_snd _ _ _
  have he2_fst_assoc :
      e2.hom ≫ pullback.fst p f.left ≫ pullback.fst B.hom b =
        pullback.snd f.left p ≫ pullback.fst B.hom b := by
    rw [← Category.assoc, he2_fst]
  have he2_fst_assoc_snd :
      e2.hom ≫ pullback.fst p f.left ≫ pullback.snd B.hom b =
        pullback.snd f.left p ≫ pullback.snd B.hom b := by
    rw [← Category.assoc, he2_fst]
  have he : d.hom ≫ pullback.fst p f.left = q := by
    apply pullback.hom_ext
    · calc
        d.hom ≫ pullback.fst p f.left ≫ pullback.fst B.hom b
            = c.hom ≫ e1.inv ≫ e2.hom ≫ pullback.fst p f.left ≫
                pullback.fst B.hom b := by
                  simp [d, Iso.trans_hom, Category.assoc]
        _ = c.hom ≫ e1.inv ≫ pullback.snd f.left p ≫
              pullback.fst B.hom b := by rw [he2_fst_assoc]
        _ = c.hom ≫ pullback.fst (f.left ≫ B.hom) b ≫ f.left := by
              rw [he1_inv_snd_fst]
        _ = pullback.fst A.hom b ≫ f.left := by
              change (c.hom ≫ pullback.fst (f.left ≫ B.hom) b) ≫ f.left = _
              rw [hc_fst]
        _ = q ≫ pullback.fst B.hom b := by rw [← hm_fst]
    · calc
        d.hom ≫ pullback.fst p f.left ≫ pullback.snd B.hom b
            = c.hom ≫ e1.inv ≫ e2.hom ≫ pullback.fst p f.left ≫
                pullback.snd B.hom b := by
                  simp [d, Iso.trans_hom, Category.assoc]
        _ = c.hom ≫ e1.inv ≫ pullback.snd f.left p ≫
              pullback.snd B.hom b := by rw [he2_fst_assoc_snd]
        _ = c.hom ≫ pullback.snd (f.left ≫ B.hom) b := by
              rw [he1_inv_snd_snd]
        _ = pullback.snd A.hom b := by
              rw [hc_snd]
        _ = q ≫ pullback.snd B.hom b := by rw [← hm_snd]
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) d.hom
    (pullback.fst p f.left)).mp
  rw [he]
  exact hq'

/- Finiteness of an isogeny after algebraic-closure base change descends to
   the original morphism.  This is the finite-map half of the geometric
   isogeny criterion and does not require a separate surjectivity hypothesis. -/
theorem finite_of_algebraicClosure_baseChange_isogeny
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f]
    (hgeom :
      let F := Over.pullback
        (Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K)))
      letI : GrpObj (F.obj A) := Functor.grpObjObj
      letI : GrpObj (F.obj B) := Functor.grpObjObj
      Isogeny (F.map f)) :
    IsFinite f.left := by
  let b : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback b
  letI : GrpObj (F.obj A) := Functor.grpObjObj
  letI : GrpObj (F.obj B) := Functor.grpObjObj
  have hgeom' : Isogeny (F.map f) := by
    simpa [F, b] using hgeom
  have hA' : IsAbelianVariety (F.obj A) := by
    exact hA.baseChange b
  have hB' : IsAbelianVariety (F.obj B) := by
    exact hB.baseChange b
  letI : IsFinite (F.map f).left :=
    Isogeny.isFinite_of_isAbelianVariety hA' hB' (F.map f) hgeom'
  have hf : IsFinite
      (pullback.fst (pullback.fst B.hom b) f.left) := by
    exact isFinite_overPullbackMap_to_fibre f b
      (inferInstance : IsFinite (F.map f).left)
  let p : pullback B.hom b ⟶ B.left := pullback.fst B.hom b
  have hff : (algebraMap K (AlgebraicClosure K)).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  have hp : Flat b ∧ Surjective b := by
    change Flat (Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))) ∧
      Surjective (Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K)))
    rwa [flat_and_surjective_SpecMap_iff]
  letI : Flat b := hp.1
  letI : Surjective b := hp.2
  letI : QuasiCompact b := inferInstance
  letI : Flat p := by
    dsimp [p]
    infer_instance
  letI : Surjective p := by
    dsimp [p]
    infer_instance
  letI : QuasiCompact p := by
    dsimp [p]
    infer_instance
  letI : IsProper f.left := isProper_left_of_isAbelianVariety hA hB f
  exact IsFinite.of_isProper_of_faithfullyFlat_baseChange p f.left hf

/- Surjectivity of an `Over` morphism descends from any surjective base change.
   The proof composes the pulled-back map with the target pullback projection,
   then cancels the source projection set-theoretically. -/
theorem surjective_of_overPullbackMap
    {S T : Scheme.{u}} {A B : Over S}
    (b : T ⟶ S) [Surjective b] (f : A ⟶ B)
    (h : Surjective ((Over.pullback b).map f).left) :
    Surjective f.left := by
  let p : pullback B.hom b ⟶ B.left := pullback.fst B.hom b
  letI : Surjective p := by
    dsimp [p]
    infer_instance
  have hcond :
      (pullback.fst A.hom b ≫ f.left) ≫ B.hom =
        pullback.snd A.hom b ≫ b := by
    rw [Category.assoc, CategoryTheory.Over.w f]
    exact pullback.condition
  let q : pullback A.hom b ⟶ pullback B.hom b :=
    pullback.lift (pullback.fst A.hom b ≫ f.left) (pullback.snd A.hom b) hcond
  have hq : Surjective q := by
    change Surjective q at h
    exact h
  letI : Surjective q := hq
  haveI : Surjective (q ≫ p) := inferInstance
  have hm_fst :
      q ≫ p = pullback.fst A.hom b ≫ f.left := by
    dsimp [q, p]
    exact pullback.lift_fst _ _ _
  haveI : Surjective (pullback.fst A.hom b ≫ f.left) := hm_fst ▸ inferInstance
  exact Surjective.of_comp (pullback.fst A.hom b) f.left

/- Surjectivity also descends from the algebraic-closure base change.  The
   specialization installs the canonical surjectivity instance for the
   algebraic-closure spectrum map and invokes the generic lemma above. -/
theorem surjective_of_algebraicClosure_baseChange_isogeny
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (f : A ⟶ B) [IsMonHom f]
    (hgeom :
      let F := Over.pullback
        (Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K)))
      letI : GrpObj (F.obj A) := Functor.grpObjObj
      letI : GrpObj (F.obj B) := Functor.grpObjObj
      Isogeny (F.map f)) :
    Surjective f.left := by
  let b : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback b
  letI : GrpObj (F.obj A) := Functor.grpObjObj
  letI : GrpObj (F.obj B) := Functor.grpObjObj
  have hgeom' : Isogeny (F.map f) := by
    simpa [F, b] using hgeom
  letI : Surjective b := by
    dsimp [b]
    infer_instance
  exact surjective_of_overPullbackMap b f hgeom'.1

/- Combining the two descent halves removes the auxiliary surjectivity input
   from the arbitrary-field algebraic-closure characterization. -/
theorem Isogeny.of_algebraicClosure_baseChange_isogeny
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f]
    (hgeom :
      let F := Over.pullback
        (Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K)))
      letI : GrpObj (F.obj A) := Functor.grpObjObj
      letI : GrpObj (F.obj B) := Functor.grpObjObj
      Isogeny (F.map f)) :
    Isogeny f := by
  letI : IsFinite f.left :=
    finite_of_algebraicClosure_baseChange_isogeny hA hB f hgeom
  exact Isogeny.of_surjective_of_finite f
    (surjective_of_algebraicClosure_baseChange_isogeny f hgeom)

/- A geometric isogeny certificate over the algebraic closure supplies the
   finite pullback required by the faithfully-flat descent theorem above.  This
   legacy corollary retains an explicit surjectivity argument for callers; the
   stronger algebraic-closure characterization immediately above derives it
   by the generic pullback-surjectivity lemma. -/
theorem Isogeny.of_surjective_of_algebraicClosure_baseChange_isogeny
    {K : Type u} [Field K]
    {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
    (hA : IsAbelianVariety A) (hB : IsAbelianVariety B)
    (f : A ⟶ B) [IsMonHom f]
    (hs : Surjective f.left)
    (hgeom :
      let F := Over.pullback
        (Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K)))
      letI : GrpObj (F.obj A) := Functor.grpObjObj
      letI : GrpObj (F.obj B) := Functor.grpObjObj
      Isogeny (F.map f)) :
    Isogeny f := by
  letI : IsFinite f.left :=
    finite_of_algebraicClosure_baseChange_isogeny hA hB f hgeom
  exact Isogeny.of_surjective_of_finite f hs

end MilneLib
