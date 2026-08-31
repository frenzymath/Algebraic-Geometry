/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.GaloisKernelCover
import AlgebraicJacobian.Picard.Pic0FiniteGaloisDescent
import AlgebraicJacobian.Picard.Pic0SigmaEtaleSheaf

/-!
# Finite-Galois invariant comparison for Picard zero
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open AlgebraicJacobian.GaloisDescent

namespace AlgebraicGeometry

noncomputable section

open Scheme Scheme.PicScheme

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable (C : Over (Spec (CommRingCat.of K)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

/-- Picard-zero classes on the finite-Galois base change of `T` fixed by every
deck transformation.  The classes are kept in the `K`-slice, where the deck
transformations are honest endomorphisms. -/
def Pic0GaloisInvariant (T : Over (Spec (CommRingCat.of K))) : Type u :=
  {x : (pic0TypeFunctor C).obj
      (op ((restrictTest K L).obj (baseTest (k' := L) T))) //
    ∀ gamma : L ≃ₐ[K] L,
      (pic0TypeFunctor C).map (twistTest T gamma).op x = x}

/-- Restriction of a Picard-zero class to the finite-Galois base change, with
its tautological invariance. -/
noncomputable def pic0RestrictToGaloisInvariant
    (T : Over (Spec (CommRingCat.of K)))
    (x : (pic0TypeFunctor C).obj (op T)) : Pic0GaloisInvariant (L := L) C T := by
  refine ⟨(pic0TypeFunctor C).map (coverMap (k' := L) T).op x, ?_⟩
  intro gamma
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
    twistTest_comp_coverMap]

omit [GeometricallyReduced C.hom] in
/-- A Galois-invariant Picard-zero class satisfies the kernel-pair equality
for the field-extension cover. -/
theorem pic0GaloisInvariant_pullback_condition
    [FiniteDimensional K L] [IsGalois K L]
    (T : Over (Spec (CommRingCat.of K)))
    (x : Pic0GaloisInvariant (L := L) C T) :
    (pic0TypeFunctor C).map
        (pullback.fst (coverMap (k' := L) T) (coverMap (k' := L) T)).op x.1 =
      (pic0TypeFunctor C).map
        (pullback.snd (coverMap (k' := L) T) (coverMap (k' := L) T)).op x.1 := by
  let f := fun gamma : L ≃ₐ[K] L => coverSelfSection (k' := L) T gamma
  letI (gamma : L ≃ₐ[K] L) : IsOpenImmersion (f gamma).left :=
    isOpenImmersion_coverSelfSection_left (k' := L) T gamma
  have hcov : ∀ p : (pullback (coverMap (k' := L) T)
      (coverMap (k' := L) T)).left, ∃ gamma, p ∈ (f gamma).left.opensRange := by
    intro p
    obtain ⟨gamma, y, hy⟩ := coverSelfSection_jointlySurjective (k' := L) T p
    exact ⟨gamma, y, hy⟩
  apply pic0Subgroup_ext_of_cover (C := C) f hcov
  intro gamma
  change (pic0TypeFunctor C).map (f gamma).op
      ((pic0TypeFunctor C).map
        (pullback.fst (coverMap (k' := L) T) (coverMap (k' := L) T)).op x.1) = _
  calc
    _ = (pic0TypeFunctor C).map
        (f gamma ≫ pullback.fst (coverMap (k' := L) T)
          (coverMap (k' := L) T)).op x.1 := by
      rw [op_comp, Functor.map_comp]
      rfl
    _ = x.1 := by
      rw [coverSelfSection_fst]
      exact Functor.map_id_apply (pic0TypeFunctor C) _ x.1
    _ = (pic0TypeFunctor C).map (twistTest T gamma).op x.1 :=
      (x.2 gamma).symm
    _ = (pic0TypeFunctor C).map (f gamma).op
        ((pic0TypeFunctor C).map
          (pullback.snd (coverMap (k' := L) T) (coverMap (k' := L) T)).op x.1) := by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
        coverSelfSection_snd]

omit [GeometricallyReduced C.hom] in
/-- Galois invariance is the full compatibility condition for the
field-extension cover, not only the equality on its chosen pullback. -/
theorem pic0GaloisInvariant_compatible
    [FiniteDimensional K L] [IsGalois K L]
    (T : Over (Spec (CommRingCat.of K)))
    (x : Pic0GaloisInvariant (L := L) C T)
    {Z : Over (Spec (CommRingCat.of K))}
    (g₁ g₂ : Z ⟶ (restrictTest K L).obj (baseTest (k' := L) T))
    (h : g₁ ≫ coverMap (k' := L) T = g₂ ≫ coverMap (k' := L) T) :
    (pic0TypeFunctor C).map g₁.op x.1 =
      (pic0TypeFunctor C).map g₂.op x.1 := by
  let q : Z ⟶ pullback (coverMap (k' := L) T) (coverMap (k' := L) T) :=
    pullback.lift g₁ g₂ h
  calc
    (pic0TypeFunctor C).map g₁.op x.1 =
        (pic0TypeFunctor C).map q.op
          ((pic0TypeFunctor C).map
            (pullback.fst (coverMap (k' := L) T) (coverMap (k' := L) T)).op x.1) := by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
        pullback.lift_fst]
    _ = (pic0TypeFunctor C).map q.op
          ((pic0TypeFunctor C).map
            (pullback.snd (coverMap (k' := L) T) (coverMap (k' := L) T)).op x.1) :=
      congrArg ((pic0TypeFunctor C).map q.op)
        (pic0GaloisInvariant_pullback_condition C T x)
    _ = (pic0TypeFunctor C).map g₂.op x.1 := by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
        pullback.lift_snd]

omit [GeometricallyReduced C.hom] in
/-- The Sigma-extension element attached to an invariant class is compatible
for the singleton field-extension cover. -/
theorem pic0GaloisInvariant_sigma_compatible
    [FiniteDimensional K L] [IsGalois K L]
    (T : Over (Spec (CommRingCat.of K)))
    (x : Pic0GaloisInvariant (L := L) C T)
    {Z : Scheme.{u}}
    (p₁ p₂ : Z ⟶ ((restrictTest K L).obj (baseTest (k' := L) T)).left)
    (hp : p₁ ≫ (coverMap (k' := L) T).left =
      p₂ ≫ (coverMap (k' := L) T).left) :
    (pic0SigmaFunctor C).map p₁.op
        ⟨((restrictTest K L).obj (baseTest (k' := L) T)).hom, x.1⟩ =
      (pic0SigmaFunctor C).map p₂.op
        ⟨((restrictTest K L).obj (baseTest (k' := L) T)).hom, x.1⟩ := by
  let B := (restrictTest K L).obj (baseTest (k' := L) T)
  have hbase : p₁ ≫ B.hom = p₂ ≫ B.hom := by
    rw [← Over.w (coverMap (k' := L) T)]
    simpa only [Category.assoc] using congrArg (fun q => q ≫ T.hom) hp
  let ZK : Over (Spec (CommRingCat.of K)) := Over.mk (p₁ ≫ B.hom)
  let g₁ : ZK ⟶ B := Over.homMk p₁ rfl
  let g₂ : ZK ⟶ B := Over.homMk p₂ hbase.symm
  have hg : g₁ ≫ coverMap (k' := L) T = g₂ ≫ coverMap (k' := L) T := by
    apply Over.OverMorphism.ext
    exact hp
  have hfib : (pic0TypeFunctor C).map g₁.op x.1 =
      (pic0TypeFunctor C).map g₂.op x.1 :=
    pic0GaloisInvariant_compatible C T x g₁ g₂ hg
  let y := (pic0TypeFunctor C).map g₁.op x.1
  have h₁ : (pic0SigmaFunctor C).map p₁.op ⟨B.hom, x.1⟩ =
      ⟨p₁ ≫ B.hom, y⟩ :=
    (Over.sigmaExtension_map_mk_eq_iff (F := pic0TypeFunctor C)
      p₁ rfl x.1 y).mpr rfl
  have h₂ : (pic0SigmaFunctor C).map p₂.op ⟨B.hom, x.1⟩ =
      ⟨p₁ ≫ B.hom, y⟩ :=
    (Over.sigmaExtension_map_mk_eq_iff (F := pic0TypeFunctor C)
      p₂ hbase.symm x.1 y).mpr hfib.symm
  exact h₁.trans h₂.symm

/-- Every invariant class descends uniquely along the finite-Galois field
extension cover.  This is the effective-descent half of the comparison. -/
theorem pic0GaloisInvariant_existsUnique_descend
    [FiniteDimensional K L] [IsGalois K L]
    (T : Over (Spec (CommRingCat.of K)))
    (x : Pic0GaloisInvariant (L := L) C T) :
    ∃! y : (pic0TypeFunctor C).obj (op T),
      (pic0TypeFunctor C).map (coverMap (k' := L) T).op y = x.1 := by
  let B := (restrictTest K L).obj (baseTest (k' := L) T)
  let f := (coverMap (k' := L) T).left
  haveI : Etale f := by
    exact Scheme.etale_pullback_fst_specMap K L T.left T.hom
  haveI : Surjective f := by
    exact Scheme.surjective_pullback_fst_specMap K L T.left T.hom
  haveI : Flat f := inferInstance
  haveI : EffectiveEpi f := inferInstance
  have hmem : Presieve.singleton f ∈ Scheme.precoverage (@Etale) T.left := by
    rw [Scheme.singleton_mem_precoverage_iff]
    exact ⟨f.surjective, inferInstance⟩
  have hsheaf : Presieve.IsSheafFor (pic0SigmaFunctor C)
      (Presieve.singleton f) :=
    (pic0SigmaFunctor_isSheaf_etale C).isSheafFor_of_mem_precoverage hmem
  rw [Presieve.isSheafFor_singleton] at hsheaf
  obtain ⟨⟨a, z⟩, hz, hzu⟩ := hsheaf ⟨B.hom, x.1⟩
    (fun p₁ p₂ hp => pic0GaloisInvariant_sigma_compatible C T x p₁ p₂ hp)
  have hfirst : f ≫ a = B.hom := congrArg Sigma.fst hz
  have hcover : f ≫ T.hom = B.hom := Over.w (coverMap (k' := L) T)
  have ha : a = T.hom := (cancel_epi f).mp (hfirst.trans hcover.symm)
  subst a
  have hz' : (pic0TypeFunctor C).map (coverMap (k' := L) T).op z = x.1 :=
    (Over.sigmaExtension_map_mk_eq_iff (F := pic0TypeFunctor C)
      f hcover z x.1).mp hz
  refine ⟨z, hz', ?_⟩
  intro y hy
  have hySigma : (pic0SigmaFunctor C).map f.op ⟨T.hom, y⟩ = ⟨B.hom, x.1⟩ :=
    (Over.sigmaExtension_map_mk_eq_iff (F := pic0TypeFunctor C)
      f hcover y x.1).mpr hy
  have hpair := hzu ⟨T.hom, y⟩ hySigma
  cases hpair
  rfl

/-- Restriction to the finite-Galois base change is a bijection onto the
Galois-invariant Picard-zero classes. -/
theorem pic0RestrictToGaloisInvariant_bijective
    [FiniteDimensional K L] [IsGalois K L]
    (T : Over (Spec (CommRingCat.of K))) :
    Function.Bijective (pic0RestrictToGaloisInvariant (L := L) C T) := by
  constructor
  · intro a b hab
    have hdesc := pic0GaloisInvariant_existsUnique_descend C T
      (pic0RestrictToGaloisInvariant (L := L) C T a)
    apply hdesc.unique
    · rfl
    · exact (congrArg Subtype.val hab).symm
  · intro x
    obtain ⟨y, hy, _⟩ := pic0GaloisInvariant_existsUnique_descend C T x
    exact ⟨y, Subtype.ext hy⟩

/-- Picard-zero classes over an arbitrary `K`-test scheme are exactly the
classes on its finite-Galois base change fixed by all deck transformations. -/
noncomputable def pic0GaloisInvariantEquiv
    [FiniteDimensional K L] [IsGalois K L]
    (T : Over (Spec (CommRingCat.of K))) :
    (pic0TypeFunctor C).obj (op T) ≃ Pic0GaloisInvariant (L := L) C T :=
  Equiv.ofBijective (pic0RestrictToGaloisInvariant (L := L) C T)
    (pic0RestrictToGaloisInvariant_bijective C T)

/-- Base change of a morphism of `K`-tests, regarded in the `K`-slice after
restriction from `L`. -/
noncomputable def pic0GaloisBaseTestMap
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T) :
    (restrictTest K L).obj (baseTest (k' := L) T') ⟶
      (restrictTest K L).obj (baseTest (k' := L) T) :=
  (restrictTest K L).map
    (Over.homMk (pullbackBaseChange K L T.hom T'.hom a.left a.w)
      (pullbackBaseChange_snd K L T.hom T'.hom a.left a.w))

/-- The base-changed test map commutes with the field-extension covers. -/
theorem pic0GaloisBaseTestMap_comp_coverMap
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T) :
    pic0GaloisBaseTestMap (L := L) a ≫ coverMap (k' := L) T =
      coverMap (k' := L) T' ≫ a := by
  apply Over.OverMorphism.ext
  exact pullbackBaseChange_fst K L T.hom T'.hom a.left a.w

/-- Base change of test schemes commutes with each deck transformation. -/
theorem twistTest_naturality
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (gamma : L ≃ₐ[K] L) :
    twistTest T' gamma ≫ pic0GaloisBaseTestMap (L := L) a =
      pic0GaloisBaseTestMap (L := L) a ≫ twistTest T gamma := by
  apply Over.OverMorphism.ext
  exact pullbackGalMap_naturality T.hom T'.hom a.left a.w gamma⁻¹

namespace Pic0GaloisInvariant

/-- Pull back an invariant Picard-zero class along a morphism of `K`-tests. -/
noncomputable def precomp
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : Pic0GaloisInvariant (L := L) C T) :
    Pic0GaloisInvariant (L := L) C T' := by
  refine ⟨(pic0TypeFunctor C).map (pic0GaloisBaseTestMap (L := L) a).op x.1, ?_⟩
  intro gamma
  calc
    (pic0TypeFunctor C).map (twistTest T' gamma).op
        ((pic0TypeFunctor C).map
          (pic0GaloisBaseTestMap (L := L) a).op x.1) =
      (pic0TypeFunctor C).map
        (twistTest T' gamma ≫ pic0GaloisBaseTestMap (L := L) a).op x.1 := by
          rw [op_comp, Functor.map_comp]
          rfl
    _ = (pic0TypeFunctor C).map
        (pic0GaloisBaseTestMap (L := L) a ≫ twistTest T gamma).op x.1 := by
          rw [twistTest_naturality (L := L) a gamma]
    _ = (pic0TypeFunctor C).map (pic0GaloisBaseTestMap (L := L) a).op
        ((pic0TypeFunctor C).map (twistTest T gamma).op x.1) := by
          rw [op_comp, Functor.map_comp]
          rfl
    _ = (pic0TypeFunctor C).map (pic0GaloisBaseTestMap (L := L) a).op x.1 :=
      congrArg ((pic0TypeFunctor C).map (pic0GaloisBaseTestMap (L := L) a).op)
        (x.2 gamma)

end Pic0GaloisInvariant

/-- The finite-Galois invariant equivalence commutes with precomposition by
arbitrary morphisms of `K`-test schemes. -/
theorem pic0GaloisInvariantEquiv_precomp
    [FiniteDimensional K L] [IsGalois K L]
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : (pic0TypeFunctor C).obj (op T)) :
    pic0GaloisInvariantEquiv (L := L) C T'
        ((pic0TypeFunctor C).map a.op x) =
      Pic0GaloisInvariant.precomp C a
        (pic0GaloisInvariantEquiv (L := L) C T x) := by
  apply Subtype.ext
  change (pic0TypeFunctor C).map (coverMap (k' := L) T').op
      ((pic0TypeFunctor C).map a.op x) =
    (pic0TypeFunctor C).map (pic0GaloisBaseTestMap (L := L) a).op
      ((pic0TypeFunctor C).map (coverMap (k' := L) T).op x)
  calc
    _ = (pic0TypeFunctor C).map (coverMap (k' := L) T' ≫ a).op x := by
      rw [op_comp, Functor.map_comp]
      rfl
    _ = (pic0TypeFunctor C).map
        (pic0GaloisBaseTestMap (L := L) a ≫ coverMap (k' := L) T).op x := by
      rw [pic0GaloisBaseTestMap_comp_coverMap (L := L) a]
    _ = _ := by
      rw [op_comp, Functor.map_comp]
      rfl

end

end AlgebraicGeometry
