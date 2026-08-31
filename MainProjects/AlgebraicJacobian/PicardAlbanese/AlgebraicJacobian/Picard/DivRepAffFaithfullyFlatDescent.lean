/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Pullbacks
import AlgebraicJacobian.Algebra.EtaleCover
import AlgebraicJacobian.Picard.DivRepAffChallenge
import AlgebraicJacobian.Picard.DivisorFamilyAffMap

/-!
# Faithfully-flat descent for the widened divisor functor, via representability

The widened divisor functor `divFunctorAff C (genus C)` is representable
(`divFunctorAff_genus_representableBy`, `Picard/DivRepAffChallenge.lean`), and over an affine
test the functor value collapses to `DivFamZarAff` (`divFamZarAffAffineEquiv`,
`Picard/DivisorFamilyAffVehicle.lean`).  Composing the two turns a widened class over a test
algebra into a **classifying morphism** to the representing scheme, naturally in the algebra
(`divFamZarAffAffineEquiv_naturality`, `Picard/DivisorFamilyAffMap.lean`).

This file cashes that in for descent: `Spec` of a faithfully flat ring map is quasi-compact,
surjective and flat, hence an **effective epimorphism** of schemes by the fpqc-subcanonicity
instance (`Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`).  Precomposition with an (effective) epi
is injective, so the widened divisor presheaf is *separated* along faithfully flat maps; and a
class over the carrier of an étale cover whose two coprojection pullbacks to the tensor square
agree has classifying morphism coequalizing the kernel pair of the cover (through
`pullbackSpecIso`), so it *descends*, uniquely, to the base ring.

## Main declarations

* `AlgebraicGeometry.DivFamZarAff.classify` — the classifying equivalence
  `DivFamZarAff C S (genus C) ≃ (overSpec k S ⟶ divRepAffGenusScheme C)`, with naturality
  `DivFamZarAff.classify_mapAlgHom`.
* `AlgebraicGeometry.effectiveEpi_specMap_of_faithfullyFlat` — `Spec` of a faithfully flat
  algebra map is an effective epimorphism.
* `AlgebraicGeometry.DivFamZarAff.mapAlgHom_injective_of_faithfullyFlat` — the
  separated-presheaf property of the widened carrier along faithfully flat maps.
* `AlgebraicGeometry.DivFamZarAff.exists_descent_of_tensor_eq` — effective-epi descent of a
  widened divisor class along an étale cover of the test algebra.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- **The classifying equivalence of the widened divisor functor at an affine test**: a widened
locally certified divisor class of degree `genus C` over a test algebra `S` is the same thing as
a morphism from `Spec S` to the representing scheme, through the affine collapse
`divFamZarAffAffineEquiv` and the representability `divFunctorAff_genus_representableBy`. -/
noncomputable def DivFamZarAff.classify (S : Type u) [CommRing S] [Algebra k S] :
    DivFamZarAff C S (genus C) ≃ (overSpec k S ⟶ divRepAffGenusScheme C) :=
  (divFamZarAffAffineEquiv C (genus C) S).symm.trans
    ((divFunctorAff_genus_representableBy C).homEquiv (X := overSpec k S)).symm

/-- **Naturality of the classifying equivalence** along a `k`-algebra map of affine tests: the
classifying morphism of the base change is `Spec` of the map followed by the classifying
morphism.  `divFamZarAffAffineEquiv_naturality` composed with the representability coherence
`Functor.RepresentableBy.comp_homEquiv_symm`. -/
theorem DivFamZarAff.classify_mapAlgHom {S S' : Type u} [CommRing S] [Algebra k S]
    [CommRing S'] [Algebra k S'] (φ : S →ₐ[k] S') (F : DivFamZarAff C S (genus C)) :
    classify S' (DivFamZarAff.mapAlgHom φ F) = Over.overSpecMap φ ≫ classify S F := by
  have hnat := divFamZarAffAffineEquiv_naturality (C := C) (n := genus C) φ
    ((divFamZarAffAffineEquiv C (genus C) S).symm F)
  rw [Equiv.apply_symm_apply] at hnat
  calc classify S' (DivFamZarAff.mapAlgHom φ F)
      = (divFunctorAff_genus_representableBy C).homEquiv.symm
          ((divFamZarAffAffineEquiv C (genus C) S').symm
            (DivFamZarAff.mapAlgHom φ F)) := rfl
    _ = (divFunctorAff_genus_representableBy C).homEquiv.symm
          ((divFunctorAff C (genus C)).map (Over.overSpecMap φ).op
            ((divFamZarAffAffineEquiv C (genus C) S).symm F)) := by
        rw [← hnat, Equiv.symm_apply_apply]
        rfl
    _ = Over.overSpecMap φ ≫ (divFunctorAff_genus_representableBy C).homEquiv.symm
          ((divFamZarAffAffineEquiv C (genus C) S).symm F) :=
        ((divFunctorAff_genus_representableBy C).comp_homEquiv_symm _ _).symm
    _ = Over.overSpecMap φ ≫ classify S F := rfl

/-- **`Spec` of a faithfully flat algebra map is an effective epimorphism** of schemes: it is
flat and surjective by `flat_and_surjective_SpecMap_iff`, quasi-compact because it is affine,
and quasi-compact surjective flat morphisms are effective epis by fpqc subcanonicity. -/
theorem effectiveEpi_specMap_of_faithfullyFlat {S S' : Type u} [CommRing S] [CommRing S']
    [Algebra S S'] [Module.FaithfullyFlat S S'] :
    EffectiveEpi (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := by
  have hff : (CommRingCat.ofHom (algebraMap S S')).hom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  obtain ⟨hflat, hsurj⟩ :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap S S'))).mpr hff
  haveI := hflat
  haveI := hsurj
  infer_instance

/-- **The separated-presheaf property of the widened carrier**: base change of widened locally
certified divisor classes along a faithfully flat map of test algebras is injective.  Through
`classify`, base change is precomposition of the classifying morphism with `Spec` of the map,
which is an (effective) epimorphism. -/
theorem DivFamZarAff.mapAlgHom_injective_of_faithfullyFlat {S S' : Type u} [CommRing S]
    [Algebra k S] [CommRing S'] [Algebra k S'] [Algebra S S'] [IsScalarTower k S S']
    [Module.FaithfullyFlat S S'] :
    Function.Injective
      (DivFamZarAff.mapAlgHom (C := C) (n := genus C) (IsScalarTower.toAlgHom k S S')) := by
  intro F G hFG
  haveI : EffectiveEpi (Spec.map (CommRingCat.ofHom (algebraMap S S'))) :=
    effectiveEpi_specMap_of_faithfullyFlat
  haveI : Epi ((Over.overSpecMap (IsScalarTower.toAlgHom k S S')).left) :=
    inferInstanceAs (Epi (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
  haveI : Epi (Over.overSpecMap (IsScalarTower.toAlgHom k S S')) :=
    Over.epi_of_epi_left _
  have hc := congrArg (classify S') hFG
  rw [classify_mapAlgHom, classify_mapAlgHom] at hc
  exact (classify S).injective
    ((cancel_epi (Over.overSpecMap (IsScalarTower.toAlgHom k S S'))).mp hc)

/-- **Effective-epi descent of a widened divisor class along an étale cover**: a widened
locally certified divisor class over the carrier of an étale cover of `Spec A` whose two
coprojection pullbacks to the tensor square of the carrier agree descends, uniquely, to a class
over `A`.

The classifying morphism of `F` coequalizes the kernel pair of the covering morphism
`Spec E.Carrier ⟶ Spec A` (the kernel pair is `Spec` of the tensor square, by
`pullbackSpecIso`), so it factors through the effective epi; the factorization lands back in
the slice over `Spec k` by epi cancellation, and uniqueness is the separated-presheaf
property. -/
theorem DivFamZarAff.exists_descent_of_tensor_eq {A : Type u} [CommRing A] [Algebra k A]
    (E : Algebra.EtaleCover A) (F : DivFamZarAff C E.Carrier (genus C))
    (h : DivFamZarAff.mapAlgHom
          ((Algebra.TensorProduct.includeLeft :
            E.Carrier →ₐ[A] E.Carrier ⊗[A] E.Carrier).restrictScalars k) F
        = DivFamZarAff.mapAlgHom
          ((Algebra.TensorProduct.includeRight :
            E.Carrier →ₐ[A] E.Carrier ⊗[A] E.Carrier).restrictScalars k) F) :
    ∃! F₀ : DivFamZarAff C A (genus C),
      DivFamZarAff.mapAlgHom ((Algebra.ofId A E.Carrier).restrictScalars k) F₀ = F := by
  classical
  haveI : EffectiveEpi (Spec.map (CommRingCat.ofHom (algebraMap A E.Carrier))) :=
    effectiveEpi_specMap_of_faithfullyFlat
  -- the double-pullback agreement of classifying morphisms, in the slice over `Spec k`
  have hOv : Over.overSpecMap ((Algebra.TensorProduct.includeLeft :
          E.Carrier →ₐ[A] E.Carrier ⊗[A] E.Carrier).restrictScalars k)
        ≫ classify E.Carrier F
      = Over.overSpecMap ((Algebra.TensorProduct.includeRight :
          E.Carrier →ₐ[A] E.Carrier ⊗[A] E.Carrier).restrictScalars k)
        ≫ classify E.Carrier F := by
    rw [← classify_mapAlgHom, ← classify_mapAlgHom, h]
  -- hence the classifying morphism coequalizes the kernel pair of the covering morphism
  have hfstsnd : pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A E.Carrier)))
        (Spec.map (CommRingCat.ofHom (algebraMap A E.Carrier)))
        ≫ (classify E.Carrier F).left
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A E.Carrier)))
          (Spec.map (CommRingCat.ofHom (algebraMap A E.Carrier)))
        ≫ (classify E.Carrier F).left := by
    rw [← cancel_epi (pullbackSpecIso A E.Carrier E.Carrier).inv,
      pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
    exact congrArg CommaMorphism.left hOv
  have hcoeq : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ Spec (.of E.Carrier)),
      g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap A E.Carrier))
        = g₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap A E.Carrier))
      → g₁ ≫ (classify E.Carrier F).left = g₂ ≫ (classify E.Carrier F).left := by
    intro Z g₁ g₂ hg
    calc g₁ ≫ (classify E.Carrier F).left
        = pullback.lift g₁ g₂ hg ≫ pullback.fst _ _ ≫ (classify E.Carrier F).left := by
          rw [← Category.assoc, pullback.lift_fst]
      _ = pullback.lift g₁ g₂ hg ≫ pullback.snd _ _ ≫ (classify E.Carrier F).left := by
          rw [hfstsnd]
      _ = g₂ ≫ (classify E.Carrier F).left := by
          rw [← Category.assoc, pullback.lift_snd]
  -- descend the classifying morphism at the scheme level
  set w : Spec (.of A) ⟶ (divRepAffGenusScheme C).left :=
    EffectiveEpi.desc (Spec.map (CommRingCat.ofHom (algebraMap A E.Carrier)))
      (classify E.Carrier F).left hcoeq with hw
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap A E.Carrier)) ≫ w
      = (classify E.Carrier F).left := by
    rw [hw]; exact EffectiveEpi.fac _ _ _
  -- the over-triangle of the descended morphism, by epi cancellation
  have htri : w ≫ (divRepAffGenusScheme C).hom = (overSpec k A).hom := by
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap A E.Carrier))),
      ← Category.assoc, hfac, Over.w]
    show Spec.map (CommRingCat.ofHom (algebraMap k E.Carrier))
        = Spec.map (CommRingCat.ofHom (algebraMap A E.Carrier))
          ≫ Spec.map (CommRingCat.ofHom (algebraMap k A))
    rw [IsScalarTower.algebraMap_eq k A E.Carrier, CommRingCat.ofHom_comp, Spec.map_comp]
  -- the descended class, through the slice-level factorization
  have hex : DivFamZarAff.mapAlgHom ((Algebra.ofId A E.Carrier).restrictScalars k)
      ((classify A).symm (Over.homMk w htri)) = F := by
    apply (classify E.Carrier).injective
    rw [classify_mapAlgHom, Equiv.apply_symm_apply]
    exact Over.OverMorphism.ext hfac
  refine ⟨(classify A).symm (Over.homMk w htri), hex, fun F₀ hF₀ => ?_⟩
  have hcan : IsScalarTower.toAlgHom k A E.Carrier
      = (Algebra.ofId A E.Carrier).restrictScalars k := AlgHom.ext fun _ => rfl
  apply DivFamZarAff.mapAlgHom_injective_of_faithfullyFlat (S := A) (S' := E.Carrier)
  rw [hcan, hF₀, hex]

end AlgebraicGeometry
