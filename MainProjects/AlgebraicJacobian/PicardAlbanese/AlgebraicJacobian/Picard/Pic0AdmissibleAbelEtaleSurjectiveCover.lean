/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveSite

/-!
# Etale covers from pointwise prime lifts

This file packages the cover used in the affine callback for admissible Abel
surjectivity.  Starting from a singleton affine etale cover, every prime of its
carrier is allowed a further, independently chosen etale algebra carrying a
prime above it.  The resulting spectra jointly cover the original affine test
scheme.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

noncomputable section

attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k]
variable (T : Over (Spec (.of k))) (U : T.left.affineOpens)
variable (E : Algebra.EtaleCover Γ(T.left, U.1))
variable (S : PrimeSpectrum E.Carrier → Type u)
variable [∀ p, CommRing (S p)] [∀ p, Algebra E.Carrier (S p)]
variable [∀ p, Algebra.Etale E.Carrier (S p)]

/-- The over-category morphism underlying the member indexed by `p` of the
pointwise prime-lift cover. -/
noncomputable def etalePrimeLiftOverHom
    [∀ p, Algebra k (S p)] [∀ p, IsScalarTower k E.Carrier (S p)]
    (p : PrimeSpectrum E.Carrier) :
    overSpec k (S p) ⟶ T :=
  Over.overSpecMap (IsScalarTower.toAlgHom k E.Carrier (S p)) ≫
    Over.overSpecMap (IsScalarTower.toAlgHom k Γ(T.left, U.1) E.Carrier) ≫
      Over.fromSpecAffine T U

/-- Etale spectra carrying chosen lifts of all primes of a singleton etale
presentation form an etale cover of the original affine-open test object.

The hypothesis `hU` is the only place affineness of the target is used: it says
that the chosen affine open is the whole target. -/
noncomputable def etalePrimeLiftCover (hU : U.1 = ⊤)
    (q : ∀ p : PrimeSpectrum E.Carrier, PrimeSpectrum (S p))
    (hq : ∀ p, PrimeSpectrum.comap (algebraMap E.Carrier (S p)) (q p) = p) :
    T.left.Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers (PrimeSpectrum E.Carrier)
    (fun p ↦ Spec (.of (S p)))
    (fun p ↦
      Spec.map (CommRingCat.ofHom (algebraMap E.Carrier (S p))) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(T.left, U.1) E.Carrier)) ≫
          (Over.fromSpecAffine T U).left)
    (fun x ↦ by
      have hx : x ∈ Set.range U.2.fromSpec.base := by
        rw [U.2.range_fromSpec, hU]
        trivial
      obtain ⟨xA, hxA⟩ := hx
      obtain ⟨p, hp⟩ := E.comap_surjective xA
      refine ⟨p, q p, ?_⟩
      change U.2.fromSpec.base
          (PrimeSpectrum.comap (algebraMap Γ(T.left, U.1) E.Carrier)
            (PrimeSpectrum.comap (algebraMap E.Carrier (S p)) (q p))) = x
      rw [hq p, hp]
      exact hxA)
    (fun p ↦ by
      haveI : Etale
          (Spec.map (CommRingCat.ofHom (algebraMap E.Carrier (S p)))) := by
        rw [HasRingHomProperty.Spec_iff (P := @Etale)]
        exact RingHom.etale_algebraMap.mpr inferInstance
      haveI : Etale
          (Spec.map (CommRingCat.ofHom
            (algebraMap Γ(T.left, U.1) E.Carrier))) := by
        rw [HasRingHomProperty.Spec_iff (P := @Etale)]
        exact RingHom.etale_algebraMap.mpr inferInstance
      haveI : IsOpenImmersion (Over.fromSpecAffine T U).left :=
        U.2.isOpenImmersion_fromSpec
      change Etale
        (Spec.map (CommRingCat.ofHom (algebraMap E.Carrier (S p))) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap Γ(T.left, U.1) E.Carrier)) ≫
            (Over.fromSpecAffine T U).left)
      exact MorphismProperty.comp_mem @Etale _ _ inferInstance
        (MorphismProperty.comp_mem @Etale _ _ inferInstance
          (HasRingHomProperty.of_isOpenImmersion
            RingHom.Etale.containsIdentities)))

set_option linter.unusedSectionVars false

/-- Every member morphism of `etalePrimeLiftCover` is definitionally the left
leg of the corresponding over-category composite. -/
@[simp]
theorem etalePrimeLiftCover_f (hU : U.1 = ⊤)
    [∀ p, Algebra k (S p)] [∀ p, IsScalarTower k E.Carrier (S p)]
    (q : ∀ p : PrimeSpectrum E.Carrier, PrimeSpectrum (S p))
    (hq : ∀ p, PrimeSpectrum.comap (algebraMap E.Carrier (S p)) (q p) = p)
    (p : PrimeSpectrum E.Carrier) :
    (etalePrimeLiftCover T U E S hU q hq).f p =
      (etalePrimeLiftOverHom T U E S p).left :=
  rfl

end

end AlgebraicGeometry
