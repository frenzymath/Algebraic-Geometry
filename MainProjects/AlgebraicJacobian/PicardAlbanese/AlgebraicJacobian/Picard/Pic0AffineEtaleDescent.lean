/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAffEtaleEffectivity
import AlgebraicJacobian.Picard.Pic0EtaleDegreeZero
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveSite

/-!
# Affine etale descent for Pic0

Compatible degree-zero Picard data over a singleton faithfully flat etale cover descend
uniquely to the affine base.  Existence first descends the underlying `PicEtAff` class, then
reflects the fibrewise degree-zero condition through the cover.  Uniqueness is affine
`PicEtAff` etale separatedness.

This is the affine algebraic input for the big-etale sheaf comparison.  It does not assert a
Scheme-site sheaf certificate or identify the raw functor with its sheafification.
-/

set_option autoImplicit false

universe u

open CategoryTheory

open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

/-- Compatible degree-zero Picard data over a singleton faithfully flat etale cover have a
unique degree-zero descent to the affine base. -/
theorem pic0Subgroup_existsUnique_of_etaleCover
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [IsProper C.hom] [GeometricallyIrreducible C.hom]
    [GeometricallyReduced C.hom]
    (E : Algebra.EtaleCover A)
    (x : pic0Subgroup C (overSpec k E.Carrier))
    (h : pic0Map C (Over.overSpecMap (doubleInl E)) x =
      pic0Map C (Over.overSpecMap (doubleInr E)) x) :
    ∃! z : pic0Subgroup C (overSpec k A),
      pic0Map C
        (Over.overSpecMap
          ((Algebra.ofId A E.Carrier).restrictScalars k)) z = x := by
  let phi : A →ₐ[k] E.Carrier :=
    (Algebra.ofId A E.Carrier).restrictScalars k
  have hPic :
      picEtMap C (Over.overSpecMap (doubleInl E))
          (x : picEt C (overSpec k E.Carrier)) =
        picEtMap C (Over.overSpecMap (doubleInr E))
          (x : picEt C (overSpec k E.Carrier)) := by
    exact congrArg Subtype.val h
  have hAff :
      PicEtAff.mapAlg C (doubleInl E)
          (picEtAffineEquiv C E.Carrier
            (x : picEt C (overSpec k E.Carrier))) =
        PicEtAff.mapAlg C (doubleInr E)
          (picEtAffineEquiv C E.Carrier
            (x : picEt C (overSpec k E.Carrier))) := by
    rw [← picEtAffineEquiv_naturality, ← picEtAffineEquiv_naturality]
    exact congrArg (picEtAffineEquiv C (E.Carrier ⊗[A] E.Carrier)) hPic
  obtain ⟨zAff, hzAff⟩ :=
    PicEtAff.exists_map_eq_of_double_eq C E
      (picEtAffineEquiv C E.Carrier
        (x : picEt C (overSpec k E.Carrier))) hAff
  let zPic : picEt C (overSpec k A) :=
    (picEtAffineEquiv C A).symm zAff
  have hzPic :
      picEtMap C (Over.overSpecMap phi) zPic =
        (x : picEt C (overSpec k E.Carrier)) := by
    apply (picEtAffineEquiv C E.Carrier).injective
    rw [picEtAffineEquiv_naturality]
    simp only [zPic, MulEquiv.apply_symm_apply]
    rw [PicEtAff.mapAlg_eq_map_of_toRingHom_eq_algebraMap C phi rfl]
    exact hzAff
  have hzMem : zPic ∈ pic0Subgroup C (overSpec k A) :=
    mem_pic0Subgroup_of_etaleCover E zPic (by
      rw [hzPic]
      exact x.2)
  let z : pic0Subgroup C (overSpec k A) := ⟨zPic, hzMem⟩
  have hz :
      pic0Map C
        (Over.overSpecMap
          ((Algebra.ofId A E.Carrier).restrictScalars k)) z = x :=
    Subtype.ext hzPic
  refine ⟨z, hz, ?_⟩
  intro y hy
  apply Subtype.ext
  apply (picEtAffineEquiv C A).injective
  apply PicEtAff.map_injective_of_etaleCover C E
  have hyz := hy.trans hz.symm
  have hyPic :
      picEtMap C (Over.overSpecMap phi)
          (y : picEt C (overSpec k A)) =
        picEtMap C (Over.overSpecMap phi)
          (z : picEt C (overSpec k A)) := by
    exact congrArg Subtype.val hyz
  have hyAff := congrArg (picEtAffineEquiv C E.Carrier) hyPic
  rw [picEtAffineEquiv_naturality, picEtAffineEquiv_naturality,
    PicEtAff.mapAlg_eq_map_of_toRingHom_eq_algebraMap C phi rfl,
    PicEtAff.mapAlg_eq_map_of_toRingHom_eq_algebraMap C phi rfl] at hyAff
  exact hyAff

end

end AlgebraicGeometry
