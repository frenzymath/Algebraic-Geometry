/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DegreeAtBaseField
import AlgebraicJacobian.Picard.Pic0VanishingAffineReduction

/-!
# Etale-locality of the degree-zero condition

The degree-zero condition on an affine test is reflected by restriction to a singleton
faithfully flat etale cover.  Given a field point of the base, base-change the cover to that
field and refine it by a finite separable field extension.  The resulting point of the cover
lies above the extended base point.  Degree zero upstairs therefore descends through
`degAt_overSpecMap_eq_zero_iff`.

This is the degree-condition half of etale descent for `pic0`.  It does not assert effectivity
of descent for the underlying `picEt` class.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-- If a Picard class becomes degree zero on a singleton faithfully flat etale cover of an
affine test, then it was already degree zero on the base. -/
theorem mem_pic0Subgroup_of_etaleCover
    {A : Type u} [CommRing A] [Algebra k A]
    (E : Algebra.EtaleCover A) (lam : picEt C (overSpec k A))
    (h : picEtMap C
        (Over.overSpecMap ((Algebra.ofId A E.Carrier).restrictScalars k)) lam
      ∈ pic0Subgroup C (overSpec k E.Carrier)) :
    lam ∈ pic0Subgroup C (overSpec k A) := by
  rw [mem_pic0Subgroup_iff] at h ⊢
  intro K _ _ t
  obtain ⟨phi, rfl⟩ := exists_algHom_eq_of_overSpec_hom (k := k) A K t
  letI : Algebra A K := phi.toRingHom.toAlgebra
  haveI : IsScalarTower k A K :=
    IsScalarTower.of_algebraMap_eq fun a => (phi.commutes a).symm
  let F : Algebra.EtaleCover K := E.baseChange K
  obtain ⟨L, instFieldL, instAlgebraKL, instFiniteKL, instSeparableKL, ⟨j⟩⟩ :=
    F.exists_finiteSeparableField_algHom
  letI : Field L := instFieldL
  letI : Algebra K L := instAlgebraKL
  letI : Module.Finite K L := instFiniteKL
  letI : Algebra.IsSeparable K L := instSeparableKL
  letI : Algebra k L :=
    ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let psi : E.Carrier →ₐ[k] L :=
    (j.restrictScalars k).comp ((E.baseChangeInclude K).restrictScalars k)
  let kappa : K →ₐ[k] L := IsScalarTower.toAlgHom k K L
  have hcomp :
      psi.comp ((Algebra.ofId A E.Carrier).restrictScalars k) =
        kappa.comp phi := by
    ext a
    simp only [psi, kappa, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.ofId_apply, IsScalarTower.coe_toAlgHom']
    rw [← j.commutes (phi a)]
    apply congrArg j
    apply (E.baseChangeEquiv K).injective
    unfold Algebra.EtaleCover.baseChangeInclude
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply]
    change (E.baseChangeEquiv K)
        ((E.baseChangeEquiv K).symm
          (1 ⊗ₜ[A] (algebraMap A E.Carrier) a)) =
      (E.baseChangeEquiv K) (algebraMap K F.Carrier (phi a))
    rw [(E.baseChangeEquiv K).apply_symm_apply,
      (E.baseChangeEquiv K).commutes,
      Algebra.TensorProduct.algebraMap_apply]
    convert (TensorProduct.smul_tmul (R := A) a
      (1 : K) (1 : E.Carrier)).symm using 1 <;>
      simp only [Algebra.smul_def, mul_one,
        RingHom.algebraMap_toAlgebra, RingHom.id_apply]
    exact congrArg (fun x : K => x ⊗ₜ[A] (1 : E.Carrier))
      (congrFun (AlgHom.coe_toRingHom phi) a).symm
  have hzero :
      degAt lam
        (Over.overSpecMap psi ≫
          Over.overSpecMap ((Algebra.ofId A E.Carrier).restrictScalars k)) = 0 := by
    rw [← degAt_picEtMap]
    exact h L (Over.overSpecMap psi)
  have hpoint :
      Over.overSpecMap kappa ≫ Over.overSpecMap phi =
        Over.overSpecMap psi ≫
          Over.overSpecMap ((Algebra.ofId A E.Carrier).restrictScalars k) := by
    rw [← Over.overSpecMap_comp, ← Over.overSpecMap_comp, hcomp]
  rw [← hpoint] at hzero
  exact (degAt_overSpecMap_eq_zero_iff lam kappa (Over.overSpecMap phi)).mp hzero

end

end AlgebraicGeometry
