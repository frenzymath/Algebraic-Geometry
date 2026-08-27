/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.CurveFiniteReplacement
import AlgebraicJacobian.Picard.FiberH0CechKernel
import AlgebraicJacobian.Picard.RigidPushforwardInstance
import AlgebraicJacobian.Picard.RigidPushforwardP1Constants
import AlgebraicJacobian.Picard.RigidPushforwardTransfer
import AlgebraicJacobian.Picard.SemicontinuityH0
import AlgebraicJacobian.Picard.TwoTermFiniteFree
import AlgebraicJacobian.Picard.TwoTermKernelSemicontinuity

/-!
# Upper semicontinuity of fibrewise h0 for a curve

This module discharges the B5 gate for every smooth proper geometrically integral curve.
For a line bundle on the constant family over an affine base, push it forward along the
finite map to the projective line and replace the standard two-chart Cech complex by its
finite Mumford complex. Upper semicontinuity is then the kernel-rank theorem for that
finite complex; the comparison with the original Cech kernel and finite pushforward
identifies its value with the fibrewise h0 of the line bundle.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Module TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k]

namespace Scheme

/-- Fibrewise h0 is upper semicontinuous for a smooth proper geometrically integral
curve, with no additional hypothesis on the curve or the line bundle. -/
instance instHasH0SemicontinuityOfCurve
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : HasH0Semicontinuity C := by
  constructor
  intro A _ _ _ L hL n
  haveI : Adelic.HasFiniteMapToP1 C := inferInstance
  haveI := hL.isFinitePresentation
  let M := (Modules.pushforward (Adelic.finiteMapToP1BaseChange A C)).obj L
  haveI hMqc : M.IsQuasicoherent := by
    haveI : IsFinite (Adelic.finiteMapToP1BaseChange A C) :=
      Adelic.isFinite_finiteMapToP1BaseChange A C
    exact Modules.pushforward_isQuasicoherent (Adelic.finiteMapToP1BaseChange A C) L
  let p := pullback.snd (Adelic.p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let U := Adelic.p1BaseChangeCoverSquare (k := k) A
  letI := p.baseSectionsModule M U.U₁
  letI := p.baseSectionsModule M U.U₂
  letI := p.baseSectionsModule M (U.U₁ ⊓ U.U₂)
  obtain ⟨R⟩ :=
    Adelic.exists_twoTermFiniteReplacement_finiteMapToP1BaseChange C A L hL
  letI : Module.FinitePresentation Γ(Spec (CommRingCat.of A), ⊤) R.K0 :=
    Module.finitePresentation_of_projective _ _
  have hOpenR := AlgebraicJacobian.TwoTerm.isOpen_finrank_ker_baseChange_le R.n R.k n
  let B := Γ(Spec (CommRingCat.of A), ⊤)
  let ε : B ≃+* A :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let H : PrimeSpectrum B ≃ₜ PrimeSpectrum A :=
    PrimeSpectrum.homeomorphOfRingEquiv ε
  have hdim (t : Spec (CommRingCat.of A)) :
      Module.finrank (H.symm t).asIdeal.ResidueField
          (LinearMap.ker (R.k.baseChange (H.symm t).asIdeal.ResidueField)) =
        (pullback.snd C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t := by
    let s := H.symm t
    let Kt := Γ(Spec ((Spec (CommRingCat.of A)).residueField t), ⊤)
    letI : Field Kt :=
      (MulEquiv.isField (Field.toIsField t.asIdeal.ResidueField)
        (specResidueFieldRingEquiv (CommRingCat.of A) t).symm.toMulEquiv).toField
    letI : Algebra B Kt :=
      (((Spec (CommRingCat.of A)).fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
    let hs : s.asIdeal = Ideal.comap ε.toRingHom t.asIdeal := rfl
    let κme := Ideal.ResidueField.map s.asIdeal t.asIdeal ε.toRingHom hs
    have hκme : Function.Bijective κme :=
      (RingEquiv.surjectiveOnStalks ε).residueFieldMap_bijective
        s.asIdeal t.asIdeal hs
    let κe := RingEquiv.ofBijective κme hκme
    let τ := κe.trans (specResidueFieldRingEquiv (CommRingCat.of A) t)
    let τAlg : s.asIdeal.ResidueField ≃ₐ[B] Kt :=
      AlgEquiv.ofRingEquiv fun b => by
        change τ ((algebraMap B s.asIdeal.ResidueField) b) = _
        change specResidueFieldRingEquiv (CommRingCat.of A) t
          (κme ((algebraMap B s.asIdeal.ResidueField) b)) = _
        rw [Ideal.ResidueField.map_algebraMap]
        exact (appLE_fromSpecResidueField_apply (CommRingCat.of A) t b).symm
    have htransport := finrank_ker_baseChange_of_algEquiv R.k τAlg
    let d := U.moduleSectionDiffBase p M
    let h₀map := AlgebraicJacobian.TwoTerm.h0Map
      (R.k.baseChange Kt) (d.baseChange Kt) (R.a0.baseChange Kt)
      (R.a1.baseChange Kt)
      (AlgebraicJacobian.TwoTerm.baseChange_square
        R.k d R.a0 R.a1 Kt R.comm)
    have hreplacement :
        Module.finrank Kt (LinearMap.ker (R.k.baseChange Kt)) =
          Module.finrank Kt (LinearMap.ker (d.baseChange Kt)) :=
      LinearEquiv.finrank_eq
        (LinearEquiv.ofBijective h₀map (R.h0_bijective Kt))
    have hcech := finrank_ker_moduleSectionDiffBase_baseChange_eq_fiberH0
      p U M t
    have hpush := Adelic.pushforward_finiteMapToP1BaseChange_fiberH0 A C L t hL
    exact htransport.trans (hreplacement.trans (hcech.trans hpush))
  rw [show {t : Spec (CommRingCat.of A) |
      (pullback.snd C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t ≤ n} =
      H.symm ⁻¹' {s : PrimeSpectrum B |
        Module.finrank s.asIdeal.ResidueField
          (LinearMap.ker (R.k.baseChange s.asIdeal.ResidueField)) ≤ n} by
    ext t
    change (pullback.snd C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t ≤ n ↔
      Module.finrank (H.symm t).asIdeal.ResidueField
        (LinearMap.ker (R.k.baseChange (H.symm t).asIdeal.ResidueField)) ≤ n
    rw [hdim t]]
  exact H.symm.continuous.isOpen_preimage _ hOpenR

end Scheme

end

end AlgebraicGeometry
