/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFieldMono
import AlgebraicJacobian.Picard.DivisorFamilyFieldSurj

/-!
# Field window generation for widened certified divisor families

Every local-equation system over a field admits a finite chart adaptation.  For the
equations of a widened certified family, the widened certificate supplies the degree
identity, so that adaptation is certified by `DivisorAdaptation.isCertified_of_deg`.
The carrier-free transport theorem `hgen_of_chart_divEq` then gives field window
generation for the original equations.  This does not type the widened cover into the
pinned charts; it constructs a separate adaptation of the same local equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {K : Type u} [Field K] [Algebra k K]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftAffFieldWindowGen :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant pi]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]

set_option maxRecDepth 8000 in
set_option synthInstance.maxHeartbeats 800000 in
-- The two field instance towers and the extracted adaptation exceed the default limit.
/-- Over a field, the first window of an arbitrary widened certified family generates its
stalk ideal, without a chart-typing or representative hypothesis.  The curve Euler
parameter `gamma` is independent of the family degree `g`. -/
theorem CertifiedDivisorFamilyAff.stalkIdeal_le_span_windowGerm_of_field_at
    (g : Nat) {gamma : Nat} (hgamma : gamma ≤ g)
    (F : CertifiedDivisorFamilyAff C K g)
    (hOk : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchiK : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    (hOK : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (hchiL : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (gamma : Int)) :
    ∀ z : relCurve C K,
      F.eqns.stalkIdeal z ≤ Ideal.span (eqnsWindowGermSet K hpi g F.eqns z) := by
  obtain ⟨A⟩ := exists_divisorAdaptation C K pi F.eqns
  let G : CertifiedDivisorFamily C K pi g :=
    ⟨F.eqns, A, A.isCertified_of_deg (certifiedAff_deg_presentationDivisor g F)⟩
  exact hgen_of_chart_divEq_at hpi g hgamma F.eqns hOk hchiK hOK hchiL G
    (Scheme.LocalEquations.divEq_refl F.eqns)

set_option maxRecDepth 8000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The diagonal specialization of
`CertifiedDivisorFamilyAff.stalkIdeal_le_span_windowGerm_of_field_at`. -/
theorem CertifiedDivisorFamilyAff.stalkIdeal_le_span_windowGerm_of_field (g : Nat)
    (F : CertifiedDivisorFamilyAff C K g)
    (hOk : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchiK : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
    (hOK : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (hchiL : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : Int)) :
    ∀ z : relCurve C K,
      F.eqns.stalkIdeal z ≤ Ideal.span (eqnsWindowGermSet K hpi g F.eqns z) :=
  F.stalkIdeal_le_span_windowGerm_of_field_at
    (gamma := g) hpi g le_rfl hOk hchiK hOK hchiL

set_option maxRecDepth 8000 in
set_option synthInstance.maxHeartbeats 800000 in
-- The field window and classifier instance towers exceed the default limit.
/-- Equal first windows of widened certified families over a field determine equal
Cartier divisors. -/
theorem CertifiedDivisorFamilyAff.divEq_of_eps_eq_of_field (g : Nat)
    (F F' : CertifiedDivisorFamilyAff C K g)
    (heps : (F.eps hpi g).1 = (F'.eps hpi g).1)
    (hOk : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchiK : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
    (hOK : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (hchiL : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : Int)) :
    F.eqns.DivEq F'.eqns :=
  divEq_of_eps_eq_of_field_of_windowGen hpi g F F' heps
    (F.stalkIdeal_le_span_windowGerm_of_field hpi g hOk hchiK hOK hchiL)
    (F'.stalkIdeal_le_span_windowGerm_of_field hpi g hOk hchiK hOK hchiL)

end AlgebraicGeometry
