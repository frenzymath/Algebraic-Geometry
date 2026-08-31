/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowPencilDivisor
import AlgebraicJacobian.Picard.DivSchemeUnivFibreHdiv

/-!
# The canonical theta pencil on a field fibre

The two canonical global sections of the theta twist have a unit component on
opposite members of the pinned two-chart cover.  Their rational readings
therefore have disjoint zero divisors.  Multiplying both readings by the
class-comparison shift unit transports this basepoint-free pencil to the
honest divisor `windowTransportDivisor`.

The final lattice lemma isolates the elementary divisor calculation used by
the high-window Koszul theorem: a basepoint-free pair in `H^0(O(S))` gives
both the spanning supremum and the relation-kernel infimum at every translate
`B`, with current window `A = B + S`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 6000

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section DivisorLattice

variable {K : Type u} [Field K]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] [IsIntegral X]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- A pair with disjoint effective zero divisors in `H^0(O(S))` gives the two
divisor identities used by the basepoint-free pencil trick at every translate
`A = B + S`. -/
theorem divisor_pencil_lattice_of_basepointFree
    (A B S : X.CurveDivisor) (v0 v1 : X.functionFieldˣ)
    (hA : A = B + S)
    (hbpf : (S + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v0) ⊓
        (S + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v1) = 0) :
    ((B - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v0) ⊔
        (B - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v1) = A) ∧
      ((A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v0) ⊓
        (A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v1) = B) := by
  let D0 := Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v0
  let D1 := Scheme.divOf (X ↘ Spec (CommRingCat.of K)) v1
  have hbpf' : (S + D0) ⊓ (S + D1) = 0 := hbpf
  constructor
  · calc
      (B - D0) ⊔ (B - D1) =
          (A - (S + D0)) ⊔ (A - (S + D1)) := by
            rw [hA]
            congr 1 <;> abel
      _ = A - ((S + D0) ⊓ (S + D1)) :=
        (Scheme.CurveDivisor.sub_inf A (S + D0) (S + D1)).symm
      _ = A := by rw [hbpf', sub_zero]
  · refine Scheme.CurveDivisor.ext_coeffAt fun x hx => ?_
    have hcoeff := congrArg (coeffAt hx) hbpf'
    rw [Scheme.CurveDivisor.coeffAt_inf, CurveDivisor.coeffAt_zero,
      CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_add] at hcoeff
    rw [Scheme.CurveDivisor.coeffAt_inf, CurveDivisor.coeffAt_add,
      CurveDivisor.coeffAt_add, hA, CurveDivisor.coeffAt_add]
    dsimp only [D0, D1] at hcoeff ⊢
    omega

end DivisorLattice

section ThetaPencil

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π] [IsDominant π]
variable (a : ℕ)
variable [IsIntegral C.left] [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

omit [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
private theorem genericPoint_mem_relPinnedChart_theta (b : Bool) :
    genericPoint (relCurve C K) ∈ relPinnedChart C K π b := by
  letI : IsIntegral (C ⊗ overSpec k K).left := by
    change IsIntegral (relCurve C K)
    infer_instance
  haveI : Surjective (fst C (overSpec k K)).left :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (Over.isPullback_left C (overSpec k K)).flip
      (surjective_specMap_algHom (Algebra.ofId k K))
  have hgen : (fst C (overSpec k K)).left.base (genericPoint (relCurve C K)) =
      genericPoint C.left := genericPoint_eq_of_surjective _
  have hmem : genericPoint C.left ∈ fiberChart₀ π ⊓ fiberChart₁ π :=
    genericPoint_mem_preimage_inf π
  cases b with
  | false =>
      change genericPoint (relCurve C K) ∈
        (fst C (overSpec k K)).left ⁻¹ᵁ (fiberTwoCover π).V₀
      rw [Scheme.Hom.mem_preimage, hgen, fiberTwoCover_V₀]
      exact hmem.1
  | true =>
      change genericPoint (relCurve C K) ∈
        (fst C (overSpec k K)).left ⁻¹ᵁ (fiberTwoCover π).V₁
      rw [Scheme.Hom.mem_preimage, hgen, fiberTwoCover_V₁]
      exact hmem.2

private theorem thetaFieldRead_relThetaSectionFst_ne_zero :
    thetaFieldRead C K π a (relThetaSectionFst C K π a) ≠ 0 := by
  intro h
  have hs : relThetaSectionFst C K π a = 0 := by
    apply thetaFieldRead_injective C K π a
    simpa using h
  have hv := congrArg (fun s : relThetaSections C K π a => s.val.2) hs
  have hv' : (1 : Γ(relCurve C K,
      ⊤ ⊓ (relCover C K (fiberTwoCover π)).V₁)) = 0 := by simpa using hv
  have hη1 : genericPoint (relCurve C K) ∈
      (relCover C K (fiberTwoCover π)).V₁ :=
    genericPoint_mem_relPinnedChart_theta C K π true
  have hstalk := congrArg
    ((relCurve C K).presheaf.germ
      (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₁)
      (genericPoint (relCurve C K))
      ⟨trivial, hη1⟩).hom hv'
  have hfield := congrArg
    (algebraMap ((relCurve C K).presheaf.stalk (genericPoint (relCurve C K)))
      (relCurve C K).functionField) hstalk
  have hfield' : (1 : (relCurve C K).functionField) = 0 := by
    simpa only [map_one, map_zero] using hfield
  exact (one_ne_zero : (1 : (relCurve C K).functionField) ≠ 0) hfield'

private theorem thetaFieldRead_relThetaSectionSnd_ne_zero :
    thetaFieldRead C K π a (relThetaSectionSnd C K π a) ≠ 0 := by
  intro h
  have hs : relThetaSectionSnd C K π a = 0 := by
    apply thetaFieldRead_injective C K π a
    simpa using h
  have hv := congrArg (fun s : relThetaSections C K π a => s.val.1) hs
  have hv' : (1 : Γ(relCurve C K,
      ⊤ ⊓ (relCover C K (fiberTwoCover π)).V₀)) = 0 := by simpa using hv
  have hη0 : genericPoint (relCurve C K) ∈
      (relCover C K (fiberTwoCover π)).V₀ :=
    genericPoint_mem_relPinnedChart_theta C K π false
  have hstalk := congrArg
    ((relCurve C K).presheaf.germ
      (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₀)
      (genericPoint (relCurve C K))
      ⟨trivial, hη0⟩).hom hv'
  have hfield := congrArg
    (algebraMap ((relCurve C K).presheaf.stalk (genericPoint (relCurve C K)))
      (relCurve C K).functionField) hstalk
  have hfield' : (1 : (relCurve C K).functionField) = 0 := by
    simpa only [map_one, map_zero] using hfield
  exact (one_ne_zero : (1 : (relCurve C K).functionField) ≠ 0) hfield'

/-- The rational reading of the canonical section `(t₀ᵃ,1)`, bundled as a
function-field unit. -/
noncomputable def thetaFieldPencilFstUnit : (relCurve C K).functionFieldˣ :=
  Units.mk0 (thetaFieldRead C K π a (relThetaSectionFst C K π a))
    (thetaFieldRead_relThetaSectionFst_ne_zero C K π a)

/-- The rational reading of the canonical section `(1,t₁ᵃ)`, bundled as a
function-field unit. -/
noncomputable def thetaFieldPencilSndUnit : (relCurve C K).functionFieldˣ :=
  Units.mk0 (thetaFieldRead C K π a (relThetaSectionSnd C K π a))
    (thetaFieldRead_relThetaSectionSnd_ne_zero C K π a)

private theorem thetaFieldPencilFst_mem :
    ((thetaFieldPencilFstUnit C K π a : (relCurve C K).functionFieldˣ) :
        (relCurve C K).functionField) ∈
      Scheme.divisorSections K (thetaFieldDivisor C K π a) ⊤ := by
  exact thetaFieldRead_mem C K π a (relThetaSectionFst C K π a)

private theorem thetaFieldPencilSnd_mem :
    ((thetaFieldPencilSndUnit C K π a : (relCurve C K).functionFieldˣ) :
        (relCurve C K).functionField) ∈
      Scheme.divisorSections K (thetaFieldDivisor C K π a) ⊤ := by
  exact thetaFieldRead_mem C K π a (relThetaSectionSnd C K π a)

omit [IsDominant π] [IsIntegral C.left] in
private theorem thetaFieldShiftUnit_mul_mem_windowTransport
    (r : (relCurve C K).functionFieldˣ)
    (hr : (r : (relCurve C K).functionField) ∈
      Scheme.divisorSections K (thetaFieldDivisor C K π a) ⊤) :
    ((thetaFieldShiftUnit C K π a * r : (relCurve C K).functionFieldˣ) :
        (relCurve C K).functionField) ∈
      Scheme.divisorSections K (windowTransportDivisor C K π a) ⊤ := by
  rw [mem_divisorSections_top_iff K
    (Units.ne_zero (thetaFieldShiftUnit C K π a * r))]
  have hmk : Units.mk0
      (((thetaFieldShiftUnit C K π a * r : (relCurve C K).functionFieldˣ) :
        (relCurve C K).functionField))
      (Units.ne_zero (thetaFieldShiftUnit C K π a * r)) =
        thetaFieldShiftUnit C K π a * r := Units.ext rfl
  rw [hmk, Scheme.divOf_mul, ← divOf_thetaFieldShiftUnit C K π a]
  rw [mem_divisorSections_top_iff K (Units.ne_zero r)] at hr
  have hmkr : Units.mk0 (r : (relCurve C K).functionField) (Units.ne_zero r) = r :=
    Units.ext rfl
  rw [hmkr] at hr
  convert hr using 1
  abel_nf

/-- The shifted reading of `(t₀ᵃ,1)` lies in the transported divisor window. -/
theorem windowTransportPencilFst_mem :
    ((thetaFieldShiftUnit C K π a * thetaFieldPencilFstUnit C K π a :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) ∈
      Scheme.divisorSections K (windowTransportDivisor C K π a) ⊤ :=
  thetaFieldShiftUnit_mul_mem_windowTransport C K π a
    (thetaFieldPencilFstUnit C K π a) (thetaFieldPencilFst_mem C K π a)

/-- The shifted reading of `(1,t₁ᵃ)` lies in the transported divisor window. -/
theorem windowTransportPencilSnd_mem :
    ((thetaFieldShiftUnit C K π a * thetaFieldPencilSndUnit C K π a :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) ∈
      Scheme.divisorSections K (windowTransportDivisor C K π a) ⊤ :=
  thetaFieldShiftUnit_mul_mem_windowTransport C K π a
    (thetaFieldPencilSndUnit C K π a) (thetaFieldPencilSnd_mem C K π a)

private theorem coeffAt_thetaFieldPencilFst_eq_zero {z : relCurve C K}
    (hzg : z ≠ genericPoint (relCurve C K))
    (hz0 : z ∉ (relCover C K (fiberTwoCover π)).V₀) :
    coeffAt hzg
      (thetaFieldDivisor C K π a + Scheme.divOf
        (relCurve C K ↘ Spec (CommRingCat.of K))
          (thetaFieldPencilFstUnit C K π a)) = 0 := by
  have hz1 : z ∈ (relCover C K (fiberTwoCover π)).V₁ :=
    mem_V₁_of_notMem_V₀ C K π hz0
  have hlocal : algebraMap ((relCurve C K).presheaf.stalk z)
      (relCurve C K).functionField
        (((relCurve C K).presheaf.germ
          (⊤ ⊓ (thetaFieldPointedCover C K π).opens z) z
          ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩).hom
          ((thetaFieldGluedEquiv C K π a
            (relThetaSectionFst C K π a)).val z)) = 1 := by
    rw [germ_thetaFieldGluedEquiv_snd C K π a
      (relThetaSectionFst C K π a) hz0
      ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩ ⟨trivial, hz1⟩,
      relThetaSectionFst_val_snd, map_one, map_one]
  have hprod :
      ((((thetaFieldPresentation C K π a).elem z :
          (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) *
        (thetaFieldPencilFstUnit C K π a : (relCurve C K).functionField)) = 1 := by
    change (((thetaFieldPresentation C K π a).elem z :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) *
      thetaFieldRead C K π a (relThetaSectionFst C K π a) = 1
    rw [← algebraMap_germ_thetaFieldGluedEquiv_eq C K π a
      (relThetaSectionFst C K π a) z]
    exact hlocal
  have hunit : (thetaFieldPresentation C K π a).elem z *
      thetaFieldPencilFstUnit C K π a = 1 := Units.ext hprod
  have hord := congrArg
    (fun q : (relCurve C K).functionFieldˣ =>
      Multiplicative.toAdd
        (Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) hzg q)) hunit
  change coeffAt hzg
    (Scheme.presentationDivisor K (thetaFieldPresentation C K π a) +
      Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
        (thetaFieldPencilFstUnit C K π a)) = 0
  rw [CurveDivisor.coeffAt_add,
    Scheme.coeffAt_presentationDivisor K (thetaFieldPresentation C K π a) hzg,
    CurveDivisor.coeffAt_divOf]
  simpa only [map_mul, map_one, toAdd_mul, toAdd_one] using hord

private theorem coeffAt_thetaFieldPencilSnd_eq_zero {z : relCurve C K}
    (hzg : z ≠ genericPoint (relCurve C K))
    (hz0 : z ∈ (relCover C K (fiberTwoCover π)).V₀) :
    coeffAt hzg
      (thetaFieldDivisor C K π a + Scheme.divOf
        (relCurve C K ↘ Spec (CommRingCat.of K))
          (thetaFieldPencilSndUnit C K π a)) = 0 := by
  have hlocal : algebraMap ((relCurve C K).presheaf.stalk z)
      (relCurve C K).functionField
        (((relCurve C K).presheaf.germ
          (⊤ ⊓ (thetaFieldPointedCover C K π).opens z) z
          ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩).hom
          ((thetaFieldGluedEquiv C K π a
            (relThetaSectionSnd C K π a)).val z)) = 1 := by
    rw [germ_thetaFieldGluedEquiv_fst C K π a
      (relThetaSectionSnd C K π a) hz0
      ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩ ⟨trivial, hz0⟩,
      relThetaSectionSnd_val_fst, map_one, map_one]
  have hprod :
      ((((thetaFieldPresentation C K π a).elem z :
          (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) *
        (thetaFieldPencilSndUnit C K π a : (relCurve C K).functionField)) = 1 := by
    change (((thetaFieldPresentation C K π a).elem z :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) *
      thetaFieldRead C K π a (relThetaSectionSnd C K π a) = 1
    rw [← algebraMap_germ_thetaFieldGluedEquiv_eq C K π a
      (relThetaSectionSnd C K π a) z]
    exact hlocal
  have hunit : (thetaFieldPresentation C K π a).elem z *
      thetaFieldPencilSndUnit C K π a = 1 := Units.ext hprod
  have hord := congrArg
    (fun q : (relCurve C K).functionFieldˣ =>
      Multiplicative.toAdd
        (Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) hzg q)) hunit
  change coeffAt hzg
    (Scheme.presentationDivisor K (thetaFieldPresentation C K π a) +
      Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
        (thetaFieldPencilSndUnit C K π a)) = 0
  rw [CurveDivisor.coeffAt_add,
    Scheme.coeffAt_presentationDivisor K (thetaFieldPresentation C K π a) hzg,
    CurveDivisor.coeffAt_divOf]
  simpa only [map_mul, map_one, toAdd_mul, toAdd_one] using hord

/-- The two canonical theta readings have disjoint effective zero divisors. -/
theorem thetaFieldPencil_basepointFree :
    (thetaFieldDivisor C K π a + Scheme.divOf
        (relCurve C K ↘ Spec (CommRingCat.of K))
          (thetaFieldPencilFstUnit C K π a)) ⊓
      (thetaFieldDivisor C K π a + Scheme.divOf
        (relCurve C K ↘ Spec (CommRingCat.of K))
          (thetaFieldPencilSndUnit C K π a)) = 0 := by
  refine Scheme.CurveDivisor.ext_coeffAt fun z hzg => ?_
  have hfst := thetaFieldPencilFst_mem C K π a
  have hsnd := thetaFieldPencilSnd_mem C K π a
  rw [mem_divisorSections_top_iff K
    (Units.ne_zero (thetaFieldPencilFstUnit C K π a))] at hfst
  rw [mem_divisorSections_top_iff K
    (Units.ne_zero (thetaFieldPencilSndUnit C K π a))] at hsnd
  have hmkF : Units.mk0
      ((thetaFieldPencilFstUnit C K π a : (relCurve C K).functionFieldˣ) :
        (relCurve C K).functionField)
      (Units.ne_zero (thetaFieldPencilFstUnit C K π a)) =
        thetaFieldPencilFstUnit C K π a := Units.ext rfl
  have hmkS : Units.mk0
      ((thetaFieldPencilSndUnit C K π a : (relCurve C K).functionFieldˣ) :
        (relCurve C K).functionField)
      (Units.ne_zero (thetaFieldPencilSndUnit C K π a)) =
        thetaFieldPencilSndUnit C K π a := Units.ext rfl
  rw [hmkF] at hfst
  rw [hmkS] at hsnd
  have hfst0 := Scheme.CurveDivisor.le_iff_coeffAt.mp hfst z hzg
  have hsnd0 := Scheme.CurveDivisor.le_iff_coeffAt.mp hsnd z hzg
  rw [CurveDivisor.coeffAt_zero] at hfst0 hsnd0
  rw [Scheme.CurveDivisor.coeffAt_inf, CurveDivisor.coeffAt_zero]
  by_cases hz0 : z ∈ (relCover C K (fiberTwoCover π)).V₀
  · rw [coeffAt_thetaFieldPencilSnd_eq_zero C K π a hzg hz0,
      min_eq_right hfst0]
  · rw [coeffAt_thetaFieldPencilFst_eq_zero C K π a hzg hz0,
      min_eq_left hsnd0]

/-- The canonical theta pencil after multiplication by the class-comparison
unit, now viewed in the transported divisor window. -/
theorem windowTransportPencil_basepointFree :
    (windowTransportDivisor C K π a + Scheme.divOf
        (relCurve C K ↘ Spec (CommRingCat.of K))
          (thetaFieldShiftUnit C K π a * thetaFieldPencilFstUnit C K π a)) ⊓
      (windowTransportDivisor C K π a + Scheme.divOf
        (relCurve C K ↘ Spec (CommRingCat.of K))
          (thetaFieldShiftUnit C K π a * thetaFieldPencilSndUnit C K π a)) = 0 := by
  rw [Scheme.divOf_mul, Scheme.divOf_mul,
    ← divOf_thetaFieldShiftUnit C K π a]
  have hbpf := thetaFieldPencil_basepointFree C K π a
  convert hbpf using 1
  abel_nf

end ThetaPencil

end AlgebraicGeometry
