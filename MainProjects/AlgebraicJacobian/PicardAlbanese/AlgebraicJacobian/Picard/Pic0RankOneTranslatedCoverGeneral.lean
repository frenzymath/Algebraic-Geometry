/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.Pic0SepClosedCover
import AlgebraicJacobian.Curve.MapToP1

/-!
# The general separably closed translated-cover producer

This file closes the field-level producer left open by `Pic0SepClosedCover`.  For every field
extension `K/k` and every `mu : picEt C (overSpec k K)`, it constructs the finite separable
splitting field and all of `SepClosedTranslatedDropData`.

The positive twist stays tied to the presenting class of `mu`.  Its exponent is chosen above
both the FLV threshold and the amount needed to put the twisted class in degree at least the
genus.  The dense-point, residue-one, finite-support, and base-subtraction fields are then filled
by the rational-point-image constructor, so the output feeds the existing translated-drop
consumer without replacing `mu` by an unrelated Picard class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] [IsSepClosed k]
variable {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

section Producer

variable {K : Type u} [Field K] [Algebra k K]

/-- Every field-valued Picard class admits the complete lambda-tied translated-drop datum.

The nested existential is the same finite-separable splitting package used by
`exists_splitting_of_picEt`.  In particular, the returned `M₀` is certified by `hM₀` to present
the given `mu`; the positive twist, its representative, and the later base subtraction all live
in that same package. -/
theorem exists_sepClosedTranslatedDropData
    (mu : picEt C (overSpec k K)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra K L)
        (_ : IsScalarTower k K L) (_ : Module.Finite K L)
        (_ : Algebra.IsSeparable K L),
      Nonempty (SepClosedTranslatedDropData (C := C) (L := L) mu) := by
  obtain ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, M₀, hM₀⟩ :=
    exists_splitting_of_picEt C mu
  letI := hLfield
  letI := hkL
  letI := hKL
  letI := htow
  letI := hfin
  letI := hsep
  haveI : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L
  haveI : SmoothOfRelativeDimension 1
      (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instSmoothOfRelativeDimensionBaseChange C L
  haveI : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instQuasiCompactBaseChange C L
  haveI : Module.Finite L
      (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
    instModuleFiniteHModuleZeroBaseChange C L
  haveI : Module.Finite L
      (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
    instModuleFiniteHModuleOneBaseChange C L
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C L).hom :=
    instSmoothOfRelativeDimensionSndLeft C L
  haveI : IsProper (baseChangeBundle C L).hom :=
    instIsProperSndLeft C L
  haveI : GeometricallyIrreducible (baseChangeBundle C L).hom :=
    instGeometricallyIrreducibleSndLeft C L
  haveI : IsIntegral (baseChangeBundle C L).left :=
    instIsIntegralBaseChange C L
  haveI : SmoothOfRelativeDimension 1
      ((baseChangeBundle C L).left ↘ Spec (CommRingCat.of L)) :=
    instSmoothOfRelativeDimensionBaseChange C L
  haveI : QuasiCompact
      ((baseChangeBundle C L).left ↘ Spec (CommRingCat.of L)) :=
    instQuasiCompactBaseChange C L
  haveI : Module.Finite L
      (Sheaf.HModule ((baseChangeBundle C L).left.moduleKSheaf L) 0) :=
    instModuleFiniteHModuleZeroBaseChange C L
  haveI : Module.Finite L
      (Sheaf.HModule ((baseChangeBundle C L).left.moduleKSheaf L) 1) :=
    instModuleFiniteHModuleOneBaseChange C L
  obtain ⟨pi, hpiFinite, hpiDominant, hpi⟩ :=
    exists_isFinite_isDominant_toP1 (C := baseChangeBundle C L)
  letI : IsFinite pi := hpiFinite
  letI : IsDominant pi := hpiDominant
  let thetaL : (C ⊗ overSpec k L).left.CechPic :=
    Scheme.CechPic.map ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left)
      (thetaCechClass C)
  have hthetaL : 1 ≤ classDeg L thetaL := by
    dsimp only [thetaL]
    exact one_le_classDeg_cechPicMap_baseFieldTransition_of_one_le
      (C := C) (Algebra.ofId k L) (thetaCechClass C)
      (one_le_classDeg_thetaCechClass (C := C))
  obtain ⟨n₀, hn₀⟩ :=
    exists_positive_twist_vanishing pi hpi M₀ thetaL hthetaL
  let deficit : ℕ := ((genus C : ℤ) - classDeg L M₀).toNat
  let m : ℕ := n₀ + deficit
  have hn₀m : n₀ ≤ m := by
    simp [m]
  have hdeficitm : deficit ≤ m := by
    simp [m]
  have hdegreeClass : (genus C : ℤ) ≤ classDeg L (M₀ * thetaL ^ m) := by
    rw [classDeg_mul, classDeg_pow]
    have hdeficit :
        (genus C : ℤ) - classDeg L M₀ ≤ (deficit : ℤ) := by
      exact Int.self_le_toNat _
    have hdeficitm' : (deficit : ℤ) ≤ (m : ℤ) := by
      exact_mod_cast hdeficitm
    have hthetaMultiple :
        (m : ℤ) ≤ (m : ℤ) * classDeg L thetaL :=
      le_mul_of_one_le_right (Int.natCast_nonneg m) hthetaL
    linarith
  obtain ⟨W₀, hW₀raw⟩ := Scheme.CurveDivisor.exists_picClass_eq L
    (M₀ * Scheme.CechPic.map
      ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left)
      (chartTwistClass C m
        (0 : (C ⊗ overSpec k k).left.CurveDivisor)))
  have hchart :
      Scheme.CechPic.map ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left)
          (chartTwistClass C m
            (0 : (C ⊗ overSpec k k).left.CurveDivisor)) =
        thetaL ^ m := by
    simp only [thetaL, chartTwistClass, Over.tensorObj_left, overSpec_left,
      Over.coe_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id,
      Scheme.CurveDivisor.picClass_zero, inv_one, mul_one]
    exact map_pow (Scheme.CechPic.map
      ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left)) (thetaCechClass C) m
  have hWtheta :
      Scheme.CurveDivisor.picClass L W₀ = M₀ * thetaL ^ m := by
    rw [hW₀raw, hchart]
  have hdegreeW₀ :
      (genus C : ℤ) ≤ Scheme.CurveDivisor.deg L W₀ := by
    rw [← classDeg_picClass L W₀, hWtheta]
    exact hdegreeClass
  have h1W₀ : Subsingleton
      (Sheaf.HModule ((C ⊗ overSpec k L).left.divisorSheaf L W₀) 1) :=
    hn₀ m hn₀m W₀ hWtheta
  let excess : ℕ :=
    (Scheme.CurveDivisor.deg L W₀ - (genus C : ℤ)).toNat
  have hexcessNonnegative :
      0 ≤ Scheme.CurveDivisor.deg L W₀ - (genus C : ℤ) :=
    sub_nonneg.mpr hdegreeW₀
  have hdegreeExact :
      Scheme.CurveDivisor.deg L W₀ = (genus C : ℤ) + excess := by
    dsimp [excess]
    rw [Int.toNat_of_nonneg hexcessNonnegative]
    ring
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : IsIntegral C.left := isIntegral_left_of_geometricallyReduced C
  haveI : LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  let M₀rel : (relCurve C L).CechPic := M₀
  have hM₀rel : PicEtAff.map C L (picEtAffineEquiv C K mu) =
      PicEtAff.unit C L (relPicMk C (overSpec k L) M₀rel) := by
    simpa only [M₀rel] using hM₀
  refine ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, ?_⟩
  exact ⟨sepClosedTranslatedDropDataOfRationalPointImage
    mu m M₀rel hM₀rel W₀ (by
      rw [relCurveMap_eq_overSpecMap_ofId]
      change Scheme.CurveDivisor.picClass L W₀ =
        M₀ * Scheme.CechPic.map
          ((C ◁ Over.overSpecMap (Algebra.ofId k L)).left)
          (chartTwistClass C m
            (0 : (C ⊗ overSpec k k).left.CurveDivisor))
      exact hW₀raw) excess hdegreeExact h1W₀⟩

/-- Immediate consumer of the general producer through the existing translated-drop theorem.

The result retains the chosen subtraction divisor and its descended base-field divisor, and its
last field is the `IsSplitWitness` for this exact input `mu` translated by that exact base class. -/
theorem exists_sepClosedTranslatedDropResult_general
    (mu : picEt C (overSpec k K)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra K L)
        (_ : IsScalarTower k K L) (_ : Module.Finite K L)
        (_ : Algebra.IsSeparable K L)
        (d : SepClosedTranslatedDropData (C := C) (L := L) mu),
      Nonempty (SepClosedTranslatedDropResult (C := C) (L := L) mu d) := by
  obtain ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, ⟨d⟩⟩ :=
    exists_sepClosedTranslatedDropData (C := C) mu
  letI := hLfield
  letI := hkL
  letI := hKL
  letI := htow
  letI := hfin
  letI := hsep
  exact ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, d,
    exists_sepClosedTranslatedDropResult mu d⟩

/-! ## General support and base-subtraction compatibility -/

section Compatibility

variable {K L : Type u} [Field K] [Algebra k K] [Field L] [Algebra k L]
  [Algebra K L] [IsScalarTower k K L]

omit [IsSepClosed k] in
/-- The exact subtraction divisor produced by a translated drop has finite support.

This belongs to the general producer rather than the `Pic^0` specialization: the support is the
`Finsupp` support of the result for an arbitrary input class `mu`. -/
theorem SepClosedTranslatedDropResult.subtraction_support_finite
    (mu : picEt C (overSpec k K))
    (d : SepClosedTranslatedDropData (C := C) (L := L) mu)
    (r : SepClosedTranslatedDropResult (C := C) (L := L) mu d) :
    Set.Finite (r.S.support : Set {x : (C ⊗ overSpec k L).left //
      x ≠ genericPoint (C ⊗ overSpec k L).left}) :=
  r.S.support.finite_toSet

omit [IsSepClosed k] in
/-- Every support point of the exact subtraction divisor has residue degree one.

The proof uses the same density image stored in `d`; it does not choose a separate residue-point
carrier. -/
theorem SepClosedTranslatedDropResult.residueDeg_one_of_mem_subtraction_support
    (mu : picEt C (overSpec k K))
    (d : SepClosedTranslatedDropData (C := C) (L := L) mu)
    (r : SepClosedTranslatedDropResult (C := C) (L := L) mu d)
    (p : {x : (C ⊗ overSpec k L).left //
      x ≠ genericPoint (C ⊗ overSpec k L).left})
    (hp : p ∈ r.S.support) :
    (C ⊗ overSpec k L).left.residueDeg L p.1 = 1 := by
  apply d.hPdeg p.1
  apply r.support p.1 p.2
  exact Finsupp.mem_support_iff.mp hp

omit [IsSepClosed k] in
/-- Bundle finite support, residue-one compatibility, and the descended class identity for the
same subtraction divisor of an arbitrary translated-drop result. -/
theorem SepClosedTranslatedDropResult.baseSubtraction_compatibility
    (mu : picEt C (overSpec k K))
    (d : SepClosedTranslatedDropData (C := C) (L := L) mu)
    (r : SepClosedTranslatedDropResult (C := C) (L := L) mu d) :
    Set.Finite (r.S.support : Set {x : (C ⊗ overSpec k L).left //
        x ≠ genericPoint (C ⊗ overSpec k L).left}) ∧
      (∀ p : {x : (C ⊗ overSpec k L).left //
          x ≠ genericPoint (C ⊗ overSpec k L).left},
        p ∈ r.S.support → (C ⊗ overSpec k L).left.residueDeg L p.1 = 1) ∧
      Scheme.CurveDivisor.picClass L r.S =
        Scheme.CechPic.map (relCurveMap C k L)
          ((chartTwistClass C 0 r.Z)⁻¹) := by
  exact ⟨r.subtraction_support_finite mu d,
    fun p hp => r.residueDeg_one_of_mem_subtraction_support mu d p hp,
    r.baseClass⟩

end Compatibility

end Producer

end

end AlgebraicGeometry
