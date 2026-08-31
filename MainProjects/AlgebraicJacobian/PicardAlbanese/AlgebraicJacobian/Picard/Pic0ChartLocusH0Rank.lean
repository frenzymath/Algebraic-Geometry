/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverageThreshold

/-!
# The section rank at a chart-locus point

`Pic0ChartLocusH0One` specializes the chart parameter to the genus and obtains the
unique-effective-representative value `h⁰ = 1`.  This file records the unspecialized
calculation.  If the chart parameter is `n` and the curve has Euler characteristic
`1 - g`, the vanishing witness extracted from `chartLocus` has

`h⁰ = n + 1 - g`.

This separates two roles that a coverage argument must not conflate: a large parameter can
force `H¹`-vanishing, while the injective Abel chart needs the genus parameter, where the
same rank formula becomes `h⁰ = 1`.
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

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-- Chart-locus membership at parameter `n` supplies a witness of section rank `n + 1 - g` on a
curve with Euler characteristic `1 - g`.

The conclusion retains the presentation, divisor-class, degree, and vanishing clauses from
`IsSplitWitness`; consequently it is tied to the given class and cannot be inhabited by an
unrelated trivial divisor. -/
theorem exists_splitting_h0_formula_of_mem_chartLocus
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) (n g : ℕ)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hlam : degAt lam (Over.testPoint t) = 0)
    (ht : t ∈ chartLocus C m Z lam) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra (Over.testPointField t) L)
        (_ : IsScalarTower k (Over.testPointField t) L)
        (_ : Module.Finite (Over.testPointField t) L)
        (_ : Algebra.IsSeparable (Over.testPointField t) L)
        (M : (relCurve C L).CechPic)
        (W : ((C ⊗ overSpec k L).left).CurveDivisor),
      PicEtAff.map C L
          (picEtAffineEquiv C (Over.testPointField t)
            (picEtMap C (Over.testPoint t) (chartTwist C m Z T lam)))
        = PicEtAff.unit C L (relPicMk C (overSpec k L) M) ∧
      Scheme.CurveDivisor.picClass L W = M ∧
      Scheme.CurveDivisor.deg L W = (n : ℤ) ∧
      Subsingleton (Sheaf.HModule
        ((C ⊗ overSpec k L).left.divisorSheaf L W) 1) ∧
      (Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L W) : ℤ)
        = (n : ℤ) + 1 - (g : ℤ) := by
  obtain ⟨L, hLf, hLa, hLKa, hLtow, hLfin, hLsep, M, hM, W, hWcl, hWh1⟩ := ht
  haveI : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L
  haveI : SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instSmoothOfRelativeDimensionBaseChange C L
  haveI : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instQuasiCompactBaseChange C L
  haveI : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
    instModuleFiniteHModuleZeroBaseChange C L
  haveI : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
    instModuleFiniteHModuleOneBaseChange C L
  have hWdeg : Scheme.CurveDivisor.deg L W = (n : ℤ) := by
    rw [← classDeg_picClass (K := L) W, hWcl,
      classDeg_presenting_eq_degAff C L _ M hM]
    change degAt (chartTwist C m Z T lam) (Over.testPoint t) = (n : ℤ)
    rw [chartTwist, degAt_mul, degAt_inv, degAt_mul, degAt_thetaFamily_pow,
      degAt_sigmaFamily, hlam, hdeg]
    ring
  have hχL : Sheaf.chi (((C ⊗ overSpec k L).left).moduleKSheaf L) = 1 - (g : ℤ) :=
    chi_relCurve_baseField C L g hχ
  have hrank := h0_eq_deg_add_chi_of_subsingleton_hModule_one (K := L) W hWh1
  rw [hWdeg, hχL] at hrank
  refine ⟨L, hLf, hLa, hLKa, hLtow, hLfin, hLsep, M, W, hM, hWcl, hWdeg, hWh1, ?_⟩
  omega

/-- Above the genus parameter, chart-locus membership supplies a witness with at least two
sections.  Thus the
large-parameter vanishing route and the `h⁰ = 1` uniqueness route are genuinely different
branches of the representability argument. -/
theorem exists_splitting_two_le_h0_of_mem_chartLocus
    {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) (n g : ℕ)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hlam : degAt lam (Over.testPoint t) = 0) (hgn : g < n)
    (ht : t ∈ chartLocus C m Z lam) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra (Over.testPointField t) L)
        (_ : IsScalarTower k (Over.testPointField t) L)
        (_ : Module.Finite (Over.testPointField t) L)
        (_ : Algebra.IsSeparable (Over.testPointField t) L)
        (M : (relCurve C L).CechPic)
        (W : ((C ⊗ overSpec k L).left).CurveDivisor),
      PicEtAff.map C L
          (picEtAffineEquiv C (Over.testPointField t)
            (picEtMap C (Over.testPoint t) (chartTwist C m Z T lam)))
        = PicEtAff.unit C L (relPicMk C (overSpec k L) M) ∧
      Scheme.CurveDivisor.picClass L W = M ∧
      Scheme.CurveDivisor.deg L W = (n : ℤ) ∧
      Subsingleton (Sheaf.HModule
        ((C ⊗ overSpec k L).left.divisorSheaf L W) 1) ∧
      2 ≤ Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L W) := by
  obtain ⟨L, hLf, hLa, hLKa, hLtow, hLfin, hLsep, M, W, hM, hWcl, hWdeg, hWh1,
      hrank⟩ := exists_splitting_h0_formula_of_mem_chartLocus
        lam t m Z n g hdeg hχ hlam ht
  refine ⟨L, hLf, hLa, hLKa, hLtow, hLfin, hLsep, M, W, hM, hWcl, hWdeg, hWh1, ?_⟩
  have htwo : (2 : ℤ) ≤
      (Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L W) : ℤ) := by
    rw [hrank]
    omega
  exact_mod_cast htwo

/-! ## The actual unconditional coverage parameter -/

/-- On a positive-genus curve, the unconditional admissible coverage parameter is strictly
larger than the genus.

The strictness does not add a cohomological hypothesis: `h⁰(𝒪_C) = 1` follows from the standing
proper, smooth, geometrically irreducible assumptions.  If the ledger contribution above `g`
were nonpositive, `genus_eq_zero_of_windowBound_nonpos` would contradict `g ≠ 0`. -/
theorem genus_lt_admissibleCoverageParameter_of_ne_zero
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.hom)
    (g : ℕ) (hg : g ≠ 0)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    letI : C.left.Over (Spec (.of k)) := ⟨C.hom⟩
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
    g < admissibleCoverageParameter (C := C) hπ g := by
  letI : C.left.Over (Spec (.of k)) := ⟨C.hom⟩
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
  have hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1 := h0_moduleKSheaf C
  have hb : 0 < windowBound π hπ := by
    by_contra hnonpos
    exact hg (genus_eq_zero_of_windowBound_nonpos π hπ g
      (not_lt.mp hnonpos) hO hχ)
  have hM := windowBound_le_M_mul π hπ g
  have hledger : (g : ℤ) <
      (windowM_choice π hπ g : ℤ) * windowδ π + (g : ℤ) := by
    omega
  have hadmissible := ledgerBound_le_admissibleCoverageParameter (C := C) hπ g
  have hcast : (g : ℤ) <
      (admissibleCoverageParameter (C := C) hπ g : ℤ) :=
    hledger.trans_le hadmissible
  exact_mod_cast hcast

/-- For positive genus, the uniform full-locus coverage chart supplies a splitting witness with
at least two sections at every degree-zero fibre point.

This is the direct join between `exists_uniform_admissibleCoverageChart` and the rank formula:
the large parameter solves vanishing and coverage, but it cannot simultaneously be read as the
genus-parameter `h⁰ = 1` chart used by the unique-effective-representative route. -/
theorem exists_uniform_admissibleCoverageChart_two_le_h0
    {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap k = C.hom)
    (g : ℕ) (hg : g ≠ 0)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    letI : C.left.Over (Spec (.of k)) := ⟨C.hom⟩
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
    ∃ (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor),
      Scheme.CurveDivisor.deg k Z
          = (m : ℤ) * classDeg k (thetaCechClass C)
            - (admissibleCoverageParameter (C := C) hπ g : ℤ) ∧
        ∀ {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left),
          degAt lam (Over.testPoint t) = 0 →
            ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
                (_ : Algebra (Over.testPointField t) L)
                (_ : IsScalarTower k (Over.testPointField t) L)
                (_ : Module.Finite (Over.testPointField t) L)
                (_ : Algebra.IsSeparable (Over.testPointField t) L)
                (M : (relCurve C L).CechPic)
                (W : ((C ⊗ overSpec k L).left).CurveDivisor),
              PicEtAff.map C L
                  (picEtAffineEquiv C (Over.testPointField t)
                    (picEtMap C (Over.testPoint t) (chartTwist C m Z T lam)))
                = PicEtAff.unit C L (relPicMk C (overSpec k L) M) ∧
              Scheme.CurveDivisor.picClass L W = M ∧
              Scheme.CurveDivisor.deg L W
                = (admissibleCoverageParameter (C := C) hπ g : ℤ) ∧
              Subsingleton (Sheaf.HModule
                ((C ⊗ overSpec k L).left.divisorSheaf L W) 1) ∧
              2 ≤ Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L W) := by
  letI : C.left.Over (Spec (.of k)) := ⟨C.hom⟩
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
  obtain ⟨m, Z, hZ, hcover⟩ := exists_uniform_admissibleCoverageChart hπ g hχ
  refine ⟨m, Z, hZ, ?_⟩
  intro T lam t hlam
  exact exists_splitting_two_le_h0_of_mem_chartLocus lam t m Z
    (admissibleCoverageParameter (C := C) hπ g) g hZ hχ hlam
    (genus_lt_admissibleCoverageParameter_of_ne_zero hπ g hg hχ)
    (hcover lam t hlam)

end

end AlgebraicGeometry
