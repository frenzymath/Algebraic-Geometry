/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeFibreH1
import AlgebraicJacobian.Picard.ThetaChartClassNaturality
import AlgebraicJacobian.Picard.DivisorThetaFibre
import AlgebraicJacobian.Picard.DivisorFamilyMapAlg
import AlgebraicJacobian.RiemannRoch.WindowFieldTransport
import AlgebraicJacobian.Picard.DivisorFamilyField
import AlgebraicJacobian.Picard.DivisorFamilyFieldCRT
import AlgebraicJacobian.Cohomology.H1BaseFieldInvariance

/-!
# G-1 — the fibrewise `H¹`-data of a certified adaptation (`informal/spec-w4-gates.md` §G-1)

The witness-production half of the theta-ideal fibre story (the residual named at
`Picard/DivisorThetaFibre.lean:33-34`), assembled from the G-0a class law
(`Picard/DivSchemeFibreH1.lean`), the theta-chart class naturality
(`Picard/ThetaChartClassNaturality.lean`) and the N-pack window transport
(`RiemannRoch/WindowFieldTransport.lean`):

* `subsingleton_h1_windowTransportDivisor_sub` — the transported normalization at ANY
  exponent `a ≥ M`: `H¹(𝒪(N(a) − D')) = 0` for `deg D' ≤ 2g` (the `hNnorm` engine of
  the N-pack, with the `a·δ ≥ M·δ` slack; covers both campaign windows `M`, `M+s`).
* `DivisorAdaptation.IsCertified.fibrewise_h1` — **the G-1 keystone, UNCONDITIONAL**: for
  a certified adaptation over any test ring, at any window `a ≥ M`, the engine's fibrewise
  hypothesis `∀ p, Subsingleton (H¹(pair (Θᵃ − d)) ⊗ κ(p))` holds — witnessed at each
  prime by `N(a) − d_p` where `d_p` is the fibre divisor of the pulled-back family.
  The class leg is G-0a + theta-chart naturality + the landed base-change laws; the `H¹`
  leg is the N-pack normalization; and the fibre degree law `deg κ(p) d_p = g` — formerly
  the named `hdeg` seam — is the general colength↔degree identity, landed at
  `DivisorAdaptation.IsCertified.deg_presentationDivisor_pulledEquations`
  (`Picard/DivisorFamilyFieldCRT.lean`; certificates base-change, and the glued colength
  is the divisor degree by the stalk-CRT decomposition).
* `DivisorAdaptation.IsCertified.thetaGluedEval_surjective` — the `hsurj` corollary:
  right exactness of the twisted section sequence for certified families, unconditional.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k) [IsFinite π]


/-! ## The G-1 keystone: the fibrewise `H¹`-data of a certified adaptation -/

section Keystone

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [IsDominant π] [IsIntegral C.left]

attribute [local instance] instOverCleftWFT

omit [IsDominant π] [IsIntegral C.left] in
/-- The Euler characteristic of the structure sheaf of the fibre curve at any field
extension, from the base-level genus normalization (`genus_baseField` +
`chi_moduleKSheaf` at both fields). -/
private lemma chi_relCurve_of_chi (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (K : Type u) [Field K] [Algebra k K] :
    Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ) := by
  haveI : IsProper (baseChangeBundle C K).hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C K).hom :=
    instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible (baseChangeBundle C K).hom :=
    instGeometricallyIrreducibleSndLeft C K
  have h1 : Sheaf.chi ((relCurve C K).moduleKSheaf K)
      = 1 - (genus (baseChangeBundle C K) : ℤ) := chi_moduleKSheaf (baseChangeBundle C K)
  have h2 : genus (baseChangeBundle C K) = genus C := genus_baseField C K
  have h3 : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (genus C : ℤ) := chi_moduleKSheaf C
  have h4 : (genus C : ℤ) = (g : ℤ) := by rw [h3] at hχ; linarith
  rw [h1, h2, h4]

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

-- The fibre-curve geometric package at every field extension, re-keyed on the
-- `relCurve` spelling (the `Curve.BaseChangeInstances` stack).
noncomputable local instance instIsIntegralRelCurveKey (K : Type u) [Field K]
    [Algebra k K] : IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveKey (K : Type u) [Field K]
    [Algebra k K] :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveKey (K : Type u) [Field K] [Algebra k K] :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveKey (K : Type u) [Field K] [Algebra k K] :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveKey (K : Type u) [Field K]
    [Algebra k K] : Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveKey (K : Type u) [Field K]
    [Algebra k K] : Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

/-- **The transported normalization at any exponent `a ≥ M`** (the `hNnorm` engine of
the N-pack, with the `a·δ ≥ M·δ` slack — covers both campaign windows `M` and `M+s`):
for every divisor `D'` of degree `≤ 2g` on the `K`-fibre,
`H¹(𝒪(N(a) − D')) = 0`.  Peeling from the transported multiplier window `s·F`
(degenerate `windowBound ≤ 0` branch: from `N(a)` itself, where `g = 0`), licensed by
the ledger budgets. -/
theorem subsingleton_h1_windowTransportDivisor_sub (K : Type u) [Field K]
    [Algebra k K] (g a : ℕ)
    (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ))
    (D' : (relCurve C K).CurveDivisor)
    (hD' : Scheme.CurveDivisor.deg K D' ≤ 2 * (g : ℤ)) :
    Subsingleton (Sheaf.HModule
      ((relCurve C K).divisorSheaf K (windowTransportDivisor C K π a - D')) 1) := by
  have hsub : Scheme.CurveDivisor.deg K (windowTransportDivisor C K π a - D')
      = Scheme.CurveDivisor.deg K (windowTransportDivisor C K π a)
        - Scheme.CurveDivisor.deg K D' := by
    rw [sub_eq_add_neg, Scheme.CurveDivisor.deg_add, Scheme.CurveDivisor.deg_neg,
      sub_eq_add_neg]
  by_cases hb : windowBound π hπ ≤ 0
  · -- degenerate branch: `g = 0`, peel from `N(a)` itself
    have hg0 : g = 0 := genus_eq_zero_of_windowBound_nonpos π hπ g hb hO hχ
    subst hg0
    refine subsingleton_hModule_one_of_witness K (windowTransportDivisor C K π a) _
      (subsingleton_h1_windowTransportDivisor C K π a ha1) ?_
    rw [hsub, hχK]
    simp only [Nat.cast_zero] at hD' ⊢
    linarith
  · -- main branch: peel from the transported multiplier window `s·F`
    refine subsingleton_hModule_one_of_witness K
      (windowTransportDivisor C K π (windowS_choice π hπ g)) _
      (subsingleton_h1_windowTransportDivisor C K π _ (relThetaPairH1_windowS C hπ g))
      ?_
    rw [hsub, hχK, deg_windowTransportDivisor, deg_windowTransportDivisor]
    have hb1 : 0 < windowBound π hπ := not_le.mp hb
    have hM := windowM_spec π hπ g
    have hδ := one_le_windowδ π
    have hs : (0 : ℤ) ≤ (windowS_choice π hπ g : ℤ) := Int.natCast_nonneg _
    have hg : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg _
    have hMa' : (windowM_choice π hπ g : ℤ) * windowδ π ≤ (a : ℤ) * windowδ π :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hMa) (windowδ_nonneg π)
    have hkey : (windowS_choice π hπ g : ℤ) * windowδ π + ((g : ℤ) + 2)
        ≤ ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) * windowδ π := by
      nlinarith [hs, hg, hδ, mul_nonneg (mul_nonneg
        (by linarith : (0 : ℤ) ≤ (g : ℤ) + 1) hs)
        (by linarith : (0 : ℤ) ≤ windowδ π)]
    linarith [hM, hkey, hb1, hD', hMa']

/-- **Decoupled transported normalization.**  The window and divisor budget are
indexed by `g`, while the fibre Euler characteristic is normalized by an independent
parameter `gamma`.  Positivity of the normalized ledger bound makes the multiplier
window a uniform witness. -/
theorem subsingleton_h1_windowTransportDivisor_sub_at
    (K : Type u) [Field K] [Algebra k K] (g a : ℕ)
    (hMa : windowM_choice π hπ g ≤ a)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hχK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (gamma : ℤ))
    (D' : (relCurve C K).CurveDivisor)
    (hD' : Scheme.CurveDivisor.deg K D' ≤ 2 * (g : ℤ)) :
    Subsingleton (Sheaf.HModule
      ((relCurve C K).divisorSheaf K (windowTransportDivisor C K π a - D')) 1) := by
  have hsub : Scheme.CurveDivisor.deg K (windowTransportDivisor C K π a - D')
      = Scheme.CurveDivisor.deg K (windowTransportDivisor C K π a)
        - Scheme.CurveDivisor.deg K D' := by
    rw [sub_eq_add_neg, Scheme.CurveDivisor.deg_add, Scheme.CurveDivisor.deg_neg,
      sub_eq_add_neg]
  refine subsingleton_hModule_one_of_witness K
    (windowTransportDivisor C K π (windowS_choice π hπ g)) _
    (subsingleton_h1_windowTransportDivisor C K π _ (relThetaPairH1_windowS C hπ g))
    ?_
  rw [hsub, hχK, deg_windowTransportDivisor, deg_windowTransportDivisor]
  have hb1 : 0 < windowBound π hπ := windowBound_pos π hπ
  have hM := windowM_spec π hπ g
  have hδ := one_le_windowδ π
  have hs : (0 : ℤ) ≤ (windowS_choice π hπ g : ℤ) := Int.natCast_nonneg _
  have hg : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg _
  have hgamma' : (gamma : ℤ) ≤ (g : ℤ) := by exact_mod_cast hgamma
  have hMa' : (windowM_choice π hπ g : ℤ) * windowδ π ≤ (a : ℤ) * windowδ π :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hMa) (windowδ_nonneg π)
  have hkey : (windowS_choice π hπ g : ℤ) * windowδ π + ((g : ℤ) + 2)
      ≤ ((g : ℤ) + 2) * ((windowS_choice π hπ g : ℤ) + 1) * windowδ π := by
    nlinarith [hs, hg, hδ, mul_nonneg (mul_nonneg
      (by linarith : (0 : ℤ) ≤ (g : ℤ) + 1) hs)
      (by linarith : (0 : ℤ) ≤ windowδ π)]
  linarith [hM, hkey, hb1, hD', hMa', hgamma']



/-- The Picard class of a negated divisor is the inverse class. -/
private lemma picClass_neg {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] [IsIntegral X]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] (D : X.CurveDivisor) :
    Scheme.CurveDivisor.picClass K (-D) = (Scheme.CurveDivisor.picClass K D)⁻¹ := by
  have h := Scheme.CurveDivisor.picClass_add K (-D) D
  rw [neg_add_cancel, Scheme.CurveDivisor.picClass_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- **The G-1 keystone — the fibrewise `H¹`-data of a certified adaptation**
(`informal/spec-w4-gates.md` §G-1 pin), UNCONDITIONAL: for a certified divisor adaptation
over any test ring and any window exponent `a ≥ M` with ledger `H¹`-input, the rigid
engine's complex-form fibrewise hypothesis

`Subsingleton (H¹(pair (Θᵃ − d)) ⊗[R] κ(p))`

holds at every prime — witnessed by `N(a) − d_p`, where `N(a)` is the transported
window divisor and `d_p` the fibre divisor of the pulled-back family.  The class leg
is the G-0a class law + theta-chart naturality + the landed base-change laws; the
`H¹` leg is the transported normalization; and the fibre degree law `deg κ(p) d_p = g`
(formerly the named `hdeg` seam) is the landed general colength↔degree identity
`IsCertified.deg_presentationDivisor_pulledEquations`
(`Picard/DivisorFamilyFieldCRT.lean`). -/
theorem DivisorAdaptation.IsCertified.fibrewise_h1 {R : Type u} [CommRing R]
    [Algebra k R] {d : (relCurve C R).LocalEquations} {A : DivisorAdaptation C R π d}
    {g : ℕ} (hc : A.IsCertified g)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a)
    (p : PrimeSpectrum R) :
    Subsingleton ((datumPair (A.thetaIdealDatum a)).H1 ⊗[R]
      p.asIdeal.ResidueField) := by
  have hdeg : ∀ q : PrimeSpectrum R,
      Scheme.CurveDivisor.deg q.asIdeal.ResidueField
        (Scheme.presentationDivisor q.asIdeal.ResidueField
          ((A.pulledEquations q.asIdeal.ResidueField
            hc.projective_colength).presentation)) = (g : ℤ) :=
    fun q => hc.deg_presentationDivisor_pulledEquations
  refine A.thetaIdealDatum_hfib_of_witness a (fun q => ?_) p
  refine ⟨windowTransportDivisor C q.asIdeal.ResidueField π a
    - Scheme.presentationDivisor q.asIdeal.ResidueField
        ((A.pulledEquations q.asIdeal.ResidueField
          hc.projective_colength).presentation), ?_, ?_⟩
  · -- the class leg: `[N(a) − d_q] = [Θᵃ] · [d_q]⁻¹` transported to the fibre
    have e1 : Scheme.CurveDivisor.picClass q.asIdeal.ResidueField
          (Scheme.presentationDivisor q.asIdeal.ResidueField
            ((A.pulledEquations q.asIdeal.ResidueField
              hc.projective_colength).presentation))
        = Scheme.CechPic.map (relCurveMap C R q.asIdeal.ResidueField) d.picClass := by
      rw [Scheme.CurveDivisor.picClass_presentationDivisor,
        Scheme.LocalEquations.presentation_picClass]
      exact A.picClass_pulledEquations q.asIdeal.ResidueField hc.projective_colength
    have e2 : Scheme.CurveDivisor.picClass q.asIdeal.ResidueField
          (windowTransportDivisor C q.asIdeal.ResidueField π a)
        = Scheme.CechPic.map (relCurveMap C R q.asIdeal.ResidueField)
            ((thetaChartDatum C R π a).cechPicClass) :=
      (picClass_windowTransportDivisor C q.asIdeal.ResidueField π a).trans
        (cechPicClass_map_thetaChartDatum C R π a q.asIdeal.ResidueField).symm
    calc Scheme.CurveDivisor.picClass q.asIdeal.ResidueField
          (windowTransportDivisor C q.asIdeal.ResidueField π a
            - Scheme.presentationDivisor q.asIdeal.ResidueField
                ((A.pulledEquations q.asIdeal.ResidueField
                  hc.projective_colength).presentation))
        = Scheme.CurveDivisor.picClass q.asIdeal.ResidueField
              (windowTransportDivisor C q.asIdeal.ResidueField π a)
            * (Scheme.CurveDivisor.picClass q.asIdeal.ResidueField
                (Scheme.presentationDivisor q.asIdeal.ResidueField
                  ((A.pulledEquations q.asIdeal.ResidueField
                    hc.projective_colength).presentation)))⁻¹ := by
          rw [sub_eq_add_neg, Scheme.CurveDivisor.picClass_add, picClass_neg]
      _ = Scheme.CechPic.map (relCurveMap C R q.asIdeal.ResidueField)
            ((thetaChartDatum C R π a).cechPicClass * d.picClass⁻¹) := by
          rw [e1, e2, map_mul, map_inv]
      _ = Scheme.CechPic.map (relCurveMap C R q.asIdeal.ResidueField)
            ((A.thetaIdealDatum a).cechPicClass) := by
          rw [A.cechPicClass_thetaIdealDatum]
      _ = ((A.thetaIdealDatum a).baseChange q.asIdeal.ResidueField).cechPicClass :=
          (BasicOpenCocycleDatum.cechPicClass_baseChange q.asIdeal.ResidueField
            (A.thetaIdealDatum a)).symm
  · -- the `H¹` leg: the transported normalization at `deg d_q = g ≤ 2g`
    refine subsingleton_h1_windowTransportDivisor_sub C π hπ q.asIdeal.ResidueField g a
      ha1 hMa hO hχ (chi_relCurve_of_chi C g hχ q.asIdeal.ResidueField) _ ?_
    rw [hdeg q]
    have := Int.natCast_nonneg g
    linarith

/-- **The `hsurj` corollary of G-1**: right exactness of the Θ-twisted section
sequence for a certified adaptation, at any window `a ≥ M` with ledger `H¹`-input,
UNCONDITIONAL.  Composes the keystone with the landed engine
`thetaGluedEval_surjective`. -/
theorem DivisorAdaptation.IsCertified.thetaGluedEval_surjective {R : Type u}
    [CommRing R] [Algebra k R] {d : (relCurve C R).LocalEquations}
    {A : DivisorAdaptation C R π d} {g : ℕ} (hc : A.IsCertified g)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {a : ℕ} (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    Function.Surjective (A.thetaGluedEval a) :=
  DivisorAdaptation.thetaGluedEval_surjective hπ
    (fun p => hc.fibrewise_h1 (C := C) (π := π) hπ hO hχ ha1 hMa p)

end Keystone

end AlgebraicGeometry
