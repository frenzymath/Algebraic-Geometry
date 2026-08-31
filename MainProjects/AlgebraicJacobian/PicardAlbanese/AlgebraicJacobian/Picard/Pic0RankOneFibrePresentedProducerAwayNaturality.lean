/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneFibrePresentedProducerAffineEvaluation
import AlgebraicJacobian.Picard.Pic0RankOneFibrePresentedProducerSectionDivEq
import AlgebraicJacobian.Picard.DivRepAwaySpanGlueAff

/-!
# Localization naturality for the rank-one evaluation divisor

The evaluation divisor cut from a tied rank-one generator on `D(f)` restricts to the
divisor cut from the same generator on `D(f * g)`.  The proof compares actual local
equations under coefficient change, transports the section through the verified cocycle
base-change tower, and only then passes to `DivFamZarAff`.

These restriction identities are the pairwise compatibility input for the finite
principal-open glue.  They assume neither a global evaluator nor
`PicRankOneOpen.FibrePresented`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {A : Type u} [CommRing A] [Algebra k A]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

namespace PicRankOneLocalPresentation

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] in
private theorem injective_components_of_cast_eq
    {B : Type u} [CommRing B] [Algebra k B]
    {D D' : BasicOpenCocycleDatum C B pi}
    (hD : D = D')
    (s : ↑(gluedSubmodule B D.pieces D.unit ⊤))
    (s' : ↑(gluedSubmodule B D'.pieces D'.unit ⊤))
    (hs : cast (congrArg (fun E : BasicOpenCocycleDatum C B pi =>
      ↑(gluedSubmodule B E.pieces E.unit ⊤)) hD) s = s')
    (hfib' : ∀ (j : D'.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D'.component s' j)).rTensor p.asIdeal.ResidueField)) :
    ∀ (j : D.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField) := by
  cases hD
  have hs0 : s = s' := by simpa using hs
  cases hs0
  exact hfib'

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] in
private theorem sectionLocalEquationsOfFibrewiseRegular_eq_of_cast_eq
    {B : Type u} [CommRing B] [Algebra k B] [IsNoetherianRing B]
    {D D' : BasicOpenCocycleDatum C B pi}
    (hD : D = D')
    (s : ↑(gluedSubmodule B D.pieces D.unit ⊤))
    (s' : ↑(gluedSubmodule B D'.pieces D'.unit ⊤))
    (hs : cast (congrArg (fun E : BasicOpenCocycleDatum C B pi =>
      ↑(gluedSubmodule B E.pieces E.unit ⊤)) hD) s = s')
    (hfib : ∀ (j : D.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField))
    (hfib' : ∀ (j : D'.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D'.component s' j)).rTensor p.asIdeal.ResidueField)) :
    D.sectionLocalEquationsOfFibrewiseRegular s hfib =
      D'.sectionLocalEquationsOfFibrewiseRegular s' hfib' := by
  cases hD
  have hs0 : s = s' := by simpa using hs
  cases hs0
  rfl

set_option maxHeartbeats 8000000 in
-- The dependent fibrewise-regularity and local-equation cast comparison is expensive to elaborate.
theorem baseOpenRankOneDivisor_mapAlgHom_mul_left
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f g : P.cover.Carrier)
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    DivFamZarAff.mapAlgHom
        (DivFamZar.awayMulOfDvd (k := k) (f * g) f g rfl)
        (P.baseOpenRankOneDivisor f y hy) =
      P.baseOpenRankOneDivisor (f * g) y
        (P.generator_nonzero_on_mul_left f g y hy) := by
  let B := Localization.Away f
  let B' := Localization.Away (f * g)
  let phi : B →ₐ[k] B' :=
    DivFamZar.awayMulOfDvd (k := k) (f * g) f g rfl
  letI algBB' : Algebra B B' := phi.toRingHom.toAlgebra
  letI smulBB' : SMul B B' := algBB'.toSMul
  haveI towPB : IsScalarTower P.cover.Carrier B B' :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (DivFamZar.awayMulOfDvd_algebraMap
        (k := k) (f * g) f g rfl x).symm)
  haveI towkB : IsScalarTower k B B' :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (phi.commutes x).symm)
  let D := P.datum.baseChange B
  let s : ↑(gluedSubmodule B D.pieces D.unit ⊤) :=
    P.datumSectionBaseChange B y
  have hsec : ∀ q : PrimeSpectrum B,
      D.sectionsMapTop q.asIdeal.ResidueField s ≠ 0 :=
    fun q => P.sectionsMapTop_datumSectionBaseChange_away_ne_zero f y hy q
  have hfib : ∀ (j : D.index) (q : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor q.asIdeal.ResidueField) :=
    fun j q => by
      letI : IsIntegral (relCurve C q.asIdeal.ResidueField) :=
        instIsIntegralBaseChange C q.asIdeal.ResidueField
      exact D.injective_rTensor_component_of_sectionsMapTop_ne_zero s q (hsec q) j
  let D' := P.datum.baseChange B'
  let s' : ↑(gluedSubmodule B' D'.pieces D'.unit ⊤) :=
    P.datumSectionBaseChange B' y
  let hy' := P.generator_nonzero_on_mul_left f g y hy
  have hsec' : ∀ q : PrimeSpectrum B',
      D'.sectionsMapTop q.asIdeal.ResidueField s' ≠ 0 :=
    fun q => P.sectionsMapTop_datumSectionBaseChange_away_ne_zero (f * g) y hy' q
  have hfib' : ∀ (j : D'.index) (q : PrimeSpectrum B'), Function.Injective
      ((Scheme.mulSectionEnd B' (D'.component s' j)).rTensor q.asIdeal.ResidueField) :=
    fun j q => by
      letI : IsIntegral (relCurve C q.asIdeal.ResidueField) :=
        instIsIntegralBaseChange C q.asIdeal.ResidueField
      exact D'.injective_rTensor_component_of_sectionsMapTop_ne_zero s' q (hsec' q) j
  let hD : D.baseChange B' = D' :=
    P.datum.baseChange_baseChange C P.cover.Carrier B B'
  have hs : cast (congrArg (fun E : BasicOpenCocycleDatum C B' pi =>
      ↑(gluedSubmodule B' E.pieces E.unit ⊤)) hD)
        (D.sectionsMapTop B' s) = s' := by
    simpa only [D, D', s, s', hD] using
      (P.datumSectionBaseChange_tower B B' y)
  have hfibIter : ∀ (j : (D.baseChange B').index) (q : PrimeSpectrum B'),
      Function.Injective
        ((Scheme.mulSectionEnd B'
          ((D.baseChange B').component (D.sectionsMapTop B' s) j)).rTensor
            q.asIdeal.ResidueField) :=
    injective_components_of_cast_eq hD (D.sectionsMapTop B' s) s' hs hfib'
  have heq :
      (D.baseChange B').sectionLocalEquationsOfFibrewiseRegular
          (D.sectionsMapTop B' s) hfibIter =
        D'.sectionLocalEquationsOfFibrewiseRegular s' hfib' :=
    sectionLocalEquationsOfFibrewiseRegular_eq_of_cast_eq
      hD (D.sectionsMapTop B' s) s' hs hfibIter hfib'
  let hcert : IsLocallyCertifiedAff (genus C)
      (P.baseOpenDatumSectionLocalEquations f y hy) :=
    isLocallyCertifiedAff_of_forall_prime_certified_adaptation
      (exists_away_certifiedAff_of_fibrewiseRegular_of_classDeg C (genus C)
        (P.baseOpenDatumSectionLocalEquations f y hy) pi
        (P.baseOpenDatumSectionLocalEquations_fibrewiseRegular f y hy)
        (P.baseOpenDatumSectionLocalEquations_classDeg f y hy))
  let hcert' : IsLocallyCertifiedAff (genus C)
      (P.baseOpenDatumSectionLocalEquations (f * g) y hy') :=
    isLocallyCertifiedAff_of_forall_prime_certified_adaptation
      (exists_away_certifiedAff_of_fibrewiseRegular_of_classDeg C (genus C)
        (P.baseOpenDatumSectionLocalEquations (f * g) y hy') pi
        (P.baseOpenDatumSectionLocalEquations_fibrewiseRegular (f * g) y hy')
        (P.baseOpenDatumSectionLocalEquations_classDeg (f * g) y hy'))
  change DivFamZarAff.mapAlgHom phi
      (DivFamZarAff.mk (P.baseOpenDatumSectionLocalEquations f y hy) hcert) =
    DivFamZarAff.mk (P.baseOpenDatumSectionLocalEquations (f * g) y hy') hcert'
  rw [DivFamZarAff.mapAlgHom_eq_mapAlg phi (fun _ => rfl),
    DivFamZarAff.mapAlg_mk]
  apply DivFamZarAff.mk_eq_mk_iff.mpr
  have hgeneric :=
    D.pullback_sectionLocalEquationsOfFibrewiseRegular_divEq_sectionsMapTop
      s hfib B' hfibIter
      (hcert.germ_pullbackEqn_mem_nonZeroDivisors B' (genus C))
  rw [heq] at hgeneric
  simpa only [D, D', s, s', hy', baseOpenDatumSectionLocalEquations,
    sectionLocalEquationsOfDatumSectionBaseChange] using hgeneric

set_option maxHeartbeats 2000000 in
-- The commutative-product transport is dependent on the localization target and needs extra budget.
/-- The same localization identity with the two factors interchanged. -/
theorem baseOpenRankOneDivisor_mapAlgHom_mul_right
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f g : P.cover.Carrier)
    (y : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, g ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    DivFamZarAff.mapAlgHom
        (DivFamZar.awayMulOfDvd (k := k) (f * g) g f (mul_comm g f))
        (P.baseOpenRankOneDivisor g y hy) =
      P.baseOpenRankOneDivisor (f * g) y
        (P.generator_nonzero_on_mul_right f g y hy) := by
  let hgen : ∀ (t : P.cover.Carrier), g * f = t →
      ∀ p : PrimeSpectrum P.cover.Carrier, t ∉ p.asIdeal →
        (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
          Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
            p.asIdeal.ResidueField) ≠ 0 :=
    fun t ht p htp => hy p (fun hg =>
      htp (ht ▸ p.asIdeal.mul_mem_right f hg))
  let Q : ∀ (t : P.cover.Carrier), g * f = t → Prop := fun t ht =>
    DivFamZarAff.mapAlgHom
        (DivFamZar.awayMulOfDvd (k := k) t g f ht)
        (P.baseOpenRankOneDivisor g y hy) =
      P.baseOpenRankOneDivisor t y (hgen t ht)
  have hleft : Q (g * f) rfl := by
    dsimp [Q, hgen]
    exact P.baseOpenRankOneDivisor_mapAlgHom_mul_left g f y hy
  have hright : Q (f * g) (mul_comm g f) :=
    Eq.rec (motive := fun t ht => Q t ht) hleft (mul_comm g f)
  simpa only [Q, hgen] using hright

/-- The two canonical comparison maps agree on the pairwise product open, after allowing
different fibrewise-nonzero rank-one generators on the two source opens. -/
theorem baseOpenRankOneDivisor_awayMul_compat
    (P : PicRankOneLocalPresentation pi lam)
    [IsNoetherianRing P.cover.Carrier]
    (f g : P.cover.Carrier)
    (y y' : Sheaf.HModule P.datum.sheaf 0)
    (hy : ∀ p : PrimeSpectrum P.cover.Carrier, f ∉ p.asIdeal →
      (y ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0)
    (hy' : ∀ p : PrimeSpectrum P.cover.Carrier, g ∉ p.asIdeal →
      (y' ⊗ₜ (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule P.datum.sheaf 0 ⊗[P.cover.Carrier]
          p.asIdeal.ResidueField) ≠ 0) :
    DivFamZarAff.mapAlgHom
        (DivFamZar.awayMulOfDvd (k := k) (f * g) f g rfl)
        (P.baseOpenRankOneDivisor f y hy) =
      DivFamZarAff.mapAlgHom
        (DivFamZar.awayMulOfDvd (k := k) (f * g) g f (mul_comm g f))
        (P.baseOpenRankOneDivisor g y' hy') := by
  calc
    _ = P.baseOpenRankOneDivisor (f * g) y
        (P.generator_nonzero_on_mul_left f g y hy) :=
      P.baseOpenRankOneDivisor_mapAlgHom_mul_left f g y hy
    _ = P.baseOpenRankOneDivisor (f * g) y'
        (P.generator_nonzero_on_mul_right f g y' hy') :=
      P.baseOpenRankOneDivisor_mul_eq f g y y' hy hy'
    _ = _ :=
      (P.baseOpenRankOneDivisor_mapAlgHom_mul_right f g y' hy').symm

end PicRankOneLocalPresentation

end AlgebraicGeometry
