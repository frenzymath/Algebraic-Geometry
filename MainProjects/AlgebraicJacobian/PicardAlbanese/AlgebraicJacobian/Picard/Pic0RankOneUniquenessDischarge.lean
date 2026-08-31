/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorDescent
import AlgebraicJacobian.Picard.Pic0RankOneDivisorUnique
import AlgebraicJacobian.Picard.RelPicBaseLocalTriviality
import AlgebraicJacobian.Picard.DivRepAwaySpanGlueAff
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveSite
import AlgebraicJacobian.Picard.DivSchemeCertZarPointwise
import AlgebraicJacobian.Cohomology.RankOneFamilyCertificates

/-!
# Discharge of the rank-one divisor uniqueness interface

`rankOneDivisorUniqueness` proves `RankOneDivisorUniqueness pi` outright: over every affine
test whose plus class lies in the rank-one locus, at most one widened locally certified
divisor class of degree `genus C` has Abel value the input class.  No auxiliary hypotheses
remain — the interface consumed by the canonical-divisor descent is closed.

The proof composes the landed engines and is local-to-global twice, both times genuinely:

* membership in `PicRankOneOpen` tested at the identity yields a presentation `P` of the
  input class over the test algebra itself, with an étale carrier `B := P.cover.Carrier`
  carrying the cocycle datum and its four rank-one certificates;
* both families restrict along the faithfully flat `S → B`, where their Abel values become
  the `PicEtAff.unit` of `P.representative` (`mapAlg_mk_eq_unit_self`), so étale
  separatedness (`PicEtAff.unit_injective`) matches both `relPic` classes with the datum's
  Čech class;
* near every prime of `B` the base-discrepancy localization
  (`exists_notMem_cechPicMap_eq_of_relPicMk_eq`) upgrades the two `relPic` equalities to
  on-the-nose `CechPic` equalities on a basic open — the two localizations are merged by
  multiplying the two good elements;
* on each such basic open the datum base-changes with its certificates
  (`RankOneFamilyCertificates.scalarExtension`), and the datum-class uniqueness core
  (`divFamZarAff_eq_of_picClass_eq_cechPicClass`) forces the two restricted families to
  agree;
* the good elements span the unit ideal (`exists_fin_span_eq_top_of_forall_prime`), so the
  away-span separatedness (`DivFamZarAff.eq_of_awaySpan_eq`) closes equality over `B`, and
  faithfully-flat injectivity (`DivFamZarAff.mapAlgHom_injective_of_faithfullyFlat`) closes
  it over the test algebra.

The rank-one hypothesis enters irreplaceably through the certificates feeding the
uniqueness core's unit-extraction engine; the glue-backs cover `Spec B` and descend a
faithfully flat cover of `Spec S`, so neither is the trivial converse (the two traps of the
uniqueness-discharge memory).  As immediate consumers, the canonical rank-one divisor and
its accessors are re-exported with the interface hypothesis discharged
(`canonicalRankOneDivisor`, `existsUnique_abel_divFamZarAff_of_presentation`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] in
/-- Equality of Čech Picard classes after base change to an away localization persists to
the away localization at any multiple: for `a * b = f` the comparison
`Localization.Away a →ₐ[k] Localization.Away f` interposes, and the relative-curve
comparisons compose over the tower `B → B_a → B_f`. -/
private lemma cechPicMap_away_eq_of_mul {B : Type u} [CommRing B] [Algebra k B]
    (a b f : B) (hab : a * b = f) {L L' : (relCurve C B).CechPic}
    (h : Scheme.CechPic.map (relCurveMap C B (Localization.Away a)) L
        = Scheme.CechPic.map (relCurveMap C B (Localization.Away a)) L') :
    Scheme.CechPic.map (relCurveMap C B (Localization.Away f)) L
      = Scheme.CechPic.map (relCurveMap C B (Localization.Away f)) L' := by
  letI : Algebra (Localization.Away a) (Localization.Away f) :=
    (DivFamZar.awayMulOfDvd (k := k) f a b hab).toRingHom.toAlgebra
  haveI : IsScalarTower k (Localization.Away a) (Localization.Away f) :=
    .of_algebraMap_eq fun x =>
      ((DivFamZar.awayMulOfDvd (k := k) f a b hab).commutes x).symm
  haveI : IsScalarTower B (Localization.Away a) (Localization.Away f) :=
    .of_algebraMap_eq fun x =>
      (DivFamZar.awayMulOfDvd_algebraMap (k := k) f a b hab x).symm
  have hcomp : Scheme.CechPic.map (relCurveMap C B (Localization.Away f))
      = (Scheme.CechPic.map
          (relCurveMap C (Localization.Away a) (Localization.Away f))).comp
        (Scheme.CechPic.map (relCurveMap C B (Localization.Away a))) := by
    rw [← Scheme.CechPic.map_comp, relCurveMap_comp]
  rw [hcomp]
  simp only [MonoidHom.comp_apply]
  exact congrArg _ h

/-- **Per-prime local agreement with the datum**: two widened divisor families over the
presentation carrier whose `picClass`es agree with the datum's Čech class in the relative
Picard group agree on the nose after restriction to a basic open around any given prime.

The base-discrepancy localization produces one good element per family; their product is
good for both, the datum base-changes with its four rank-one certificates, and the
datum-class uniqueness core forces the two restricted families to coincide. -/
theorem PicRankOneLocalPresentation.exists_notMem_mapAlgHom_eq
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (P : PicRankOneLocalPresentation pi lam)
    {F G : DivFamZarAff C P.cover.Carrier (genus C)}
    (hF : relPicMk C (overSpec k P.cover.Carrier) F.picClass
        = relPicMk C (overSpec k P.cover.Carrier) P.datum.cechPicClass)
    (hG : relPicMk C (overSpec k P.cover.Carrier) G.picClass
        = relPicMk C (overSpec k P.cover.Carrier) P.datum.cechPicClass)
    (q : PrimeSpectrum P.cover.Carrier) :
    ∃ f : P.cover.Carrier, f ∉ q.asIdeal ∧
      DivFamZarAff.mapAlgHom
          (IsScalarTower.toAlgHom k P.cover.Carrier (Localization.Away f)) F
        = DivFamZarAff.mapAlgHom
          (IsScalarTower.toAlgHom k P.cover.Carrier (Localization.Away f)) G := by
  classical
  obtain ⟨f₁, hf₁, h₁⟩ := exists_notMem_cechPicMap_eq_of_relPicMk_eq hF q
  obtain ⟨f₂, hf₂, h₂⟩ := exists_notMem_cechPicMap_eq_of_relPicMk_eq hG q
  have hmul : f₁ * f₂ ∉ q.asIdeal := fun hmem => by
    rcases q.isPrime.mem_or_mem hmem with h | h
    exacts [hf₁ h, hf₂ h]
  refine ⟨f₁ * f₂, hmul, ?_⟩
  set B' := Localization.Away (f₁ * f₂)
  -- both restricted families have `picClass` the base-changed datum class on the nose
  have h₁' := cechPicMap_away_eq_of_mul (C := C) f₁ f₂ (f₁ * f₂) rfl h₁
  have h₂' := cechPicMap_away_eq_of_mul (C := C) f₂ f₁ (f₁ * f₂) (mul_comm f₂ f₁) h₂
  have hFpic : (DivFamZarAff.mapAlgHom
      (IsScalarTower.toAlgHom k P.cover.Carrier B') F).picClass
      = (P.datum.baseChange B').cechPicClass := by
    rw [DivFamZarAff.mapAlgHom_eq_mapAlg _ (fun _ => rfl), DivFamZarAff.picClass_mapAlg,
      P.datum.cechPicClass_baseChange B']
    exact h₁'
  have hGpic : (DivFamZarAff.mapAlgHom
      (IsScalarTower.toAlgHom k P.cover.Carrier B') G).picClass
      = (P.datum.baseChange B').cechPicClass := by
    rw [DivFamZarAff.mapAlgHom_eq_mapAlg _ (fun _ => rfl), DivFamZarAff.picClass_mapAlg,
      P.datum.cechPicClass_baseChange B']
    exact h₂'
  -- the presentation's four certificates base-change to the basic open
  have cert : RankOneFamilyCertificates (P.datum.baseChange B') :=
    (RankOneFamilyCertificates.mk P.h1_vanishing P.h0_finite P.h0_projective
      P.h0_rank_one).scalarExtension B'
  exact BasicOpenCocycleDatum.divFamZarAff_eq_of_picClass_eq_cechPicClass
    (P.datum.baseChange B') cert.h1_vanishing cert.h0_finite cert.h0_projective
    cert.h0_rank_one _ _ hFpic hGpic

/-- **The rank-one divisor uniqueness interface holds** (the T5 discharge): over every
affine test whose plus class lies in the rank-one locus, at most one widened locally
certified divisor class of degree `genus C` has Abel value the input class.

Injectivity is restored on the rank-one locus precisely because the presentation's `H⁰` is
finite projective of stalk rank one — single-point linear systems — which feeds the
unit-extraction engine of the datum-class uniqueness core; away from the locus the widened
Abel map is genuinely non-injective (`Pic0ChartAbelNonInjective`). -/
theorem rankOneDivisorUniqueness : RankOneDivisorUniqueness pi := by
  intro S _ _ lam hlam F G hF hG
  classical
  -- a presentation of the input class, from the identity test; its plus class is `lam.1`
  obtain ⟨P⟩ := (mem_picRankOneOpen_iff pi lam).mp hlam S (𝟙 (overSpec k S))
  have e : ((picDegLayerFunctor C (genus C : ℤ)).map
      (𝟙 (overSpec k S)).op lam).1 = lam.1 :=
    picEtMap_id C lam.1
  -- inject along the faithfully flat étale carrier
  apply DivFamZarAff.mapAlgHom_injective_of_faithfullyFlat
    (S := S) (S' := P.cover.Carrier)
  set φ0 : S →ₐ[k] P.cover.Carrier := IsScalarTower.toAlgHom k S P.cover.Carrier with hφ0
  -- the restricted Abel values are the unit of the representative, so both restricted
  -- `picClass`es agree with the datum's Čech class in the relative Picard group
  have hofId : ((Algebra.ofId S P.cover.Carrier).restrictScalars k) = φ0 :=
    AlgHom.ext fun _ => rfl
  have hrep : PicEtAff.mk C P.cover P.representative = picEtAffineEquiv C S lam.1 := by
    rw [← e]
    exact P.represents
  have htarget : PicEtAff.mapAlg C φ0 (picEtAffineEquiv C S lam.1)
      = PicEtAff.unit C P.cover.Carrier
          (P.representative : relPic C (overSpec k P.cover.Carrier)) := by
    rw [← hrep, ← hofId, PicEtAff.mapAlg_mk_eq_unit_self]
  have key : ∀ H : DivFamZarAff C S (genus C),
      abelDivAffPlus C S H = picEtAffineEquiv C S lam.1 →
      relPicMk C (overSpec k P.cover.Carrier)
          (DivFamZarAff.mapAlgHom φ0 H).picClass
        = relPicMk C (overSpec k P.cover.Carrier) P.datum.cechPicClass := by
    intro H hH
    rw [← P.datum_class]
    apply PicEtAff.unit_injective C P.cover.Carrier
    calc PicEtAff.unit C P.cover.Carrier (relPicMk C (overSpec k P.cover.Carrier)
          (DivFamZarAff.mapAlgHom φ0 H).picClass)
        = abelDivAffPlus C P.cover.Carrier (DivFamZarAff.mapAlgHom φ0 H) := rfl
      _ = PicEtAff.mapAlg C φ0 (abelDivAffPlus C S H) :=
          (abelDivAffPlus_mapAlgHom φ0 H).symm
      _ = PicEtAff.mapAlg C φ0 (picEtAffineEquiv C S lam.1) := by rw [hH]
      _ = PicEtAff.unit C P.cover.Carrier
            (P.representative : relPic C (overSpec k P.cover.Carrier)) := htarget
  -- per-prime agreement, upgraded to a finite spanning family, separates over the carrier
  obtain ⟨m, g, hgspan, hggood⟩ := exists_fin_span_eq_top_of_forall_prime
    (fun f => DivFamZarAff.mapAlgHom
        (IsScalarTower.toAlgHom k P.cover.Carrier (Localization.Away f))
        (DivFamZarAff.mapAlgHom φ0 F)
      = DivFamZarAff.mapAlgHom
        (IsScalarTower.toAlgHom k P.cover.Carrier (Localization.Away f))
        (DivFamZarAff.mapAlgHom φ0 G))
    (fun q => P.exists_notMem_mapAlgHom_eq pi (key F hF) (key G hG) q)
  exact DivFamZarAff.eq_of_awaySpan_eq g hgspan hggood

/-! ## Immediate consumers: the canonical rank-one divisor, unconditionally -/

variable {A : Type u} [CommRing A] [Algebra k A]
  {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

/-- The unique Abel-correct divisor of a rank-one local presentation, with the uniqueness
interface discharged. -/
theorem existsUnique_abel_divFamZarAff_of_presentation
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A)))
    (P : PicRankOneLocalPresentation pi lam) [IsNoetherianRing P.cover.Carrier] :
    ∃! F : DivFamZarAff C A (genus C),
      abelDivAffPlus C A F = picEtAffineEquiv C A lam.1 :=
  existsUnique_abel_divFamZarAff_of_localPresentation pi
    (rankOneDivisorUniqueness pi) hlam P

/-- **The canonical rank-one divisor**, with the uniqueness interface discharged. -/
noncomputable def canonicalRankOneDivisor
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A)))
    (P : PicRankOneLocalPresentation pi lam) [IsNoetherianRing P.cover.Carrier] :
    DivFamZarAff C A (genus C) :=
  canonicalRankOneDivisorOfPresentation pi (rankOneDivisorUniqueness pi) hlam P

/-- The canonical rank-one divisor satisfies the Abel equation. -/
theorem canonicalRankOneDivisor_abel
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A)))
    (P : PicRankOneLocalPresentation pi lam) [IsNoetherianRing P.cover.Carrier] :
    abelDivAffPlus C A (canonicalRankOneDivisor pi hlam P)
      = picEtAffineEquiv C A lam.1 :=
  canonicalRankOneDivisorOfPresentation_abel pi (rankOneDivisorUniqueness pi) hlam P

/-- Any Abel-correct widened divisor class equals the canonical rank-one divisor. -/
theorem canonicalRankOneDivisor_unique
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A)))
    (P : PicRankOneLocalPresentation pi lam) [IsNoetherianRing P.cover.Carrier]
    (F : DivFamZarAff C A (genus C))
    (hF : abelDivAffPlus C A F = picEtAffineEquiv C A lam.1) :
    F = canonicalRankOneDivisor pi hlam P :=
  canonicalRankOneDivisorOfPresentation_unique pi (rankOneDivisorUniqueness pi) hlam P F hF

end AlgebraicGeometry
