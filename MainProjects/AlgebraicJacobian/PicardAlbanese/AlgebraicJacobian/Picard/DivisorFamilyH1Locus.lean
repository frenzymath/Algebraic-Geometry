/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorDatumInverse
import AlgebraicJacobian.Picard.DivSchemeAbel
import AlgebraicJacobian.Picard.DivRepClassifyZarKit
import AlgebraicJacobian.Cohomology.GluedSheafDatumFibre
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# DAT-C C1 — the fibrewise h¹-vanishing locus of a locally certified divisor class
(`informal/w4-datc-worksheet.md` §1.2–§1.3, GAP-6 Σ-H1LOC)

The ONE fibre dictionary of the h¹-vanishing locus, and its openness on affine tests
through the single sanctioned mechanism `datumRigidEngine_isOpen_vanishing`:

* `AlgebraicGeometry.DivFamZar.IsH1VanishingAt` — the membership predicate in the
  **fibre-witness form** (the `hwit` slot of
  `subsingleton_h1_residueField_tensor_of_witness`, class-intrinsic): a witness
  divisor of the fibre class at `κ(p)` with vanishing `H¹`.
* `AlgebraicGeometry.picClass_divFamDivisor` — the missing class law of the field
  dictionary's forward map: `𝒪(divFamDivisor G) = G.picClass`.
* `DivFamZar.exists_effective_witness` — **(V1a) witness production**: at every field
  `L` of the test, the fibre class has an effective witness of degree `n`
  (`divFamDivisor` of a globally certified representative, via `DivFam.exists_toZar_eq`).
* `DivFamZar.IsH1VanishingAt.subsingleton_of_picClass_eq` /
  `DivFamZar.isH1VanishingAt_iff_of_picClass_eq` — **(V1a) class-only dependence**:
  any witness serves (`subsingleton_hModule_one_of_picClass_eq`).
* `BasicOpenCocycleDatum.subsingleton_h1_tensor_iff_exists_witness` — **the two-way
  datum dictionary** (the heart of GAP-6): for a pinned cocycle datum over `S` and ANY
  field `L` in a `k`/`S`-tower, `H¹(pair) ⊗[S] L` vanishes iff the mapped class has a
  vanishing-`H¹` witness over `L`.  Forward: the δ-naturality square
  (`datumDiffBaseChange`) carries surjectivity of the base-changed Čech differential to
  the fibre datum, then the presentation bridge (`presentationSheafIso`) and the core
  isomorphism (`subsingleton_hModule_gluedSheaf_one_iff`) read `H¹` on the witness
  `presentationDivisor`.  Backward: `subsingleton_sheaf_h1_of_picClass_eq` +
  `subsingleton_h1_tensor_of_baseChange_sheaf` (the landed seam, at generic `L`).
* `CertifiedDivisorFamily.isH1VanishingAt_toZar_iff` — **(V1b) the worksheet
  dictionary**: for a certified `G` with divisor datum
  `D_G := G.adaptation.divisorDatum` (I-0249 spelling),
  `IsH1VanishingAt (toZar G) p ↔ Subsingleton (H¹(pair D_G) ⊗[S] κ(p))`.
* `DivFamZar.isH1VanishingAt_comap_away_iff` — **(V1c) locality**: on an away piece
  `Localization.Away f` carrying a certified representative of the class, the
  predicate at `comap q` reads as the engine's fibre condition at `q` — the
  residue-field seam `κ(comap q) ≃ κ(q)` is crossed by mathlib's
  `Ideal.ResidueField.map` (bijective for localizations, `SurjectiveOnStalks`).
* `DivFamZar.isOpen_setOf_isH1VanishingAt` — **§1.3 openness, affine tests**: the
  locus is the union over a certificate cover (`exists_certified_away_rep`, I-0243) of
  the open images of the engine opens `datumRigidEngine_isOpen_vanishing`
  (Noetherian-free; no Fitting ideals, no semicontinuity — dat-d §3.5 discipline).

Change of certified representative is free: (V1b) pins the datum side by the
class-intrinsic predicate, so two representatives of one Zar class have equivalent
fibre conditions.

**SCOPE, corrected 2026-07-29 (`review-ajcr`, inbox `I-0917`).**  An earlier version of this
paragraph said "the vehicle-level extension to arbitrary tests is C6's `mem_V_iff`".  **No
declaration of that name exists**, here or anywhere in the workspace or mathlib (checked by
`horizon search` and by grep at HEAD), so the sentence named the extension without providing
it.  What is actually landed is what the statements below say: the openness theorem
`DivFamZar.isOpen_setOf_isH1VanishingAt` is for an **affine** test `Spec S`, and the
locality dictionary `isH1VanishingAt_comap_away_iff` crosses only an *away* piece of such a
test.  The extension of the locus to a general (non-affine) test object is **open work**, owed
by whoever needs the locus on a scheme rather than on `Spec S`.

It is, however, *cheaper than it looks*, because the sibling predicate has already made this
exact crossing and its side condition is discharged.  `chartLocus`
(`Picard/Pic0ChartLocus.lean:244`) is the `IsSplitWitness` locus, whose witness clause is the
same `Subsingleton (Sheaf.HModule (divisorSheaf … W) 1)` as `IsH1VanishingAt`'s, and for it
the general-test assembly is landed **unconditionally**:
`isOpen_chartLocus_of_affineLocal` (`Picard/Pic0ChartLocusGeneralTest.lean:191`) reduces
openness on `T` to openness on each affine open, `chartLocus_fromSpecAffine_eq_preimage`
(`:168`) supplies the preimage identity across the carrier map, and the `hinv`
(`IsSplitWitnessIsoInvariant`) hypothesis both of them carry is **proved**, not assumed —
`isSplitWitnessIsoInvariant_holds` (`Picard/Pic0ChartLocusIsoInvariance.lean:263`), sorry-free.
So a general-test statement for `IsH1VanishingAt` is a transport along that template plus the
dictionary that identifies the two witness clauses, not a fresh piece of geometry.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`;
see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {S : Type u} [CommRing S] [Algebra k S]
variable {π : C.left ⟶ P1 k} [IsFinite π] {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-! ## The membership predicate (worksheet §1.2, the fibre-witness form) -/

/-- **The fibrewise h¹-vanishing predicate** (worksheet §1.2, GAP-6): a locally
certified divisor class `F₀` over the affine test `S` is *h¹-vanishing at* the prime
`p` if the fibre class of `𝒪(F₀)` at `κ(p)` admits a witness divisor with vanishing
`H¹` — exactly the `hwit` slot of `subsingleton_h1_residueField_tensor_of_witness`,
class-intrinsic by (V1a). -/
def DivFamZar.IsH1VanishingAt (F₀ : DivFamZar C S π n) (p : PrimeSpectrum S) : Prop :=
  ∃ W : ((C ⊗ overSpec k p.asIdeal.ResidueField).left).CurveDivisor,
    Scheme.CurveDivisor.picClass p.asIdeal.ResidueField W
        = Scheme.CechPic.map (relCurveMap C S p.asIdeal.ResidueField) F₀.picClass
      ∧ Subsingleton (Sheaf.HModule
          ((C ⊗ overSpec k p.asIdeal.ResidueField).left.divisorSheaf
            p.asIdeal.ResidueField W) 1)

/-! ## (V1a) Witness production and class-only dependence -/

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] in
/-- **The class law of the field dictionary's forward map**: the Čech Picard class of
the Weil divisor of a divisor family over a field is the class of the family. -/
theorem picClass_divFamDivisor {L : Type u} [Field L] [Algebra k L]
    [IsIntegral (relCurve C L)]
    [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
    (G : DivFam C L π n) :
    Scheme.CurveDivisor.picClass L (divFamDivisor G) = G.picClass := by
  induction G using Quotient.inductionOn with
  | h F =>
    rw [show (⟦F⟧ : DivFam C L π n) = DivFam.mk F from rfl, divFamDivisor_mk,
      Scheme.CurveDivisor.picClass_presentationDivisor,
      Scheme.LocalEquations.presentation_picClass, DivFam.picClass_mk]

/-- **(V1a) witness production**: at every field `L` of the test tower, the fibre
class of a locally certified degree-`n` class has an **effective** witness divisor of
degree `n` — `divFamDivisor` of a globally certified representative of the restricted
class (`DivFam.exists_toZar_eq`). -/
theorem DivFamZar.exists_effective_witness (F₀ : DivFamZar C S π n) (L : Type u)
    [Field L] [Algebra k L] [Algebra S L] [IsScalarTower k S L] :
    ∃ W : ((C ⊗ overSpec k L).left).CurveDivisor,
      0 ≤ W
        ∧ Scheme.CurveDivisor.picClass L W
            = Scheme.CechPic.map (relCurveMap C S L) F₀.picClass
        ∧ Scheme.CurveDivisor.deg L W = (n : ℤ) := by
  haveI : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L
  haveI : SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instSmoothOfRelativeDimensionBaseChange C L
  haveI : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instQuasiCompactBaseChange C L
  obtain ⟨G, hG⟩ := DivFam.exists_toZar_eq (DivFamZar.mapAlg L n F₀)
  refine ⟨divFamDivisor G, zero_le_divFamDivisor G, ?_, deg_divFamDivisor G⟩
  rw [picClass_divFamDivisor G, ← DivFamZar.picClass_toZar, hG,
    DivFamZar.picClass_mapAlg]

/-- **(V1a) class-only dependence — any witness serves**: if `F₀` is h¹-vanishing at
`p`, then `H¹(𝒪(W))` vanishes for EVERY witness divisor `W` of the fibre class
(`subsingleton_hModule_one_of_picClass_eq`). -/
theorem DivFamZar.IsH1VanishingAt.subsingleton_of_picClass_eq
    {F₀ : DivFamZar C S π n} {p : PrimeSpectrum S} (hvan : F₀.IsH1VanishingAt p)
    {W : ((C ⊗ overSpec k p.asIdeal.ResidueField).left).CurveDivisor}
    (hW : Scheme.CurveDivisor.picClass p.asIdeal.ResidueField W
      = Scheme.CechPic.map (relCurveMap C S p.asIdeal.ResidueField) F₀.picClass) :
    Subsingleton (Sheaf.HModule
      ((C ⊗ overSpec k p.asIdeal.ResidueField).left.divisorSheaf
        p.asIdeal.ResidueField W) 1) := by
  obtain ⟨W₀, hW₀, hsub⟩ := hvan
  exact subsingleton_hModule_one_of_picClass_eq p.asIdeal.ResidueField
    (hW₀.trans hW.symm) hsub

/-- **(V1a), iff form**: against any fixed witness of the fibre class, membership is
exactly the vanishing of `H¹(𝒪(W))`. -/
theorem DivFamZar.isH1VanishingAt_iff_of_picClass_eq
    {F₀ : DivFamZar C S π n} {p : PrimeSpectrum S}
    {W : ((C ⊗ overSpec k p.asIdeal.ResidueField).left).CurveDivisor}
    (hW : Scheme.CurveDivisor.picClass p.asIdeal.ResidueField W
      = Scheme.CechPic.map (relCurveMap C S p.asIdeal.ResidueField) F₀.picClass) :
    F₀.IsH1VanishingAt p ↔ Subsingleton (Sheaf.HModule
      ((C ⊗ overSpec k p.asIdeal.ResidueField).left.divisorSheaf
        p.asIdeal.ResidueField W) 1) :=
  ⟨fun hvan => hvan.subsingleton_of_picClass_eq hW, fun hsub => ⟨W, hW, hsub⟩⟩

/-! ## The two-way datum dictionary (the heart of GAP-6) -/

/-- **The two-way fibre dictionary of the datum engine** (worksheet (V1b), stated at an
arbitrary field of the test tower): for a pinned cocycle datum `D` over `S` and a field
`L` in a `k`/`S`-tower, the engine's complex-form fibre condition
`Subsingleton (H¹(pair D) ⊗[S] L)` holds iff the mapped class of the datum has a
vanishing-`H¹` witness divisor over `L`.

Forward: right-exactness (`subsingleton_h1_rTensor_iff`) makes the base-changed Čech
differential surjective; the δ-naturality square (`datumDiffBaseChange`) carries
surjectivity to the fibre datum's differential; `subsingleton_datumPair_h1_iff`, the
presentation bridge (`presentationSheafIso`) and the core isomorphism
(`subsingleton_hModule_gluedSheaf_one_iff`) then read the vanishing on the witness
`presentationDivisor` of the canonical subordinated presentation.  Backward: the landed
seam `subsingleton_sheaf_h1_of_picClass_eq` + `subsingleton_h1_tensor_of_baseChange_sheaf`. -/
theorem BasicOpenCocycleDatum.subsingleton_h1_tensor_iff_exists_witness
    (D : BasicOpenCocycleDatum C S π) (L : Type u) [Field L] [Algebra k L]
    [Algebra S L] [IsScalarTower k S L] :
    Subsingleton ((datumPair D).H1 ⊗[S] L) ↔
      ∃ W : ((C ⊗ overSpec k L).left).CurveDivisor,
        Scheme.CurveDivisor.picClass L W
            = Scheme.CechPic.map (relCurveMap C S L) D.cechPicClass
          ∧ Subsingleton (Sheaf.HModule
              ((C ⊗ overSpec k L).left.divisorSheaf L W) 1) := by
  haveI : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L
  haveI : SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instSmoothOfRelativeDimensionBaseChange C L
  haveI : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instQuasiCompactBaseChange C L
  constructor
  · intro h
    -- surjectivity of the base-changed differential, through right-exactness
    have hcok := ((datumPair D).subsingleton_h1_rTensor_iff L).mp h
    have hbc : Function.Surjective ((datumPair D).diff.baseChange L) := by
      rw [← LinearMap.range_eq_top]
      exact Submodule.Quotient.subsingleton_iff.mp hcok
    -- across the δ-naturality square to the fibre datum's differential
    have hsurj' : Function.Surjective (datumPair (D.baseChange L)).diff :=
      RigidEngine.surjective_congr _ _ (D.datumDomBaseChange L)
        (D.termBaseChangeInf L) (fun x => D.datumDiffBaseChange L x) hbc
    haveI hH1L : Subsingleton (datumPair (D.baseChange L)).H1 := by
      have himg : (datumPair (D.baseChange L)).imageLattice = ⊤ := by
        rw [← (datumPair (D.baseChange L)).range_diff_eq, LinearMap.range_eq_top]
        exact hsurj'
      rw [TwoLatticePair.H1, himg]
      infer_instance
    have hsheaf : Subsingleton (Sheaf.HModule (D.baseChange L).sheaf 1) :=
      (subsingleton_datumPair_h1_iff (D.baseChange L)).mp hH1L
    -- the presentation bridge and the core isomorphism, on the canonical witness
    set P : (relCurve C L).MeromorphicPresentation :=
      Scheme.MeromorphicPresentation.ofCocycle (D.baseChange L).pointedCover
        (gluedSubordCocycle (D.baseChange L).isGluingCocycle
          (D.baseChange L).pointedCover (D.baseChange L).pieceIndex
          fun _ => le_rfl) with hP
    have hglued : Subsingleton (Sheaf.HModule (P.gluedSheaf L) 1) :=
      (Sheaf.HModule.mapEquiv (presentationSheafIso (D.baseChange L))
        1).toEquiv.subsingleton_congr.mp hsheaf
    have hdiv := (subsingleton_hModule_gluedSheaf_one_iff L P).mp hglued
    refine ⟨Scheme.presentationDivisor L P, ?_, hdiv⟩
    calc Scheme.CurveDivisor.picClass L (Scheme.presentationDivisor L P)
        = P.picClass := Scheme.CurveDivisor.picClass_presentationDivisor L P
      _ = (D.baseChange L).cechPicClass := rfl
      _ = Scheme.CechPic.map (relCurveMap C S L) D.cechPicClass :=
          D.cechPicClass_baseChange L
  · rintro ⟨W, hW, hvan⟩
    have hW' : Scheme.CurveDivisor.picClass L W = (D.baseChange L).cechPicClass := by
      rw [hW, D.cechPicClass_baseChange L]
    exact D.subsingleton_h1_tensor_of_baseChange_sheaf L
      (subsingleton_sheaf_h1_of_picClass_eq (D.baseChange L) hW' hvan)

/-! ## (V1b) The worksheet dictionary on a certified representative -/

/-- **(V1b) the datum bridge** (worksheet §1.2, at `D_G := G.adaptation.divisorDatum`
per I-0249): for a certified divisor family `G` over the affine test `S`, membership of
`toZar G` at `p` is exactly the engine's complex-form fibre condition of the divisor
datum, `Subsingleton (H¹(pair D_G) ⊗[S] κ(p))` — the `hfib p` slot of
`datumRigidEngine`. -/
theorem CertifiedDivisorFamily.isH1VanishingAt_toZar_iff
    (G : CertifiedDivisorFamily C S π n) (p : PrimeSpectrum S) :
    (DivFam.mk G).toZar.IsH1VanishingAt p ↔
      Subsingleton ((datumPair G.adaptation.divisorDatum).H1 ⊗[S]
        p.asIdeal.ResidueField) := by
  have hcl : G.adaptation.divisorDatum.cechPicClass = (DivFam.mk G).toZar.picClass := by
    rw [G.adaptation.cechPicClass_divisorDatum, DivFamZar.picClass_toZar,
      DivFam.picClass_mk]
  have h := (G.adaptation.divisorDatum.subsingleton_h1_tensor_iff_exists_witness
    p.asIdeal.ResidueField).symm
  rw [hcl] at h
  exact h

/-! ## (V1c) Locality: the residue-field seam and the away-piece bridge -/

/-- (Implementation) The fibre condition of a module is invariant under a structure-
compatible bijection of coefficient algebras. -/
private theorem subsingleton_tensor_congr_of_bijective
    {R M K₁ K₂ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing K₁] [CommRing K₂] [Algebra R K₁] [Algebra R K₂]
    (ψ : K₁ →+* K₂) (hψ : ψ.comp (algebraMap R K₁) = algebraMap R K₂)
    (hbij : Function.Bijective ψ) :
    Subsingleton (M ⊗[R] K₁) ↔ Subsingleton (M ⊗[R] K₂) := by
  have hsmul : ∀ (r : R) (x : K₁), ψ (r • x) = (RingHom.id R r) • ψ x := fun r x => by
    rw [RingHom.id_apply, Algebra.smul_def, map_mul, Algebra.smul_def,
      ← RingHom.congr_fun hψ r, RingHom.comp_apply]
  exact (TensorProduct.congr (LinearEquiv.refl R M)
    (LinearEquiv.ofBijective ⟨⟨ψ, map_add ψ⟩, hsmul⟩ hbij)).toEquiv.subsingleton_congr

/-- (Implementation) **The residue-field seam of a localization**: for a localization
`R'` of `S₀` at a submonoid, a prime `q` of `R'` over `comap q`, and an `R'`-algebra
structure on `κ(comap q)` in the `S₀`-tower, the fibre conditions of an `R'`-module at
`κ(comap q)` and at `κ(q)` agree — mathlib's residue-field comparison
`Ideal.ResidueField.map` is bijective (localizations are surjective on stalks) and
`R'`-linear (`IsLocalization.ringHom_ext`). -/
private theorem subsingleton_tensor_residueField_comap_iff
    {S₀ R' : Type u} [CommRing S₀] [CommRing R'] [Algebra S₀ R'] (M₀ : Submonoid S₀)
    [IsLocalization M₀ R'] (M : Type u) [AddCommGroup M] [Module R' M]
    (q : PrimeSpectrum R')
    [Algebra R' (PrimeSpectrum.comap (algebraMap S₀ R') q).asIdeal.ResidueField]
    [IsScalarTower S₀ R'
      (PrimeSpectrum.comap (algebraMap S₀ R') q).asIdeal.ResidueField] :
    Subsingleton (M ⊗[R']
        (PrimeSpectrum.comap (algebraMap S₀ R') q).asIdeal.ResidueField) ↔
      Subsingleton (M ⊗[R'] q.asIdeal.ResidueField) := by
  have hcom : (PrimeSpectrum.comap (algebraMap S₀ R') q).asIdeal
      = q.asIdeal.comap (algebraMap S₀ R') := rfl
  refine subsingleton_tensor_congr_of_bijective
    (Ideal.ResidueField.map _ q.asIdeal (algebraMap S₀ R') hcom) ?_ ?_
  · refine IsLocalization.ringHom_ext M₀ (RingHom.ext fun s => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply S₀ R', Ideal.ResidueField.map_algebraMap]
  · exact (RingHom.surjectiveOnStalks_of_isLocalization (M := M₀)
      R').residueFieldMap_bijective _ q.asIdeal hcom

/-- **(V1c) the away-piece bridge** (worksheet §1.2 locality, the openness engine's
consumption shape): if the away piece `Localization.Away f` carries a certified
representative `G` of the restricted class, then membership of `F₀` at the trace
`comap q` of a prime `q` of the piece is exactly the engine's fibre condition of the
piece's divisor datum at `q`.  In particular the predicate is invariant under
`mapAlg` along `S → Localization.Away f` at lying-over primes. -/
theorem DivFamZar.isH1VanishingAt_comap_away_iff (F₀ : DivFamZar C S π n) (f : S)
    (G : CertifiedDivisorFamily C (Localization.Away f) π n)
    (hGZ : (DivFam.mk G).toZar = DivFamZar.mapAlg (Localization.Away f) n F₀)
    (q : PrimeSpectrum (Localization.Away f)) :
    F₀.IsH1VanishingAt (PrimeSpectrum.comap (algebraMap S (Localization.Away f)) q)
      ↔ Subsingleton ((datumPair G.adaptation.divisorDatum).H1
          ⊗[Localization.Away f] q.asIdeal.ResidueField) := by
  -- `f` is invertible at the trace prime, so `κ(comap q)` receives the localization
  have hfp : f ∉ (PrimeSpectrum.comap (algebraMap S (Localization.Away f))
      q).asIdeal := by
    intro hf
    refine q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem q.asIdeal
      (Ideal.mem_comap.mp hf) ?_)
    exact IsLocalization.Away.algebraMap_isUnit f
  have hunit : IsUnit (algebraMap S
      (PrimeSpectrum.comap (algebraMap S (Localization.Away f))
        q).asIdeal.ResidueField f) :=
    isUnit_iff_ne_zero.mpr fun h0 => hfp (Ideal.algebraMap_residueField_eq_zero.mp h0)
  letI : Algebra (Localization.Away f)
      (PrimeSpectrum.comap (algebraMap S (Localization.Away f))
        q).asIdeal.ResidueField :=
    (IsLocalization.Away.lift (S := Localization.Away f) f hunit).toAlgebra
  haveI : IsScalarTower S (Localization.Away f)
      (PrimeSpectrum.comap (algebraMap S (Localization.Away f))
        q).asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp])
  haveI : IsScalarTower k (Localization.Away f)
      (PrimeSpectrum.comap (algebraMap S (Localization.Away f))
        q).asIdeal.ResidueField :=
    isScalarTower_left_of_isScalarTower (R₀ := S)
  -- the class of the piece datum, pulled to `κ(comap q)`, is the mapped class of `F₀`
  have hZcl : G.eqns.picClass
      = Scheme.CechPic.map (relCurveMap C S (Localization.Away f)) F₀.picClass := by
    have h := congrArg DivFamZar.picClass hGZ
    rw [DivFamZar.picClass_toZar, DivFam.picClass_mk, DivFamZar.picClass_mapAlg] at h
    exact h
  have hdict := (G.adaptation.divisorDatum.subsingleton_h1_tensor_iff_exists_witness
    (PrimeSpectrum.comap (algebraMap S (Localization.Away f))
      q).asIdeal.ResidueField).symm
  rw [G.adaptation.cechPicClass_divisorDatum, hZcl, ← MonoidHom.comp_apply,
    ← Scheme.CechPic.map_comp,
    relCurveMap_comp (R' := Localization.Away f)
      (R'' := (PrimeSpectrum.comap (algebraMap S (Localization.Away f))
        q).asIdeal.ResidueField)]
    at hdict
  exact hdict.trans
    (subsingleton_tensor_residueField_comap_iff (Submonoid.powers f) _ q)

/-! ## §1.3 Openness on affine tests (the ONE audited mechanism) -/

/-- **Openness of the h¹-vanishing locus on an affine test** (worksheet §1.3): the
locus `{p | IsH1VanishingAt F₀ p}` is open in `Spec S`.  Per certificate piece of
`DivFamZar.exists_certified_away_rep` the trace of the locus is the engine open
`datumRigidEngine_isOpen_vanishing` of the piece's divisor datum ((V1b) + (V1c)),
carried across the away open immersion; the pieces glue since they compute one
predicate.  This is the single sanctioned openness mechanism of the campaign
(dat-d §3.5): no Fitting ideals, no semicontinuity, Noetherian-free. -/
theorem DivFamZar.isOpen_setOf_isH1VanishingAt
    (hπ : π ≫ P1.structureMap k = C.hom) (F₀ : DivFamZar C S π n) :
    IsOpen {p : PrimeSpectrum S | F₀.IsH1VanishingAt p} := by
  obtain ⟨m, h, hspan, hG⟩ := DivFamZar.exists_certified_away_rep F₀
  choose G hGZ using hG
  have hkey : {p : PrimeSpectrum S | F₀.IsH1VanishingAt p}
      = ⋃ l : Fin m,
          (PrimeSpectrum.comap (algebraMap S (Localization.Away (h l)))) ''
            {q : PrimeSpectrum (Localization.Away (h l)) |
              Subsingleton ((datumPair (G l).adaptation.divisorDatum).H1
                ⊗[Localization.Away (h l)] q.asIdeal.ResidueField)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hp
      -- some certificate piece sees `p` (span-⊤ prime avoidance)
      have hex : ∃ l, h l ∉ p.asIdeal := by
        by_contra hall
        have hmem : ∀ l, h l ∈ p.asIdeal := fun l => of_not_not fun hl => hall ⟨l, hl⟩
        have hle : Ideal.span (Set.range h) ≤ p.asIdeal :=
          Ideal.span_le.mpr (by rintro x ⟨l, rfl⟩; exact hmem l)
        rw [hspan] at hle
        exact p.isPrime.ne_top (top_le_iff.mp hle)
      obtain ⟨l, hl⟩ := hex
      have hrange : p ∈ Set.range
          (PrimeSpectrum.comap (algebraMap S (Localization.Away (h l)))) := by
        rw [PrimeSpectrum.localization_away_comap_range
          (S := Localization.Away (h l)) (h l)]
        exact hl
      obtain ⟨q, hq⟩ := hrange
      exact ⟨l, q,
        (F₀.isH1VanishingAt_comap_away_iff (h l) (G l) (hGZ l) q).mp (hq ▸ hp), hq⟩
    · rintro ⟨l, q, hsub, rfl⟩
      exact (F₀.isH1VanishingAt_comap_away_iff (h l) (G l) (hGZ l) q).mpr hsub
  rw [hkey]
  refine isOpen_iUnion fun l => ?_
  refine (PrimeSpectrum.localization_away_isOpenEmbedding
    (Localization.Away (h l)) (h l)).isOpenMap _ ?_
  exact datumRigidEngine_isOpen_vanishing (G l).adaptation.divisorDatum hπ

end AlgebraicGeometry
