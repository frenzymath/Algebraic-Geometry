/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyH1Locus
import AlgebraicJacobian.Picard.LocalGenerators
import AlgebraicJacobian.Cohomology.H1BaseFieldInvariance
import AlgebraicJacobian.RiemannRoch.ChiCurve

/-!
# DAT-C C2 — the rank-1 H⁰ export and the generator kit
(`informal/w4-datc-worksheet.md` GAP-3 Σ-RANK1, §2 (N1)/(N3))

On the fibrewise h¹-vanishing locus, at fibre degree `n` with the base χ-normalization
`χ(𝒪_C) = 1 − n`, the datum engine's `H⁰` is an **invertible** module: finite,
projective, and of stalk-rank exactly `1`.  This is the rank export the engine
(`datumRigidEngine`, `Cohomology/GluedSheafEngine.lean`) leaves open — it delivers
finite + projective, never `rankAtStalk = 1`.

* `AlgebraicGeometry.chi_relCurve` — the χ transport `χ(𝒪_{C_L}) = 1 − n` to every
  field `L` of the test tower (base-field invariance of the genus, `chi_moduleKSheaf`
  + `genus_baseField`; a re-derivation of the private lemma of `DivSchemeMonoBridgeRel`).
* `AlgebraicGeometry.BasicOpenCocycleDatum.h0_sheaf_baseChange_eq_one` — **the fibre
  computation**: for a datum whose fibre class over `L` has `classDeg = n`, with `H¹` of
  the base-changed sheaf vanishing, `h⁰(C_L, F_{D_L}) = 1` — the Riemann–Roch anchor
  `h0_gluedSheaf_eq_classDeg_add_chi` (`n + (1 − n)`) read through the presentation
  bridge `presentationSheafIso`.  The fibre geometric package is threaded as instance
  arguments (`Curve.BaseChangeInstances`).
* `AlgebraicGeometry.BasicOpenCocycleDatum.rankAtStalk_hModule_zero_eq_one` — **Σ-RANK1,
  the datum-level export**: on the vanishing locus (fibre degree `n`, `χ = 1 − n`),
  `Module.rankAtStalk (H⁰(F_D)) p = 1`.  Route: `Module.rankAtStalk_eq` reads the rank as
  the `κ(p)`-fibre dimension; `datumH0BaseChange` (on the nose) identifies the fibre with
  `H⁰(C_{κ(p)}, F_{D_{κ(p)}})`; the fibre computation above pins it at `1`.
* `AlgebraicGeometry.CertifiedDivisorFamily.rankAtStalk_divisorDatum_eq_one` — the
  certified-family specialization (**N1**): for `G` landing in the h¹-vanishing locus
  `V`, the divisor datum `D_G := G.adaptation.divisorDatum` has invertible `H⁰`.  The
  fibre-degree hypothesis is discharged uniformly by `DivFamZar.classDeg_picClass` (the
  fibre class has `classDeg = n` at every field).
* `AlgebraicGeometry.CertifiedDivisorFamily.exists_fibrewise_generator_divisorDatum`
  — **N3, the generator kit**: since `H⁰(F_{D_G})` is projective of rank `1` (hence has a
  nontrivial fibre at every prime of the locus), a fibrewise-nonzero **global** section
  exists Zariski-locally (`Module.exists_fibrewise_tmul_ne_zero_of_projective`).

Noetherian discipline (worksheet §2): every rank statement carries `[IsNoetherianRing S]`
through the engine; the arbitrary-test consumers reach it through RE-5 stages.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {S : Type u} [CommRing S] [Algebra k S]
variable {π : C.left ⟶ P1 k} [IsFinite π] {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- The standing `C.left`-over-`k` structure, keyed on `C.hom` — the instance the base
χ-normalization `hχ : χ(𝒪_C) = 1 − n` is phrased against (defeq to `.ofHom C.hom`, so
`chi_moduleKSheaf C` unifies with it). -/
noncomputable local instance instOverCleftRankOne : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

/-! ## The χ transport to the fibre curve -/

/-- **`χ(𝒪) = 1 − n` at every field extension**, from the base normalization
(`chi_moduleKSheaf` at the base-changed bundle + `genus_baseField`; a re-derivation of the
`DivSchemeMonoBridgeRel` private lemma). -/
theorem chi_relCurve (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (n : ℤ))
    (L : Type u) [Field L] [Algebra k L] :
    Sheaf.chi ((relCurve C L).moduleKSheaf L) = 1 - (n : ℤ) := by
  haveI : IsProper (baseChangeBundle C L).hom := instIsProperSndLeft C L
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C L).hom :=
    instSmoothOfRelativeDimensionSndLeft C L
  haveI : GeometricallyIrreducible (baseChangeBundle C L).hom :=
    instGeometricallyIrreducibleSndLeft C L
  have h1 : Sheaf.chi ((relCurve C L).moduleKSheaf L)
      = 1 - (genus (baseChangeBundle C L) : ℤ) := chi_moduleKSheaf (baseChangeBundle C L)
  have h2 : genus (baseChangeBundle C L) = genus C := genus_baseField C L
  have h3 : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (genus C : ℤ) := chi_moduleKSheaf C
  have h4 : (genus C : ℤ) = (n : ℤ) := by rw [h3] at hχ; linarith
  rw [h1, h2, h4]

/-! ## The fibre computation: `h⁰(C_L, F_{D_L}) = 1`

The fibre geometric instances (`Curve.BaseChangeInstances`) are threaded as instance
arguments — they cannot be synthesized through the `relCurve` `def` barrier, so consumers
install them by `haveI` (the `degAt_abelDiv` block, I-0249 (iv)) before calling. -/

/-- **The fibre h⁰ pin**: for a datum whose fibre class over the field `L` has
`classDeg = n`, with the base χ-normalization and vanishing `H¹` of the base-changed
sheaf, the fibre global-section count is exactly `1` — the Riemann–Roch rank anchor
`h0_gluedSheaf_eq_classDeg_add_chi` read through the presentation bridge
`presentationSheafIso`, at `n + (1 − n)`. -/
theorem BasicOpenCocycleDatum.h0_sheaf_baseChange_eq_one
    (D : BasicOpenCocycleDatum C S π)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (n : ℤ))
    (L : Type u) [Field L] [Algebra k L] [Algebra S L] [IsScalarTower k S L]
    [IsIntegral (relCurve C L)]
    [SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L))]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0)]
    [Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1)]
    (hg : classDeg L (D.baseChange L).cechPicClass = (n : ℤ))
    (hsub : Subsingleton (Sheaf.HModule (D.baseChange L).sheaf 1)) :
    Sheaf.h0 (D.baseChange L).sheaf = 1 := by
  set P : (relCurve C L).MeromorphicPresentation :=
    Scheme.MeromorphicPresentation.ofCocycle (D.baseChange L).pointedCover
      (gluedSubordCocycle (D.baseChange L).isGluingCocycle
        (D.baseChange L).pointedCover (D.baseChange L).pieceIndex
        fun _ => le_rfl) with hP
  have hsubP : Subsingleton (Sheaf.HModule (P.gluedSheaf L) 1) :=
    (Sheaf.HModule.mapEquiv (presentationSheafIso (D.baseChange L)) 1).toEquiv.subsingleton_congr.mp
      hsub
  have h0eq : Sheaf.h0 (D.baseChange L).sheaf = Sheaf.h0 (P.gluedSheaf L) :=
    Sheaf.h0_congr (presentationSheafIso (D.baseChange L))
  have hformula := h0_gluedSheaf_eq_classDeg_add_chi L P hsubP
  have hPclass : P.picClass = (D.baseChange L).cechPicClass := rfl
  have hint : (Sheaf.h0 (D.baseChange L).sheaf : ℤ) = 1 := by
    rw [h0eq, hformula, hPclass, hg, chi_relCurve hχ L]; ring
  exact_mod_cast hint

/-! ## Σ-RANK1: the rank-1 export on the vanishing locus -/

/-- **Σ-RANK1, the datum-level rank export** (worksheet GAP-3): on the fibrewise
h¹-vanishing locus, at fibre degree `n` with the base χ-normalization `χ(𝒪_C) = 1 − n`,
the datum engine's `H⁰` has stalk-rank exactly `1` at `p`.

`Module.rankAtStalk_eq` reads the rank as the `κ(p)`-dimension of the fibre
`κ(p) ⊗[S] H⁰`; the on-the-nose base change `datumH0BaseChange` identifies this fibre with
`H⁰(C_{κ(p)}, F_{D_{κ(p)}})`, whose dimension is `1` by the fibre computation. The global
fibrewise hypothesis `hfib` supplies finiteness/projectivity (hence flatness) through
`datumRigidEngine`. -/
theorem BasicOpenCocycleDatum.rankAtStalk_hModule_zero_eq_one
    (D : BasicOpenCocycleDatum C S π) [IsNoetherianRing S]
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (n : ℤ))
    (hfib : ∀ q : PrimeSpectrum S,
      Subsingleton ((datumPair D).H1 ⊗[S] q.asIdeal.ResidueField))
    (p : PrimeSpectrum S)
    [IsIntegral (relCurve C p.asIdeal.ResidueField)]
    [SmoothOfRelativeDimension 1
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField))]
    [QuasiCompact
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField))]
    [Module.Finite p.asIdeal.ResidueField
      (Sheaf.HModule ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 0)]
    [Module.Finite p.asIdeal.ResidueField
      (Sheaf.HModule ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 1)]
    (hg : classDeg p.asIdeal.ResidueField
      (D.baseChange p.asIdeal.ResidueField).cechPicClass = (n : ℤ)) :
    Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p = 1 := by
  obtain ⟨-, hfin, hproj⟩ := datumRigidEngine D hπ hfib
  haveI := hfin
  haveI := hproj
  have hH1 : Subsingleton (datumPair D).H1 := datum_subsingleton_pairH1 D hπ hfib
  have hfibre : Sheaf.h0 (D.baseChange p.asIdeal.ResidueField).sheaf = 1 :=
    D.h0_sheaf_baseChange_eq_one hχ p.asIdeal.ResidueField hg
      (D.datum_subsingleton_h1_baseChange p.asIdeal.ResidueField hH1)
  calc Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p
      = Module.finrank p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[S] (Sheaf.HModule D.sheaf 0)) :=
        Module.rankAtStalk_eq p
    _ = Module.finrank p.asIdeal.ResidueField
          (Sheaf.HModule (D.baseChange p.asIdeal.ResidueField).sheaf 0) :=
        (D.datumH0BaseChange p.asIdeal.ResidueField hH1).finrank_eq
    _ = Sheaf.h0 (D.baseChange p.asIdeal.ResidueField).sheaf := rfl
    _ = 1 := hfibre

/-! ## The certified-family specialization: N1 (invertible `H⁰`) and N3 (generators) -/

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- (Implementation) The fibre class of the divisor datum has `classDeg = n` at `κ(p)`:
the base change of `G.eqns`, read through `DivFamZar.classDeg_picClass`. -/
private theorem CertifiedDivisorFamily.classDeg_baseChange_divisorDatum
    (G : CertifiedDivisorFamily C S π n) (p : PrimeSpectrum S)
    [IsIntegral (relCurve C p.asIdeal.ResidueField)]
    [SmoothOfRelativeDimension 1
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField))]
    [QuasiCompact
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField))]
    [Module.Finite p.asIdeal.ResidueField
      (Sheaf.HModule ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 0)]
    [Module.Finite p.asIdeal.ResidueField
      (Sheaf.HModule ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 1)] :
    classDeg p.asIdeal.ResidueField
      (G.adaptation.divisorDatum.baseChange p.asIdeal.ResidueField).cechPicClass = (n : ℤ) := by
  have hcl : G.adaptation.divisorDatum.cechPicClass = (DivFam.mk G).toZar.picClass := by
    rw [G.adaptation.cechPicClass_divisorDatum, DivFamZar.picClass_toZar, DivFam.picClass_mk]
  rw [G.adaptation.divisorDatum.cechPicClass_baseChange p.asIdeal.ResidueField, hcl,
    ← DivFamZar.picClass_mapAlg]
  exact DivFamZar.classDeg_picClass
    (DivFamZar.mapAlg p.asIdeal.ResidueField n (DivFam.mk G).toZar)

/-- **N1 — invertibility of the canonical `H⁰`** (worksheet §2 (N1)): for a certified
divisor family `G` landing in the h¹-vanishing locus `V` (`hvan`), the divisor datum
`D_G := G.adaptation.divisorDatum` has `H⁰` of stalk-rank exactly `1` at every prime.

The fibre-degree hypothesis of `rankAtStalk_hModule_zero_eq_one` is discharged uniformly:
the fibre class of `D_G` at `κ(p)` is the base change of `G.eqns`, which has
`classDeg = n` at every field (`DivFamZar.classDeg_picClass`). -/
theorem CertifiedDivisorFamily.rankAtStalk_divisorDatum_eq_one
    (G : CertifiedDivisorFamily C S π n) [IsNoetherianRing S]
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (n : ℤ))
    (hvan : ∀ p : PrimeSpectrum S, (DivFam.mk G).toZar.IsH1VanishingAt p)
    (p : PrimeSpectrum S) :
    Module.rankAtStalk (Sheaf.HModule G.adaptation.divisorDatum.sheaf 0) p = 1 := by
  have hfib : ∀ q : PrimeSpectrum S,
      Subsingleton ((datumPair G.adaptation.divisorDatum).H1 ⊗[S] q.asIdeal.ResidueField) :=
    fun q => (G.isH1VanishingAt_toZar_iff q).mp (hvan q)
  haveI : IsIntegral (relCurve C p.asIdeal.ResidueField) :=
    instIsIntegralBaseChange C p.asIdeal.ResidueField
  haveI : SmoothOfRelativeDimension 1
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instSmoothOfRelativeDimensionBaseChange C p.asIdeal.ResidueField
  haveI : QuasiCompact
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instQuasiCompactBaseChange C p.asIdeal.ResidueField
  haveI : Module.Finite p.asIdeal.ResidueField
      (Sheaf.HModule ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 0) :=
    instModuleFiniteHModuleZeroBaseChange C p.asIdeal.ResidueField
  haveI : Module.Finite p.asIdeal.ResidueField
      (Sheaf.HModule ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 1) :=
    instModuleFiniteHModuleOneBaseChange C p.asIdeal.ResidueField
  exact G.adaptation.divisorDatum.rankAtStalk_hModule_zero_eq_one hπ hχ hfib p
    (G.classDeg_baseChange_divisorDatum p)

/-- **N3 — the generator kit** (worksheet §2 (N3)): since `H⁰(F_{D_G})` is projective of
stalk-rank `1` on the locus, its `κ(p)`-fibre is nontrivial, so a fibrewise-nonzero
**global** section exists on a basic open `D(f) ∋ p` — the Zariski-local generator
(`Module.exists_fibrewise_tmul_ne_zero_of_projective`, the Nakayama-neighbourhood kit of
`Picard/LocalGenerators.lean`). -/
theorem CertifiedDivisorFamily.exists_fibrewise_generator_divisorDatum
    (G : CertifiedDivisorFamily C S π n) [IsNoetherianRing S]
    (hπ : π ≫ P1.structureMap k = C.hom)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (n : ℤ))
    (hvan : ∀ p : PrimeSpectrum S, (DivFam.mk G).toZar.IsH1VanishingAt p)
    (p : PrimeSpectrum S) :
    ∃ f : S, f ∉ p.asIdeal ∧ ∃ q : Sheaf.HModule G.adaptation.divisorDatum.sheaf 0,
      ∀ q' : PrimeSpectrum S, f ∉ q'.asIdeal →
        (q ⊗ₜ (1 : q'.asIdeal.ResidueField) :
            Sheaf.HModule G.adaptation.divisorDatum.sheaf 0 ⊗[S] q'.asIdeal.ResidueField) ≠ 0 := by
  have hfib : ∀ q : PrimeSpectrum S,
      Subsingleton ((datumPair G.adaptation.divisorDatum).H1 ⊗[S] q.asIdeal.ResidueField) :=
    fun q => (G.isH1VanishingAt_toZar_iff q).mp (hvan q)
  obtain ⟨-, hfin, hproj⟩ := datumRigidEngine G.adaptation.divisorDatum hπ hfib
  haveI := hfin
  haveI := hproj
  have hrank : Module.rankAtStalk (Sheaf.HModule G.adaptation.divisorDatum.sheaf 0) p = 1 :=
    G.rankAtStalk_divisorDatum_eq_one hπ hχ hvan p
  -- rank 1 ⟹ the `κ(p)`-fibre is nontrivial
  have hfr : Module.finrank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[S] Sheaf.HModule G.adaptation.divisorDatum.sheaf 0) = 1 := by
    rw [← Module.rankAtStalk_eq]; exact hrank
  haveI : Nontrivial (p.asIdeal.ResidueField ⊗[S]
      Sheaf.HModule G.adaptation.divisorDatum.sheaf 0) :=
    Module.nontrivial_of_finrank_pos (by rw [hfr]; norm_num)
  have hnt : Nontrivial (Sheaf.HModule G.adaptation.divisorDatum.sheaf 0 ⊗[S]
      p.asIdeal.ResidueField) :=
    (TensorProduct.comm S _ _).toEquiv.symm.nontrivial
  exact Module.exists_fibrewise_tmul_ne_zero_of_projective p hnt

end AlgebraicGeometry
