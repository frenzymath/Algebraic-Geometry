/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorDatumRankOne
import AlgebraicJacobian.Picard.Pic0VanishingFieldTest

/-!
# THE RIGID ENGINE FIRES AT GENUS `0` ON A FIBREWISE-TRIVIAL CLASS, OVER A TEST RING

`Picard/Pic0VanishingFieldTest.lean` closed every **field** instance of the degree-zero
Picard vanishing at genus `0`; `Picard/Pic0VanishingAffineReduction.lean` proved the `∀ T`
binder *is* the `∀` test-ring binder.  What remained was the **ring** case, and the note
released with it priced that as "cohomology and base change, absent from this tree".

**That price was wrong, and this file is the correction.**  The relevant engine is landed and
is stated over an arbitrary test ring for an arbitrary class:

* `Cohomology/GluedSheafExtraction.lean:301` — every Čech Picard class on `C_B` is
  `D.cechPicClass` for some `BasicOpenCocycleDatum C B π`, at **every** `k`-algebra `B`;
* `Cohomology/GluedSheafEngine.lean:198` — `datumRigidEngine`: from a *fibrewise* `H¹`
  hypothesis, `H¹(C_B, F_D) = 0` and `H⁰(C_B, F_D)` is finite projective over `B`;
* `Cohomology/GluedSheafDatumFibre.lean:169` — the fibrewise hypothesis follows from a
  witness divisor on the fibre curve with vanishing `H¹`;
* `Picard/DivisorDatumRankOne.lean:148` — on the vanishing locus, at fibre degree `n` and
  `χ(𝒪_C) = 1 − n`, the stalk rank of `H⁰` is `1`.

What nobody had connected is that at **genus `0`** the fibre inputs of that chain are *free*
rather than expensive, and this file proves exactly that.

## The two results, and why the hypothesis is the cheap one

The fibre witness is the **zero divisor**.  Its class is `1` (`picClass_zero`) and its sheaf is
the structure sheaf (`moduleKSheafDivisorSheafZeroIso`), whose `H¹` has `K`-dimension
`genus C` at every field extension `K/k` (`finrank_h1_baseField_eq_genus`) — so at genus `0` it
vanishes, at every prime of `B` at once, with no locus, no openness argument and no
spreading-out.  Hence:

* `subsingleton_h1_residueField_tensor_of_genus_zero` — the engine's `hfib` clause, for **any**
  datum whose fibre classes are trivial;
* `rankAtStalk_hModule_zero_eq_one_of_genus_zero` — `H⁰` of stalk rank `1` at every prime,
  i.e. `π_*L` invertible in the rank spelling, with `χ = 1` supplied by `genus C = 0` rather
  than assumed.

**The hypothesis is fibre-class triviality, not fibre degree.**  That spelling is deliberate
and is not a strengthening in disguise: at genus `0` the two are *equivalent* by the landed
field-level converse (`eq_one_of_classDeg_eq_zero_of_chi_one`), and
`fibre_cechPicClass_eq_one_of_classDeg_eq_zero` below is that equivalence at this site.  The
reason to state the theorems on triviality is mechanical, and worth recording because it will
bite the next lane: `classDeg K` carries five instance binders on the fibre curve
(`IsIntegral`, `SmoothOfRelativeDimension 1`, `QuasiCompact`, and both `Module.Finite`
Betti-number clauses) which do not synthesize through the `relCurve` `def` barrier, so a
hypothesis phrased `∀ p, classDeg κ(p) … = 0` **cannot be stated** at a general prime without
`haveI`-installing them first — measured, not guessed.  Triviality of the class needs none of
them.

## What this does NOT do

* **It does not discharge the `pic⁰` vanishing at a test ring.**  It supplies the two
  cohomological outputs — `H¹ = 0` and `H⁰` invertible — that the classical proof consumes
  next through the evaluation map `π^*π_*L → L`.

  **CORRECTED after a fresh-context audit (`I-1651`).**  An earlier version of this bullet said
  that map "does not exist in this tree, in the sibling project, or in mathlib (measured this
  session)".  **The mathlib half was false and unmeasured**: the map is the counit of
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`
  (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`), and the sibling project applies
  `.counit.app` to it in two files.  What is genuinely absent is any theorem saying that counit
  is an **isomorphism** at a sheaf of this kind — that is the real residue, and it is a
  narrower and more defensible claim than the one this bullet used to make.  AJCR's own
  carriers are `Sheaf (Opens.grothendieckTopology X) (ModuleCat R)`, not `Scheme.Modules`, so
  reaching the counit here is itself a port.
* **It says nothing at positive genus**, where the fibre `H¹` is genuinely nonzero and the
  witness above fails at the first step.
* It introduces **no hypothesis on the curve** beyond the three standing binders and
  `genus C = 0`, and no hypothesis on the test ring beyond `IsNoetherianRing` — which
  `Cohomology/DatumDescent.lean:547` is designed to remove and which a consumer should remove
  through that route rather than by re-proving anything here.

## Main declarations

* `AlgebraicGeometry.BasicOpenCocycleDatum.subsingleton_h1_residueField_tensor_of_genus_zero`
  — **the engine's fibrewise hypothesis, free at genus `0`**.
* `AlgebraicGeometry.BasicOpenCocycleDatum.rigidEngine_of_genus_zero` — the engine's three
  conclusions with the fibrewise clause discharged.
* `AlgebraicGeometry.BasicOpenCocycleDatum.rankAtStalk_hModule_zero_eq_one_of_genus_zero` —
  **`H⁰` of stalk rank `1`**, at every prime.
* `AlgebraicGeometry.BasicOpenCocycleDatum.fibre_cechPicClass_eq_one_of_classDeg_eq_zero` — the
  degree-`0` spelling of the hypothesis implies the triviality spelling, so nothing is lost by
  stating the results on the latter.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable section

namespace BasicOpenCocycleDatum

/-! ## The fibre inputs at genus `0` -/

/-- **`H¹` of the structure sheaf of the fibre curve vanishes at genus `0`**, at every field
extension of the base.

`finrank_h1_baseField_eq_genus` computes that dimension as `genus C` on the nose, so this is
the hypothesis read as a dimension count; the `Module.Free` instance the `finrank` criterion
wants is the vector-space one. -/
theorem subsingleton_h1_moduleKSheaf_baseChange_of_genus_zero (hg : genus C = 0)
    (K : Type u) [Field K] [Algebra k K] :
    Subsingleton (Sheaf.HModule ((C ⊗ overSpec k K).left.moduleKSheaf K) 1) := by
  have h : Module.finrank K
      (Sheaf.HModule ((C ⊗ overSpec k K).left.moduleKSheaf K) 1) = genus C :=
    finrank_h1_baseField_eq_genus C K
  rw [hg] at h
  exact (Module.finrank_eq_zero_iff_of_free _ _).mp h

/-- **The zero divisor is a vanishing witness at genus `0`**: `H¹(𝒪(0)) = H¹(𝒪) = 0`.

`moduleKSheafDivisorSheafZeroIso` is the identification of the two sheaves; the transport is
`Sheaf.HModule.mapEquiv`. -/
theorem subsingleton_h1_divisorSheaf_zero_of_genus_zero (hg : genus C = 0)
    (K : Type u) [Field K] [Algebra k K] :
    Subsingleton (Sheaf.HModule ((C ⊗ overSpec k K).left.divisorSheaf K
      (0 : (C ⊗ overSpec k K).left.CurveDivisor)) 1) :=
  (Sheaf.HModule.mapEquiv (Scheme.moduleKSheafDivisorSheafZeroIso
    (X := (C ⊗ overSpec k K).left) K) 1).toEquiv.subsingleton_congr.mp
      (subsingleton_h1_moduleKSheaf_baseChange_of_genus_zero hg K)

/-- **THE ENGINE'S FIBREWISE HYPOTHESIS, FREE AT GENUS `0`**: for a datum whose fibre class at
the prime `p` is trivial, the complex-form clause `hfib p` of `datumRigidEngine` holds.

The witness fed to `subsingleton_h1_residueField_tensor_of_witness` is the **zero divisor**:
its class is `1` by `picClass_zero`, which is the fibre class by hypothesis, and its `H¹`
vanishes by the lemma above.  No locus, no openness, no spreading-out, and the argument is
uniform in `p`. -/
theorem subsingleton_h1_residueField_tensor_of_genus_zero
    (D : BasicOpenCocycleDatum C B π) (hg : genus C = 0) (p : PrimeSpectrum B)
    (htriv : (D.baseChange p.asIdeal.ResidueField).cechPicClass = 1) :
    Subsingleton ((datumPair D).H1 ⊗[B] p.asIdeal.ResidueField) := by
  refine D.subsingleton_h1_residueField_tensor_of_witness p ⟨0, ?_, ?_⟩
  · rw [Scheme.CurveDivisor.picClass_zero, htriv]
    rfl
  · exact subsingleton_h1_divisorSheaf_zero_of_genus_zero hg p.asIdeal.ResidueField

/-! ## The engine, and the rank-`1` export -/

/-- **The rigid engine at genus `0` on a fibrewise-trivial class**: `H¹(C_B, F_D) = 0` and
`H⁰(C_B, F_D)` finite projective over `B`, with the fibrewise clause discharged by the
genus hypothesis rather than assumed. -/
theorem rigidEngine_of_genus_zero (D : BasicOpenCocycleDatum C B π) [IsNoetherianRing B]
    (hπ : π ≫ P1.structureMap k = C.hom) (hg : genus C = 0)
    (htriv : ∀ p : PrimeSpectrum B,
      (D.baseChange p.asIdeal.ResidueField).cechPicClass = 1) :
    Subsingleton (Sheaf.HModule D.sheaf 1) ∧
      Module.Finite B (Sheaf.HModule D.sheaf 0) ∧
      Module.Projective B (Sheaf.HModule D.sheaf 0) :=
  datumRigidEngine D hπ fun p =>
    D.subsingleton_h1_residueField_tensor_of_genus_zero hg p (htriv p)

/-- **`H⁰` HAS STALK RANK `1` AT EVERY PRIME** — `π_*L` invertible, in the rank spelling, for a
fibrewise-trivial class on a genus-`0` curve over an arbitrary Noetherian test ring.

`rankAtStalk_hModule_zero_eq_one` is applied at `n := 0`: its χ-normalization
`χ(𝒪_C) = 1 − n` is `χ = 1`, which `chi_moduleKSheaf` plus `genus C = 0` supplies, and its
fibre-degree clause is `classDeg κ(p) 1 = 0`, which is `classDeg_one`.  The five fibre
instances are installed by hand — they do not synthesize through the `relCurve` `def`
barrier. -/
theorem rankAtStalk_hModule_zero_eq_one_of_genus_zero
    (D : BasicOpenCocycleDatum C B π) [IsNoetherianRing B]
    (hπ : π ≫ P1.structureMap k = C.hom) (hg : genus C = 0)
    (htriv : ∀ p : PrimeSpectrum B,
      (D.baseChange p.asIdeal.ResidueField).cechPicClass = 1)
    (p : PrimeSpectrum B) :
    Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p = 1 := by
  haveI : IsIntegral (relCurve C p.asIdeal.ResidueField) :=
    instIsIntegralBaseChange C p.asIdeal.ResidueField
  haveI : SmoothOfRelativeDimension 1
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instSmoothOfRelativeDimensionBaseChange C p.asIdeal.ResidueField
  haveI : QuasiCompact
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instQuasiCompactBaseChange C p.asIdeal.ResidueField
  haveI : Module.Finite p.asIdeal.ResidueField (Sheaf.HModule
      ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 0) :=
    instModuleFiniteHModuleZeroBaseChange C p.asIdeal.ResidueField
  haveI : Module.Finite p.asIdeal.ResidueField (Sheaf.HModule
      ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 1) :=
    instModuleFiniteHModuleOneBaseChange C p.asIdeal.ResidueField
  refine D.rankAtStalk_hModule_zero_eq_one (n := 0) hπ ?_
    (fun q => D.subsingleton_h1_residueField_tensor_of_genus_zero hg q (htriv q)) p ?_
  · rw [chi_moduleKSheaf C, hg]
  · rw [htriv p, Nat.cast_zero]
    exact classDeg_one _

/-! ## The degree spelling is the same hypothesis at genus `0` -/

/-- **The degree-`0` spelling implies the triviality spelling**, at genus `0`: a fibre class of
degree `0` *is* trivial, by the landed field-level converse
`eq_one_of_classDeg_eq_zero_of_chi_one` at `χ = 1`.

So the theorems above lose no generality by taking triviality as the hypothesis; what they
gain is that the hypothesis is statable without the five fibre instances `classDeg` needs.
Consumers holding a degree hypothesis at a prime pass through here. -/
theorem fibre_cechPicClass_eq_one_of_classDeg_eq_zero
    (D : BasicOpenCocycleDatum C B π) (hg : genus C = 0) (p : PrimeSpectrum B)
    [IsIntegral (relCurve C p.asIdeal.ResidueField)]
    [SmoothOfRelativeDimension 1
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField))]
    [QuasiCompact
      (relCurve C p.asIdeal.ResidueField ↘ Spec (CommRingCat.of p.asIdeal.ResidueField))]
    [Module.Finite p.asIdeal.ResidueField (Sheaf.HModule
      ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 0)]
    [Module.Finite p.asIdeal.ResidueField (Sheaf.HModule
      ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 1)]
    (hdeg : classDeg p.asIdeal.ResidueField
      (D.baseChange p.asIdeal.ResidueField).cechPicClass = 0) :
    (D.baseChange p.asIdeal.ResidueField).cechPicClass = 1 :=
  eq_one_of_classDeg_eq_zero_of_chi_one p.asIdeal.ResidueField
    (chi_moduleKSheaf_baseChange_eq_one_of_genus_zero C p.asIdeal.ResidueField hg) _ hdeg

end BasicOpenCocycleDatum

end

end AlgebraicGeometry
