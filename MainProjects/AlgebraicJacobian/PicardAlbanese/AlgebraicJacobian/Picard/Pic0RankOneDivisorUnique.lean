/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneSectionFibreNonzero
import AlgebraicJacobian.Picard.DivisorDatumSectionOfClass
import AlgebraicJacobian.Picard.DivisorFamilyMonoH1
import AlgebraicJacobian.Cohomology.GluedSheafFibre

/-!
# T5 core — uniqueness of the divisor family in a rank-one datum class

The localization-free heart of the `RankOneDivisorUniqueness` discharge: over an arbitrary
test algebra `B` carrying a pinned cocycle datum whose `H⁰` is finite, projective, and of
stalk rank one, **at most one** widened locally certified divisor family of degree
`genus C` has Picard class the datum's Čech class
(`divFamZarAff_eq_of_picClass_eq_cechPicClass`).

The proof is the assembly of the three landed engines, with no localization anywhere:

* T3 (`exists_gluedSection_sectionLocalEquations_divEq`) cuts each family, up to `DivEq`,
  from a germ-regular global section of the datum's glued sheaf;
* T4 (`tmul_residueField_ne_zero_of_divEq_certified`) makes the two `H⁰` classes
  fibrewise-nonzero at every prime of the base;
* the rank-one unit-extraction engine
  (`Module.existsUnique_unit_smul_of_forall_tmul_ne_zero`) then exhibits the second `H⁰`
  class as a global unit multiple of the first, and the unit-rescaling law
  (`sectionLocalEquations_smul_divEq`) transports the cut divisors into each other.

The `DivEq` chain `d₁ ∼ cut(s₁) ∼ cut(v·s₁) = cut(s₂) ∼ d₂` closes equality in the
`DivFamZarAff` quotient (`mk_eq_mk_iff`).

This is the exact reason injectivity is restored on the rank-one locus — single-point
linear systems — as demanded by the uniqueness-discharge memory (I-1981, trap 2): the
rank-one hypotheses enter irreplaceably through the unit-extraction engine, and nothing
here restates the uniqueness goal as a hypothesis.  The remaining (localizing) work of the
discharge — matching each family's class to a presentation datum near every prime — is the
per-prime base-discrepancy assembly, not this file.
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
variable {B : Type u} [CommRing B] [Algebra k B]
variable {pi : C.left ⟶ P1 k}

namespace BasicOpenCocycleDatum

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] in
/-- Equal glued sections cut equal local-equation systems (the germ-regularity witnesses
are proof-irrelevant). -/
private lemma sectionLocalEquations_congr [IsAffineHom pi]
    (D : BasicOpenCocycleDatum C B pi)
    {s s' : ↥(gluedSubmodule B D.pieces D.unit ⊤)} (hss' : s = s')
    (𝒲 : (relCurve C B).PointedCover) (σ : relCurve C B → D.index)
    (hσ : ∀ x : relCurve C B, 𝒲.opens x ≤ D.pieces (σ x))
    (hreg : ∀ (j : D.index) (x : relCurve C B) (hx : x ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) x hx).hom (D.component s j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk x))
    (hreg' : ∀ (j : D.index) (x : relCurve C B) (hx : x ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) x hx).hom (D.component s' j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk x)) :
    D.sectionLocalEquations s 𝒲 σ hσ hreg = D.sectionLocalEquations s' 𝒲 σ hσ hreg' := by
  cases hss'
  rfl

/-- **Uniqueness of the divisor family in a rank-one datum class** (the T5 core, with no
localization): over an arbitrary test algebra whose pinned cocycle datum has `H⁰` finite,
projective, and of stalk rank one at every prime, two widened locally certified divisor
families of degree `genus C` with Picard class the datum's Čech class are equal.

The two families are cut from `H⁰` classes of the datum (T3); both classes are
fibrewise-nonzero at every prime (T4), so the rank-one engine makes the second a global
unit multiple of the first, and unit rescaling does not move the cut divisor. -/
theorem divFamZarAff_eq_of_picClass_eq_cechPicClass [IsFinite pi]
    (D : BasicOpenCocycleDatum C B pi)
    (hH1 : Subsingleton (Sheaf.HModule D.sheaf 1))
    (hfin : Module.Finite B (Sheaf.HModule D.sheaf 0))
    (hproj : Module.Projective B (Sheaf.HModule D.sheaf 0))
    (hrank : ∀ p : PrimeSpectrum B,
      Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p = 1)
    (F₁ F₂ : DivFamZarAff C B (genus C))
    (h₁ : F₁.picClass = D.cechPicClass)
    (h₂ : F₂.picClass = D.cechPicClass) :
    F₁ = F₂ := by
  classical
  haveI := hfin
  haveI := hproj
  induction F₁ using Quotient.ind with | _ x₁ => ?_
  induction F₂ using Quotient.ind with | _ x₂ => ?_
  obtain ⟨d₁, hd₁⟩ := x₁
  obtain ⟨d₂, hd₂⟩ := x₂
  have h₁' : d₁.picClass = D.cechPicClass := h₁
  have h₂' : d₂.picClass = D.cechPicClass := h₂
  -- T3: cut both families from glued sections
  obtain ⟨s₁, hreg₁, hdiv₁⟩ := D.exists_gluedSection_sectionLocalEquations_divEq d₁ h₁'
  obtain ⟨s₂, hreg₂, hdiv₂⟩ := D.exists_gluedSection_sectionLocalEquations_divEq d₂ h₂'
  -- realize the sections as `H⁰` classes
  obtain ⟨y₁, rfl⟩ : ∃ y, Sheaf.HModule.linearEquiv₀
      (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
      isTerminalTop D.sheaf y = s₁ :=
    ⟨(Sheaf.HModule.linearEquiv₀ _ isTerminalTop D.sheaf).symm s₁,
      (Sheaf.HModule.linearEquiv₀ _ isTerminalTop D.sheaf).apply_symm_apply s₁⟩
  obtain ⟨y₂, rfl⟩ : ∃ y, Sheaf.HModule.linearEquiv₀
      (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
      isTerminalTop D.sheaf y = s₂ :=
    ⟨(Sheaf.HModule.linearEquiv₀ _ isTerminalTop D.sheaf).symm s₂,
      (Sheaf.HModule.linearEquiv₀ _ isTerminalTop D.sheaf).apply_symm_apply s₂⟩
  set e₀ := Sheaf.HModule.linearEquiv₀
    (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
    isTerminalTop D.sheaf with he₀
  -- T4: both `H⁰` classes are fibrewise-nonzero at every prime
  have hH1' : Subsingleton (datumPair D).H1 :=
    (subsingleton_datumPair_h1_iff D).mpr hH1
  have hq₁ : ∀ p : PrimeSpectrum B,
      (y₁ ⊗ₜ[B] (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule D.sheaf 0 ⊗[B] p.asIdeal.ResidueField) ≠ 0 :=
    fun p => D.tmul_residueField_ne_zero_of_divEq_certified hH1' y₁
      D.pointedCover D.pieceIndex (fun _ => le_rfl) hreg₁ hd₁
      (hdiv₁ D.pointedCover D.pieceIndex fun _ => le_rfl) p
  have hq₂ : ∀ p : PrimeSpectrum B,
      (y₂ ⊗ₜ[B] (1 : p.asIdeal.ResidueField) :
        Sheaf.HModule D.sheaf 0 ⊗[B] p.asIdeal.ResidueField) ≠ 0 :=
    fun p => D.tmul_residueField_ne_zero_of_divEq_certified hH1' y₂
      D.pointedCover D.pieceIndex (fun _ => le_rfl) hreg₂ hd₂
      (hdiv₂ D.pointedCover D.pieceIndex fun _ => le_rfl) p
  -- the rank-one engine: the second class is a global unit multiple of the first
  obtain ⟨v, hv, -⟩ := Module.existsUnique_unit_smul_of_forall_tmul_ne_zero
    (B := B) (Q := Sheaf.HModule D.sheaf 0) hrank y₁ y₂ hq₁ hq₂
  -- transport the unit through the sections and chain the divisor equalities
  have hs₂ : e₀ y₂ = (v : B) • e₀ y₁ := by rw [hv, map_smul]
  have hreg_smul : ∀ (j : D.index) (x : relCurve C B) (hx : x ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) x hx).hom
        (D.component ((v : B) • e₀ y₁) j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk x) :=
    D.germ_component_smul_mem_nonZeroDivisors v (e₀ y₁) hreg₁
  have hcongr : D.sectionLocalEquations (e₀ y₂) D.pointedCover D.pieceIndex
        (fun _ => le_rfl) hreg₂
      = D.sectionLocalEquations ((v : B) • e₀ y₁) D.pointedCover D.pieceIndex
        (fun _ => le_rfl) hreg_smul :=
    D.sectionLocalEquations_congr hs₂ D.pointedCover D.pieceIndex (fun _ => le_rfl)
      hreg₂ hreg_smul
  have hchain₁ : Scheme.LocalEquations.DivEq d₁
      (D.sectionLocalEquations (e₀ y₁) D.pointedCover D.pieceIndex
        (fun _ => le_rfl) hreg₁) :=
    (hdiv₁ D.pointedCover D.pieceIndex fun _ => le_rfl).symm
  have hchain₂ : Scheme.LocalEquations.DivEq
      (D.sectionLocalEquations (e₀ y₁) D.pointedCover D.pieceIndex
        (fun _ => le_rfl) hreg₁)
      (D.sectionLocalEquations ((v : B) • e₀ y₁) D.pointedCover D.pieceIndex
        (fun _ => le_rfl) hreg_smul) :=
    (D.sectionLocalEquations_smul_divEq v (e₀ y₁) D.pointedCover D.pieceIndex
      (fun _ => le_rfl) hreg₁ hreg_smul).symm
  have hchain₃ : Scheme.LocalEquations.DivEq
      (D.sectionLocalEquations ((v : B) • e₀ y₁) D.pointedCover D.pieceIndex
        (fun _ => le_rfl) hreg_smul) d₂ :=
    hcongr ▸ hdiv₂ D.pointedCover D.pieceIndex fun _ => le_rfl
  exact DivFamZarAff.mk_eq_mk_iff.mpr (hchain₁.trans (hchain₂.trans hchain₃))

end BasicOpenCocycleDatum

end AlgebraicGeometry
