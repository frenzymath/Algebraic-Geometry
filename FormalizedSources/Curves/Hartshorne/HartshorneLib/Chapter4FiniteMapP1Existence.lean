/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1CurveStalks
import HartshorneLib.Chapter4P1Points
import HartshorneLib.Chapter4P1Topology
import HartshorneLib.Chapter4MapToP1

/-!
# Spreading an explicit transcendental function to a finite map to `P1`

This module isolates the genuine input to the finite-map construction.  A
function-field element together with an explicit polynomial-evaluation
nonvanishing certificate is supplied; the two chart morphisms are then glued
using the valuation-ring description of the stalks of a smooth integral
curve.  No existence of a function or map is asserted by a typeclass.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

set_option backward.isDefEq.respectTransparency false in
theorem Opens.fromSpecStalkOfMem_stalkSpecializes {X : Scheme} {U : X.Opens} {x y : X}
    (h : y ⤳ x) (hx : x ∈ U) (hy : y ∈ U) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem x hx =
      U.fromSpecStalkOfMem y hy := by
  have hU : (⟨y, hy⟩ : U.toScheme) ⤳ (⟨x, hx⟩ : U.toScheme) :=
    (subtype_specializes_iff _ _).mpr h
  have hsq := Scheme.Hom.stalkSpecializes_stalkMap U.ι ⟨y, hy⟩ ⟨x, hx⟩ hU
  have hkey : inv (U.ι.stalkMap ⟨x, hx⟩) ≫
        X.presheaf.stalkSpecializes (U.ι.base.hom.map_specializes hU) =
      U.toScheme.presheaf.stalkSpecializes hU ≫ inv (U.ι.stalkMap ⟨y, hy⟩) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
    exact hsq
  suffices hgoal : Spec.map (X.presheaf.stalkSpecializes
      (U.ι.base.hom.map_specializes hU)) ≫ U.fromSpecStalkOfMem x hx =
      U.fromSpecStalkOfMem y hy by exact hgoal
  simp only [Scheme.Opens.fromSpecStalkOfMem]
  rw [← Category.assoc, ← Spec.map_comp, hkey, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

theorem PartialMap.fromFunctionField_eq {X Y : Scheme} [IrreducibleSpace X]
    (g : X.PartialMap Y) {x : X} (hx : x ∈ g.domain) :
    g.fromFunctionField = Spec.map (X.presheaf.stalkSpecializes
      (genericPoint_specializes x)) ≫ g.fromSpecStalkOfMem hx := by
  change g.fromSpecStalkOfMem _ = _
  rw [Scheme.PartialMap.fromSpecStalkOfMem, Scheme.PartialMap.fromSpecStalkOfMem,
    ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_stalkSpecializes
      (genericPoint_specializes x) hx]

end Scheme

section StructureStalk

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The structure map from `k` to the stalk at a point of a scheme over `k`. -/
noncomputable def Scheme.Hom.structureStalk (x : X) :
    CommRingCat.of k ⟶ X.presheaf.stalk x :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x trivial

theorem Scheme.Hom.Spec_map_structureStalk (x : X) :
    Spec.map (f.structureStalk x) = X.fromSpecStalk x ≫ f := by
  rw [Scheme.Hom.structureStalk, Spec.map_comp, Spec.map_comp,
    ← Scheme.fromSpecStalk_toSpecΓ X x]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem Scheme.Hom.structureStalk_stalkSpecializes {x y : X} (h : y ⤳ x) :
    f.structureStalk x ≫ X.presheaf.stalkSpecializes h = f.structureStalk y := by
  rw [Scheme.Hom.structureStalk, Scheme.Hom.structureStalk, Category.assoc, Category.assoc,
    TopCat.Presheaf.germ_stalkSpecializes]

end StructureStalk

section Main

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- A function-field element which is transcendental over `k` (expressed by
its explicit polynomial-evaluation certificate) spreads to a locally
quasi-finite dominant morphism `X ⟶ P1 k` under the smooth proper curve
hypotheses.  The function and its transcendence certificate are explicit
inputs, so this theorem does not claim that such an element exists. -/
theorem exists_locallyQuasiFinite_isDominant_toP1_of_transcendental
    [IsIntegral X] [IsProper f] [SmoothOfRelativeDimension 1 f]
    [LocallyOfFiniteType (P1.structureMap k)] [IsSeparated (P1.structureMap k)]
    [Scheme.IsSeparated (P1 k)]
    (f₀ : X.functionField)
    (hf₀ : ∀ P : Polynomial k, P ≠ 0 →
      Polynomial.eval₂ (f.structureStalk (genericPoint X)).hom f₀ P ≠ 0)
    (hclosedP1 : ∀ y : P1 k, y ≠ genericPoint (P1 k) →
      IsClosed ({y} : Set (P1 k)))
    (zP1 : P1 k) (hzP1 : zP1 ≠ genericPoint (P1 k)) :
    ∃ π : X ⟶ P1 k, LocallyQuasiFinite π ∧ IsDominant π ∧
      π ≫ P1.structureMap k = f := by
  classical
  have hf₀ne : f₀ ≠ 0 := by
    have h := hf₀ Polynomial.X Polynomial.X_ne_zero
    rwa [Polynomial.eval₂_X] at h
  set φK : Spec (X.presheaf.stalk (genericPoint X)) ⟶ P1 k :=
    P1.fromSpecChart k (f.structureStalk (genericPoint X)) 0 f₀
  have hφKover : φK ≫ P1.structureMap k =
      X.fromSpecStalk (genericPoint X) ≫ f := by
    rw [show φK = P1.fromSpecChart k (f.structureStalk (genericPoint X)) 0 f₀ by rfl,
      P1.fromSpecChart_structureMap, Scheme.Hom.Spec_map_structureStalk]
  have key : ∀ x : X, ∃ φx : Spec (X.presheaf.stalk x) ⟶ P1 k,
      φx ≫ P1.structureMap k = X.fromSpecStalk x ≫ f ∧
      Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫ φx = φK := by
    intro x
    letI : ValuationRing (X.presheaf.stalk x) := Hartshorne.smoothCurve_stalk_valuationRing f x
    have hnat : f.structureStalk x ≫
        X.presheaf.stalkSpecializes (genericPoint_specializes x) =
        f.structureStalk (genericPoint X) :=
      f.structureStalk_stalkSpecializes (genericPoint_specializes x)
    rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk x) f₀ with ⟨a, ha⟩ | ⟨b, hb⟩
    · refine ⟨P1.fromSpecChart k (f.structureStalk x) 0 a, ?_, ?_⟩
      · rw [P1.fromSpecChart_structureMap, Scheme.Hom.Spec_map_structureStalk]
      · have ha' : (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom a = f₀ := ha
        rw [P1.SpecMap_fromSpecChart, hnat, ha']
    · refine ⟨P1.fromSpecChart k (f.structureStalk x) 1 b, ?_, ?_⟩
      · rw [P1.fromSpecChart_structureMap, Scheme.Hom.Spec_map_structureStalk]
      · have hb' : (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom b = f₀⁻¹ := hb
        rw [P1.SpecMap_fromSpecChart, hnat, hb']
        have hu := P1.fromSpecChart_units k (f.structureStalk (genericPoint X))
          (Units.mk0 f₀ hf₀ne)
        simpa using hu.symm
  set F : X ⤏ P1 k :=
    Scheme.RationalMap.ofFunctionField f (P1.structureMap k) φK hφKover
  have hFff : F.fromFunctionField = φK :=
    Scheme.RationalMap.fromFunctionField_ofFunctionField f (P1.structureMap k) φK hφKover
  have hdom : F.domain = ⊤ := by
    refine le_antisymm le_top fun x _ => ?_
    obtain ⟨φx, hφxover, hφxspec⟩ := key x
    set gx : X.PartialMap (P1 k) :=
      Scheme.PartialMap.ofFromSpecStalk f (P1.structureMap k) φx hφxover
    refine Scheme.RationalMap.mem_domain.mpr
      ⟨gx, Scheme.PartialMap.mem_domain_ofFromSpecStalk f (P1.structureMap k) φx hφxover, ?_⟩
    refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap, hFff,
      Scheme.PartialMap.fromFunctionField_eq gx
        (Scheme.PartialMap.mem_domain_ofFromSpecStalk f (P1.structureMap k) φx hφxover),
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk, hφxspec]
  set π : X ⟶ P1 k := X.topIso.inv ≫ (X.isoOfEq hdom).inv ≫ F.toPartialMap.hom
  have hξdom : genericPoint X ∈ F.domain := by rw [hdom]; trivial
  have hstalk : X.fromSpecStalk (genericPoint X) ≫ X.topIso.inv ≫
      (X.isoOfEq hdom).inv = F.domain.fromSpecStalkOfMem (genericPoint X) hξdom := by
    rw [← cancel_mono F.domain.ι]
    rw [Category.assoc, Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι,
      Category.comp_id, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hgen : X.fromSpecStalk (genericPoint X) ≫ π = φK := by
    have h2 : F.domain.fromSpecStalkOfMem (genericPoint X) hξdom ≫ F.toPartialMap.hom =
        F.toPartialMap.fromFunctionField := rfl
    rw [show π = X.topIso.inv ≫ (X.isoOfEq hdom).inv ≫ F.toPartialMap.hom by rfl,
      reassoc_of% hstalk, h2, ← Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.toRationalMap_toPartialMap, hFff]
  have hπover : π ≫ P1.structureMap k = f := by
    have hdense : IsDominant (X.fromSpecStalk (genericPoint X)) := by
      constructor
      have hsub : {genericPoint X} ⊆ Set.range
          (X.fromSpecStalk (genericPoint X)).base :=
        Set.singleton_subset_iff.mpr ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
      intro z
      have hz := closure_mono hsub
      rw [(genericPoint_spec X).def] at hz
      exact hz trivial
    refine ext_of_isDominant (ι := X.fromSpecStalk (genericPoint X)) ?_
    rw [← Category.assoc, hgen, hφKover]
  haveI : LocallyOfFiniteType (π ≫ P1.structureMap k) := by rw [hπover]; infer_instance
  haveI : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π (P1.structureMap k)
  haveI : IsProper (π ≫ P1.structureMap k) := by rw [hπover]; infer_instance
  haveI : IsProper π := IsProper.of_comp π (P1.structureMap k)
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := ⟨⟩
  letI : Subsingleton (Spec (X.presheaf.stalk (genericPoint X))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (X.presheaf.stalk (genericPoint X))))
  have hπξ : π.base (genericPoint X) = genericPoint (P1 k) := by
    have h1 : (X.fromSpecStalk (genericPoint X) ≫ π).base
        (IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X))) =
        π.base (genericPoint X) := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
    rw [← h1, hgen]
    have h2 := P1.fromSpecChart_base_genericPoint k
      (f.structureStalk (genericPoint X)) f₀ hf₀
    rwa [show genericPoint (Spec (X.presheaf.stalk (genericPoint X))) =
      IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)) by subsingleton] at h2
  have hcurve : ∀ x y : X, y ⤳ x → y = genericPoint X ∨ y = x := fun _ _ h =>
    Hartshorne.smoothCurve_specializes_eq_genericPoint_or_eq f h
  have hfib : ∀ y : P1 k, (π ⁻¹' {y}).Finite := by
    intro y
    by_cases hy : y = genericPoint (P1 k)
    · subst hy
      refine Set.Finite.subset (Set.finite_singleton (genericPoint X)) fun x hx => ?_
      by_contra hxξ
      have hclosed : IsClosed ({x} : Set X) :=
        Hartshorne.closed_singleton_of_curve_specializations hcurve hxξ
      have himg : IsClosed (π.base '' {x}) := π.isClosedMap _ hclosed
      rw [Set.image_singleton, hx] at himg
      have huniv : closure ({genericPoint (P1 k)} : Set (P1 k)) = Set.univ :=
        (genericPoint_spec (P1 k)).def
      rw [himg.closure_eq] at huniv
      apply hzP1
      apply Set.mem_singleton_iff.mp
      rw [huniv]
      trivial
    · have hcl : IsClosed (π ⁻¹' {y}) :=
        (hclosedP1 y hy).preimage π.continuous
      refine Hartshorne.finite_closed_of_avoids_genericPoint hcurve hcl ?_
      intro hmem
      exact hy ((Set.mem_singleton_iff.mp hmem).symm.trans hπξ)
  have hdominant : IsDominant π := by
    constructor
    have hsub : {genericPoint (P1 k)} ⊆ Set.range π.base :=
      Set.singleton_subset_iff.mpr ⟨genericPoint X, hπξ⟩
    intro z
    have hz := closure_mono hsub
    rw [(genericPoint_spec (P1 k)).def] at hz
    exact hz trivial
  exact ⟨π, LocallyQuasiFinite.of_finite_preimage_singleton π hfib, hdominant, hπover⟩

/-- The finite-map form of
`exists_locallyQuasiFinite_isDominant_toP1_of_transcendental`. -/
theorem exists_isFinite_isDominant_toP1_of_transcendental
    [IsIntegral X] [IsProper f] [SmoothOfRelativeDimension 1 f]
    [LocallyOfFiniteType (P1.structureMap k)] [IsSeparated (P1.structureMap k)]
    [Scheme.IsSeparated (P1 k)]
    (f₀ : X.functionField)
    (hf₀ : ∀ P : Polynomial k, P ≠ 0 →
      Polynomial.eval₂ (f.structureStalk (genericPoint X)).hom f₀ P ≠ 0)
    (hclosedP1 : ∀ y : P1 k, y ≠ genericPoint (P1 k) →
      IsClosed ({y} : Set (P1 k)))
    (zP1 : P1 k) (hzP1 : zP1 ≠ genericPoint (P1 k)) :
    ∃ π : X ⟶ P1 k, IsFinite π ∧ IsDominant π ∧
      π ≫ P1.structureMap k = f := by
  obtain ⟨π, hqf, hdom, hcomp⟩ :=
    exists_locallyQuasiFinite_isDominant_toP1_of_transcendental f f₀ hf₀
      hclosedP1 zP1 hzP1
  letI : LocallyQuasiFinite π := hqf
  exact ⟨π, isFinite_toP1_of_locallyQuasiFinite f π hcomp, hdom, hcomp⟩

/-- A smooth proper integral curve over a field admits a finite dominant map to `P1`.

The transcendental function and the elementary point-topology certificates are supplied by
the Hartshorne library itself; this is the source-facing entry point for the construction. -/
theorem exists_isFinite_isDominant_toP1
    [IsIntegral X] [IsProper f] [SmoothOfRelativeDimension 1 f] :
    ∃ π : X ⟶ P1 k, IsFinite π ∧ IsDominant π ∧
      π ≫ P1.structureMap k = f := by
  letI : LocallyOfFiniteType (P1.structureMap k) := by
    infer_instance
  letI : IsSeparated (P1.structureMap k) := by
    infer_instance
  letI : Scheme.IsSeparated (P1 k) := by infer_instance
  obtain ⟨f₀, hf₀⟩ := Hartshorne.SmoothOfRelativeDimension.exists_transcendental_functionField f
  obtain ⟨zP1, hzP1⟩ := P1.exists_ne_genericPoint k
  have hclosedP1 : ∀ y : P1 k, y ≠ genericPoint (P1 k) →
      IsClosed ({y} : Set (P1 k)) := fun y hy => P1.isClosed_singleton_of_ne_genericPoint k hy
  exact exists_isFinite_isDominant_toP1_of_transcendental f f₀ hf₀
    hclosedP1 zP1 hzP1

end Main

end AlgebraicGeometry
