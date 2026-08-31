/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.P1Points

/-!
# Spreading a transcendental rational function out to a morphism to `ℙ¹`

On an integral scheme `X`, proper and smooth of relative dimension `1` over a field `k`
(a smooth projective curve), a rational function `f₀ ∈ K(X)` transcendental over `k`
spreads out to a `k`-morphism `π : X ⟶ ℙ¹` with finite fibers:

* every stalk of `X` is a valuation ring of `K(X)`
  (`SmoothOfRelativeDimension.valuationRing_stalk`), so at every point `x` either `f₀` or
  `f₀⁻¹` is a regular germ; the corresponding chart morphism
  `Spec 𝒪_x ⟶ ℙ¹` (`P1.fromSpecChart`) agrees generically with the "generic point"
  morphism `Spec K(X) ⟶ ℙ¹` by the gluing identity `P1.fromSpecChart_units`;
* by the spreading-out theory of rational maps (`Scheme.RationalMap`), the generic
  morphism defines a rational map `X ⤏ ℙ¹` over `k` whose domain of definition therefore
  contains every point, and `Scheme.RationalMap.toPartialMap` glues it to a morphism
  `π : X ⟶ ℙ¹`;
* transcendence of `f₀` makes `π` send the generic point to the generic point, whence
  every fiber of `π` is finite: the fiber of the generic point is a set of closed points
  mapping onto the non-closed generic point of `ℙ¹` (impossible for the proper `π` unless
  the fiber is `{ξ}`), and any other fiber is a closed subset of the Noetherian
  curve avoiding the generic point, hence finite
  (`Scheme.finite_of_isClosed_of_notMem_genericPoint`).

The main result is `AlgebraicGeometry.exists_locallyQuasiFinite_isDominant_toP1` (with the
locally-quasi-finite-only projection `exists_locallyQuasiFinite_toP1` kept for the existing
finiteness consumer); it also records that `π` is **dominant**, read off from the
generic-point image. Zariski's main theorem (in `AlgebraicJacobian.Curve.MapToP1`) upgrades
local quasi-finiteness to finiteness.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

section StalkSpecializes

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- `Scheme.Opens.fromSpecStalkOfMem` is compatible with specialization: the canonical map
`Spec 𝒪_{X,x} ⟶ U` restricted along a generalization `y ⤳ x` (with `y ∈ U`) is the
canonical map at `y`. -/
theorem Scheme.Opens.fromSpecStalkOfMem_stalkSpecializes {U : X.Opens} {x y : X}
    (h : y ⤳ x) (hx : x ∈ U) (hy : y ∈ U) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem x hx =
      U.fromSpecStalkOfMem y hy := by
  have hU : (⟨y, hy⟩ : U.toScheme) ⤳ (⟨x, hx⟩ : U.toScheme) :=
    (subtype_specializes_iff _ _).mpr h
  -- Naturality of `stalkSpecializes` along the open immersion `U.ι`.
  have hsq := Scheme.Hom.stalkSpecializes_stalkMap U.ι ⟨y, hy⟩ ⟨x, hx⟩ hU
  have hkey : inv (U.ι.stalkMap ⟨x, hx⟩) ≫
        X.presheaf.stalkSpecializes (U.ι.base.hom.map_specializes hU) =
      U.toScheme.presheaf.stalkSpecializes hU ≫ inv (U.ι.stalkMap ⟨y, hy⟩) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
    exact hsq
  suffices hgoal : Spec.map (X.presheaf.stalkSpecializes (U.ι.base.hom.map_specializes hU)) ≫
      U.fromSpecStalkOfMem x hx = U.fromSpecStalkOfMem y hy by exact hgoal
  simp only [Scheme.Opens.fromSpecStalkOfMem]
  rw [← Category.assoc, ← Spec.map_comp, hkey, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/-- A partial map restricted to `Spec K(X)` factors through `Spec 𝒪_x` for every `x` in its
domain: `g.fromFunctionField = Spec K(X) ⟶ Spec 𝒪_x ⟶ Y`. -/
theorem Scheme.PartialMap.fromFunctionField_eq [IrreducibleSpace X] (g : X.PartialMap Y)
    {x : X} (hx : x ∈ g.domain) :
    g.fromFunctionField = Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x))
      ≫ g.fromSpecStalkOfMem hx := by
  change g.fromSpecStalkOfMem _ = _
  rw [Scheme.PartialMap.fromSpecStalkOfMem, Scheme.PartialMap.fromSpecStalkOfMem,
    ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_stalkSpecializes
      (genericPoint_specializes x) hx]

end StalkSpecializes

section StructureStalk

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The composite `k ⟶ Γ(X, ⊤) ⟶ 𝒪_{X,x}` through which every stalk of a scheme over `k`
becomes a ring under `k`. -/
noncomputable def Scheme.Hom.structureStalk (x : X) :
    CommRingCat.of k ⟶ X.presheaf.stalk x :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial

/-- On `Spec`, the structure map of a stalk is the canonical map `Spec 𝒪_x ⟶ X ⟶ Spec k`. -/
theorem Scheme.Hom.Spec_map_structureStalk (x : X) :
    Spec.map (f.structureStalk x) = X.fromSpecStalk x ≫ f := by
  rw [Scheme.Hom.structureStalk, Spec.map_comp, Spec.map_comp,
    ← Scheme.fromSpecStalk_toSpecΓ X x]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The structure maps of the stalks are compatible with specialization. -/
theorem Scheme.Hom.structureStalk_stalkSpecializes {x y : X} (h : y ⤳ x) :
    f.structureStalk x ≫ X.presheaf.stalkSpecializes h = f.structureStalk y := by
  rw [Scheme.Hom.structureStalk, Scheme.Hom.structureStalk, Category.assoc, Category.assoc,
    TopCat.Presheaf.germ_stalkSpecializes]

end StructureStalk

section Main

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **A smooth projective curve admits a locally quasi-finite dominant morphism to `ℙ¹`.**

For `X` integral, proper and smooth of relative dimension `1` over a field `k`, there is a
`k`-morphism `π : X ⟶ ℙ¹` with finite fibers (hence locally quasi-finite) which is moreover
**dominant**: the spreading out of a rational function transcendental over `k`. Transcendence
sends the generic point of `X` to the generic point of `ℙ¹` (`hπξ` below), and dominance is
read off from that generic-point image. -/
theorem exists_locallyQuasiFinite_isDominant_toP1 [IsIntegral X] [IsProper f]
    [SmoothOfRelativeDimension 1 f] :
    ∃ π : X ⟶ P1 k, LocallyQuasiFinite π ∧ IsDominant π ∧ π ≫ P1.structureMap k = f := by
  classical
  -- A rational function transcendental over `k`.
  obtain ⟨f₀, hf₀⟩ := SmoothOfRelativeDimension.exists_transcendental_functionField f
  have hf₀ne : f₀ ≠ 0 := by
    have := hf₀ Polynomial.X Polynomial.X_ne_zero
    rwa [Polynomial.eval₂_X] at this
  -- The generic morphism `Spec K(X) ⟶ ℙ¹`, `t ↦ f₀` on chart 0.
  set φK : Spec (X.presheaf.stalk (genericPoint X)) ⟶ P1 k :=
    P1.fromSpecChart k (f.structureStalk (genericPoint X)) 0 f₀ with hφK
  have hφKover : φK ≫ P1.structureMap k = X.fromSpecStalk (genericPoint X) ≫ f := by
    rw [hφK, P1.fromSpecChart_structureMap, Scheme.Hom.Spec_map_structureStalk]
  -- At every point, `f₀` or `f₀⁻¹` is a regular germ, giving a chart morphism from the
  -- stalk agreeing with the generic morphism.
  have key : ∀ x : X, ∃ φx : Spec (X.presheaf.stalk x) ⟶ P1 k,
      φx ≫ P1.structureMap k = X.fromSpecStalk x ≫ f ∧
      Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫ φx = φK := by
    intro x
    letI : ValuationRing (X.presheaf.stalk x) :=
      SmoothOfRelativeDimension.valuationRing_stalk f x
    have hnat : f.structureStalk x ≫
        X.presheaf.stalkSpecializes (genericPoint_specializes x) =
        f.structureStalk (genericPoint X) :=
      f.structureStalk_stalkSpecializes (genericPoint_specializes x)
    rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk x) f₀ with ⟨a, ha⟩ | ⟨b, hb⟩
    · refine ⟨P1.fromSpecChart k (f.structureStalk x) 0 a, ?_, ?_⟩
      · rw [P1.fromSpecChart_structureMap, Scheme.Hom.Spec_map_structureStalk]
      · have ha' : (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom a = f₀ := ha
        rw [P1.SpecMap_fromSpecChart, hnat, ha', hφK]
    · refine ⟨P1.fromSpecChart k (f.structureStalk x) 1 b, ?_, ?_⟩
      · rw [P1.fromSpecChart_structureMap, Scheme.Hom.Spec_map_structureStalk]
      · have hb' : (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom b = f₀⁻¹ :=
          hb
        rw [P1.SpecMap_fromSpecChart, hnat, hb', hφK]
        have := P1.fromSpecChart_units k (f.structureStalk (genericPoint X))
          (Units.mk0 f₀ hf₀ne)
        simpa using this.symm
  -- The rational map spread out from the generic morphism.
  set F : X ⤏ P1 k :=
    Scheme.RationalMap.ofFunctionField f (P1.structureMap k) φK hφKover with hF
  have hFff : F.fromFunctionField = φK :=
    Scheme.RationalMap.fromFunctionField_ofFunctionField f (P1.structureMap k) φK hφKover
  -- Every point lies in the domain of definition.
  have hdom : F.domain = ⊤ := by
    refine le_antisymm le_top fun x _ => ?_
    obtain ⟨φx, hφxover, hφxspec⟩ := key x
    set gx : X.PartialMap (P1 k) :=
      Scheme.PartialMap.ofFromSpecStalk f (P1.structureMap k) φx hφxover with hgx
    refine Scheme.RationalMap.mem_domain.mpr
      ⟨gx, Scheme.PartialMap.mem_domain_ofFromSpecStalk f (P1.structureMap k) φx hφxover, ?_⟩
    refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap, hFff,
      Scheme.PartialMap.fromFunctionField_eq gx
        (Scheme.PartialMap.mem_domain_ofFromSpecStalk f (P1.structureMap k) φx hφxover),
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk, hφxspec]
  -- Glue to an honest morphism.
  set π : X ⟶ P1 k := X.topIso.inv ≫ (X.isoOfEq hdom).inv ≫ F.toPartialMap.hom with hπ
  -- The generic behaviour of `π`: on `Spec K(X)` it is the generic chart morphism.
  have hξdom : genericPoint X ∈ F.domain := by rw [hdom]; trivial
  have hstalk : X.fromSpecStalk (genericPoint X) ≫ X.topIso.inv ≫ (X.isoOfEq hdom).inv =
      F.domain.fromSpecStalkOfMem (genericPoint X) hξdom := by
    rw [← cancel_mono F.domain.ι]
    rw [Category.assoc, Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι,
      Category.comp_id, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hgen : X.fromSpecStalk (genericPoint X) ≫ π = φK := by
    have h2 : F.domain.fromSpecStalkOfMem (genericPoint X) hξdom ≫ F.toPartialMap.hom =
        F.toPartialMap.fromFunctionField := rfl
    rw [hπ, reassoc_of% hstalk, h2, ← Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.toRationalMap_toPartialMap, hFff]
  -- `π` is a morphism over `k`.
  have hdominant : IsDominant (X.fromSpecStalk (genericPoint X)) := by
    constructor
    have hsub : {genericPoint X} ⊆ Set.range (X.fromSpecStalk (genericPoint X)).base := by
      exact Set.singleton_subset_iff.mpr
        ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
    intro z
    have := closure_mono hsub
    rw [(genericPoint_spec X).def] at this
    exact this trivial
  have hπover : π ≫ P1.structureMap k = f := by
    refine ext_of_isDominant (ι := X.fromSpecStalk (genericPoint X)) ?_
    rw [← Category.assoc, hgen, hφKover]
  -- `π` is locally of finite type and proper by cancellation.
  haveI : LocallyOfFiniteType (π ≫ P1.structureMap k) := by rw [hπover]; infer_instance
  haveI : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π (P1.structureMap k)
  haveI : IsProper (π ≫ P1.structureMap k) := by rw [hπover]; infer_instance
  haveI : IsProper π := IsProper.of_comp π (P1.structureMap k)
  -- The underlying space of `X` is a Noetherian space.
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := ⟨⟩
  -- `π` sends the generic point to the generic point (transcendence of `f₀`).
  haveI : Subsingleton (Spec (X.presheaf.stalk (genericPoint X))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (X.presheaf.stalk (genericPoint X))))
  have hπξ : π.base (genericPoint X) = genericPoint (P1 k) := by
    have h1 : (X.fromSpecStalk (genericPoint X) ≫ π).base
        (IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X))) =
        π.base (genericPoint X) := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
    rw [← h1, hgen, hφK]
    have h2 := P1.fromSpecChart_base_genericPoint k (f.structureStalk (genericPoint X)) f₀ hf₀
    rwa [show genericPoint (Spec (X.presheaf.stalk (genericPoint X))) =
      IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)) from
        Subsingleton.elim _ _] at h2
  -- All fibers of `π` are finite.
  have hcurve : ∀ x y : X, y ⤳ x → y = genericPoint X ∨ y = x := fun _ _ h =>
    SmoothOfRelativeDimension.specializes_eq_genericPoint_or_eq f h
  have hfib : ∀ y : P1 k, (π ⁻¹' {y}).Finite := by
    intro y
    by_cases hy : y = genericPoint (P1 k)
    · -- The fiber of the generic point is `{ξ}`: any other point of it would be closed
      -- with closed (= generic) image point, which is absurd since `ℙ¹` has more than one
      -- point.
      subst hy
      refine Set.Finite.subset (Set.finite_singleton (genericPoint X)) fun x hx => ?_
      by_contra hxξ
      have hclosed : IsClosed ({x} : Set X) :=
        Scheme.isClosed_singleton_of_forall_specializes hcurve hxξ
      have himg : IsClosed (π.base '' {x}) := π.isClosedMap _ hclosed
      have hxval : π.base x = genericPoint (P1 k) := hx
      rw [Set.image_singleton, hxval] at himg
      obtain ⟨z, hz⟩ := P1.exists_ne_genericPoint k
      have huniv : closure ({genericPoint (P1 k)} : Set (P1 k)) = Set.univ :=
        (genericPoint_spec (P1 k)).def
      rw [himg.closure_eq] at huniv
      have hzmem : z ∈ ({genericPoint (P1 k)} : Set (P1 k)) := by
        rw [huniv]
        trivial
      exact hz hzmem
    · -- Any other fiber is a closed subset avoiding the generic point.
      have hcl : IsClosed (π ⁻¹' {y}) :=
        (P1.isClosed_singleton_of_ne_genericPoint k hy).preimage π.continuous
      refine Scheme.finite_of_isClosed_of_notMem_genericPoint hcurve hcl ?_
      intro hmem
      exact hy ((Set.mem_singleton_iff.mp hmem).symm.trans hπξ)
  -- `π` is dominant: its range contains the generic point of `ℙ¹` (`hπξ`), which is dense.
  have hdominant : IsDominant π := by
    constructor
    have hsub : {genericPoint (P1 k)} ⊆ Set.range π.base :=
      Set.singleton_subset_iff.mpr ⟨genericPoint X, hπξ⟩
    intro z
    have := closure_mono hsub
    rw [(genericPoint_spec (P1 k)).def] at this
    exact this trivial
  exact ⟨π, LocallyQuasiFinite.of_finite_preimage_singleton π hfib, hdominant, hπover⟩

/-- **A smooth projective curve admits a locally quasi-finite morphism to `ℙ¹`.** The
locally-quasi-finite half of `exists_locallyQuasiFinite_isDominant_toP1`, kept under its
original name and postcondition for the existing finiteness consumer
(`AlgebraicJacobian.Curve.MapToP1.exists_isFinite_toP1`). -/
theorem exists_locallyQuasiFinite_toP1 [IsIntegral X] [IsProper f]
    [SmoothOfRelativeDimension 1 f] :
    ∃ π : X ⟶ P1 k, LocallyQuasiFinite π ∧ π ≫ P1.structureMap k = f := by
  obtain ⟨π, hqf, _, hcomp⟩ := exists_locallyQuasiFinite_isDominant_toP1 f
  exact ⟨π, hqf, hcomp⟩

end Main

end AlgebraicGeometry
