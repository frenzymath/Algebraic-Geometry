/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Albanese.CodimOneIndeterminacy
import AlgebraicJacobian.Albanese.CodimOneDVRStalk

/-!
# Milne Theorem 3.1 — codim-≥2 indeterminacy

Ported from §4 (first half) of `Albanese/CodimOneExtension.lean` of the
previous Algebraic-Jacobian tree (identical toolchain and mathlib pin),
re-kernel-verified here. Fifth file of the codim-one extension layer.

* `indeterminacy_codimGe2_of_smooth_of_complete` — **Milne Theorem 3.1**
  (*Abelian Varieties*, §I.3, p. 16): for a rational map of `k̄`-varieties
  from a nonsingular variety to a complete variety, every point of the
  indeterminacy locus has coheight (codimension) at least `2`. Proof: at a
  coheight-≤1 point, either the point is generic (lies in the dense open
  domain) or the stalk is a DVR (`localRing_dvr_of_codim_one`,
  `Albanese/CodimOneDVRStalk.lean`) and the valuative criterion of
  properness spreads the lift out to a `PartialMap` defined there
  (`PartialMap.ofFromSpecStalk`).
* `codimOneFree_of_smooth_of_complete` — the `CodimOneFree` phrasing.

The over-`k̄` hypothesis `f.compHom Y.hom = X.hom.toRationalMap` is Milne's
ambient "rational map of varieties over `k`" assumption, needed for the
valuative square's base compatibility.

Blueprint pins: `thm:indeterminacy_codimGe2`, `cor:codim_one_free`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

namespace Scheme

namespace RationalMap

/-! ## §4. Milne Theorem 3.1 — codim-≥2 indeterminacy, and extension from ∅

A rational map from a nonsingular variety to a complete variety has
indeterminacy locus of codimension `≥ 2`
(`indeterminacy_codimGe2_of_smooth_of_complete`, = Milne 3.1; equivalently
`CodimOneFree f`, `codimOneFree_of_smooth_of_complete`). Separately, a
rational map (from any reduced scheme to any separated scheme) with *empty*
indeterminacy locus is uniquely represented by a regular morphism
(`existsUnique_hom_of_indeterminacyLocus_eq_empty`). Milne 3.2 combines the
two through Lemma 3.3, which forces `Z(f) = ∅` for group-variety targets.

NOTE: the former `extend_of_codimOneFree_of_smooth` ("CodimOneFree alone ⇒
extension, complete target") was removed in run-0006 T6 session 0015 — its
statement was false (counterexample `ℙ² ⇢ ℙ¹`; see the docstring of
`existsUnique_hom_of_indeterminacyLocus_eq_empty`), so its `sorry` was
unclosable.

Blueprint pins: `thm:indeterminacy_codimGe2`, `cor:codim_one_free`,
`thm:codim_one_extension` (Milne §I.3 Theorem 3.1 p. 16). -/

/-- Glue helper: the function-field morphism of a partial map factors through
the `Spec`-of-stalk morphism at any point of its domain. Both sides are
`(fromSpecStalkOfMem) ≫ g.hom` for the domain open; the factorization is the
open-immersion cancellation of Mathlib's
`SpecMap_stalkSpecializes_fromSpecStalk` along `g.domain.ι`. -/
private lemma fromFunctionField_factor
    {X Y : Scheme.{u}} [IrreducibleSpace X] (g : X.PartialMap Y) {x : X}
    (hx : x ∈ g.domain) :
    g.fromFunctionField =
      Spec.map (X.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes trivial)) ≫
        g.fromSpecStalkOfMem hx := by
  dsimp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem]
  rw [← Category.assoc]
  congr 1
  rw [← cancel_mono g.domain.ι, Category.assoc, Opens.fromSpecStalkOfMem_ι,
    Opens.fromSpecStalkOfMem_ι, SpecMap_stalkSpecializes_fromSpecStalk]

set_option backward.isDefEq.respectTransparency false in
/-- **Milne Theorem 3.1, codim-≥2 conclusion (unbundled).** For a rational map
`f : X ⇢ Y` of varieties over `k̄` (the `hf` hypothesis is the "over `k̄`"
condition: `f` composed with `Y`'s structure morphism is `X`'s structure
morphism, as rational maps) with `X` nonsingular and `Y` complete, every
point of the indeterminacy locus has coheight (codimension) at least `2`.

This *is* Milne Theorem 3.1 (the theorem asserts exactly the codim-≥2
property of the indeterminacy locus — not an everywhere-extension, which
for general complete targets is false; see
`existsUnique_hom_of_indeterminacyLocus_eq_empty` below).
`av_indeterminacyLocus_eq_empty` in `Thm32RationalMapExtension.lean`
combines this conclusion with Milne Lemma 3.3's pure-codim-1 disjunct to
force the locus empty for abelian-variety targets.

**Proved (run-0006 T6, second session).** Proof: let `z ∈ Z(f)` with
`coheight z ≤ 1`. If `coheight z = 0` then `z` is the generic point (maximal
in the specialisation preorder of the irreducible sober space `X`), which
lies in the dense open `f.domain` — contradiction. If `coheight z = 1`, the
stalk `O_{X,z}` is a DVR (`localRing_dvr_of_codim_one`, sorry-free via
`SmoothPrimeRegularity.lean`) with fraction field `K(X)`
(Mathlib `IsFractionRing (stalk z) functionField` for integral schemes), so
`Spec K(X) ⟶ Y` (`f.fromFunctionField`) together with
`Spec O_{X,z} ⟶ Spec k̄` forms a `ValuativeCommSq` over `Y.hom` — the
square commutes by `hf` pushed to the function field. Properness of `Y.hom`
supplies a lift `L : Spec O_{X,z} ⟶ Y` (Mathlib
`IsProper.eq_valuativeCriterion`), which spreads out to a partial map
defined at `z` (Mathlib `PartialMap.ofFromSpecStalk`, using germ-injectivity
of integral schemes); its rational class is `f` by comparison at the
function field (`RationalMap.eq_of_fromFunctionField_eq` + the
`fromFunctionField_factor` glue above), so `z ∈ f.domain` — contradiction.

The over-`k̄` hypothesis `hf` is necessary: the valuative square's base
compatibility identifies the `k̄`-structure on `K(X)` induced by `f` with
the one induced by `X`, which can fail for abstract-scheme rational maps.
This matches Milne's setting (rational maps of varieties *over* `k`). -/
theorem indeterminacy_codimGe2_of_smooth_of_complete
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    {Y : Over (Spec (.of kbar))}
    [IsProper Y.hom] [GeometricallyIrreducible Y.hom]
    [IsIntegral Y.left] [IsReduced Y.left]
    (f : X.left.RationalMap Y.left)
    (hf : f.compHom Y.hom = X.hom.toRationalMap) :
    ∀ z ∈ indeterminacyLocus f, 2 ≤ Order.coheight z := by
  intro z hz
  have hzdom : z ∉ f.domain := hz
  by_contra hlt
  have hle : Order.coheight z ≤ 1 := by
    have h2 : Order.coheight z < 2 := not_le.mp hlt
    rwa [ENat.lt_two_iff] at h2
  -- The generic point of X.
  have hspec : genericPoint X.left ⤳ z :=
    (genericPoint_spec X.left).specializes trivial
  -- Over-ness at the function-field level.
  have hff : f.fromFunctionField ≫ Y.hom
      = X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom := by
    obtain ⟨g0, rfl⟩ := f.exists_rep
    have h1' : (g0.compHom Y.hom).toRationalMap
        = X.hom.toPartialMap.toRationalMap := by
      rw [RationalMap.compHom_toRationalMap]; exact hf
    have h2 := congrArg RationalMap.fromFunctionField h1'
    rw [RationalMap.fromFunctionField_toRationalMap,
      RationalMap.fromFunctionField_toRationalMap] at h2
    simpa using h2
  rcases hle.lt_or_eq with h0 | h1
  · -- coheight 0: `z` is the generic point, which lies in the dense open domain.
    rw [Order.lt_one_iff] at h0
    have hmax : IsMax z := Order.coheight_eq_zero.mp h0
    have hzeq : z = genericPoint X.left :=
      ((show z ⤳ genericPoint X.left from hmax hspec).antisymm hspec).eq
    obtain ⟨w, hw⟩ := f.dense_domain.nonempty
    exact hzdom (hzeq ▸ (genericPoint_specializes w).mem_open f.domain.2 hw)
  · -- coheight 1: valuative criterion at the DVR stalk.
    haveI hDVR : IsDiscreteValuationRing (X.left.presheaf.stalk z) :=
      localRing_dvr_of_codim_one z h1
    haveI : ValuationRing (X.left.presheaf.stalk z) := inferInstance
    -- The valuative criterion for the proper structure morphism of Y.
    have hVC : ValuativeCriterion Y.hom := by
      have hP : IsProper Y.hom := inferInstance
      rw [IsProper.eq_valuativeCriterion] at hP
      exact hP.1.1.1
    -- The valuative commutative square. Note `algebraMap (stalk z) K(X)` is
    -- definitionally the stalk-specialization map (`stalkFunctionFieldAlgebra`).
    have hcommSq : CommSq f.fromFunctionField
        (Spec.map (CommRingCat.ofHom
          (algebraMap (X.left.presheaf.stalk z) X.left.functionField)))
        Y.hom (X.left.fromSpecStalk z ≫ X.hom) := ⟨by
      rw [hff, ← Category.assoc]
      congr 1
      exact (SpecMap_stalkSpecializes_fromSpecStalk hspec).symm⟩
    -- Materialise the instance fields outside the structure literal (inside it
    -- the stalk term is unfolded past `Scheme.presheaf`, so the keyed
    -- instances no longer fire). Plain `have`/`let` (NOT `haveI`/`letI`): an
    -- opaque local `Field` instance would poison the `Semiring`-path defeq.
    have hdom : IsDomain (X.left.presheaf.stalk z) := inferInstance
    have hvr : ValuationRing (X.left.presheaf.stalk z) := inferInstance
    let hfld : Field X.left.functionField := inferInstance
    have hfr : IsFractionRing (X.left.presheaf.stalk z) X.left.functionField :=
      inferInstance
    obtain ⟨hlift⟩ := hVC
      { R := X.left.presheaf.stalk z
        commRing := inferInstance
        domain := hdom
        valuationRing := hvr
        K := X.left.functionField
        field := hfld
        algebra := stalkFunctionFieldAlgebra X.left z
        isFractionRing := hfr
        i₁ := f.fromFunctionField
        i₂ := X.left.fromSpecStalk z ≫ X.hom
        commSq := hcommSq }
    obtain ⟨L₀, hfacl₀, hfacr₀⟩ := hlift.default
    -- Retype the lift through the (definitional) `CommRingCat.of ↥R = R` and
    -- `algebraMap = stalkSpecializes` identifications.
    let L : Spec (X.left.presheaf.stalk z) ⟶ Y.left := L₀
    have hfacl : Spec.map (X.left.presheaf.stalkSpecializes hspec) ≫ L
        = f.fromFunctionField := hfacl₀
    have hfacr : L ≫ Y.hom = X.left.fromSpecStalk z ≫ X.hom := hfacr₀
    -- Spread the lift out to a partial map defined at z.
    let g : X.left.PartialMap Y.left :=
      PartialMap.ofFromSpecStalk (x := z) X.hom Y.hom L hfacr
    have hzg : z ∈ g.domain :=
      PartialMap.mem_domain_ofFromSpecStalk (x := z) X.hom Y.hom L hfacr
    have hgL : g.fromSpecStalkOfMem hzg = L :=
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk (x := z) X.hom Y.hom L hfacr
    have hgen : g.toRationalMap = f := by
      refine RationalMap.eq_of_fromFunctionField_eq _ _ ?_
      rw [RationalMap.fromFunctionField_toRationalMap,
        fromFunctionField_factor g hzg, hgL]
      exact hfacl
    exact hzdom (RationalMap.mem_domain.mpr ⟨g, hzg, hgen⟩)

/-- **Milne Theorem 3.1, `CodimOneFree` phrasing.** A rational map of
`k̄`-varieties from a nonsingular variety to a complete variety is
codim-1-indeterminacy-free: every codim-1 point of `X` lies in the domain
of definition. Immediate from the codim-≥2 conclusion
`indeterminacy_codimGe2_of_smooth_of_complete`.

Blueprint reference: `cor:codim_one_free` (Milne, *Abelian Varieties*,
Theorem 3.1, §I.3, p. 16, the "equivalently" clause). -/
theorem codimOneFree_of_smooth_of_complete
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    {Y : Over (Spec (.of kbar))}
    [IsProper Y.hom] [GeometricallyIrreducible Y.hom]
    [IsIntegral Y.left] [IsReduced Y.left]
    (f : X.left.RationalMap Y.left)
    (hf : f.compHom Y.hom = X.hom.toRationalMap) :
    CodimOneFree f := by
  intro x hx
  by_contra hnotin
  have h2 := indeterminacy_codimGe2_of_smooth_of_complete f hf x hnotin
  rw [hx] at h2
  norm_num at h2


end RationalMap

end Scheme

end AlgebraicGeometry
