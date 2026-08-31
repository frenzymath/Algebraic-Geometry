/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.DedekindSections

/-!
# Stalks and specializations on a scheme with Dedekind section rings

A scheme covered by affine opens whose section rings are Dedekind domains behaves like a
smooth curve: its stalks are valuation rings (fields at generic points, DVRs at closed
points), and its specialization order has height one.  This file proves the pointwise
statements from the single hypothesis "`x` lies in an affine open with Dedekind section
ring", and derives the two consumers needed for the finite-fibers argument of the map to
`ℙ¹`:

* `AlgebraicGeometry.IsAffineOpen.valuationRing_stalk`: the stalk at a point of an affine
  open with Dedekind section ring is a valuation ring.
* `AlgebraicGeometry.IsAffineOpen.specializes_eq_genericPoint_or_eq`: on an irreducible
  scheme, a generalization of such a point is the generic point or the point itself.
* `AlgebraicGeometry.Scheme.finite_of_isClosed_of_notMem_genericPoint`: on an irreducible,
  Noetherian scheme all of whose points have only trivial generalizations, a closed subset
  avoiding the generic point is finite.

Finally the hypotheses are discharged for a scheme smooth of relative dimension one over a
field, using the standard smooth charts and
`Algebra.IsStandardSmoothOfRelativeDimension.isDedekindDomain`:

* `AlgebraicGeometry.SmoothOfRelativeDimension.exists_isDedekindDomain_section`,
* `AlgebraicGeometry.SmoothOfRelativeDimension.valuationRing_stalk`,
* `AlgebraicGeometry.SmoothOfRelativeDimension.exists_transcendental_section`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

section Pointwise

/-- The stalk of an integral scheme at a point of an affine open whose section ring is a
Dedekind domain is a valuation ring: the localization of a Dedekind domain at a prime is a
field (at `⊥`) or a discrete valuation ring (at a maximal ideal), and both are valuation
rings. -/
theorem IsAffineOpen.valuationRing_stalk [IsIntegral X] {V : X.Opens} (hV : IsAffineOpen V)
    (hD : IsDedekindDomain Γ(X, V)) {x : X} (hx : x ∈ V) :
    ValuationRing (X.presheaf.stalk x) := by
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  set q := hV.primeIdealOf ⟨x, hx⟩ with hq
  by_cases hbot : q.asIdeal = ⊥
  · -- At the generic point of `V` the stalk is the fraction field.
    have hsub : q.asIdeal.primeCompl = nonZeroDivisors Γ(X, V) := by
      ext z
      simp [Ideal.primeCompl, hbot, mem_nonZeroDivisors_iff_ne_zero]
    have hfrac : IsLocalization (nonZeroDivisors Γ(X, V)) (X.presheaf.stalk x) := by
      rw [← hsub]
      exact hloc
    letI : Field (X.presheaf.stalk x) := IsFractionRing.toField Γ(X, V)
    infer_instance
  · -- At other points the stalk is a DVR.
    have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain Γ(X, V) hbot _
    infer_instance

/-- On an irreducible scheme, a generalization of a point of an affine open with Dedekind
section ring is the generic point or the point itself: primes of a Dedekind domain below a
given prime are `⊥` or the prime itself. -/
theorem IsAffineOpen.specializes_eq_genericPoint_or_eq [IrreducibleSpace X] {V : X.Opens}
    (hV : IsAffineOpen V) (hD : IsDedekindDomain Γ(X, V)) {x y : X} (hx : x ∈ V)
    (h : y ⤳ x) : y = genericPoint X ∨ y = x := by
  have hy : y ∈ V := h.mem_open V.2 hx
  set py := hV.primeIdealOf ⟨y, hy⟩ with hpy
  set px := hV.primeIdealOf ⟨x, hx⟩ with hpx
  have hyx : hV.fromSpec.base py = y := hV.fromSpec_primeIdealOf ⟨y, hy⟩
  have hxx : hV.fromSpec.base px = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  -- Transfer the specialization along the open immersion `Spec Γ(X, V) ⟶ X`.
  have hspec : py ⤳ px := by
    refine hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp ?_
    rw [hyx, hxx]
    exact h
  have hle : py.asIdeal ≤ px.asIdeal := (PrimeSpectrum.le_iff_specializes py px).mpr hspec
  by_cases hbot : py.asIdeal = ⊥
  · -- `y` is the image of the generic point of `Spec Γ(X, V)`.
    left
    have hgen : (genericPoint (Spec Γ(X, V)) : Spec Γ(X, V)) = py := by
      rw [genericPoint_eq_bot_of_affine]
      exact (PrimeSpectrum.ext hbot).symm
    rw [← hyx, ← hgen, genericPoint_eq_of_isOpenImmersion hV.fromSpec]
  · -- A nonzero prime of a Dedekind domain is maximal, so `py = px`.
    right
    have hmax : py.asIdeal.IsMaximal := py.isPrime.isMaximal hbot
    have : py.asIdeal = px.asIdeal := hmax.eq_of_le px.isPrime.ne_top hle
    rw [← hyx, ← hxx, PrimeSpectrum.ext this]

end Pointwise

section Finiteness

/-- On an irreducible scheme whose specialization order has height one (every strict
generalization is the generic point), every non-generic point is closed. -/
theorem Scheme.isClosed_singleton_of_forall_specializes [IrreducibleSpace X]
    (hgen : ∀ x y : X, y ⤳ x → y = genericPoint X ∨ y = x) {x : X}
    (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  have : closure ({x} : Set X) ⊆ {x} := by
    intro y hy
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
    rcases hgen y x hxy with h | h
    · exact absurd h hx
    · exact h ▸ rfl
  exact closure_subset_iff_isClosed.mp this

/-- **Finiteness of proper closed subsets of a curve-like scheme.**  On an irreducible,
Noetherian (as a topological space), sober scheme whose specialization order has height one,
a closed subset avoiding the generic point is finite: it is a finite union of irreducible
closed subsets, and each of these is the closure of a non-generic point, hence a singleton. -/
theorem Scheme.finite_of_isClosed_of_notMem_genericPoint [IrreducibleSpace X]
    [TopologicalSpace.NoetherianSpace X]
    (hgen : ∀ x y : X, y ⤳ x → y = genericPoint X ∨ y = x) {Z : Set X} (hZ : IsClosed Z)
    (hξ : genericPoint X ∉ Z) : Z.Finite := by
  obtain ⟨S, hSfin, hScl, hSirr, hSsup⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hSsup]
  refine Set.Finite.sUnion hSfin fun t ht => ?_
  -- Each irreducible component of `Z` is the closure of a non-generic point, hence a
  -- singleton.
  obtain ⟨z, hz⟩ := QuasiSober.sober (hSirr t ht) (hScl t ht)
  have hzZ : z ∈ Z := hSsup ▸ Set.mem_sUnion.mpr ⟨t, ht, hz.mem⟩
  have hzξ : z ≠ genericPoint X := fun h => hξ (h ▸ hzZ)
  have hcl : IsClosed ({z} : Set X) :=
    Scheme.isClosed_singleton_of_forall_specializes hgen hzξ
  have : t = {z} := by
    rw [← hz.def, hcl.closure_eq]
  rw [this]
  exact Set.finite_singleton z

end Finiteness

section SmoothCurve

variable {K : Type u} [Field K] (f : X ⟶ Spec (CommRingCat.of K))

/-- Every point of an integral scheme smooth of relative dimension `1` over a field lies in
an affine open whose section ring is a Dedekind domain: a standard smooth chart of relative
dimension `1`. -/
theorem SmoothOfRelativeDimension.exists_isDedekindDomain_section
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ IsDedekindDomain Γ(X, V) := by
  obtain ⟨U, hU, V, hV, hxV, e, hsm⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  -- The base affine open is nonempty, hence is all of the one-point space `Spec K`.
  have hUtop : U = ⊤ := by
    have hsub : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => ?_)
    exact Subsingleton.elim (f.base x) y ▸ e hxV
  subst hUtop
  letI : Field Γ(Spec (CommRingCat.of K), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  algebraize [(f.appLE ⊤ V e).hom]
  exact ⟨V, hV, hxV, Algebra.IsStandardSmoothOfRelativeDimension.isDedekindDomain
    Γ(Spec (CommRingCat.of K), ⊤) Γ(X, V)⟩

/-- The stalks of an integral scheme smooth of relative dimension `1` over a field are
valuation rings. -/
theorem SmoothOfRelativeDimension.valuationRing_stalk
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] (x : X) :
    ValuationRing (X.presheaf.stalk x) := by
  obtain ⟨V, hV, hxV, hD⟩ :=
    SmoothOfRelativeDimension.exists_isDedekindDomain_section f x
  exact hV.valuationRing_stalk hD hxV

/-- On an integral scheme smooth of relative dimension `1` over a field, the only
generalizations of a point are the generic point and the point itself. -/
theorem SmoothOfRelativeDimension.specializes_eq_genericPoint_or_eq
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x y : X} (h : y ⤳ x) :
    y = genericPoint X ∨ y = x := by
  obtain ⟨V, hV, hxV, hD⟩ :=
    SmoothOfRelativeDimension.exists_isDedekindDomain_section f x
  exact hV.specializes_eq_genericPoint_or_eq hD hxV h

/-- **Existence of a transcendental rational function.**  On an integral scheme smooth of
relative dimension `1` over a field `K`, the function field contains an element `f₀`
transcendental over `K`, where `K` acts on the function field through the structure morphism
(global sections followed by the germ at the generic point).

The element is the étale coordinate of a standard smooth chart
(`Algebra.IsStandardSmoothOfRelativeDimension.exists_transcendental`). -/
theorem SmoothOfRelativeDimension.exists_transcendental_functionField
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] :
    ∃ f₀ : X.functionField, ∀ P : Polynomial K, P ≠ 0 →
      Polynomial.eval₂ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom f₀ P ≠ 0 := by
  classical
  obtain ⟨U, hU, V, hV, hxV, e, hsm⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f)
      (genericPoint X)
  have hUtop : U = ⊤ := by
    have hsub : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => ?_)
    exact Subsingleton.elim (f.base (genericPoint X)) y ▸ e hxV
  subst hUtop
  letI : Field Γ(Spec (CommRingCat.of K), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  haveI : Nonempty V := ⟨⟨genericPoint X, hxV⟩⟩
  algebraize [(f.appLE ⊤ V e).hom]
  obtain ⟨t, ht⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_transcendental
    Γ(Spec (CommRingCat.of K), ⊤) Γ(X, V)
  refine ⟨(X.presheaf.germ V (genericPoint X) hxV).hom t, fun P hP => ?_⟩
  -- Rewrite the structure composite through the chart.
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ V e ≫
        X.presheaf.germ V (genericPoint X) hxV := by
    simp only [Scheme.Hom.appLE, Category.assoc]
    rw [X.presheaf.germ_res (homOfLE e) _ hxV]
    rfl
  rw [hcomp]
  -- Unfold the composite evaluation into a germ of an `aeval` in the chart.
  have heval : Polynomial.eval₂ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ V e ≫
      X.presheaf.germ V (genericPoint X) hxV).hom
        ((X.presheaf.germ V (genericPoint X) hxV).hom t) P =
      (X.presheaf.germ V (genericPoint X) hxV).hom
        (Polynomial.aeval t (P.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) := by
    rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra, Polynomial.hom_eval₂,
      Polynomial.eval₂_map]
    rfl
  rw [heval]
  -- The germ map is injective on the integral scheme `X`, and `t` is transcendental.
  intro hzero
  have hinj : Function.Injective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom : K →+* _) :=
    ((ConcreteCategory.isIso_iff_bijective
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv).mp inferInstance).injective
  have hmap : P.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ≠ 0 :=
    fun h0 => hP ((Polynomial.map_eq_zero_iff hinj).mp h0)
  refine ht ⟨P.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom, hmap, ?_⟩
  refine germ_injective_of_isIntegral X (genericPoint X) hxV ?_
  rw [map_zero]
  exact hzero

end SmoothCurve

end AlgebraicGeometry
