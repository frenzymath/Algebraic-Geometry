/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyField
import AlgebraicJacobian.Picard.OpenImmersionUnits

/-!
# The colength↔degree identity for divisor families over a field (`informal/spec-dd-1.md` §3 (f))

Over a field `K` the forward map `divFamDivisor` (`AlgebraicJacobian.Picard.DivisorFamilyField`)
sends a certified divisor family to its Weil divisor. This file lands the **degree identity**

`deg K (divFamDivisor F) = finrank K W(d)`

(so, with the field half `DivisorAdaptation.IsCertified.finrank_glued`, `deg = n`), the
colength↔degree bridge across the glued equalizer `W(d) = ker (δ⁻ − δ⁺)`.

## The support-separated assembly

The equalizer does not decompose over the cover naively — a supported closed point may lie in
two pieces. This file proves the **support-separated** case, which is the one the DD-1c backward
map consumes (its adaptations isolate the support points by construction): when the overlap
colength modules vanish (`ovlColength i j` is subsingleton for `i ≠ j`), the equalizer is the
*whole* product of the chart-local colengths, so

`finrank K W(d) = ∑ⱼ finrank K (Γ(D(hⱼ)) ⧸ (fⱼ))`  (`finrank_glued_eq_sum_of_separated`),

pure module algebra (`Module.finrank_pi_fintype` over the field, where every factor is free).
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite
open Module (finrank)

namespace AlgebraicGeometry

/-! ## A unit-germ ↔ trivial-order dictionary on the curve bundle

Reusable core: on the curve bundle `X/K`, a section `f` over an open `U ∋ η` is a unit at a
closed point `z ∈ U` exactly when the order at `z` of its germ at `η` is trivial. Both
directions of the private `ChartColength` machinery, packaged as a public equivalence through
the DVR valuation of the stalk. -/

namespace Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]

/-- **Unit germ ↔ trivial order.** For a section `f` over an open `U ∋ η` whose germ at `η` is
the field unit `g`, the germ of `f` at a closed point `z ∈ U` is a unit of the stalk exactly
when the order of `g` at `z` is trivial (`ordZ = 1`). -/
theorem isUnit_germ_iff_ordZ_eq_one {U : X.Opens} (hη : genericPoint X ∈ U)
    (f : Γ(X, U)) (g : X.functionFieldˣ)
    (hg : (g : X.functionField) = (X.presheaf.germ U (genericPoint X) hη).hom f)
    {z : X} (hz : z ∈ U) (hzg : z ≠ genericPoint X) :
    IsUnit ((X.presheaf.germ U z hz).hom f)
      ↔ Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hzg g = 1 := by
  rw [Scheme.ordZ_eq_one_iff]
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hzg
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hzg
  have hord : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hzg
      = (stalkHeightOne X z).valuation X.functionField := rfl
  have hgs : (X.presheaf.germ U (genericPoint X) hη).hom f
      = algebraMap (X.presheaf.stalk z) X.functionField
          ((X.presheaf.germ U z hz).hom f) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact (X.presheaf.germ_stalkSpecializes_apply hz
      ((genericPoint_spec X).specializes trivial) f).symm
  rw [hg, hgs, hord, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact (IsLocalRing.notMem_maximalIdeal).symm

/-- A unit in a closed-point stalk remains a unit in the function field, hence has
trivial `ordZ`.  This is the valuation form of the stalk-unit transition bridge used
when comparing a pulled local equation with a theta-chart reading. -/
theorem ordZ_unitsMap_stalk_eq_one {z : X} (hz : z ≠ genericPoint X)
    (v : (X.presheaf.stalk z)ˣ) :
    Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz
      (Units.map (algebraMap (X.presheaf.stalk z) X.functionField).toMonoidHom v) = 1 := by
  rw [Scheme.ordZ_eq_one_iff (X ↘ Spec (CommRingCat.of K)) hz]
  exact Valuation.Integers.one_of_isUnit'
    (v := Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz)
    v.isUnit (fun y => Scheme.ord_algebraMap_stalk_le_one K hz y)

/-- Multiplication by the function-field image of a stalk unit does not change the
additive order at the closed point. -/
theorem toAdd_ordZ_mul_unitsMap_stalk {z : X} (hz : z ≠ genericPoint X)
    (a : X.functionFieldˣ) (v : (X.presheaf.stalk z)ˣ) :
    Multiplicative.toAdd
        (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz
          (a * Units.map (algebraMap (X.presheaf.stalk z) X.functionField).toMonoidHom v))
      = Multiplicative.toAdd (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz a) := by
  rw [map_mul, ordZ_unitsMap_stalk_eq_one K hz v, mul_one]

end Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {K : Type u} [Field K] [Algebra k K]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

namespace DivisorAdaptation

variable {d : (relCurve C K).LocalEquations} (A : DivisorAdaptation C K π d)

/-- On the diagonal `i = i` the two overlap-restriction maps of the equalizer coincide: the two
`≤`-witnesses `pieces i ⊓ pieces i ≤ pieces i` are definitionally equal (proof irrelevance), so
`toOvlLeft i i` and `toOvlRight i i` are the same map. -/
lemma toOvlLeft_self_eq_toOvlRight_self (i : A.index) :
    A.toOvlLeft i i = A.toOvlRight i i :=
  rfl

/-- **Support separation collapses the equalizer to the whole product.** If the overlap colength
modules vanish off the diagonal (`ovlColength i j` subsingleton for `i ≠ j`), then every element
of the product of chart-local colengths satisfies the equalizer condition, so the glued
submodule is all of `∏ⱼ colength j`. -/
lemma gluedSubmodule_eq_top_of_separated
    (hsep : ∀ i j : A.index, i ≠ j → Subsingleton (A.ovlColength i j)) :
    A.gluedSubmodule = ⊤ := by
  refine eq_top_iff.mpr fun s _ => ?_
  rw [mem_gluedSubmodule_iff]
  rintro ⟨i, j⟩
  by_cases hij : i = j
  · subst hij
    exact congrFun (congrArg (fun f : A.colength i →ₐ[K] A.ovlColength i i => (f : _ → _))
      (A.toOvlLeft_self_eq_toOvlRight_self i)) (s i)
  · haveI := hsep i j hij
    exact Subsingleton.elim _ _

/-- The equalizer as the whole product, when the glued submodule is `⊤`. -/
noncomputable def gluedTopEquiv (h : A.gluedSubmodule = ⊤) : A.Glued ≃ₗ[K] A.chartProd :=
  (LinearEquiv.ofEq _ _ h).trans Submodule.topEquiv

/-- **The support-separated colength↔degree bridge, algebraic half** (worksheet's
Mayer–Vietoris finrank additivity, no overlap correction): when the overlaps vanish, the
`K`-dimension of the glued equalizer is the sum of the chart-local colength dimensions. Pure
module algebra over the field — every colength is free, and the equalizer is the whole product
(`Module.finrank_pi_fintype`). -/
theorem finrank_glued_eq_sum_of_separated
    (hfin : ∀ j : A.index, Module.Finite K (A.colength j))
    (hsep : ∀ i j : A.index, i ≠ j → Subsingleton (A.ovlColength i j)) :
    finrank K A.Glued = ∑ j : A.index, finrank K (A.colength j) := by
  haveI : ∀ j : A.index, Module.Free K (A.colength j) := fun j => Module.Free.of_divisionRing _ _
  haveI := hfin
  rw [LinearEquiv.finrank_eq (A.gluedTopEquiv (A.gluedSubmodule_eq_top_of_separated hsep))]
  exact Module.finrank_pi_fintype K

end DivisorAdaptation

/-! ## The per-piece degree reading and the support-separated assembly -/

section Degree

variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

namespace DivisorAdaptation

variable {d : (relCurve C K).LocalEquations} (A : DivisorAdaptation C K π d)

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- Each piece `D(h_j)` is an affine open: a basic open of one of the two affine pinned charts. -/
lemma isAffineOpen_pieces (j : A.index) : IsAffineOpen (A.pieces j) := by
  rcases j with j | j
  · rw [FinCoverData.pieces_inl]
    exact (relCover_isAffineOpen₀ C K (fiberTwoCover π)).basicOpen (A.h₀ j)
  · rw [FinCoverData.pieces_inr]
    exact (relCover_isAffineOpen₁ C K (fiberTwoCover π)).basicOpen (A.h₁ j)

/-- **The divisor coefficient is read off any piece.** At a closed point `z` of a piece
`D(h_j)`, the order of vanishing of the piece equation `f_j` (any field unit `g_j` presenting
its germ at `η`) equals the coefficient of the presentation divisor `D = div(d)` at `z`: the
pointwise clause `eqn_rel j z` presents `f_j` as a unit section (trivial order) times `d`'s
equation at the member of `z` itself, whose order is the coefficient by definition. -/
lemma coeffAt_eq_toAdd_ordZ_eqn (j : A.index) {z : relCurve C K}
    (hz : z ∈ A.pieces j) (hzg : z ≠ genericPoint (relCurve C K))
    (gⱼ : (relCurve C K).functionFieldˣ)
    (hgⱼ : (gⱼ : (relCurve C K).functionField)
      = ((relCurve C K).presheaf.germ (A.pieces j) (genericPoint (relCurve C K))
          (Scheme.genericPoint_mem_of_nonempty ⟨z, hz⟩)).hom (A.eqn j)) :
    Multiplicative.toAdd (Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) hzg gⱼ)
      = coeffAt hzg (Scheme.presentationDivisor K d.presentation) := by
  have hηj : genericPoint (relCurve C K) ∈ A.pieces j :=
    Scheme.genericPoint_mem_of_nonempty ⟨z, hz⟩
  obtain ⟨u, hu⟩ := A.eqn_rel j z
  have hηW : genericPoint (relCurve C K) ∈ A.pieces j ⊓ d.cover.opens z :=
    ⟨hηj, d.cover.genericPoint_mem_opens z⟩
  have hzW : z ∈ A.pieces j ⊓ d.cover.opens z := ⟨hz, d.cover.mem_opens z⟩
  have hval : (gⱼ : (relCurve C K).functionField)
      = (Scheme.germGenericUnits hηW u : (relCurve C K).functionField)
        * (d.presentation.elem z : (relCurve C K).functionField) := by
    have h := congrArg ((relCurve C K).presheaf.germ
      (A.pieces j ⊓ d.cover.opens z) (genericPoint (relCurve C K)) hηW).hom hu
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
    rw [hgⱼ, Scheme.germGenericUnits_val, Scheme.LocalEquations.presentation_elem_val]
    exact h
  have hunit : gⱼ = Scheme.germGenericUnits hηW u * d.presentation.elem z :=
    Units.ext hval
  rw [Scheme.coeffAt_presentationDivisor, hunit, map_mul,
    Scheme.ordZ_germGenericUnits K hηW u hzg hzW, one_mul]

open scoped Classical in
/-- **The per-piece degree reading.** The `K`-dimension of the chart-local colength module
`Γ(D(h_j)) ⧸ (f_j)` equals the local degree contribution: the sum, over the support points of
the presentation divisor `D` lying in the piece, of the coefficient weighted by residue degree.
The chart colength keystone (`finrank_quotient_span_section`) read through the piece (affine,
containing `η` unless empty), with the coefficient dictionary
(`coeffAt_eq_toAdd_ordZ_eqn`); empty pieces contribute `0` (colength subsingleton). -/
lemma finrank_colength_eq_sum (j : A.index) :
    (finrank K (A.colength j) : ℤ)
      = ∑ p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
          (fun p => p.1 ∈ A.pieces j),
        coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
          * ((relCurve C K).residueDeg K p.1 : ℤ) := by
  classical
  haveI : LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
      SmoothOfRelativeDimension.smooth 1 _
    inferInstance
  by_cases hη : genericPoint (relCurve C K) ∈ A.pieces j
  · -- nonempty piece: the chart colength keystone reads off the local degree
    have hne : ((relCurve C K).presheaf.germ (A.pieces j) (genericPoint (relCurve C K)) hη).hom
        (A.eqn j) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp (A.eqn_regular j (genericPoint (relCurve C K)) hη)
    set gⱼ : (relCurve C K).functionFieldˣ := Units.mk0 _ hne with hgⱼdef
    have hg : (gⱼ : (relCurve C K).functionField)
        = ((relCurve C K).presheaf.germ (A.pieces j) (genericPoint (relCurve C K)) hη).hom
            (A.eqn j) := rfl
    have hout : ∀ (z : relCurve C K) (hz : z ∈ A.pieces j)
        (hzg : z ≠ genericPoint (relCurve C K)),
        (⟨z, hzg⟩ : {x : relCurve C K // x ≠ genericPoint (relCurve C K)})
          ∉ (Scheme.presentationDivisor K d.presentation).support.filter
            (fun p => p.1 ∈ A.pieces j) →
        IsUnit (((relCurve C K).presheaf.germ (A.pieces j) z hz).hom (A.eqn j)) := by
      intro z hz hzg hznot
      have hzsupp : (⟨z, hzg⟩ : {x : relCurve C K // x ≠ genericPoint (relCurve C K)})
          ∉ (Scheme.presentationDivisor K d.presentation).support :=
        fun hin => hznot (Finset.mem_filter.mpr ⟨hin, hz⟩)
      have hcoeff : coeffAt hzg (Scheme.presentationDivisor K d.presentation) = 0 := by
        by_contra hc
        exact hzsupp (Finsupp.mem_support_iff.mpr hc)
      have h1 := A.coeffAt_eq_toAdd_ordZ_eqn j hz hzg gⱼ hg
      rw [hcoeff] at h1
      have hord : Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) hzg gⱼ = 1 :=
        Multiplicative.toAdd.injective (by rw [h1]; exact toAdd_one.symm)
      exact (Scheme.isUnit_germ_iff_ordZ_eq_one K hη (A.eqn j) gⱼ hg hz hzg).mpr hord
    calc (finrank K (A.colength j) : ℤ)
        = ∑ p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
            (fun p => p.1 ∈ A.pieces j),
            Multiplicative.toAdd (Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) p.2 gⱼ)
              * ((relCurve C K).residueDeg K p.1 : ℤ) :=
          finrank_quotient_span_section K (A.isAffineOpen_pieces j) hη gⱼ hg _
            (fun p hp => (Finset.mem_filter.mp hp).2) hout
      _ = ∑ p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
            (fun p => p.1 ∈ A.pieces j),
            coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
              * ((relCurve C K).residueDeg K p.1 : ℤ) :=
          Finset.sum_congr rfl fun p hp => by
            rw [A.coeffAt_eq_toAdd_ordZ_eqn j (Finset.mem_filter.mp hp).2 p.2 gⱼ hg]
  · -- empty piece: `pieces j = ⊥`, so the colength is subsingleton and the filter is empty
    have hbot : A.pieces j ≤ ⊥ :=
      fun x hx => hη (Scheme.genericPoint_mem_of_nonempty ⟨x, hx⟩)
    haveI : Subsingleton Γ(relCurve C K, A.pieces j) :=
      (relCurve C K).subsingleton_sections_of_le_bot hbot
    haveI : Subsingleton (A.colength j) :=
      (Ideal.Quotient.mk_surjective (I := Ideal.span {A.eqn j})).subsingleton
    rw [show finrank K (A.colength j) = 0 from Module.finrank_zero_of_subsingleton,
      Nat.cast_zero,
      Finset.filter_false_of_mem fun p _ hp => by simpa using hbot hp, Finset.sum_empty]

/-- Where a piece equation `f_j` is a unit at a closed point `z ∈ D(h_j)`, the divisor coefficient
there vanishes: the order of `f_j` at `z` is trivial (`isUnit_germ_iff_ordZ_eq_one`), and that order
is the coefficient (`coeffAt_eq_toAdd_ordZ_eqn`). -/
lemma coeffAt_eq_zero_of_isUnit_germ (j : A.index) {z : relCurve C K} (hz : z ∈ A.pieces j)
    (hzg : z ≠ genericPoint (relCurve C K))
    (hu : IsUnit (((relCurve C K).presheaf.germ (A.pieces j) z hz).hom (A.eqn j))) :
    coeffAt hzg (Scheme.presentationDivisor K d.presentation) = 0 := by
  have hηj : genericPoint (relCurve C K) ∈ A.pieces j :=
    Scheme.genericPoint_mem_of_nonempty ⟨z, hz⟩
  have hne : ((relCurve C K).presheaf.germ (A.pieces j) (genericPoint (relCurve C K)) hηj).hom
      (A.eqn j) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (A.eqn_regular j (genericPoint (relCurve C K)) hηj)
  set gⱼ : (relCurve C K).functionFieldˣ := Units.mk0 _ hne with hgⱼdef
  have hg : (gⱼ : (relCurve C K).functionField)
      = ((relCurve C K).presheaf.germ (A.pieces j) (genericPoint (relCurve C K)) hηj).hom
          (A.eqn j) := rfl
  have hord : Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) hzg gⱼ = 1 :=
    (Scheme.isUnit_germ_iff_ordZ_eq_one K hηj (A.eqn j) gⱼ hg hz hzg).mp hu
  have h1 := A.coeffAt_eq_toAdd_ordZ_eqn j hz hzg gⱼ hg
  rw [hord, toAdd_one] at h1
  exact h1.symm

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **Overlap vanishing from separation.** If each piece equation is a unit at every point of each
overlap (the support-separation hypothesis), the overlap colength modules vanish: the restricted
equation is a unit section (`isUnit_of_isUnit_germ`), so the overlap ideal is the unit ideal. This
supplies the input to `finrank_glued_eq_sum_of_separated`. -/
lemma subsingleton_ovlColength_of_sep
    (hsep : ∀ i j : A.index, i ≠ j → ∀ (z : relCurve C K) (hzi : z ∈ A.pieces i),
      z ∈ A.pieces j → IsUnit (((relCurve C K).presheaf.germ (A.pieces i) z hzi).hom (A.eqn i)))
    (i j : A.index) (hij : i ≠ j) : Subsingleton (A.ovlColength i j) := by
  have hunit : IsUnit (relResAlgHom C K
      (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i) (A.eqn i)) := by
    rw [relResAlgHom_apply]
    apply (relCurve C K).toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    rw [(relCurve C K).presheaf.germ_res_apply]
    exact hsep i j hij z hz.1 hz.2
  have htop : A.ovlIdeal i j = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert _ _)) hunit
  exact (Ideal.Quotient.subsingleton_iff).mpr htop

open scoped Classical in
/-- **The colength↔degree identity, support-separated case** (`informal/spec-dd-1.md` §3 (f), the
DD-1c degree half). For a certified divisor adaptation over the field `K` whose pieces are
*support-separated* (each piece equation `f_i` is a unit at every point of every overlap), the
degree of the presentation divisor equals the `K`-dimension of the glued equalizer `W(d)`:

`deg K D = finrank K W(d)`.

Assembly: separation collapses the equalizer to the product of chart-local colengths
(`finrank_glued_eq_sum_of_separated` via `subsingleton_ovlColength_of_sep`); each colength reads the
local degree (`finrank_colength_eq_sum`); and, because the pieces cover the curve (`relCover_sup`,
`cover₀`/`cover₁`) with each supported point in a *unique* piece (separation forces the coefficient
to vanish on overlaps), the double sum over pieces collapses to the full-support degree sum. -/
theorem deg_presentationDivisor_eq_finrank_glued
    (hsep : ∀ i j : A.index, i ≠ j → ∀ (z : relCurve C K) (hzi : z ∈ A.pieces i),
      z ∈ A.pieces j → IsUnit (((relCurve C K).presheaf.germ (A.pieces i) z hzi).hom (A.eqn i)))
    (hfin : ∀ j : A.index, Module.Finite K (A.colength j)) :
    Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K d.presentation)
      = (finrank K A.Glued : ℤ) := by
  classical
  have hW : (finrank K A.Glued : ℤ) = ∑ j : A.index, (finrank K (A.colength j) : ℤ) := by
    rw [A.finrank_glued_eq_sum_of_separated hfin
      (fun i j hij => A.subsingleton_ovlColength_of_sep hsep i j hij), Nat.cast_sum]
  -- the inner collapse: each supported point lies in a unique piece
  have hinner : ∀ p ∈ (Scheme.presentationDivisor K d.presentation).support,
      (∑ j : A.index, if p.1 ∈ A.pieces j then
        coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
          * ((relCurve C K).residueDeg K p.1 : ℤ) else 0)
        = coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
          * ((relCurve C K).residueDeg K p.1 : ℤ) := by
    intro p hp
    obtain ⟨j₀, hj₀⟩ : ∃ j : A.index, p.1 ∈ A.pieces j := by
      have hle : (⊤ : (relCurve C K).Opens) ≤ ⨆ j : A.index, A.pieces j := by
        rw [← relCover_sup C K (fiberTwoCover π)]
        exact sup_le (A.cover₀.trans (iSup_le fun j => le_iSup (fun i => A.pieces i) (Sum.inl j)))
          (A.cover₁.trans (iSup_le fun j => le_iSup (fun i => A.pieces i) (Sum.inr j)))
      exact TopologicalSpace.Opens.mem_iSup.mp (hle (TopologicalSpace.Opens.mem_top p.1))
    have huniq : ∀ b : A.index, p.1 ∈ A.pieces b → b = j₀ := by
      intro b hb
      by_contra hbne
      exact (Finsupp.mem_support_iff.mp hp)
        (A.coeffAt_eq_zero_of_isUnit_germ b hb p.2 (hsep b j₀ hbne p.1 hb hj₀))
    rw [Finset.sum_eq_single j₀ (fun b _ hbne => if_neg fun hb => hbne (huniq b hb))
      (fun h => absurd (Finset.mem_univ j₀) h), if_pos hj₀]
  calc Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K d.presentation)
      = ∑ p ∈ (Scheme.presentationDivisor K d.presentation).support,
          coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
            * ((relCurve C K).residueDeg K p.1 : ℤ) :=
        Finset.sum_congr rfl fun p _ => rfl
    _ = ∑ p ∈ (Scheme.presentationDivisor K d.presentation).support,
          ∑ j : A.index, if p.1 ∈ A.pieces j then
            coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
              * ((relCurve C K).residueDeg K p.1 : ℤ) else 0 :=
        Finset.sum_congr rfl fun p hp => (hinner p hp).symm
    _ = ∑ j : A.index, ∑ p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
          (fun p => p.1 ∈ A.pieces j),
            coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
              * ((relCurve C K).residueDeg K p.1 : ℤ) := by
        rw [Finset.sum_comm]; simp_rw [Finset.sum_filter]
    _ = ∑ j : A.index, (finrank K (A.colength j) : ℤ) :=
        Finset.sum_congr rfl fun j _ => (A.finrank_colength_eq_sum j).symm
    _ = (finrank K A.Glued : ℤ) := hW.symm

end DivisorAdaptation

variable {n : ℕ}

open scoped Classical in
/-- **The degree of a support-separated certified family is its rank** (`informal/spec-dd-1.md` §3
(f)): combining the geometric colength↔degree identity
(`DivisorAdaptation.deg_presentationDivisor_eq_finrank_glued`) with the field half of the
certificate (`DivisorAdaptation.IsCertified.finrank_glued`, `finrank K W(d) = n`), the forward
divisor of a certified family with a support-separated adaptation has degree exactly `n`. This is
the identity the DD-1c backward map consumes (its adaptations isolate the support points, so they
are support-separated by construction). -/
theorem deg_divFamDivisor_of_separated {F : CertifiedDivisorFamily C K π n}
    (hsep : ∀ i j : F.adaptation.index, i ≠ j → ∀ (z : relCurve C K)
      (hzi : z ∈ F.adaptation.pieces i), z ∈ F.adaptation.pieces j →
      IsUnit (((relCurve C K).presheaf.germ (F.adaptation.pieces i) z hzi).hom
        (F.adaptation.eqn i))) :
    Scheme.CurveDivisor.deg K (divFamDivisor (DivFam.mk F)) = (n : ℤ) := by
  rw [divFamDivisor_mk,
    F.adaptation.deg_presentationDivisor_eq_finrank_glued hsep F.certified.finite_colength,
    F.certified.finrank_glued]

end Degree

end AlgebraicGeometry
