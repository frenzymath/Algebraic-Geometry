/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffAbel
import AlgebraicJacobian.Picard.DivisorFamilyAffCompare
import AlgebraicJacobian.Picard.DivisorFamilyFieldDegree

/-!
# The SUPPORT-SEPARATED degree ledger on the WIDENED adaptation

**Read `Picard/DivisorFamilyAffStalkEval.lean` first if you want to consume the widened degree
identity.**  That file proves the same conclusion with **no separation hypothesis**, for every
widened adaptation, and it is the route a consumer should use.  This file proves the
support-separated case: a shorter argument, but its `hsep` has zero producers in conclusion
position anywhere in the project and is refutable against a support point in `V₀ ⊓ V₁`.  Both facts
were measured after this file was written; the docstrings below carry the corrections at the
statements they affect.

The colength↔degree identity of `Picard/DivisorFamilyFieldDegree.lean`, ported from
`DivisorAdaptation` (pieces typed into a fixed pair of pinned `P¹` charts) to `AffAdaptation`
(arbitrary affine opens, human decision I-0492).  The port is **complete**: the widened
`deg_presentationDivisor_eq_finrank_glued` and its `deg = n` corollary are proved here, and
nothing in the chain remains conditional on the chart typing.

## What the port cost, measured rather than predicted

The board carried this as a **four**-lemma port.  It is five: the prescription omitted
`coeffAt_eq_toAdd_ordZ_eqn`, the coefficient dictionary that both other geometric lemmas call.
That is the only way the estimate was wrong, and it was wrong in the cheap direction — not one
proof step of any of the five differs from its chart-typed original.

Two substitutions carry the entire widening, and both replace a *derivation* by a structure
**field**:

* `DivisorAdaptation.isAffineOpen_pieces` is a two-case `rcases` on the `Sum` index proving each
  piece is a basic open of a pinned affine chart; `AffCoverData.isAffineOpen_pieces` is the field.
  The keystone that consumes it, `finrank_quotient_span_section`
  (`RiemannRoch/ChartColength.lean`, in `AlgebraicGeometry` with no further namespace), takes
  `IsAffineOpen V` as an *argument* — it never wanted a chart.
* the three-line `relCover_sup` + `cover₀`/`cover₁` block inside the assembly produces exactly
  `∃ j, p.1 ∈ pieces j`; widened, that is `AffCoverData.exists_mem_pieces`, the joint covering
  field.

So the pinned pair was never load-bearing for the degree ledger.  It was the chart-typed **cost**
of two facts `AffCoverData` assumes, which is why an earlier pricing of this port as *obstructed*
by the covering was backwards (retracted at `Picard/DivisorFamilyAffAbel.lean`, issue I-1098).

## Main declarations

* `AffAdaptation.gluedSubmodule_eq_top_of_separated`, `finrank_glued_eq_sum_of_separated` — the
  algebraic half: separation collapses the equalizer to the product, and Mayer–Vietoris finrank
  additivity with no overlap correction.
* `AffAdaptation.coeffAt_eq_toAdd_ordZ_eqn` — the coefficient dictionary (the fifth lemma).
* `AffAdaptation.finrank_colength_eq_sum` — the per-piece degree reading, on an arbitrary affine
  piece.
* `AffAdaptation.coeffAt_eq_zero_of_isUnit_germ`, `subsingleton_ovlColength_of_sep` — the
  separation inputs.
* `AffAdaptation.deg_presentationDivisor_eq_finrank_glued` — the geometric half.
* `AffAdaptation.IsCertified.finrank_glued` — the field half.
* `AffAdaptation.deg_presentationDivisor_eq_of_isCertified` — `deg D = n`.
* `DivisorAdaptation.sep_toAff`, `exists_widened_deg_eq_of_certifiedFamily_sep` — the joint
  non-vacuity witness for the corollary's two hypotheses, at every `n`.

## What is NOT closed by this file

`hdegAff` (`Picard/DivisorFamilyAffAbel.lean`) is the *Abel-value* ledger — the widened Abel value
of a degree-`n` widened class has degree `n` at every field point — and it is still an explicit
hypothesis there.  This file supplies an identity that gate needs, not the gate.

One further correction, since the distance was misdescribed here too: the remaining step is **not**
"the widened analogue of `DivFamZar.classDeg_picClass`" via *this* identity.  `classDeg_picClass`
routes through `deg_divFamDivisor` (`Picard/DivisorFamilyFieldCRT.lean:376`), whose proof term calls
the **CRT** `DivisorAdaptation.deg_presentationDivisor` — the separation-free route — and not the
separated `_eq_finrank_glued` this file ports.  So the input a widened `classDeg_picClass` actually
wants is `AffAdaptation.deg_presentationDivisor` in `Picard/DivisorFamilyAffStalkEval.lean`.
Nothing here or there discharges `rep` or any antecedent of the atlas assembly.

**That correction was right about the route and wrong about the count** (review-ajcr, 2026-07-30,
issue I-1197).  "The input a widened `classDeg_picClass` actually wants" is singular here, and
`classDeg_picClass` wants **two**: the CRT identity named above *and* the field collapse
`DivFam.exists_toZar_eq` (`Picard/DivSchemeAbel.lean:77`), which its proof consumes on its first
line.  The collapse was the input with no widened analogue at all — `DivFamAff` is zero tokens
project-wide — so tracking only the CRT half left the genuinely missing piece uncosted.  Both are
now measured, `hdegAff` closes, and the widened collapse
(`DivFamZarAff.exists_toZarAff_eq`) transports verbatim from `DivSchemeAbel.lean:79-130`.  The
sentence about `rep` and the atlas antecedents stands unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); pin in-file. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Module

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {K : Type u} [Field K] [Algebra k K]

namespace AffAdaptation

variable {D : AffCoverData C K} {d : (relCurve C K).LocalEquations} (A : AffAdaptation D d)

/-- On the diagonal the two overlap-restriction maps coincide: the two `≤`-witnesses
`pieces i ⊓ pieces i ≤ pieces i` are definitionally equal by proof irrelevance. -/
lemma toOvlLeft_self_eq_toOvlRight_self (i : D.index) :
    A.toOvlLeft i i = A.toOvlRight i i :=
  rfl

/-- **Support separation collapses the equalizer to the whole product**, widened.  If the
overlap colength modules vanish off the diagonal then every element of `∏ⱼ colength j` satisfies
the equalizer condition. -/
lemma gluedSubmodule_eq_top_of_separated
    (hsep : ∀ i j : D.index, i ≠ j → Subsingleton (A.ovlColength i j)) :
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

/-- **The support-separated colength↔degree bridge, algebraic half — on the WIDENED
adaptation.**  When the overlaps vanish, the `K`-dimension of the glued equalizer is the sum of
the piece-local colength dimensions.

Pure module algebra over the field: every colength is free, and the equalizer is the whole
product.  Not one step of the chart-typed proof
(`DivisorAdaptation.finrank_glued_eq_sum_of_separated`) had to change, which is the substantive
content — it confirms, rather than assumes, that this half of the degree ledger owes the
widening nothing. -/
theorem finrank_glued_eq_sum_of_separated
    (hfin : ∀ j : D.index, Module.Finite K (A.colength j))
    (hsep : ∀ i j : D.index, i ≠ j → Subsingleton (A.ovlColength i j)) :
    finrank K A.Glued = ∑ j : D.index, finrank K (A.colength j) := by
  haveI : ∀ j : D.index, Module.Free K (A.colength j) := fun j => Module.Free.of_divisionRing _ _
  haveI := hfin
  rw [LinearEquiv.finrank_eq (A.gluedTopEquiv (A.gluedSubmodule_eq_top_of_separated hsep))]
  exact Module.finrank_pi_fintype K

/-! ## The geometric half: the presentation divisor read off an arbitrary affine piece -/

section Geometric

variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **The divisor coefficient is read off any piece**, widened. -/
lemma coeffAt_eq_toAdd_ordZ_eqn (j : D.index) {z : relCurve C K}
    (hz : z ∈ D.pieces j) (hzg : z ≠ genericPoint (relCurve C K))
    (gⱼ : (relCurve C K).functionFieldˣ)
    (hgⱼ : (gⱼ : (relCurve C K).functionField)
      = ((relCurve C K).presheaf.germ (D.pieces j) (genericPoint (relCurve C K))
          (Scheme.genericPoint_mem_of_nonempty ⟨z, hz⟩)).hom (A.eqn j)) :
    Multiplicative.toAdd (Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) hzg gⱼ)
      = coeffAt hzg (Scheme.presentationDivisor K d.presentation) := by
  have hηj : genericPoint (relCurve C K) ∈ D.pieces j :=
    Scheme.genericPoint_mem_of_nonempty ⟨z, hz⟩
  obtain ⟨u, hu⟩ := A.eqn_rel j z
  have hηW : genericPoint (relCurve C K) ∈ D.pieces j ⊓ d.cover.opens z :=
    ⟨hηj, d.cover.genericPoint_mem_opens z⟩
  have hzW : z ∈ D.pieces j ⊓ d.cover.opens z := ⟨hz, d.cover.mem_opens z⟩
  have hval : (gⱼ : (relCurve C K).functionField)
      = (Scheme.germGenericUnits hηW u : (relCurve C K).functionField)
        * (d.presentation.elem z : (relCurve C K).functionField) := by
    have h := congrArg ((relCurve C K).presheaf.germ
      (D.pieces j ⊓ d.cover.opens z) (genericPoint (relCurve C K)) hηW).hom hu
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
    rw [hgⱼ, Scheme.germGenericUnits_val, Scheme.LocalEquations.presentation_elem_val]
    exact h
  have hunit : gⱼ = Scheme.germGenericUnits hηW u * d.presentation.elem z :=
    Units.ext hval
  rw [Scheme.coeffAt_presentationDivisor, hunit, map_mul,
    Scheme.ordZ_germGenericUnits K hηW u hzg hzW, one_mul]

open scoped Classical in
/-- **The per-piece degree reading**, widened. -/
lemma finrank_colength_eq_sum (j : D.index) :
    (finrank K (A.colength j) : ℤ)
      = ∑ p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
          (fun p => p.1 ∈ D.pieces j),
        coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
          * ((relCurve C K).residueDeg K p.1 : ℤ) := by
  classical
  haveI : LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
      SmoothOfRelativeDimension.smooth 1 _
    inferInstance
  by_cases hη : genericPoint (relCurve C K) ∈ D.pieces j
  · have hne : ((relCurve C K).presheaf.germ (D.pieces j) (genericPoint (relCurve C K)) hη).hom
        (A.eqn j) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp (A.eqn_regular j (genericPoint (relCurve C K)) hη)
    set gⱼ : (relCurve C K).functionFieldˣ := Units.mk0 _ hne with hgⱼdef
    have hg : (gⱼ : (relCurve C K).functionField)
        = ((relCurve C K).presheaf.germ (D.pieces j) (genericPoint (relCurve C K)) hη).hom
            (A.eqn j) := rfl
    have hout : ∀ (z : relCurve C K) (hz : z ∈ D.pieces j)
        (hzg : z ≠ genericPoint (relCurve C K)),
        (⟨z, hzg⟩ : {x : relCurve C K // x ≠ genericPoint (relCurve C K)})
          ∉ (Scheme.presentationDivisor K d.presentation).support.filter
            (fun p => p.1 ∈ D.pieces j) →
        IsUnit (((relCurve C K).presheaf.germ (D.pieces j) z hz).hom (A.eqn j)) := by
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
            (fun p => p.1 ∈ D.pieces j),
            Multiplicative.toAdd (Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) p.2 gⱼ)
              * ((relCurve C K).residueDeg K p.1 : ℤ) :=
          finrank_quotient_span_section K (D.isAffineOpen_pieces j) hη gⱼ hg _
            (fun p hp => (Finset.mem_filter.mp hp).2) hout
      _ = ∑ p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
            (fun p => p.1 ∈ D.pieces j),
            coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
              * ((relCurve C K).residueDeg K p.1 : ℤ) :=
          Finset.sum_congr rfl fun p hp => by
            rw [A.coeffAt_eq_toAdd_ordZ_eqn j (Finset.mem_filter.mp hp).2 p.2 gⱼ hg]
  · have hbot : D.pieces j ≤ ⊥ :=
      fun x hx => hη (Scheme.genericPoint_mem_of_nonempty ⟨x, hx⟩)
    haveI : Subsingleton Γ(relCurve C K, D.pieces j) :=
      (relCurve C K).subsingleton_sections_of_le_bot hbot
    haveI : Subsingleton (A.colength j) :=
      (Ideal.Quotient.mk_surjective (I := Ideal.span {A.eqn j})).subsingleton
    rw [show finrank K (A.colength j) = 0 from Module.finrank_zero_of_subsingleton,
      Nat.cast_zero,
      Finset.filter_false_of_mem fun p _ hp => by simpa using hbot hp, Finset.sum_empty]

/-- Unit germ on a piece kills the coefficient, widened. -/
lemma coeffAt_eq_zero_of_isUnit_germ (j : D.index) {z : relCurve C K} (hz : z ∈ D.pieces j)
    (hzg : z ≠ genericPoint (relCurve C K))
    (hu : IsUnit (((relCurve C K).presheaf.germ (D.pieces j) z hz).hom (A.eqn j))) :
    coeffAt hzg (Scheme.presentationDivisor K d.presentation) = 0 := by
  have hηj : genericPoint (relCurve C K) ∈ D.pieces j :=
    Scheme.genericPoint_mem_of_nonempty ⟨z, hz⟩
  have hne : ((relCurve C K).presheaf.germ (D.pieces j) (genericPoint (relCurve C K)) hηj).hom
      (A.eqn j) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (A.eqn_regular j (genericPoint (relCurve C K)) hηj)
  set gⱼ : (relCurve C K).functionFieldˣ := Units.mk0 _ hne with hgⱼdef
  have hg : (gⱼ : (relCurve C K).functionField)
      = ((relCurve C K).presheaf.germ (D.pieces j) (genericPoint (relCurve C K)) hηj).hom
          (A.eqn j) := rfl
  have hord : Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) hzg gⱼ = 1 :=
    (Scheme.isUnit_germ_iff_ordZ_eq_one K hηj (A.eqn j) gⱼ hg hz hzg).mp hu
  have h1 := A.coeffAt_eq_toAdd_ordZ_eqn j hz hzg gⱼ hg
  rw [hord, toAdd_one] at h1
  exact h1.symm

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- Overlap vanishing from separation, widened. -/
lemma subsingleton_ovlColength_of_sep
    (hsep : ∀ i j : D.index, i ≠ j → ∀ (z : relCurve C K) (hzi : z ∈ D.pieces i),
      z ∈ D.pieces j → IsUnit (((relCurve C K).presheaf.germ (D.pieces i) z hzi).hom (A.eqn i)))
    (i j : D.index) (hij : i ≠ j) : Subsingleton (A.ovlColength i j) := by
  have hunit : IsUnit (relResAlgHom C K
      (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (A.eqn i)) := by
    rw [relResAlgHom_apply]
    apply (relCurve C K).toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    rw [(relCurve C K).presheaf.germ_res_apply]
    exact hsep i j hij z hz.1 hz.2
  have htop : A.ovlIdeal i j = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert _ _)) hunit
  exact (Ideal.Quotient.subsingleton_iff).mpr htop

/-- **The colength↔degree identity, support-separated case — WIDENED.** -/
theorem deg_presentationDivisor_eq_finrank_glued
    (hsep : ∀ i j : D.index, i ≠ j → ∀ (z : relCurve C K) (hzi : z ∈ D.pieces i),
      z ∈ D.pieces j → IsUnit (((relCurve C K).presheaf.germ (D.pieces i) z hzi).hom (A.eqn i)))
    (hfin : ∀ j : D.index, Module.Finite K (A.colength j)) :
    Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K d.presentation)
      = (finrank K A.Glued : ℤ) := by
  classical
  have hW : (finrank K A.Glued : ℤ) = ∑ j : D.index, (finrank K (A.colength j) : ℤ) := by
    rw [A.finrank_glued_eq_sum_of_separated hfin
      (fun i j hij => A.subsingleton_ovlColength_of_sep hsep i j hij), Nat.cast_sum]
  -- the inner collapse: each supported point lies in a unique piece
  have hinner : ∀ p ∈ (Scheme.presentationDivisor K d.presentation).support,
      (∑ j : D.index, if p.1 ∈ D.pieces j then
        coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
          * ((relCurve C K).residueDeg K p.1 : ℤ) else 0)
        = coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
          * ((relCurve C K).residueDeg K p.1 : ℤ) := by
    intro p hp
    -- THE one substitution the widening makes: the chart-typed proof spends three lines here
    -- (`relCover_sup` with `cover₀`/`cover₁`) to produce exactly this existential.  Widened, it
    -- is the structure field `AffCoverData.cover`, extracted as `exists_mem_pieces`.
    obtain ⟨j₀, hj₀⟩ : ∃ j : D.index, p.1 ∈ D.pieces j := D.exists_mem_pieces p.1
    have huniq : ∀ b : D.index, p.1 ∈ D.pieces b → b = j₀ := by
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
          ∑ j : D.index, if p.1 ∈ D.pieces j then
            coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
              * ((relCurve C K).residueDeg K p.1 : ℤ) else 0 :=
        Finset.sum_congr rfl fun p hp => (hinner p hp).symm
    _ = ∑ j : D.index, ∑ p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
          (fun p => p.1 ∈ D.pieces j),
            coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
              * ((relCurve C K).residueDeg K p.1 : ℤ) := by
        rw [Finset.sum_comm]; simp_rw [Finset.sum_filter]
    _ = ∑ j : D.index, (finrank K (A.colength j) : ℤ) :=
        Finset.sum_congr rfl fun j _ => (A.finrank_colength_eq_sum j).symm
    _ = (finrank K A.Glued : ℤ) := hW.symm

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **The field half of the degree identity, widened.**  Over a field every module is free, so
the constant fibre rank of the glued colength module is its `K`-dimension: a widened certificate
of degree `n` forces `finrank K W(d) = n`.

Verbatim `DivisorAdaptation.IsCertified.finrank_glued` — it reads only `rankAtStalk_glued`, a
clause `AffAdaptation.IsCertified` carries unchanged (`DivisorFamilyAffAdaptation.lean`: "nothing
is added and nothing is dropped"), so the widening cannot touch it. -/
theorem IsCertified.finrank_glued {n : ℕ} (hc : A.IsCertified n) :
    finrank K A.Glued = n := by
  haveI : Module.Free K A.Glued := Module.Free.of_divisionRing K A.Glued
  have h := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := A.Glued))
    (⊥ : PrimeSpectrum K)
  rw [hc.rankAtStalk_glued ⊥] at h
  simpa using h.symm

/-- **The degree of a support-separated widened certified adaptation is exactly `n`.**

**SUPERSEDED — use `AffAdaptation.IsCertified.deg_presentationDivisor`
(`Picard/DivisorFamilyAffStalkEval.lean`) instead.**  That one has the same conclusion with **no**
`hsep` at all, for every widened adaptation, by evaluating the equalizer at stalks over the support
rather than decomposing it over the cover.  This declaration is kept because the separated route is
the shorter argument and a reader may want it, not because anything should consume it.

Two corrections to what this docstring previously claimed, both from a `work-reviewer` audit and
both material:

* it said this was "the first statement in the widened tail not conditional on an `hrank` with no
  producer (I-1109)".  Escaping *that* class was true and not worth much: `hsep` itself has **zero
  producers in conclusion position** anywhere in the project, so the obligation moved rather than
  went away;
* it said "the DD-1c backward map satisfies it by construction because its adaptations isolate the
  support points".  That sentence was inherited verbatim from the chart-typed
  `deg_divFamDivisor_of_separated` and nothing stands behind it.  Worse, `hsep` is **refutable**: it
  together with a support point in `V₀ ⊓ V₁` yields `False`.  So it holds only for fibre-confined
  systems, and the non-vacuity witness below witnesses a pair that is jointly satisfiable but not
  freely available.

`hc` is the certificate and is genuinely inhabited at every `n`
(`exists_divFam_divFamDivisor_eq`, `Picard/DivisorFamilyFieldSurj.lean:147`, whose certificate
comes from the CRT identity with no rank hypothesis).  What this declaration establishes is that
the two hypotheses SUFFICE over arbitrary affine pieces — which is what the pinned pair was
believed to be paying for, and it was not. -/
theorem deg_presentationDivisor_eq_of_isCertified {n : ℕ}
    (hsep : ∀ i j : D.index, i ≠ j → ∀ (z : relCurve C K) (hzi : z ∈ D.pieces i),
      z ∈ D.pieces j → IsUnit (((relCurve C K).presheaf.germ (D.pieces i) z hzi).hom (A.eqn i)))
    (hc : A.IsCertified n) :
    Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K d.presentation) = (n : ℤ) := by
  rw [A.deg_presentationDivisor_eq_finrank_glued hsep hc.finite_colength, hc.finrank_glued]

end Geometric

end AffAdaptation

/-! ## Non-vacuity of the pair, at every `n`

The audit standard for this project is that a discharged implication is worth what its
antecedents are worth, and I-1109 measured the specific failure mode in this tail: every widened
certificate at `n > 0` was conditional on an `hrank` with no producer at any `n > 0`, so the only
exhibited inhabitant anywhere was the zero divisor.

That is not the situation for `deg_presentationDivisor_eq_of_isCertified`, and the reason is that
its two hypotheses transport TOGETHER along the migration `DivisorAdaptation.toAff`.  The lemma
below is deliberately the joint statement rather than two separate ones: witnessing `hsep` and
`hc` at different adaptations would prove nothing about the conjunction.

What this does NOT claim: it does not say the degree ledger holds for a widened class with no
chart-typed preimage.  It says the theorem's hypotheses are simultaneously satisfiable at every
`n`, which is what separates a real hypothesis from an unsatisfiable one. -/

section NonVacuity

variable {π : C.left ⟶ P1 k} [IsAffineHom π]

/-- **Chart-typed separation is widened separation on the migrated cover.**  The migrated index
is the chart-typed index relabelled by `finSumFinEquiv`, and both `pieces` and `eqn` are that
relabelling applied, so distinctness pulls back through `reindexEquiv.injective` and the germ
statement is the same one. -/
lemma DivisorAdaptation.sep_toAff {d : (relCurve C K).LocalEquations}
    (A : DivisorAdaptation C K π d)
    (hsep : ∀ i j : A.index, i ≠ j → ∀ (z : relCurve C K) (hzi : z ∈ A.pieces i),
      z ∈ A.pieces j → IsUnit (((relCurve C K).presheaf.germ (A.pieces i) z hzi).hom (A.eqn i))) :
    ∀ i j : (A.toFinCoverData.toAffCoverData).index, i ≠ j →
      ∀ (z : relCurve C K) (hzi : z ∈ (A.toFinCoverData.toAffCoverData).pieces i),
      z ∈ (A.toFinCoverData.toAffCoverData).pieces j →
      IsUnit (((relCurve C K).presheaf.germ
        ((A.toFinCoverData.toAffCoverData).pieces i) z hzi).hom (A.toAff.eqn i)) := by
  intro i j hij z hzi hzj
  exact hsep _ _ (fun h => hij (A.reindexEquiv.injective h)) z hzi hzj

/-- **The widened degree identity is inhabited at every `n`.**  Given a chart-typed certified
family of degree `n` whose adaptation is support-separated, the migrated widened adaptation
satisfies BOTH hypotheses of `deg_presentationDivisor_eq_of_isCertified`, and the conclusion is
its degree identity — so the pair `(hsep, hc)` is satisfiable for every `n`, not only `n = 0`.

The certificate half is `CertifiedDivisorFamily.toAff`, unconditional; the separation half is
`sep_toAff` above. -/
theorem exists_widened_deg_eq_of_certifiedFamily_sep [IsIntegral (relCurve C K)]
    [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] {n : ℕ}
    (F : CertifiedDivisorFamily C K π n)
    (hsep : ∀ i j : F.adaptation.index, i ≠ j → ∀ (z : relCurve C K)
      (hzi : z ∈ F.adaptation.pieces i), z ∈ F.adaptation.pieces j →
      IsUnit (((relCurve C K).presheaf.germ (F.adaptation.pieces i) z hzi).hom
        (F.adaptation.eqn i))) :
    Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K F.toAff.eqns.presentation)
      = (n : ℤ) :=
  F.toAff.adaptation.deg_presentationDivisor_eq_of_isCertified
    (F.adaptation.sep_toAff hsep) F.toAff.certified

end NonVacuity

end AlgebraicGeometry
