/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.StalkColength
import AlgebraicJacobian.Picard.DivisorFamilyFieldDegree
import AlgebraicJacobian.Picard.DivisorStalkIdeal

/-!
# Stalk evaluation of the colength modules of a divisor adaptation

The chart-independent local apparatus behind the general colength↔degree identity
(`AlgebraicJacobian.Picard.DivisorFamilyFieldCRT`): over the field `K`, the colength
modules of a divisor adaptation evaluate into the stalk quotients `𝒪_z ⧸ I_d(z)` cut by the
(adaptation-free) stalk ideals of `d` — the local models of the CRT decomposition of the
glued equalizer `W(d)`.

* `DivisorAdaptation.span_germ_eqn_eq_stalkIdeal` — every piece equation generates the
  stalk ideal of `d` at each of its points (the pointwise clause `eqn_rel`).
* `DivisorAdaptation.stalkColEval`, `DivisorAdaptation.ovlStalkColEval` — the stalk
  evaluations `Γ(D(h_j))/(f_j) →ₐ[K] 𝒪_z ⧸ I_d(z)` of the chart-local and overlap
  colength modules, intertwining the equalizer arrows
  (`ovlStalkColEval_toOvlLeft`/`_toOvlRight`).
* `DivisorAdaptation.stalkColEval_glued` — **chart independence on the equalizer**: two
  pieces seeing the same point read the same stalk value on `W(d)` — the resolution of the
  cross-chart double counting of the Mayer–Vietoris wall (I-0179).
* `mem_span_singleton_of_isUnit_or_mem` — stalk-locality against a support: membership in
  the span of a germwise-regular section follows from membership at its non-unit closed
  points.
* `DivisorAdaptation.moduleFinite_stalkQuot`,
  `DivisorAdaptation.finrank_stalkQuot_eq_coeffAt_mul` — **the pointwise divisor
  dictionary** `finrank K (𝒪_z ⧸ I_d(z)) = coeff_z(div d) · [κ(z) : K]`, from the stalk
  colength dictionary (`AlgebraicJacobian.RiemannRoch.StalkColength`) through the
  coefficient and multiplicity legs.

The `K`-structures are the house local instances `Scheme.overSectionsAlgebra` (sections)
and `Scheme.stalkOverAlgebra` (stalks); consumers must activate the same instances.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open Module (finrank)

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.stalkOverAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {K : Type u} [Field K] [Algebra k K]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

namespace DivisorAdaptation

variable {d : (relCurve C K).LocalEquations} (A : DivisorAdaptation C K π d)

/-! ## Piece equations generate the stalk ideals -/

/-- Two elements differing by a unit factor span the same ideal (file-local copy of the
`DivisorStalkIdeal` private lemma). -/
private lemma span_eq_of_unit_mul {S : Type u} [CommRing S] {a b c : S} (hc : IsUnit c)
    (h : a = c * b) : Ideal.span {a} = Ideal.span {b} := by
  obtain ⟨u, rfl⟩ := hc
  refine le_antisymm (Ideal.span_singleton_le_span_singleton.mpr ⟨u, by rw [h, mul_comm]⟩)
    (Ideal.span_singleton_le_span_singleton.mpr ⟨(↑u⁻¹ : S), ?_⟩)
  rw [h, mul_comm (u : S) b, mul_assoc, Units.mul_inv, mul_one]

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **A piece equation generates the stalk ideal of `d` at each of its points**: the
pointwise clause `eqn_rel j z` presents the germ of `f_j` as a unit germ times the germ of
`d`'s equation at the member of `z` itself, whose span is the (adaptation-free) stalk
ideal. -/
lemma span_germ_eqn_eq_stalkIdeal (j : A.index) {z : relCurve C K} (hz : z ∈ A.pieces j) :
    Ideal.span {((relCurve C K).presheaf.germ (A.pieces j) z hz).hom (A.eqn j)}
      = d.stalkIdeal z := by
  obtain ⟨u, hu⟩ := A.eqn_rel j z
  have hzW : z ∈ A.pieces j ⊓ d.cover.opens z := ⟨hz, d.cover.mem_opens z⟩
  have hgerm := congrArg ((relCurve C K).presheaf.germ
    (A.pieces j ⊓ d.cover.opens z) z hzW).hom hu
  rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hgerm
  exact span_eq_of_unit_mul (u.isUnit.map ((relCurve C K).presheaf.germ
    (A.pieces j ⊓ d.cover.opens z) z hzW).hom) hgerm

/-- Where the divisor coefficient vanishes, the piece equation is a stalk unit (the
`hout` core of the separated assembly, factored out): the order of `f_j` at `z` reads the
coefficient (`coeffAt_eq_toAdd_ordZ_eqn`), and trivial order means unit germ
(`isUnit_germ_iff_ordZ_eq_one`). -/
lemma isUnit_germ_eqn_of_coeffAt_eq_zero (j : A.index) {z : relCurve C K}
    (hz : z ∈ A.pieces j) (hzg : z ≠ genericPoint (relCurve C K))
    (h0 : coeffAt hzg (Scheme.presentationDivisor K d.presentation) = 0) :
    IsUnit (((relCurve C K).presheaf.germ (A.pieces j) z hz).hom (A.eqn j)) := by
  have hη : genericPoint (relCurve C K) ∈ A.pieces j :=
    Scheme.genericPoint_mem_of_nonempty ⟨z, hz⟩
  have hne : ((relCurve C K).presheaf.germ (A.pieces j) (genericPoint (relCurve C K))
      hη).hom (A.eqn j) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (A.eqn_regular j (genericPoint (relCurve C K)) hη)
  set g : (relCurve C K).functionFieldˣ := Units.mk0 _ hne with hgdef
  have hg : (g : (relCurve C K).functionField)
      = ((relCurve C K).presheaf.germ (A.pieces j) (genericPoint (relCurve C K)) hη).hom
          (A.eqn j) := rfl
  have h1 := A.coeffAt_eq_toAdd_ordZ_eqn j hz hzg g hg
  rw [h0] at h1
  have hord : Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) hzg g = 1 :=
    Multiplicative.toAdd.injective (by rw [h1]; exact toAdd_one.symm)
  exact (Scheme.isUnit_germ_iff_ordZ_eq_one K hη (A.eqn j) g hg hz hzg).mpr hord

omit [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **Stalk-locality against the support**: a section of an open of the curve lies in the
span of a germwise-regular section `b` as soon as it does so at every closed point where
`b` is not a unit — at unit points and at the generic point (a field stalk) the span is
everything, and stalkwise membership globalizes
(`Scheme.mem_span_singleton_of_forall_germ`). -/
lemma mem_span_singleton_of_isUnit_or_mem {V : (relCurve C K).Opens}
    {b t : Γ(relCurve C K, V)}
    (hreg : ∀ (z : relCurve C K) (hz : z ∈ V),
      ((relCurve C K).presheaf.germ V z hz).hom b
        ∈ nonZeroDivisors ((relCurve C K).presheaf.stalk z))
    (h : ∀ (z : relCurve C K) (hz : z ∈ V), z ≠ genericPoint (relCurve C K) →
      IsUnit (((relCurve C K).presheaf.germ V z hz).hom b) ∨
        ((relCurve C K).presheaf.germ V z hz).hom t
          ∈ Ideal.span {((relCurve C K).presheaf.germ V z hz).hom b}) :
    t ∈ Ideal.span {b} := by
  refine Scheme.mem_span_singleton_of_forall_germ hreg fun z hz => ?_
  by_cases hzg : z = genericPoint (relCurve C K)
  · subst hzg
    have hne : ((relCurve C K).presheaf.germ V _ hz).hom b ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp (hreg _ hz)
    have hu : IsUnit (((relCurve C K).presheaf.germ V _ hz).hom b) :=
      (Units.mk0 (G₀ := (relCurve C K).functionField) _ hne).isUnit
    rw [Ideal.span_singleton_eq_top.mpr hu]
    exact Submodule.mem_top
  · rcases h z hz hzg with hu | hmem
    · rw [Ideal.span_singleton_eq_top.mpr hu]
      exact Submodule.mem_top
    · exact hmem

/-! ## The stalk evaluations of the colength modules -/

/-- **The stalk evaluation of a chart-local colength module** at a point of the piece:
`Γ(D(h_j))/(f_j) →ₐ[K] 𝒪_z ⧸ I_d(z)`, induced by the germ.  Well defined because the piece
equation generates the stalk ideal (`span_germ_eqn_eq_stalkIdeal`); the target is
adaptation-free and chart-free — the local model of the CRT decomposition. -/
noncomputable def stalkColEval (j : A.index) {z : relCurve C K} (hz : z ∈ A.pieces j) :
    A.colength j →ₐ[K] ((relCurve C K).presheaf.stalk z ⧸ d.stalkIdeal z) :=
  Ideal.Quotient.liftₐ (Ideal.span {A.eqn j})
    ((Ideal.Quotient.mkₐ K (d.stalkIdeal z)).comp (Scheme.germAlgHom K hz))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      simp only [AlgHom.comp_apply, map_mul]
      have hmem : ((relCurve C K).presheaf.germ (A.pieces j) z hz).hom (A.eqn j)
          ∈ d.stalkIdeal z := by
        rw [← A.span_germ_eqn_eq_stalkIdeal j hz]
        exact Ideal.mem_span_singleton_self _
      rw [show (Scheme.germAlgHom K hz) (A.eqn j)
          = ((relCurve C K).presheaf.germ (A.pieces j) z hz).hom (A.eqn j) from rfl,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_mul])

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
@[simp]
lemma stalkColEval_mk (j : A.index) {z : relCurve C K} (hz : z ∈ A.pieces j)
    (t : Γ(relCurve C K, A.pieces j)) :
    A.stalkColEval j hz (Ideal.Quotient.mk (Ideal.span {A.eqn j}) t)
      = Ideal.Quotient.mk (d.stalkIdeal z)
          (((relCurve C K).presheaf.germ (A.pieces j) z hz).hom t) :=
  rfl

/-- The overlap variant: `Γ(D(h_i) ⊓ D(h_j))/(f_i, f_j) →ₐ[K] 𝒪_z ⧸ I_d(z)` at a point of
the overlap — both overlap generators germ into the stalk ideal. -/
noncomputable def ovlStalkColEval (i j : A.index) {z : relCurve C K}
    (hz : z ∈ A.pieces i ⊓ A.pieces j) :
    A.ovlColength i j →ₐ[K] ((relCurve C K).presheaf.stalk z ⧸ d.stalkIdeal z) :=
  Ideal.Quotient.liftₐ (A.ovlIdeal i j)
    ((Ideal.Quotient.mkₐ K (d.stalkIdeal z)).comp (Scheme.germAlgHom K hz))
    (by
      intro a ha
      have hgen : ∀ x ∈ ({relResAlgHom C K
            (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i) (A.eqn i),
          relResAlgHom C K
            (inf_le_right : A.pieces i ⊓ A.pieces j ≤ A.pieces j) (A.eqn j)} :
            Set Γ(relCurve C K, A.pieces i ⊓ A.pieces j)),
          ((Ideal.Quotient.mkₐ K (d.stalkIdeal z)).comp (Scheme.germAlgHom K hz)) x = 0 := by
        rintro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · have hmem : ((relCurve C K).presheaf.germ (A.pieces i) z hz.1).hom (A.eqn i)
              ∈ d.stalkIdeal z := by
            rw [← A.span_germ_eqn_eq_stalkIdeal i hz.1]
            exact Ideal.mem_span_singleton_self _
          rw [AlgHom.comp_apply,
            show (Scheme.germAlgHom K hz) (relResAlgHom C K inf_le_left (A.eqn i))
              = ((relCurve C K).presheaf.germ (A.pieces i ⊓ A.pieces j) z hz).hom
                  (((relCurve C K).presheaf.map (homOfLE inf_le_left).op).hom (A.eqn i))
              from rfl,
            TopCat.Presheaf.germ_res_apply, Ideal.Quotient.mkₐ_eq_mk,
            Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
        · have hmem : ((relCurve C K).presheaf.germ (A.pieces j) z hz.2).hom (A.eqn j)
              ∈ d.stalkIdeal z := by
            rw [← A.span_germ_eqn_eq_stalkIdeal j hz.2]
            exact Ideal.mem_span_singleton_self _
          rw [AlgHom.comp_apply,
            show (Scheme.germAlgHom K hz) (relResAlgHom C K inf_le_right (A.eqn j))
              = ((relCurve C K).presheaf.germ (A.pieces i ⊓ A.pieces j) z hz).hom
                  (((relCurve C K).presheaf.map (homOfLE inf_le_right).op).hom (A.eqn j))
              from rfl,
            TopCat.Presheaf.germ_res_apply, Ideal.Quotient.mkₐ_eq_mk,
            Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
      have hle : A.ovlIdeal i j ≤ RingHom.ker
          ((Ideal.Quotient.mkₐ K (d.stalkIdeal z)).comp (Scheme.germAlgHom K hz)) := by
        rw [Ideal.span_le]
        intro x hx
        rw [SetLike.mem_coe, RingHom.mem_ker]
        exact hgen x hx
      exact hle ha)

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
lemma ovlStalkColEval_toOvlLeft (i j : A.index) {z : relCurve C K}
    (hz : z ∈ A.pieces i ⊓ A.pieces j) (x : A.colength i) :
    A.ovlStalkColEval i j hz (A.toOvlLeft i j x) = A.stalkColEval i hz.1 x := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (d.stalkIdeal z)
      (((relCurve C K).presheaf.germ (A.pieces i ⊓ A.pieces j) z hz).hom
        (((relCurve C K).presheaf.map (homOfLE inf_le_left).op).hom t))
    = Ideal.Quotient.mk (d.stalkIdeal z)
        (((relCurve C K).presheaf.germ (A.pieces i) z hz.1).hom t)
  rw [TopCat.Presheaf.germ_res_apply]

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
lemma ovlStalkColEval_toOvlRight (i j : A.index) {z : relCurve C K}
    (hz : z ∈ A.pieces i ⊓ A.pieces j) (x : A.colength j) :
    A.ovlStalkColEval i j hz (A.toOvlRight i j x) = A.stalkColEval j hz.2 x := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (d.stalkIdeal z)
      (((relCurve C K).presheaf.germ (A.pieces i ⊓ A.pieces j) z hz).hom
        (((relCurve C K).presheaf.map (homOfLE inf_le_right).op).hom t))
    = Ideal.Quotient.mk (d.stalkIdeal z)
        (((relCurve C K).presheaf.germ (A.pieces j) z hz.2).hom t)
  rw [TopCat.Presheaf.germ_res_apply]

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **The equalizer condition makes stalk evaluation chart-independent**: for an element of
the glued submodule, any two pieces seeing the point `z` read the SAME value in
`𝒪_z ⧸ I_d(z)` — the resolution of the cross-chart double counting. -/
lemma stalkColEval_glued {s : A.chartProd} (hs : s ∈ A.gluedSubmodule) (i j : A.index)
    {z : relCurve C K} (hzi : z ∈ A.pieces i) (hzj : z ∈ A.pieces j) :
    A.stalkColEval i hzi (s i) = A.stalkColEval j hzj (s j) := by
  have h := (A.mem_gluedSubmodule_iff s).mp hs (i, j)
  rw [← A.ovlStalkColEval_toOvlLeft i j ⟨hzi, hzj⟩ (s i), h,
    A.ovlStalkColEval_toOvlRight i j ⟨hzi, hzj⟩ (s j)]

/-! ## The pointwise stalk dictionary along the divisor -/

omit [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- The piece equation is a nonzero section (its germ at `η` is regular in the field
stalk). -/
lemma eqn_ne_zero (j : A.index) (hη : genericPoint (relCurve C K) ∈ A.pieces j) :
    A.eqn j ≠ 0 := by
  intro h0
  have hne := mem_nonZeroDivisors_iff_ne_zero.mp
    (A.eqn_regular j (genericPoint (relCurve C K)) hη)
  exact hne (by rw [h0, map_zero])

omit [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **Finiteness of the stalk colength along the divisor**: `𝒪_z ⧸ I_d(z)` is a finite
`K`-module at every closed point of a piece. -/
lemma moduleFinite_stalkQuot (j : A.index) {z : relCurve C K} (hz : z ∈ A.pieces j)
    (hzg : z ≠ genericPoint (relCurve C K)) :
    Module.Finite K ((relCurve C K).presheaf.stalk z ⧸ d.stalkIdeal z) := by
  haveI : LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
      SmoothOfRelativeDimension.smooth 1 _
    inferInstance
  have hη : genericPoint (relCurve C K) ∈ A.pieces j :=
    Scheme.genericPoint_mem_of_nonempty ⟨z, hz⟩
  haveI : IsDedekindDomain Γ(relCurve C K, A.pieces j) :=
    isDedekindDomain_section K (A.isAffineOpen_pieces j) hη
  have h := moduleFinite_stalkQuot_span_germ K (A.isAffineOpen_pieces j) hz hzg
    (A.eqn_ne_zero j hη)
  rwa [A.span_germ_eqn_eq_stalkIdeal j hz] at h

/-- **The pointwise divisor dictionary**: at a closed point `z` of a piece, the
`K`-colength of the stalk ideal is the divisor coefficient weighted by the residue degree:

`finrank K (𝒪_z ⧸ I_d(z)) = coeff_z(div d) · [κ(z) : K]`.

The stalk colength dictionary (`finrank_stalkQuot_span_germ`) read through the coefficient
(`coeffAt_eq_toAdd_ordZ_eqn`) and multiplicity (`toAdd_ordZ_eq_count_factors`) legs. -/
lemma finrank_stalkQuot_eq_coeffAt_mul (j : A.index) {z : relCurve C K}
    (hz : z ∈ A.pieces j) (hzg : z ≠ genericPoint (relCurve C K)) :
    (finrank K ((relCurve C K).presheaf.stalk z ⧸ d.stalkIdeal z) : ℤ)
      = coeffAt hzg (Scheme.presentationDivisor K d.presentation)
          * ((relCurve C K).residueDeg K z : ℤ) := by
  haveI : LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
      SmoothOfRelativeDimension.smooth 1 _
    inferInstance
  have hη : genericPoint (relCurve C K) ∈ A.pieces j :=
    Scheme.genericPoint_mem_of_nonempty ⟨z, hz⟩
  haveI : IsDedekindDomain Γ(relCurve C K, A.pieces j) :=
    isDedekindDomain_section K (A.isAffineOpen_pieces j) hη
  have hf : A.eqn j ≠ 0 := A.eqn_ne_zero j hη
  have hne : ((relCurve C K).presheaf.germ (A.pieces j) (genericPoint (relCurve C K))
      hη).hom (A.eqn j) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (A.eqn_regular j (genericPoint (relCurve C K)) hη)
  set g : (relCurve C K).functionFieldˣ := Units.mk0 _ hne with hgdef
  have hg : (g : (relCurve C K).functionField)
      = ((relCurve C K).presheaf.germ (A.pieces j) (genericPoint (relCurve C K)) hη).hom
          (A.eqn j) := rfl
  have hcoeff := A.coeffAt_eq_toAdd_ordZ_eqn j hz hzg g hg
  have hcount := toAdd_ordZ_eq_count_factors K (A.isAffineOpen_pieces j) hη hz hzg hf g hg
  have hfr : finrank K ((relCurve C K).presheaf.stalk z ⧸ d.stalkIdeal z)
      = Multiset.count ((A.isAffineOpen_pieces j).primeIdealOf ⟨z, hz⟩).asIdeal
          (UniqueFactorizationMonoid.factors (Ideal.span {A.eqn j}))
        * (relCurve C K).residueDeg K z := by
    have h := finrank_stalkQuot_span_germ K (A.isAffineOpen_pieces j) hz hzg hf
    rwa [A.span_germ_eqn_eq_stalkIdeal j hz] at h
  have hcc : (Multiset.count ((A.isAffineOpen_pieces j).primeIdealOf ⟨z, hz⟩).asIdeal
      (UniqueFactorizationMonoid.factors (Ideal.span {A.eqn j})) : ℤ)
      = coeffAt hzg (Scheme.presentationDivisor K d.presentation) :=
    hcount.symm.trans hcoeff
  rw [hfr]
  push_cast
  rw [hcc]


end DivisorAdaptation

end AlgebraicGeometry
