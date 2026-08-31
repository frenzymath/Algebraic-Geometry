/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFieldDegree
import AlgebraicJacobian.Picard.DivisorFamilyStalkEval
import AlgebraicJacobian.Picard.DivisorFamilyFieldCRT

/-!
# The colength↔degree identity on the WIDENED adaptation, with NO separation hypothesis

`Picard/DivisorFamilyAffFieldDegree.lean` ports the *support-separated* colength↔degree identity
to `AffAdaptation`.  That route works, but its `hsep` is a real restriction and it has no
producer: a `work-reviewer` audit this session closed a refutation showing that `hsep` together
with a support point in `V₀ ⊓ V₁` gives `False`, and a conclusion-position census over the whole
project found zero producers of either separation shape.  So the separated identity's
"the DD-1c backward map satisfies it by construction" was inherited prose with nothing behind it.

The chart-typed side already retired that route.  `DivisorAdaptation.deg_presentationDivisor`
(`Picard/DivisorFamilyFieldCRT.lean:324`) proves the identity for **every** adaptation, with no
separation hypothesis at all, by evaluating the glued equalizer at stalks over the support
(`gluedStalkEval` bijective) instead of decomposing it over the cover.  This file ports that
route, which is the one a consumer should use.

## Why this port is cheaper than it looks

The stalk route touches the cover *less* than the separated route did, not more.  Measured:
`Picard/DivisorFamilyStalkEval.lean` contains **zero** chart-specific tokens, and
`Picard/DivisorFamilyFieldCRT.lean` contains exactly four, all inside one block
(`:181-184`) whose entire output is "every point lies in some piece" — the same
`AffCoverData.exists_mem_pieces` substitution that carried the separated port.  Every member the
engine reads (`pieces`, `index`, `eqn`, `eqn_regular`, `colength`, `ovlColength`, `ovlIdeal`,
`chartProd`, `Glued`, `gluedSubmodule`, `mem_gluedSubmodule_iff`) is carried by `AffAdaptation`
under the same name.

## Main declarations

* `AffAdaptation.span_germ_eqn_eq_stalkIdeal` — a piece equation generates `d`'s stalk ideal at
  each of its points, so the piece-local data is adaptation-free at stalks.
* `AffAdaptation.isUnit_germ_eqn_of_coeffAt_eq_zero` — vanishing coefficient means unit germ.
* `AffAdaptation.stalkColEval`, `stalkColEval_mk` — the piece colength evaluated at a stalk.
* `AffAdaptation.ovlStalkColEval`, `ovlStalkColEval_toOvlLeft`/`_toOvlRight` — the overlap
  variant, intertwining the two equalizer arrows.
* `AffAdaptation.stalkColEval_glued` — **piece independence on the equalizer**: two pieces
  seeing the same point read the same stalk value on `W(d)`.
* `AffAdaptation.eqn_ne_zero`, `moduleFinite_stalkQuot`, `finrank_stalkQuot_eq_coeffAt_mul` —
  the pointwise divisor dictionary `finrank K (𝒪_z ⧸ I_d(z)) = coeff_z(div d) · [κ(z) : K]`.
* `AffAdaptation.pieceStalkEval`, `pieceStalkEval_injective`, `pieceStalkEval_bijective` — the
  per-piece CRT decomposition.
* `AffAdaptation.gluedStalkEval`, `gluedStalkEval_injective`, `gluedStalkEval_surjective` — the
  glued CRT decomposition `W(d) ≅ Π_{z ∈ supp} 𝒪_z ⧸ I_d(z)`.
* `AffAdaptation.deg_presentationDivisor` — **the identity with no `hsep`**, for every widened
  adaptation.
* `AffAdaptation.IsCertified.deg_presentationDivisor` — `deg D = n`, unconditionally on the cover.

## What this does NOT close

`hdegAff` (`Picard/DivisorFamilyAffAbel.lean`) is the *Abel-value* ledger and remains an explicit
hypothesis there; the distance to it is the widened transport from the presentation divisor's
degree to the Picard class.  Nothing here touches `rep` or any antecedent of the atlas assembly.

**The first two sentences are stale as of 2026-07-30** (review-ajcr, I-1197; working proof at
I-1196).  `hdegAff` is still written as a hypothesis at `…AffAbel.lean:309`, but it is *provable*
from what this file lands plus the widened field collapse, and the "distance" sentence under-counts
by one input: the chart-typed `classDeg_picClass` consumes the CRT identity this file supplies
**and** `DivFam.exists_toZar_eq` (`Picard/DivSchemeAbel.lean:77`), the collapse over a field.  Only
the CRT half was tracked in any pricing, and the collapse was the one with no widened analogue —
which is why the step read as the expensive one.  It transports verbatim.  The last sentence
stands: `rep`, `IsChartUniv` and Zariski-local surjectivity of `Sigma.desc f` are untouched.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); pin in-file. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open Module (finrank)

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {K : Type u} [Field K] [Algebra k K]

namespace AffAdaptation

variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

variable {D : AffCoverData C K} {d : (relCurve C K).LocalEquations} (A : AffAdaptation D d)

/-- Two elements differing by a unit factor span the same ideal.  A pure five-line commutative
ring fact, copied because both existing statements of it are `private` — in
`Picard/DivisorStalkIdeal.lean:155` (as `Scheme.LocalEquations.span_eq_of_unit_mul`) and in
`Picard/DivisorFamilyStalkEval.lean:69` (as `DivisorAdaptation.span_eq_of_unit_mul`, itself
labelled a file-local copy of the first).  `private` makes them invisible to name search as well
as to use, so this is the third copy rather than the second; the right fix is to make one of them
public, which is a change to another lane's file and not mine to make mid-session. -/
private lemma span_eq_of_unit_mul {S : Type u} [CommRing S] {a b c : S} (hc : IsUnit c)
    (h : a = c * b) : Ideal.span {a} = Ideal.span {b} := by
  obtain ⟨u, rfl⟩ := hc
  refine le_antisymm (Ideal.span_singleton_le_span_singleton.mpr ⟨u, by rw [h, mul_comm]⟩)
    (Ideal.span_singleton_le_span_singleton.mpr ⟨(↑u⁻¹ : S), ?_⟩)
  rw [h, mul_comm (u : S) b, mul_assoc, Units.mul_inv, mul_one]

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **A piece equation generates the stalk ideal of `d` at each of its points**, widened. -/
lemma span_germ_eqn_eq_stalkIdeal (j : D.index) {z : relCurve C K} (hz : z ∈ D.pieces j) :
    Ideal.span {((relCurve C K).presheaf.germ (D.pieces j) z hz).hom (A.eqn j)}
      = d.stalkIdeal z := by
  obtain ⟨u, hu⟩ := A.eqn_rel j z
  have hzW : z ∈ D.pieces j ⊓ d.cover.opens z := ⟨hz, d.cover.mem_opens z⟩
  have hgerm := congrArg ((relCurve C K).presheaf.germ
    (D.pieces j ⊓ d.cover.opens z) z hzW).hom hu
  rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hgerm
  exact span_eq_of_unit_mul (u.isUnit.map ((relCurve C K).presheaf.germ
    (D.pieces j ⊓ d.cover.opens z) z hzW).hom) hgerm

/-- Where the divisor coefficient vanishes, the piece equation is a stalk unit, widened. -/
lemma isUnit_germ_eqn_of_coeffAt_eq_zero (j : D.index) {z : relCurve C K}
    (hz : z ∈ D.pieces j) (hzg : z ≠ genericPoint (relCurve C K))
    (h0 : coeffAt hzg (Scheme.presentationDivisor K d.presentation) = 0) :
    IsUnit (((relCurve C K).presheaf.germ (D.pieces j) z hz).hom (A.eqn j)) := by
  have hη : genericPoint (relCurve C K) ∈ D.pieces j :=
    Scheme.genericPoint_mem_of_nonempty ⟨z, hz⟩
  have hne : ((relCurve C K).presheaf.germ (D.pieces j) (genericPoint (relCurve C K))
      hη).hom (A.eqn j) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (A.eqn_regular j (genericPoint (relCurve C K)) hη)
  set g : (relCurve C K).functionFieldˣ := Units.mk0 _ hne with hgdef
  have hg : (g : (relCurve C K).functionField)
      = ((relCurve C K).presheaf.germ (D.pieces j) (genericPoint (relCurve C K)) hη).hom
          (A.eqn j) := rfl
  have h1 := A.coeffAt_eq_toAdd_ordZ_eqn j hz hzg g hg
  rw [h0] at h1
  have hord : Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) hzg g = 1 :=
    Multiplicative.toAdd.injective (by rw [h1]; exact toAdd_one.symm)
  exact (Scheme.isUnit_germ_iff_ordZ_eq_one K hη (A.eqn j) g hg hz hzg).mpr hord

/-! ## The stalk evaluations of the widened colength modules

Ported from `DivisorAdaptation.stalkColEval` and friends
(`Picard/DivisorFamilyStalkEval.lean:150-269`).  The stalk `K`-algebra structure is the house
local instance `Scheme.stalkOverAlgebra`, activated here rather than at the top of the file so
the three already-landed section-only lemmas above are elaborated in the environment they were
written in. -/

attribute [local instance] Scheme.stalkOverAlgebra

/-- **The stalk evaluation of a piece-local colength module** at a point of the piece:
`Γ(pieces j)/(f_j) →ₐ[K] 𝒪_z ⧸ I_d(z)`, induced by the germ.  Well defined because the piece
equation generates the stalk ideal (`span_germ_eqn_eq_stalkIdeal`); the target is
adaptation-free *and cover-free* — it mentions neither a chart nor a piece, which is why the
whole stalk route transports to the widened carrier unchanged. -/
noncomputable def stalkColEval (j : D.index) {z : relCurve C K} (hz : z ∈ D.pieces j) :
    A.colength j →ₐ[K] ((relCurve C K).presheaf.stalk z ⧸ d.stalkIdeal z) :=
  Ideal.Quotient.liftₐ (Ideal.span {A.eqn j})
    ((Ideal.Quotient.mkₐ K (d.stalkIdeal z)).comp (Scheme.germAlgHom K hz))
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      simp only [AlgHom.comp_apply, map_mul]
      have hmem : ((relCurve C K).presheaf.germ (D.pieces j) z hz).hom (A.eqn j)
          ∈ d.stalkIdeal z := by
        rw [← A.span_germ_eqn_eq_stalkIdeal j hz]
        exact Ideal.mem_span_singleton_self _
      rw [show (Scheme.germAlgHom K hz) (A.eqn j)
          = ((relCurve C K).presheaf.germ (D.pieces j) z hz).hom (A.eqn j) from rfl,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_mul])

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
@[simp]
lemma stalkColEval_mk (j : D.index) {z : relCurve C K} (hz : z ∈ D.pieces j)
    (t : Γ(relCurve C K, D.pieces j)) :
    A.stalkColEval j hz (Ideal.Quotient.mk (Ideal.span {A.eqn j}) t)
      = Ideal.Quotient.mk (d.stalkIdeal z)
          (((relCurve C K).presheaf.germ (D.pieces j) z hz).hom t) :=
  rfl

/-- The overlap variant: `Γ(pieces i ⊓ pieces j)/(f_i, f_j) →ₐ[K] 𝒪_z ⧸ I_d(z)` at a point of
the overlap — both overlap generators germ into the stalk ideal. -/
noncomputable def ovlStalkColEval (i j : D.index) {z : relCurve C K}
    (hz : z ∈ D.pieces i ⊓ D.pieces j) :
    A.ovlColength i j →ₐ[K] ((relCurve C K).presheaf.stalk z ⧸ d.stalkIdeal z) :=
  Ideal.Quotient.liftₐ (A.ovlIdeal i j)
    ((Ideal.Quotient.mkₐ K (d.stalkIdeal z)).comp (Scheme.germAlgHom K hz))
    (by
      intro a ha
      have hgen : ∀ x ∈ ({relResAlgHom C K
            (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (A.eqn i),
          relResAlgHom C K
            (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j) (A.eqn j)} :
            Set Γ(relCurve C K, D.pieces i ⊓ D.pieces j)),
          ((Ideal.Quotient.mkₐ K (d.stalkIdeal z)).comp (Scheme.germAlgHom K hz)) x = 0 := by
        rintro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · have hmem : ((relCurve C K).presheaf.germ (D.pieces i) z hz.1).hom (A.eqn i)
              ∈ d.stalkIdeal z := by
            rw [← A.span_germ_eqn_eq_stalkIdeal i hz.1]
            exact Ideal.mem_span_singleton_self _
          rw [AlgHom.comp_apply,
            show (Scheme.germAlgHom K hz) (relResAlgHom C K inf_le_left (A.eqn i))
              = ((relCurve C K).presheaf.germ (D.pieces i ⊓ D.pieces j) z hz).hom
                  (((relCurve C K).presheaf.map (homOfLE inf_le_left).op).hom (A.eqn i))
              from rfl,
            TopCat.Presheaf.germ_res_apply, Ideal.Quotient.mkₐ_eq_mk,
            Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
        · have hmem : ((relCurve C K).presheaf.germ (D.pieces j) z hz.2).hom (A.eqn j)
              ∈ d.stalkIdeal z := by
            rw [← A.span_germ_eqn_eq_stalkIdeal j hz.2]
            exact Ideal.mem_span_singleton_self _
          rw [AlgHom.comp_apply,
            show (Scheme.germAlgHom K hz) (relResAlgHom C K inf_le_right (A.eqn j))
              = ((relCurve C K).presheaf.germ (D.pieces i ⊓ D.pieces j) z hz).hom
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
lemma ovlStalkColEval_toOvlLeft (i j : D.index) {z : relCurve C K}
    (hz : z ∈ D.pieces i ⊓ D.pieces j) (x : A.colength i) :
    A.ovlStalkColEval i j hz (A.toOvlLeft i j x) = A.stalkColEval i hz.1 x := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (d.stalkIdeal z)
      (((relCurve C K).presheaf.germ (D.pieces i ⊓ D.pieces j) z hz).hom
        (((relCurve C K).presheaf.map (homOfLE inf_le_left).op).hom t))
    = Ideal.Quotient.mk (d.stalkIdeal z)
        (((relCurve C K).presheaf.germ (D.pieces i) z hz.1).hom t)
  rw [TopCat.Presheaf.germ_res_apply]

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
lemma ovlStalkColEval_toOvlRight (i j : D.index) {z : relCurve C K}
    (hz : z ∈ D.pieces i ⊓ D.pieces j) (x : A.colength j) :
    A.ovlStalkColEval i j hz (A.toOvlRight i j x) = A.stalkColEval j hz.2 x := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (d.stalkIdeal z)
      (((relCurve C K).presheaf.germ (D.pieces i ⊓ D.pieces j) z hz).hom
        (((relCurve C K).presheaf.map (homOfLE inf_le_right).op).hom t))
    = Ideal.Quotient.mk (d.stalkIdeal z)
        (((relCurve C K).presheaf.germ (D.pieces j) z hz.2).hom t)
  rw [TopCat.Presheaf.germ_res_apply]

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **The equalizer condition makes stalk evaluation piece-independent**: for an element of
the glued submodule, any two pieces seeing the point `z` read the SAME value in
`𝒪_z ⧸ I_d(z)`.  On the chart-typed side this was the resolution of the cross-chart double
counting; widened, "chart" is simply "piece" and the statement is the same one — the
`mem_gluedSubmodule_iff` clause `AffAdaptation` carries unchanged. -/
lemma stalkColEval_glued {s : A.chartProd} (hs : s ∈ A.gluedSubmodule) (i j : D.index)
    {z : relCurve C K} (hzi : z ∈ D.pieces i) (hzj : z ∈ D.pieces j) :
    A.stalkColEval i hzi (s i) = A.stalkColEval j hzj (s j) := by
  have h := (A.mem_gluedSubmodule_iff s).mp hs (i, j)
  rw [← A.ovlStalkColEval_toOvlLeft i j ⟨hzi, hzj⟩ (s i), h,
    A.ovlStalkColEval_toOvlRight i j ⟨hzi, hzj⟩ (s j)]

/-! ## The pointwise stalk dictionary along the divisor -/

omit [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- The piece equation is a nonzero section (its germ at `η` is regular in the field
stalk). -/
lemma eqn_ne_zero (j : D.index) (hη : genericPoint (relCurve C K) ∈ D.pieces j) :
    A.eqn j ≠ 0 := by
  intro h0
  have hne := mem_nonZeroDivisors_iff_ne_zero.mp
    (A.eqn_regular j (genericPoint (relCurve C K)) hη)
  exact hne (by rw [h0, map_zero])

omit [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/- The chart-typed original indexes by `A.index`, which auto-includes `A`; the widened
statement indexes by `D.index` (the substitution rule) and its conclusion is
adaptation-free, so `A` has to be included by hand. -/
include A in
/-- **Finiteness of the stalk colength along the divisor**: `𝒪_z ⧸ I_d(z)` is a finite
`K`-module at every closed point of a piece.  The chart-typed proof's
`isAffineOpen_pieces` was a two-case `rcases` on the `Sum` index; here it is the
`AffCoverData` field, and `isDedekindDomain_section` / `moduleFinite_stalkQuot_span_germ`
take `IsAffineOpen V` as an argument, so nothing else changes. -/
lemma moduleFinite_stalkQuot (j : D.index) {z : relCurve C K} (hz : z ∈ D.pieces j)
    (hzg : z ≠ genericPoint (relCurve C K)) :
    Module.Finite K ((relCurve C K).presheaf.stalk z ⧸ d.stalkIdeal z) := by
  haveI : LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
      SmoothOfRelativeDimension.smooth 1 _
    inferInstance
  have hη : genericPoint (relCurve C K) ∈ D.pieces j :=
    Scheme.genericPoint_mem_of_nonempty ⟨z, hz⟩
  haveI : IsDedekindDomain Γ(relCurve C K, D.pieces j) :=
    isDedekindDomain_section K (D.isAffineOpen_pieces j) hη
  have h := moduleFinite_stalkQuot_span_germ K (D.isAffineOpen_pieces j) hz hzg
    (A.eqn_ne_zero j hη)
  rwa [A.span_germ_eqn_eq_stalkIdeal j hz] at h

include A in
/-- **The pointwise divisor dictionary**, widened: at a closed point `z` of a piece, the
`K`-colength of the stalk ideal is the divisor coefficient weighted by the residue degree:

`finrank K (𝒪_z ⧸ I_d(z)) = coeff_z(div d) · [κ(z) : K]`.

The stalk colength dictionary (`finrank_stalkQuot_span_germ`) read through the widened
coefficient leg (`AffAdaptation.coeffAt_eq_toAdd_ordZ_eqn`,
`Picard/DivisorFamilyAffFieldDegree.lean`) and the multiplicity leg
(`toAdd_ordZ_eq_count_factors`).

As with `moduleFinite_stalkQuot`, the widened statement is indexed by `D.index` and its
conclusion is adaptation-free, so `A` is included explicitly. -/
lemma finrank_stalkQuot_eq_coeffAt_mul (j : D.index) {z : relCurve C K}
    (hz : z ∈ D.pieces j) (hzg : z ≠ genericPoint (relCurve C K)) :
    (finrank K ((relCurve C K).presheaf.stalk z ⧸ d.stalkIdeal z) : ℤ)
      = coeffAt hzg (Scheme.presentationDivisor K d.presentation)
          * ((relCurve C K).residueDeg K z : ℤ) := by
  haveI : LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
      SmoothOfRelativeDimension.smooth 1 _
    inferInstance
  have hη : genericPoint (relCurve C K) ∈ D.pieces j :=
    Scheme.genericPoint_mem_of_nonempty ⟨z, hz⟩
  haveI : IsDedekindDomain Γ(relCurve C K, D.pieces j) :=
    isDedekindDomain_section K (D.isAffineOpen_pieces j) hη
  have hf : A.eqn j ≠ 0 := A.eqn_ne_zero j hη
  have hne : ((relCurve C K).presheaf.germ (D.pieces j) (genericPoint (relCurve C K))
      hη).hom (A.eqn j) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (A.eqn_regular j (genericPoint (relCurve C K)) hη)
  set g : (relCurve C K).functionFieldˣ := Units.mk0 _ hne with hgdef
  have hg : (g : (relCurve C K).functionField)
      = ((relCurve C K).presheaf.germ (D.pieces j) (genericPoint (relCurve C K)) hη).hom
          (A.eqn j) := rfl
  have hcoeff := A.coeffAt_eq_toAdd_ordZ_eqn j hz hzg g hg
  have hcount := toAdd_ordZ_eq_count_factors K (D.isAffineOpen_pieces j) hη hz hzg hf g hg
  have hfr : finrank K ((relCurve C K).presheaf.stalk z ⧸ d.stalkIdeal z)
      = Multiset.count ((D.isAffineOpen_pieces j).primeIdealOf ⟨z, hz⟩).asIdeal
          (UniqueFactorizationMonoid.factors (Ideal.span {A.eqn j}))
        * (relCurve C K).residueDeg K z := by
    have h := finrank_stalkQuot_span_germ K (D.isAffineOpen_pieces j) hz hzg hf
    rwa [A.span_germ_eqn_eq_stalkIdeal j hz] at h
  have hcc : (Multiset.count ((D.isAffineOpen_pieces j).primeIdealOf ⟨z, hz⟩).asIdeal
      (UniqueFactorizationMonoid.factors (Ideal.span {A.eqn j})) : ℤ)
      = coeffAt hzg (Scheme.presentationDivisor K d.presentation) :=
    hcount.symm.trans hcoeff
  rw [hfr]
  push_cast
  rw [hcc]

/-! ## The per-piece CRT decomposition

Ported from `DivisorAdaptation.pieceStalkEval` and friends
(`Picard/DivisorFamilyFieldCRT.lean:82-170`). -/

open scoped Classical in
/-- The stalk evaluation of a piece over the supported points it sees, as one linear map
into the product of local models. -/
noncomputable def pieceStalkEval (j : D.index) :
    A.colength j →ₗ[K]
      ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
        (fun p => p.1 ∈ D.pieces j)},
        ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
  LinearMap.pi fun p =>
    (A.stalkColEval j (Finset.mem_filter.mp p.2).2).toLinearMap

open scoped Classical in
/-- **Injectivity of the per-piece stalk evaluation**: a piece section whose germs lie in the
stalk ideals at every supported point of the piece lies in `(f_j)` — stalk-locality of
regular principal ideals, with the equation a unit off the support.  The stalk-locality input
`mem_span_singleton_of_isUnit_or_mem` is itself carrier-free (it quantifies over an arbitrary
open of the curve), so it is used from `Picard/DivisorFamilyStalkEval.lean` rather than
recopied. -/
lemma pieceStalkEval_injective (j : D.index) : Function.Injective (A.pieceStalkEval j) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine DivisorAdaptation.mem_span_singleton_of_isUnit_or_mem (A.eqn_regular j)
    fun z hz hzg => ?_
  by_cases hsupp : (⟨z, hzg⟩ : {x : relCurve C K // x ≠ genericPoint (relCurve C K)})
      ∈ (Scheme.presentationDivisor K d.presentation).support
  · right
    have hp : (⟨z, hzg⟩ : {x : relCurve C K // x ≠ genericPoint (relCurve C K)})
        ∈ (Scheme.presentationDivisor K d.presentation).support.filter
          (fun p => p.1 ∈ D.pieces j) := Finset.mem_filter.mpr ⟨hsupp, hz⟩
    have hcomp := congrFun hx ⟨⟨z, hzg⟩, hp⟩
    have hzero : Ideal.Quotient.mk (d.stalkIdeal z)
        (((relCurve C K).presheaf.germ (D.pieces j) z hz).hom t) = 0 := hcomp
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rwa [← A.span_germ_eqn_eq_stalkIdeal j hz] at hmem
  · left
    refine A.isUnit_germ_eqn_of_coeffAt_eq_zero j hz hzg ?_
    by_contra hc
    exact hsupp (Finsupp.mem_support_iff.mpr hc)

open scoped Classical in
/-- **The per-piece CRT decomposition**: the piece-local colength module is the product of the
stalk colengths at the supported points of the piece.  Injectivity is stalk-locality;
surjectivity is a dimension count — the landed per-piece degree reading
(`AffAdaptation.finrank_colength_eq_sum`, `Picard/DivisorFamilyAffFieldDegree.lean`) equals the
summed pointwise dictionary (`finrank_stalkQuot_eq_coeffAt_mul`), so the injection is onto.

The one input that reads the cover is `D.isAffineOpen_pieces`, a structure field here where
the chart-typed original derived it by cases on the `Sum` index. -/
lemma pieceStalkEval_bijective (j : D.index) : Function.Bijective (A.pieceStalkEval j) := by
  refine ⟨A.pieceStalkEval_injective j, ?_⟩
  by_cases hη : genericPoint (relCurve C K) ∈ D.pieces j
  · -- nonempty piece: dimension count
    haveI : Module.Finite K (A.colength j) :=
      moduleFinite_quotient_span_section K (D.isAffineOpen_pieces j) hη
        (A.eqn_ne_zero j hη)
    haveI hfinL : ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
        (fun p => p.1 ∈ D.pieces j)},
        Module.Finite K ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
      fun p => A.moduleFinite_stalkQuot j (Finset.mem_filter.mp p.2).2 p.1.2
    haveI : ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
        (fun p => p.1 ∈ D.pieces j)},
        Module.Free K ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
      fun p => Module.Free.of_divisionRing _ _
    have hrank : finrank K
        (∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
          (fun p => p.1 ∈ D.pieces j)},
          ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1))
        = finrank K (A.colength j) := by
      have hZ : (finrank K
          (∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
            (fun p => p.1 ∈ D.pieces j)},
            ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1)) : ℤ)
          = (finrank K (A.colength j) : ℤ) := by
        rw [Module.finrank_pi_fintype K, Nat.cast_sum, A.finrank_colength_eq_sum j,
          ← Finset.sum_coe_sort
            ((Scheme.presentationDivisor K d.presentation).support.filter
              (fun p => p.1 ∈ D.pieces j))
            (fun p => coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
              * ((relCurve C K).residueDeg K p.1 : ℤ))]
        exact Finset.sum_congr rfl fun p _ =>
          A.finrank_stalkQuot_eq_coeffAt_mul j (Finset.mem_filter.mp p.2).2 p.1.2
      exact_mod_cast hZ
    have hrange : LinearMap.range (A.pieceStalkEval j) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj (A.pieceStalkEval_injective j)]
      exact hrank.symm
    exact LinearMap.range_eq_top.mp hrange
  · -- empty piece: no supported points, subsingleton target
    haveI : IsEmpty {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
        (fun p => p.1 ∈ D.pieces j)} := by
      refine ⟨fun p => ?_⟩
      exact hη (Scheme.genericPoint_mem_of_nonempty ⟨p.1.1, (Finset.mem_filter.mp p.2).2⟩)
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

/-! ## The glued CRT decomposition

Ported from `Picard/DivisorFamilyFieldCRT.lean:172-309`.  **The one non-verbatim step of the
whole port lives here**: the chart-typed original opens this section with its own
`DivisorAdaptation.exists_mem_pieces` (`:179-185`), a three-line derivation from `relCover_sup`
plus `cover₀`/`cover₁`.  That lemma is not ported — widened, "every point lies in a piece" is
`AffCoverData.exists_mem_pieces` (`Picard/DivisorFamilyAffCover.lean:166`), the joint-covering
structure field, used directly below. -/

/-- **The glued stalk evaluation**: the equalizer `W(d)` evaluated into the product of the
stalk colengths over the FULL support, each point read through a chosen piece —
well defined on the equalizer by `stalkColEval_glued`.  The choice of piece comes from the
joint cover field `D.exists_mem_pieces`. -/
noncomputable def gluedStalkEval :
    A.Glued →ₗ[K]
      ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support},
        ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
  LinearMap.pi fun p =>
    (A.stalkColEval (D.exists_mem_pieces p.1.1).choose
        (D.exists_mem_pieces p.1.1).choose_spec).toLinearMap
      ∘ₗ LinearMap.proj (D.exists_mem_pieces p.1.1).choose
      ∘ₗ A.gluedSubmodule.subtype

open scoped Classical in
/-- **Injectivity of the glued stalk evaluation**: an equalizer element vanishing in every
stalk colength vanishes in every piece — piece-independence transfers the vanishing from the
chosen piece to any piece, and the per-piece evaluation is injective. -/
lemma gluedStalkEval_injective : Function.Injective A.gluedStalkEval := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have hj : ∀ j : D.index, (s : A.chartProd) j = 0 := by
    intro j
    apply A.pieceStalkEval_injective j
    rw [map_zero]
    funext p
    have hp := Finset.mem_filter.mp p.2
    have hcomp := congrFun hs ⟨p.1, hp.1⟩
    have hglue := A.stalkColEval_glued s.2 j (D.exists_mem_pieces p.1.1).choose hp.2
      (D.exists_mem_pieces p.1.1).choose_spec
    exact hglue.trans hcomp
  exact Subtype.ext (funext hj)

open scoped Classical in
/-- The sub-family of prescribed stalk values seen by a piece (a named definition, so that
the per-piece surjectivity target elaborates without a re-indexing lambda — the inline
lambda sends `isDefEq` into a `whnf` loop against the stored codomain of `pieceStalkEval`).

Copied as `private` rather than referenced because the chart-typed
`DivisorAdaptation.pieceTarget` (`Picard/DivisorFamilyFieldCRT.lean:224`) is `private`
there.

Its statement mentions the adaptation only through the index, which on the widened side is
`D.index` rather than `A.index`, so the adaptation is taken as an EXPLICIT argument (shadowing
the section variable) instead of being auto-included; that keeps the `A.pieceTarget` dot
spelling of the two call sites, which an `include`d section variable does not support. -/
private noncomputable def pieceTarget (_A : AffAdaptation D d)
    (a : ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support},
      ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1)) (j : D.index) :
    ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
      (fun p => p.1 ∈ D.pieces j)},
      ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
  fun p => a ⟨p.1, (Finset.mem_filter.mp p.2).1⟩

open scoped Classical in
/-- **Surjectivity of the glued stalk evaluation**: any family of stalk values assembles —
each piece realizes its sub-family (per-piece surjectivity), and the pieces agree on
overlaps because at shared supported points both read the same prescribed value, at
unsupported points the equations are units, and stalkwise agreement globalizes. -/
lemma gluedStalkEval_surjective : Function.Surjective A.gluedStalkEval := by
  intro a
  have hsec : ∀ j : D.index, ∃ x : A.colength j,
      A.pieceStalkEval j x = A.pieceTarget a j :=
    fun j => (A.pieceStalkEval_bijective j).2 (A.pieceTarget a j)
  choose s hs using hsec
  have hval : ∀ (j : D.index) (p : {x : relCurve C K // x ≠ genericPoint (relCurve C K)})
      (hp : p ∈ (Scheme.presentationDivisor K d.presentation).support)
      (hzj : p.1 ∈ D.pieces j),
      A.stalkColEval j hzj (s j) = a ⟨p, hp⟩ := by
    intro j p hp hzj
    have hpf : p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
        (fun q => q.1 ∈ D.pieces j) := Finset.mem_filter.mpr ⟨hp, hzj⟩
    have h := congrFun (hs j) ⟨p, hpf⟩
    rw [show A.pieceTarget a j ⟨p, hpf⟩ = a ⟨p, hp⟩ from rfl] at h
    exact h
  have hmem : s ∈ A.gluedSubmodule := by
    rw [A.mem_gluedSubmodule_iff]
    rintro ⟨i, j⟩
    by_cases hη : genericPoint (relCurve C K) ∈ D.pieces i ⊓ D.pieces j
    · obtain ⟨ti, hti⟩ := Ideal.Quotient.mk_surjective (s i)
      obtain ⟨tj, htj⟩ := Ideal.Quotient.mk_surjective (s j)
      rw [← hti, ← htj]
      change Ideal.Quotient.mk (A.ovlIdeal i j)
          (((relCurve C K).presheaf.map (homOfLE inf_le_left).op).hom ti)
        = Ideal.Quotient.mk (A.ovlIdeal i j)
            (((relCurve C K).presheaf.map (homOfLE inf_le_right).op).hom tj)
      rw [Ideal.Quotient.eq]
      have hsub : Ideal.span {relResAlgHom C K
          (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (A.eqn i)}
          ≤ A.ovlIdeal i j :=
        Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
      refine hsub (DivisorAdaptation.mem_span_singleton_of_isUnit_or_mem
        (fun z hz => ?_) fun z hz hzg => ?_)
      · rw [relResAlgHom_apply, TopCat.Presheaf.germ_res_apply]
        exact A.eqn_regular i z hz.1
      · by_cases hsupp : (⟨z, hzg⟩ : {x : relCurve C K // x ≠ genericPoint (relCurve C K)})
            ∈ (Scheme.presentationDivisor K d.presentation).support
        · right
          have h1 : Ideal.Quotient.mk (d.stalkIdeal z)
              (((relCurve C K).presheaf.germ (D.pieces i) z hz.1).hom ti)
              = a ⟨⟨z, hzg⟩, hsupp⟩ := by
            have h := hval i ⟨z, hzg⟩ hsupp hz.1
            rw [← hti, A.stalkColEval_mk i hz.1 ti] at h
            exact h
          have h2 : Ideal.Quotient.mk (d.stalkIdeal z)
              (((relCurve C K).presheaf.germ (D.pieces j) z hz.2).hom tj)
              = a ⟨⟨z, hzg⟩, hsupp⟩ := by
            have h := hval j ⟨z, hzg⟩ hsupp hz.2
            rw [← htj, A.stalkColEval_mk j hz.2 tj] at h
            exact h
          have hdiff : ((relCurve C K).presheaf.germ (D.pieces i) z hz.1).hom ti
              - ((relCurve C K).presheaf.germ (D.pieces j) z hz.2).hom tj
              ∈ d.stalkIdeal z := by
            rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, h2, sub_self]
          simp only [relResAlgHom_apply]
          rw [map_sub, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
            TopCat.Presheaf.germ_res_apply, A.span_germ_eqn_eq_stalkIdeal i hz.1]
          exact hdiff
        · left
          rw [relResAlgHom_apply, TopCat.Presheaf.germ_res_apply]
          refine A.isUnit_germ_eqn_of_coeffAt_eq_zero i hz.1 hzg ?_
          by_contra hc
          exact hsupp (Finsupp.mem_support_iff.mpr hc)
    · have hbot : D.pieces i ⊓ D.pieces j ≤ ⊥ := fun x hx =>
        absurd (Scheme.genericPoint_mem_of_nonempty ⟨x, hx⟩) hη
      haveI : Subsingleton Γ(relCurve C K, D.pieces i ⊓ D.pieces j) :=
        (relCurve C K).subsingleton_sections_of_le_bot hbot
      haveI : Subsingleton (A.ovlColength i j) :=
        (Ideal.Quotient.mk_surjective (I := A.ovlIdeal i j)).subsingleton
      exact Subsingleton.elim _ _
  refine ⟨⟨s, hmem⟩, ?_⟩
  funext p
  exact hval (D.exists_mem_pieces p.1.1).choose p.1 p.2
    (D.exists_mem_pieces p.1.1).choose_spec

/-! ## The general colength↔degree identity -/

/-- **The colength↔degree identity for EVERY widened adaptation** — no separation hypothesis.

The glued equalizer is the product of the stalk colengths over the support
(`gluedStalkEval` bijective), and each stalk colength reads the local degree
(`finrank_stalkQuot_eq_coeffAt_mul`).  Since the left-hand side is adaptation-free and
cover-free, adaptation-independence of the glued rank is a corollary, not an input.

Verbatim `DivisorAdaptation.deg_presentationDivisor` (`Picard/DivisorFamilyFieldCRT.lean:324`)
apart from the piece-choice, which is `D.exists_mem_pieces` (the joint-covering field) instead
of the chart-typed lemma of the same name. -/
theorem deg_presentationDivisor :
    Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K d.presentation)
      = (finrank K A.Glued : ℤ) := by
  have e :
      A.Glued ≃ₗ[K]
        ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support},
          ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
    LinearEquiv.ofBijective A.gluedStalkEval
      ⟨A.gluedStalkEval_injective, A.gluedStalkEval_surjective⟩
  haveI : ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support},
      Module.Finite K ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
    fun p => A.moduleFinite_stalkQuot (D.exists_mem_pieces p.1.1).choose
      (D.exists_mem_pieces p.1.1).choose_spec p.1.2
  haveI : ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support},
      Module.Free K ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
    fun p => Module.Free.of_divisionRing _ _
  calc Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K d.presentation)
      = ∑ p ∈ (Scheme.presentationDivisor K d.presentation).support,
          coeffAt p.2 (Scheme.presentationDivisor K d.presentation)
            * ((relCurve C K).residueDeg K p.1 : ℤ) :=
        Finset.sum_congr rfl fun p _ => rfl
    _ = ∑ p ∈ (Scheme.presentationDivisor K d.presentation).support,
          (finrank K ((relCurve C K).presheaf.stalk p.1 ⧸ d.stalkIdeal p.1) : ℤ) :=
        Finset.sum_congr rfl fun p _ =>
          (A.finrank_stalkQuot_eq_coeffAt_mul (D.exists_mem_pieces p.1).choose
            (D.exists_mem_pieces p.1).choose_spec p.2).symm
    _ = ((∑ p ∈ (Scheme.presentationDivisor K d.presentation).support,
          finrank K ((relCurve C K).presheaf.stalk p.1 ⧸ d.stalkIdeal p.1) : ℕ) : ℤ) := by
        rw [Nat.cast_sum]
    _ = ((finrank K
          (∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support},
            ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1)) : ℕ) : ℤ) := by
        rw [Module.finrank_pi_fintype K, Finset.sum_coe_sort
          (Scheme.presentationDivisor K d.presentation).support
          (fun q : {x : relCurve C K // x ≠ genericPoint (relCurve C K)} =>
            finrank K ((relCurve C K).presheaf.stalk q.1 ⧸ d.stalkIdeal q.1))]
    _ = (finrank K A.Glued : ℤ) := by rw [← e.finrank_eq]

/-- **`deg D = n` for every widened certified adaptation**, with no hypothesis on the cover:
the general identity above against the field half of the widened certificate
(`AffAdaptation.IsCertified.finrank_glued`, `Picard/DivisorFamilyAffFieldDegree.lean`).  This
supersedes `deg_presentationDivisor_eq_of_isCertified`, which needed `hsep`. -/
theorem IsCertified.deg_presentationDivisor {n : ℕ} (hc : A.IsCertified n) :
    Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K d.presentation) = (n : ℤ) := by
  rw [A.deg_presentationDivisor, hc.finrank_glued]

end AffAdaptation

end AlgebraicGeometry
