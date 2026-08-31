/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyStalkEval
import AlgebraicJacobian.Picard.DivisorFamilyMapAlg

/-!
# The general colength↔degree identity over a field (the Mayer–Vietoris wall, I-0179)

For an ARBITRARY divisor adaptation `A` of a local-equation system `d` on the relative curve
over a field `K` — no support-separation hypothesis — this file proves

`deg K (div d) = finrank K W(d)`   (`DivisorAdaptation.deg_presentationDivisor`),

the general colength↔degree identity threaded as `hdeg` through the G-1 keystones
(`Picard/DivisorThetaFibreData.lean`) and the field dictionary
(`divFamFieldEquivOfDegOfSurj`, `Picard/DivisorFamilyFieldEquiv.lean`).

## The CRT route (why the wall falls)

The glued equalizer `W(d) ⊆ Π_j Γ(D(h_j))/(f_j)` does not decompose over the cover naively —
a supported point may be seen by several pieces.  The resolution
(`AlgebraicJacobian.Picard.DivisorFamilyStalkEval`): decompose into **stalk** quotients
`𝒪_z ⧸ I_d(z)`, which are chart-independent — on the equalizer, every piece seeing `z`
reads the same stalk value (`stalkColEval_glued`).  Then:

* per piece, `Γ(D(h_j))/(f_j) ≅ Π_{z ∈ supp ∩ D(h_j)} 𝒪_z ⧸ I_d(z)`
  (`pieceStalkEval_bijective`): injectivity is the stalk-locality of regular principal
  ideals (`Scheme.mem_span_singleton_of_forall_germ`), surjectivity is a dimension count —
  the landed per-piece degree reading (`finrank_colength_eq_sum`) against the pointwise
  stalk dictionary (`finrank_stalkQuot_eq_coeffAt_mul`), an honest CRT with no new
  constructions;
* globally, `W(d) ≅ Π_{z ∈ supp} 𝒪_z ⧸ I_d(z)` (`gluedStalkEval_injective` +
  `gluedStalkEval_surjective`): the equalizer condition makes the per-piece local values
  agree at shared points, and conversely any family of stalk values assembles to an
  equalizer element piece by piece.

Summing `finrank K (𝒪_z ⧸ I_d(z)) = coeff_z(D) · [κ(z) : K]` over the support gives the
degree.  Since the left-hand side `deg K (div d)` is adaptation-free and the identity holds
for EVERY adaptation of `d`, adaptation-independence of the glued rank is a corollary, not
an input — the circularity of the refine-to-separated shortcut (I-0179) is dissolved.

## Consequences

* `deg_divFamDivisor` — `deg K (divFamDivisor F) = n` for every certified family
  `F : DivFam C K π n` (the `hdeg` input of `divFamFieldEquivOfDegOfSurj`, unconditional).
* `DivisorAdaptation.IsCertified.deg_presentationDivisor` — the field-level seam shape.
* `DivisorAdaptation.IsCertified.deg_presentationDivisor_pulledEquations` — the exact
  fibrewise form consumed by G-1: for a certified adaptation over any test ring, the divisor
  cut on the `K`-fibre by the pulled equations has degree `n` (certificates base-change,
  `isCertified_pullback`).
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

/-! ## The per-piece CRT decomposition -/

open scoped Classical in
/-- The stalk evaluation of a piece over the supported points it sees, as one linear map
into the product of local models. -/
noncomputable def pieceStalkEval (j : A.index) :
    A.colength j →ₗ[K]
      ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
        (fun p => p.1 ∈ A.pieces j)},
        ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
  LinearMap.pi fun p =>
    (A.stalkColEval j (Finset.mem_filter.mp p.2).2).toLinearMap

open scoped Classical in
/-- **Injectivity of the per-piece stalk evaluation**: a chart section whose germs lie in
the stalk ideals at every supported point of the piece lies in `(f_j)` — stalk-locality of
regular principal ideals, with the equation a unit off the support. -/
lemma pieceStalkEval_injective (j : A.index) : Function.Injective (A.pieceStalkEval j) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine mem_span_singleton_of_isUnit_or_mem (A.eqn_regular j) fun z hz hzg => ?_
  by_cases hsupp : (⟨z, hzg⟩ : {x : relCurve C K // x ≠ genericPoint (relCurve C K)})
      ∈ (Scheme.presentationDivisor K d.presentation).support
  · right
    have hp : (⟨z, hzg⟩ : {x : relCurve C K // x ≠ genericPoint (relCurve C K)})
        ∈ (Scheme.presentationDivisor K d.presentation).support.filter
          (fun p => p.1 ∈ A.pieces j) := Finset.mem_filter.mpr ⟨hsupp, hz⟩
    have hcomp := congrFun hx ⟨⟨z, hzg⟩, hp⟩
    have hzero : Ideal.Quotient.mk (d.stalkIdeal z)
        (((relCurve C K).presheaf.germ (A.pieces j) z hz).hom t) = 0 := hcomp
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rwa [← A.span_germ_eqn_eq_stalkIdeal j hz] at hmem
  · left
    refine A.isUnit_germ_eqn_of_coeffAt_eq_zero j hz hzg ?_
    by_contra hc
    exact hsupp (Finsupp.mem_support_iff.mpr hc)

open scoped Classical in
/-- **The per-piece CRT decomposition**: the chart-local colength module is the product of
the stalk colengths at the supported points of the piece.  Injectivity is stalk-locality;
surjectivity is a dimension count — the landed per-piece degree reading
(`finrank_colength_eq_sum`) equals the summed pointwise dictionary
(`finrank_stalkQuot_eq_coeffAt_mul`), so the injection is onto. -/
lemma pieceStalkEval_bijective (j : A.index) : Function.Bijective (A.pieceStalkEval j) := by
  refine ⟨A.pieceStalkEval_injective j, ?_⟩
  by_cases hη : genericPoint (relCurve C K) ∈ A.pieces j
  · -- nonempty piece: dimension count
    haveI : Module.Finite K (A.colength j) :=
      moduleFinite_quotient_span_section K (A.isAffineOpen_pieces j) hη
        (A.eqn_ne_zero j hη)
    haveI hfinL : ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
        (fun p => p.1 ∈ A.pieces j)},
        Module.Finite K ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
      fun p => A.moduleFinite_stalkQuot j (Finset.mem_filter.mp p.2).2 p.1.2
    haveI : ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
        (fun p => p.1 ∈ A.pieces j)},
        Module.Free K ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
      fun p => Module.Free.of_divisionRing _ _
    have hrank : finrank K
        (∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
          (fun p => p.1 ∈ A.pieces j)},
          ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1))
        = finrank K (A.colength j) := by
      have hZ : (finrank K
          (∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
            (fun p => p.1 ∈ A.pieces j)},
            ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1)) : ℤ)
          = (finrank K (A.colength j) : ℤ) := by
        rw [Module.finrank_pi_fintype K, Nat.cast_sum, A.finrank_colength_eq_sum j,
          ← Finset.sum_coe_sort
            ((Scheme.presentationDivisor K d.presentation).support.filter
              (fun p => p.1 ∈ A.pieces j))
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
        (fun p => p.1 ∈ A.pieces j)} := by
      refine ⟨fun p => ?_⟩
      exact hη (Scheme.genericPoint_mem_of_nonempty ⟨p.1.1, (Finset.mem_filter.mp p.2).2⟩)
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

/-! ## The glued CRT decomposition -/

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- Every point of the curve lies in some piece (the two-chart cover refined by the
partitions). -/
lemma exists_mem_pieces (z : relCurve C K) : ∃ j : A.index, z ∈ A.pieces j := by
  have hle : (⊤ : (relCurve C K).Opens) ≤ ⨆ j : A.index, A.pieces j := by
    rw [← relCover_sup C K (fiberTwoCover π)]
    exact sup_le
      (A.cover₀.trans (iSup_le fun j => le_iSup (fun i => A.pieces i) (Sum.inl j)))
      (A.cover₁.trans (iSup_le fun j => le_iSup (fun i => A.pieces i) (Sum.inr j)))
  exact TopologicalSpace.Opens.mem_iSup.mp (hle (TopologicalSpace.Opens.mem_top z))

/-- **The glued stalk evaluation**: the equalizer `W(d)` evaluated into the product of the
stalk colengths over the FULL support, each point read through a chosen piece —
well defined on the equalizer by `stalkColEval_glued`. -/
noncomputable def gluedStalkEval :
    A.Glued →ₗ[K]
      ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support},
        ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
  LinearMap.pi fun p =>
    (A.stalkColEval (A.exists_mem_pieces p.1.1).choose
        (A.exists_mem_pieces p.1.1).choose_spec).toLinearMap
      ∘ₗ LinearMap.proj (A.exists_mem_pieces p.1.1).choose
      ∘ₗ A.gluedSubmodule.subtype

open scoped Classical in
/-- **Injectivity of the glued stalk evaluation**: an equalizer element vanishing in every
stalk colength vanishes in every piece — chart-independence transfers the vanishing from
the chosen piece to any piece, and the per-piece evaluation is injective. -/
lemma gluedStalkEval_injective : Function.Injective A.gluedStalkEval := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have hj : ∀ j : A.index, (s : A.chartProd) j = 0 := by
    intro j
    apply A.pieceStalkEval_injective j
    rw [map_zero]
    funext p
    have hp := Finset.mem_filter.mp p.2
    have hcomp := congrFun hs ⟨p.1, hp.1⟩
    have hglue := A.stalkColEval_glued s.2 j (A.exists_mem_pieces p.1.1).choose hp.2
      (A.exists_mem_pieces p.1.1).choose_spec
    exact hglue.trans hcomp
  exact Subtype.ext (funext hj)

open scoped Classical in
/-- The sub-family of prescribed stalk values seen by a piece (a named definition, so that
the per-piece surjectivity target elaborates without a re-indexing lambda — the inline
lambda sends `isDefEq` into a `whnf` loop against the stored codomain of
`pieceStalkEval`). -/
private noncomputable def pieceTarget
    (a : ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support},
      ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1)) (j : A.index) :
    ∀ p : {p // p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
      (fun p => p.1 ∈ A.pieces j)},
      ((relCurve C K).presheaf.stalk p.1.1 ⧸ d.stalkIdeal p.1.1) :=
  fun p => a ⟨p.1, (Finset.mem_filter.mp p.2).1⟩

open scoped Classical in
/-- **Surjectivity of the glued stalk evaluation**: any family of stalk values assembles —
each piece realizes its sub-family (per-piece surjectivity), and the pieces agree on
overlaps because at shared supported points both read the same prescribed value, at
unsupported points the equations are units, and stalkwise agreement globalizes. -/
lemma gluedStalkEval_surjective : Function.Surjective A.gluedStalkEval := by
  intro a
  have hsec : ∀ j : A.index, ∃ x : A.colength j,
      A.pieceStalkEval j x = A.pieceTarget a j :=
    fun j => (A.pieceStalkEval_bijective j).2 (A.pieceTarget a j)
  choose s hs using hsec
  have hval : ∀ (j : A.index) (p : {x : relCurve C K // x ≠ genericPoint (relCurve C K)})
      (hp : p ∈ (Scheme.presentationDivisor K d.presentation).support)
      (hzj : p.1 ∈ A.pieces j),
      A.stalkColEval j hzj (s j) = a ⟨p, hp⟩ := by
    intro j p hp hzj
    have hpf : p ∈ (Scheme.presentationDivisor K d.presentation).support.filter
        (fun q => q.1 ∈ A.pieces j) := Finset.mem_filter.mpr ⟨hp, hzj⟩
    have h := congrFun (hs j) ⟨p, hpf⟩
    rw [show A.pieceTarget a j ⟨p, hpf⟩ = a ⟨p, hp⟩ from rfl] at h
    exact h
  have hmem : s ∈ A.gluedSubmodule := by
    rw [A.mem_gluedSubmodule_iff]
    rintro ⟨i, j⟩
    by_cases hη : genericPoint (relCurve C K) ∈ A.pieces i ⊓ A.pieces j
    · obtain ⟨ti, hti⟩ := Ideal.Quotient.mk_surjective (s i)
      obtain ⟨tj, htj⟩ := Ideal.Quotient.mk_surjective (s j)
      rw [← hti, ← htj]
      change Ideal.Quotient.mk (A.ovlIdeal i j)
          (((relCurve C K).presheaf.map (homOfLE inf_le_left).op).hom ti)
        = Ideal.Quotient.mk (A.ovlIdeal i j)
            (((relCurve C K).presheaf.map (homOfLE inf_le_right).op).hom tj)
      rw [Ideal.Quotient.eq]
      have hsub : Ideal.span {relResAlgHom C K
          (inf_le_left : A.pieces i ⊓ A.pieces j ≤ A.pieces i) (A.eqn i)}
          ≤ A.ovlIdeal i j :=
        Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
      refine hsub (mem_span_singleton_of_isUnit_or_mem (fun z hz => ?_) fun z hz hzg => ?_)
      · rw [relResAlgHom_apply, TopCat.Presheaf.germ_res_apply]
        exact A.eqn_regular i z hz.1
      · by_cases hsupp : (⟨z, hzg⟩ : {x : relCurve C K // x ≠ genericPoint (relCurve C K)})
            ∈ (Scheme.presentationDivisor K d.presentation).support
        · right
          have h1 : Ideal.Quotient.mk (d.stalkIdeal z)
              (((relCurve C K).presheaf.germ (A.pieces i) z hz.1).hom ti)
              = a ⟨⟨z, hzg⟩, hsupp⟩ := by
            have h := hval i ⟨z, hzg⟩ hsupp hz.1
            rw [← hti, A.stalkColEval_mk i hz.1 ti] at h
            exact h
          have h2 : Ideal.Quotient.mk (d.stalkIdeal z)
              (((relCurve C K).presheaf.germ (A.pieces j) z hz.2).hom tj)
              = a ⟨⟨z, hzg⟩, hsupp⟩ := by
            have h := hval j ⟨z, hzg⟩ hsupp hz.2
            rw [← htj, A.stalkColEval_mk j hz.2 tj] at h
            exact h
          have hdiff : ((relCurve C K).presheaf.germ (A.pieces i) z hz.1).hom ti
              - ((relCurve C K).presheaf.germ (A.pieces j) z hz.2).hom tj
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
    · have hbot : A.pieces i ⊓ A.pieces j ≤ ⊥ := fun x hx =>
        absurd (Scheme.genericPoint_mem_of_nonempty ⟨x, hx⟩) hη
      haveI : Subsingleton Γ(relCurve C K, A.pieces i ⊓ A.pieces j) :=
        (relCurve C K).subsingleton_sections_of_le_bot hbot
      haveI : Subsingleton (A.ovlColength i j) :=
        (Ideal.Quotient.mk_surjective (I := A.ovlIdeal i j)).subsingleton
      exact Subsingleton.elim _ _
  refine ⟨⟨s, hmem⟩, ?_⟩
  funext p
  exact hval (A.exists_mem_pieces p.1.1).choose p.1 p.2
    (A.exists_mem_pieces p.1.1).choose_spec

/-! ## The general colength↔degree identity -/

/-- **The general colength↔degree identity** (`informal/spec-dd-1.md` §3 (f), the
Mayer–Vietoris wall of I-0179, general case): for EVERY divisor adaptation `A` of `d` over
the field `K` — no support-separation hypothesis —

`deg K (div d) = finrank K W(d)`.

The glued equalizer is the product of the stalk colengths over the support
(`gluedStalkEval` bijective), and each stalk colength reads the local degree
(`finrank_stalkQuot_eq_coeffAt_mul`).  Since the left-hand side is adaptation-free,
adaptation-independence of the glued rank is a corollary. -/
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
    fun p => A.moduleFinite_stalkQuot (A.exists_mem_pieces p.1.1).choose
      (A.exists_mem_pieces p.1.1).choose_spec p.1.2
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
          (A.finrank_stalkQuot_eq_coeffAt_mul (A.exists_mem_pieces p.1).choose
            (A.exists_mem_pieces p.1).choose_spec p.2).symm
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

/-- **The degree of a certified adaptation is its rank** — the field-level `hdeg` seam
shape: combining the general colength↔degree identity with the field half of the
certificate (`IsCertified.finrank_glued`). -/
theorem IsCertified.deg_presentationDivisor {n : ℕ} (hc : A.IsCertified n) :
    Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K d.presentation) = (n : ℤ) := by
  rw [A.deg_presentationDivisor, hc.finrank_glued]

end DivisorAdaptation

/-- **The degree of a certified family is its rank** (`informal/spec-dd-1.md` §3 (f),
UNCONDITIONAL): `deg K (divFamDivisor F) = n` for every certified divisor family, with no
support-separation hypothesis — the `hdeg` input of `divFamFieldEquivOfDegOfSurj`
(`Picard/DivisorFamilyFieldEquiv.lean`), discharged.  Supersedes
`deg_divFamDivisor_of_separated`. -/
theorem deg_divFamDivisor {n : ℕ} (F : DivFam C K π n) :
    Scheme.CurveDivisor.deg K (divFamDivisor F) = (n : ℤ) := by
  induction F using Quotient.ind with
  | _ G =>
    change Scheme.CurveDivisor.deg K (divFamDivisor (DivFam.mk G)) = (n : ℤ)
    rw [divFamDivisor_mk, G.adaptation.deg_presentationDivisor, G.certified.finrank_glued]

/-! ## Discharge of the G-1 `hdeg` seam -/

namespace DivisorAdaptation

section PulledSeam

variable {R : Type u} [CommRing R] [Algebra k R] [Algebra R K] [IsScalarTower k R K]

/-- **The fibre degree law of a certified adaptation** — the exact `hdeg` seam shape of the
G-1 keystones (`Picard/DivisorThetaFibreData.lean`): for a certified adaptation over any
test ring and any field-valued point `R → K`, the divisor cut on the `K`-fibre by the
pulled equations has degree exactly the certificate rank.  Certificates base-change
(`isCertified_pullback`), and the general colength↔degree identity applies to the pulled
adaptation over the field. -/
theorem IsCertified.deg_presentationDivisor_pulledEquations
    {d : (relCurve C R).LocalEquations} {A : DivisorAdaptation C R π d} {n : ℕ}
    (hc : A.IsCertified n) :
    Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K
      ((A.pulledEquations K hc.projective_colength).presentation)) = (n : ℤ) := by
  have h := (A.pullback K hc.projective_colength).deg_presentationDivisor
  rwa [(A.isCertified_pullback K hc).finrank_glued] at h

end PulledSeam

end DivisorAdaptation

end AlgebraicGeometry
