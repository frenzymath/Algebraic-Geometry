/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffPerPiece
import AlgebraicJacobian.Picard.DivisorFamilyZar
import AlgebraicJacobian.Picard.DivSchemeCertZarPointwise

/-!
# The widened `DivFamZar` (R2, human decision I-0492)

The endpoint of the widening.  `IsLocallyCertifiedAff` is the locally-certified predicate
whose local certificates are carried by **arbitrary affine-open covers** rather than by basic
opens of a fixed pair of pinned `P¹` charts, and `DivFamZarAff` is its `DivEq` quotient —
the object the human decision of 2026-07-28 is about.

## Why this is strictly weaker than the old predicate, which is the whole point

`FinCoverData.toAffCoverData` (`DivisorFamilyAffCover.lean`) turns every old cover datum into
a widened one, and `DivisorFamilyAffCompare.lean` migrates the CERTIFICATE on top of it, so
`isLocallyCertifiedAff_of_isLocallyCertified` holds: anything the old
predicate certified, the new one certifies.  The converse fails, and its failure is exactly
the content of R2 — a divisor straddling both pinned vertical fibres has no chart-typed
certificate (`informal/spec-dd-r.md` ADDENDUM 4 §4.3, on-stratum witness at every `g ≥ 2`)
but does admit an affine-open one, because `supp D` is finite over `R` and therefore lies in a
single affine open of `C ×_k Spec R` (Stacks `0B8B`).

So `DivFamZarAff` is the value on which the divisor functor can be a Zariski sheaf over an
ARBITRARY field, with no `|P¹(k)| ≥ n + 2` hypothesis anywhere — the field-uniform fix.

## The two relocated obligations (I-0492 clause 4)

* **(i) fibrewise-finite support.** NOT a field of anything here.  It is not implied by
  what a `LocalEquations` carries (`d.eqn ≡ r` for a non-unit `r ∈ R` is germ-regular with a
  whole fibre curve in its support), so it must come from the seed's own degree data.  It
  enters as an explicit hypothesis at the point of use, never as carrier data: concretely as
  the `hfib` argument of `AffAdaptation.isCertified_of_swallowedBy`
  (`DivisorFamilyAffAssemble.lean`) and as `AffCoverData.SwallowedBy`
  (`DivisorFamilyAffSwallow.lean`).  Neither is a field of anything in this file.
* **(ii) what the fixed-pair confinement was silently supplying.** Discharged in
  `DivisorFamilyAffCover.lean` (`exists_mem_pieces` from the joint cover,
  `flat_sections_pieces` from the flat structure morphism) and in
  `DivisorFamilyAffPerPiece.lean` (the whole per-piece layer, from openness and affineness).

## Main declarations

* `AlgebraicGeometry.CertifiedDivisorFamilyAff` — a certified family over a widened cover.
* `AlgebraicGeometry.IsLocallyCertifiedAff` — the widened locally-certified predicate.
* `IsLocallyCertifiedAff.of_divEq` — it respects divisor equality.
* `AlgebraicGeometry.DivFamZarAff` — the widened functor value, with `mk`, `mk_eq_mk_iff`
  and `picClass`.

The comparison with the chart-typed predicate — `isLocallyCertifiedAff_of_isLocallyCertified`
and `DivFamZar.toAff` — is in `DivisorFamilyAffCompare.lean`, which imports this file.
* `AlgebraicGeometry.isLocallyCertifiedAff_of_forall_prime_exists_away` — the pointwise gate,
  one base point at a time, over the widened predicate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k))) (R : Type u) [CommRing R]
  [Algebra k R]
variable (π : C.left ⟶ P1 k)

/-! ## Certified families over a widened cover -/

/-- **A certified divisor family of degree `n` over a widened cover**: a local-equation
system, an affine-open cover datum, an adaptation, and the certificate.  The cover is part of
the data (it is chosen per family), exactly as the old `adaptation` field bundled its own
`FinCoverData`. -/
structure CertifiedDivisorFamilyAff (n : ℕ) : Type u where
  /-- The local-equation system on the relative curve. -/
  eqns : (relCurve C R).LocalEquations
  /-- The affine-open cover carrying the certificate. -/
  cover : AffCoverData C R
  /-- The adaptation of the system to that cover. -/
  adaptation : AffAdaptation cover eqns
  /-- The colength certificate of degree `n`. -/
  certified : adaptation.IsCertified n

/-! ## The widened locally-certified predicate -/

variable {C R}

/-- **The widened locally-certified pin.**  Identical in shape to `IsLocallyCertified`
(`DivisorFamilyZar.lean`) — a span-`⊤` family `g : Fin m → R` with certified families over
the away localizations, divisor-equal to the pulled system — except that the local
certificates live over ARBITRARY AFFINE-OPEN covers.

The base-side structure is untouched on purpose: R2 widens where the pieces live on the
CURVE, and changes nothing about the Zariski cover of the base. -/
def IsLocallyCertifiedAff (n : ℕ) (d : (relCurve C R).LocalEquations) : Prop :=
  ∃ (m : ℕ) (g : Fin m → R), Ideal.span (Set.range g) = ⊤ ∧
    ∀ i : Fin m,
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (g i))) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away (g i)) (g i)
      ∃ G : CertifiedDivisorFamilyAff C (Localization.Away (g i)) n,
        Scheme.LocalEquations.DivEq G.eqns
          (d.pullback (relCurveMap C R (Localization.Away (g i)))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away (g i))) d))

/-- **The widened pin respects divisor equality** — the local `DivEq`s transport through
`divEq_pullback`, verbatim as in the chart-typed case. -/
theorem IsLocallyCertifiedAff.of_divEq {n : ℕ} {d d' : (relCurve C R).LocalEquations}
    (hd : IsLocallyCertifiedAff n d) (h : Scheme.LocalEquations.DivEq d d') :
    IsLocallyCertifiedAff n d' := by
  obtain ⟨m, g, hg, hG⟩ := hd
  refine ⟨m, g, hg, fun i => ?_⟩
  haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (g i))) :=
    isOpenImmersion_relCurveMap_away C R (Localization.Away (g i)) (g i)
  obtain ⟨G, hGdiv⟩ := hG i
  exact ⟨G, hGdiv.trans
    (Scheme.LocalEquations.divEq_pullback (relCurveMap C R (Localization.Away (g i)))
      h _ _)⟩

/-! ## The comparison with the chart-typed predicate

`FinCoverData.toAffCoverData` (`DivisorFamilyAffCover.lean`) already migrates the COVER
sorry-free, and the adaptation's equations and `eqn_rel` transport with it because the pieces
are literally the same opens, only reindexed along `finSumFinEquiv`.

The migration of the CERTIFICATE is landed too, in `DivisorFamilyAffCompare.lean`
(`DivisorAdaptation.isCertified_toAff`, all seven clauses).  Clauses (c1) are `rfl` at the
relabelled index; the glued clauses (c2)/(c3)/(c4) transport along `LinearEquiv.piCongrLeft`
in its `symm` direction, which evaluates cast-free, so the intertwining with
`deltaLeft`/`deltaRight` is componentwise and `Module.rankAtStalk` invariance is
`rankAtStalk_eq_of_equiv`.  No clause changes, only the index does.

A predecessor docstring here estimated that transport at about a hundred lines of equalizer
bookkeeping.  That was wrong by an order of magnitude and the reason generalises: arrange the
reindexed cover so its pieces are DEFINITIONALLY the original pieces at the relabelled index,
and the overlap data at `(i, j)` becomes `rfl`-equal to the original at `(e i, e j)`, because
reindexing acts diagonally on the pair index.  Then no intertwining lemma exists to prove. -/

/-! ## The widened functor value -/

variable (C R) (n : ℕ)

/-- The divisor-equality setoid on widened locally-certified systems. -/
def divFamZarAffSetoid : Setoid {d : (relCurve C R).LocalEquations //
    IsLocallyCertifiedAff n d} where
  r d₁ d₂ := Scheme.LocalEquations.DivEq d₁.1 d₂.1
  iseqv :=
    ⟨fun d => Scheme.LocalEquations.divEq_refl d.1,
     fun h => h.symm, fun h h' => h.trans h'⟩

/-- **The widened divisor-functor value on the affine test `R`** (R2, I-0492): locally
certified systems of degree `n` up to divisor equality, where "certified" is now witnessed by
arbitrary affine-open covers of the relative curve.

This is the carrier that is field-uniform: no hypothesis on `|P¹(k)|` appears anywhere in its
definition or in the per-piece layer that produces it. -/
def DivFamZarAff : Type u := Quotient (divFamZarAffSetoid C R n)

namespace DivFamZarAff

variable {C R n}

/-- The class of a widened locally certified system. -/
def mk (d : (relCurve C R).LocalEquations) (hd : IsLocallyCertifiedAff n d) :
    DivFamZarAff C R n :=
  Quotient.mk (divFamZarAffSetoid C R n) ⟨d, hd⟩

lemma mk_eq_mk_iff {d₁ d₂ : (relCurve C R).LocalEquations}
    {h₁ : IsLocallyCertifiedAff n d₁} {h₂ : IsLocallyCertifiedAff n d₂} :
    mk d₁ h₁ = mk d₂ h₂ ↔ Scheme.LocalEquations.DivEq d₁ d₂ :=
  Quotient.eq (r := divFamZarAffSetoid C R n)

/-- **The Picard class of a widened divisor class** `𝒪(D)`, well defined by
`picClass_eq_of_divEq`.  This is the Abel hook DAT-C consumes, unchanged by the widening. -/
noncomputable def picClass (F : DivFamZarAff C R n) : (relCurve C R).CechPic :=
  Quotient.lift
    (fun d : {d : (relCurve C R).LocalEquations // IsLocallyCertifiedAff n d} =>
      d.1.picClass)
    (fun _ _ h => Scheme.LocalEquations.picClass_eq_of_divEq h) F

@[simp]
lemma picClass_mk (d : (relCurve C R).LocalEquations)
    (hd : IsLocallyCertifiedAff n d) : picClass (mk d hd) = d.picClass :=
  rfl

end DivFamZarAff

/-! ## The pointwise gate over the widened predicate -/

variable {C R n}

/-- **The pointwise certificate gate, widened.** If over every prime of the base there is an
away localization carrying a widened certified family divisor-equal to the pulled system, the
system is widened-locally certified.  Same quasi-compactness step as
`isLocallyCertified_of_forall_prime_exists_away` (`DivSchemeCertZarPointwise.lean`): the good
elements' basic opens cover `Spec R`, so finitely many span the unit ideal.

This is the shape the geometry produces — the support tube isolates pieces over a
neighbourhood of ONE base point, and every fibre analysis reads at a single prime. -/
theorem isLocallyCertifiedAff_of_forall_prime_exists_away
    {d : (relCurve C R).LocalEquations}
    (h : ∀ p : PrimeSpectrum R, ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ G : CertifiedDivisorFamilyAff C (Localization.Away r) n,
        Scheme.LocalEquations.DivEq G.eqns
          (d.pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) d))) :
    IsLocallyCertifiedAff n d := by
  obtain ⟨m, g, hg, hgood⟩ := exists_fin_span_eq_top_of_forall_prime
    (fun r =>
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ G : CertifiedDivisorFamilyAff C (Localization.Away r) n,
        Scheme.LocalEquations.DivEq G.eqns
          (d.pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) d))) h
  exact ⟨m, g, hg, hgood⟩

end AlgebraicGeometry
