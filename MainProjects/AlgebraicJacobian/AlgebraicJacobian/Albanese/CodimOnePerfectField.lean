/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Albanese.CodimOneExtension
import AlgebraicJacobian.Albanese.Milne33
import AlgebraicJacobian.Picard.Pic0Dimension

/-!
# Milne 3.1 over a perfect field, and the one link of §I.3 that is not

Headline obligation 5 of the Jacobian (`isAlbanese_pic0Et`, `Jacobian.lean`) is
stated over an **arbitrary** field, and its supply route — Milne Theorem 3.2
(`Scheme.RationalMap.extend_to_av`, `Albanese/Thm32RationalMapExtension.lean`) —
is stated over an algebraically closed one.  This file measures which links of
that chain actually need the hypothesis, and contributes the ones that had no
weaker form already in the tree.

## What is here, after an adversarial audit cut it down

Three theorems: `localRing_dvr_of_codim_one_perfectField`,
`indeterminacy_codimGe2_of_smooth_of_complete_perfectField` (**Milne 3.1**) and
`codimOneFree_of_smooth_of_complete_perfectField`.  These have no perfect-field
or arbitrary-field predecessor in AJC, AJCR, `SubProjects/Albanese` or mathlib —
Milne 3.1 is `[IsAlgClosed]`-only in all of them.  Non-vacuity is witnessed by
instantiation at `ℙ¹_ℚ` and `ℙ¹_{𝔽₅}` in
`Albanese/CodimOnePerfectFieldWitness.lean`.

**Two theorems were deleted from this file after it landed** (`I-1302`,
`I-1303`, a fresh-context audit whose findings I reproduced before acting).
Both were weaker than something already proved, and the mechanism is worth more
than the deletions:

* A perfect-field Stacks-`00TT` stalk-regularity theorem.  **Already landed and
  strictly stronger**: `Scheme.isRegularLocalRing_stalk_of_smooth_of_perfectField`
  (`Picard/Pic0Dimension.lean`, lane `ajc-pic0av`, 2026-07-29) asks for
  `[Smooth]` alone, where mine carried five further instance binders inherited
  from the alg-closed original.  The DVR theorem below now calls it.
* A perfect-field reducedness theorem.  **Dead, not merely duplicated**:
  `AlgebraicGeometry.Smooth.isReduced_of_field`
  (`Curve/GeometricallyReduced.lean`) is the same conclusion on the same single
  `[Smooth]` binder over an **arbitrary** field, and it is in this file's own
  import closure.  My 30-line stalkwise proof re-derived it, and a paragraph
  explaining why reducedness "needed a different route" was explaining a route
  nobody needs.

THE LESSON, since it cost two declarations: a binder-weakening must be checked
against the **weakest landed form of the conclusion**, not against the theorem
the proof was copied from.  Transcribing a proof anchors the search on the
original's name and binder set, so a stronger sibling under a different name, in
a different file, written for a different lane, is invisible.  Search by
statement.

## The costing this file corrects

`I-1115` (`ajc-p4`, run 0086 r2 — my own measurement) localised the chain's
`[IsAlgClosed]` to one lemma and priced it: "the single obligation is Milne 3.1's
regularity input over a non-closed residue field … the statement needs a
residue-degree-aware version, not a binder deletion."  **Both halves are wrong,
in opposite directions** (retraction: `I-1285`).

* The regularity input is not an obligation.  `isRegularLocalRing_stalk_of_smooth`
  (`CodimOneExtension.lean`) already routes through
  `isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField`
  (`Albanese/SmoothPrimeRegularity.lean`), `sorry`-free at an **arbitrary** prime
  over a **perfect** field.  The residue-degree-aware version my costing said had
  to be built was in the tree and is what the chain's own proof calls.
* Milne **3.3** is the load-bearing link, and `I-1115` said it carried no such
  binder at all.  It binds `[IsAlgClosed]` on its section `variable` line
  (`Milne33.lean`), which is why reading the declaration header showed nothing
  and `#check` shows it at once.

So the restriction sits one link **above** where I put it, and the link I named
is discharged.

## The negative, and it is prose

Restating Milne 3.3 over `[PerfectField k]` and closing it by its own core fails
with `failed to synthesize instance of type class IsAlgClosed k`.  The
consumption site is `Milne33RowSection.mem_domain_of_selfDiag_mem_domain`, whose
row argument calls mathlib's `pointOfClosedPoint` — which needs the residue field
at a closed point to **be** the base field (`residueFieldIsoBase`, via
`IsAlgClosed.ringHom_bijective_of_isIntegral`), false already over `ℚ`.  Three of
the twelve modules in that cone carry the binder (`Milne33.lean`,
`Milne33RowSection.lean`, `Milne33Transport.lean`); the latter two are the
closed-point layers.  Milne 3.3's own docstring now records this at the site.

**This paragraph is a report of a probe, not a declaration.**  An earlier
revision of this docstring named `milne33_needs_isAlgClosed` as "a documented
negative" and referred to a "§2" of this file; no such declaration and no such
section ever existed (`I-1302`, finding 3).  A failing elaboration cannot be
committed as Lean, so the evidence for the negative is the quoted error and the
named site, and a reader who wants it must re-run the probe.

## What this does NOT establish

Nothing here closes `isAlbanese_pic0Et`, and no antecedent of it is witnessed at
any curve.  The three theorems are Milne 3.1 and its two immediate neighbours
over a weaker field hypothesis; `PerfectField` is not `Field`, so a curve over an
**imperfect** field (`𝔽_p(t)` and its like) is outside all of them — measured,
not assumed: `PerfectField (RatFunc (ZMod p))` does not hold.  What the file buys
is that the remaining distance on the supply route is **one named link**, Milne
3.3's closed-point row argument, rather than the four-link chain the previous
costing described.
-/
universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ### Milne 3.1 and its two neighbours over a perfect field -/

/-- **Smooth + codim 1 ⇒ DVR, over a perfect field.**  `localRing_dvr_of_codim_one`
with the field hypothesis weakened: the geometric input is regularity of the
stalk (now the landed `isRegularLocalRing_stalk_of_smooth_of_perfectField` of
`Picard/Pic0Dimension.lean`, which is strictly stronger than the alg-closed
version this proof was transcribed from) and the rest is
the dimension bookkeeping, which never mentions the field. -/
theorem localRing_dvr_of_codim_one_perfectField
    {k : Type u} [Field k] [PerfectField k]
    (X : Over (Spec (.of k)))
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    (z : X.left) (hz : Order.coheight z = 1) :
    IsDiscreteValuationRing (X.left.presheaf.stalk z) := by
  haveI : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hreg : IsRegularLocalRing (X.left.presheaf.stalk z) :=
    isRegularLocalRing_stalk_of_smooth_of_perfectField X z
  have hdim : ringKrullDim (X.left.presheaf.stalk z) = 1 := by
    rw [Scheme.ringKrullDim_stalk_eq_coheight]
    exact_mod_cast hz
  have hfin :
      Module.finrank
        (IsLocalRing.ResidueField (X.left.presheaf.stalk z))
        (IsLocalRing.CotangentSpace (X.left.presheaf.stalk z)) = 1 := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hreg
    rw [hdim] at h
    exact_mod_cast h
  have hprin : Submodule.IsPrincipal
      (IsLocalRing.maximalIdeal (X.left.presheaf.stalk z)) :=
    IsLocalRing.finrank_cotangentSpace_le_one_iff.mp hfin.le
  have hne : IsLocalRing.maximalIdeal (X.left.presheaf.stalk z) ≠ ⊥ := by
    intro hbot
    have hF : IsField (X.left.presheaf.stalk z) :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot
    have h0 : ringKrullDim (X.left.presheaf.stalk z) = 0 :=
      ringKrullDim_eq_zero_of_isField hF
    rw [hdim] at h0
    exact_mod_cast h0
  have hfield : ¬ IsField (X.left.presheaf.stalk z) := fun hF =>
    hne ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF)
  exact ((IsDiscreteValuationRing.TFAE (X.left.presheaf.stalk z) hfield).out 0 4).mpr hprin

namespace RationalMap

/-- **Milne Theorem 3.1 over a perfect field.**  For a rational map `f : X ⇢ Y`
of varieties over a perfect field `k` with `X` nonsingular and `Y` complete,
every point of the indeterminacy locus has coheight at least `2`.

The proof is `indeterminacy_codimGe2_of_smooth_of_complete`'s, verbatim except
that the DVR step calls the perfect-field version.  The `IsAlgClosed` binder on
the original is not consumed anywhere else: the coheight-`0` branch is pure
topology of an irreducible sober space, and the coheight-`1` branch is the
valuative criterion at the DVR stalk, which asks nothing of the base field.

**This is the theorem `I-1115` said needed a new residue-degree-aware
ingredient.**  It needed none; the ingredient existed. -/
theorem indeterminacy_codimGe2_of_smooth_of_complete_perfectField
    {k : Type u} [Field k] [PerfectField k]
    {X : Over (Spec (.of k))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    {Y : Over (Spec (.of k))}
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
  have hspec : genericPoint X.left ⤳ z :=
    (genericPoint_spec X.left).specializes trivial
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
  · rw [Order.lt_one_iff] at h0
    have hmax : IsMax z := Order.coheight_eq_zero.mp h0
    have hzeq : z = genericPoint X.left :=
      ((show z ⤳ genericPoint X.left from hmax hspec).antisymm hspec).eq
    obtain ⟨w, hw⟩ := f.dense_domain.nonempty
    exact hzdom (hzeq ▸ (genericPoint_specializes w).mem_open f.domain.2 hw)
  · haveI hDVR : IsDiscreteValuationRing (X.left.presheaf.stalk z) :=
      localRing_dvr_of_codim_one_perfectField X z h1
    haveI : ValuationRing (X.left.presheaf.stalk z) := inferInstance
    have hVC : ValuativeCriterion Y.hom := by
      have hP : IsProper Y.hom := inferInstance
      rw [IsProper.eq_valuativeCriterion] at hP
      exact hP.1.1.1
    have hcommSq : CommSq f.fromFunctionField
        (Spec.map (CommRingCat.ofHom
          (algebraMap (X.left.presheaf.stalk z) X.left.functionField)))
        Y.hom (X.left.fromSpecStalk z ≫ X.hom) := ⟨by
      rw [hff, ← Category.assoc]
      congr 1
      exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hspec).symm⟩
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
    let L : Spec (X.left.presheaf.stalk z) ⟶ Y.left := L₀
    have hfacl : Spec.map (X.left.presheaf.stalkSpecializes hspec) ≫ L
        = f.fromFunctionField := hfacl₀
    have hfacr : L ≫ Y.hom = X.left.fromSpecStalk z ≫ X.hom := hfacr₀
    let g : X.left.PartialMap Y.left :=
      PartialMap.ofFromSpecStalk (x := z) X.hom Y.hom L hfacr
    have hzg : z ∈ g.domain :=
      PartialMap.mem_domain_ofFromSpecStalk (x := z) X.hom Y.hom L hfacr
    have hgL : g.fromSpecStalkOfMem hzg = L :=
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk (x := z) X.hom Y.hom L hfacr
    have hfactor : g.fromFunctionField =
        Spec.map (X.left.presheaf.stalkSpecializes hspec) ≫
          g.fromSpecStalkOfMem hzg := by
      dsimp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem]
      rw [← Category.assoc]
      congr 1
      rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    have hgen : g.toRationalMap = f := by
      refine RationalMap.eq_of_fromFunctionField_eq _ _ ?_
      rw [RationalMap.fromFunctionField_toRationalMap, hfactor, hgL]
      exact hfacl
    exact hzdom (RationalMap.mem_domain.mpr ⟨g, hzg, hgen⟩)

/-- **Milne Theorem 3.1, `CodimOneFree` phrasing, over a perfect field.** -/
theorem codimOneFree_of_smooth_of_complete_perfectField
    {k : Type u} [Field k] [PerfectField k]
    {X : Over (Spec (.of k))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    {Y : Over (Spec (.of k))}
    [IsProper Y.hom] [GeometricallyIrreducible Y.hom]
    [IsIntegral Y.left] [IsReduced Y.left]
    (f : X.left.RationalMap Y.left)
    (hf : f.compHom Y.hom = X.hom.toRationalMap) :
    CodimOneFree f := by
  intro x hx
  by_contra hnotin
  have h2 :=
    indeterminacy_codimGe2_of_smooth_of_complete_perfectField f hf x hnotin
  rw [hx] at h2
  norm_num at h2

end RationalMap

end Scheme

end AlgebraicGeometry
