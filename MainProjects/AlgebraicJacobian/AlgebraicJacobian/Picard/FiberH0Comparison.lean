/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RigidPushforwardRank

/-!
# The fibre `h⁰` comparison, without projectivity

**The bridge B5 needs, and the one `rank_pushforward_eq_fiberH0` cannot give.**

`AlgebraicGeometry.rank_pushforward_eq_fiberH0` (`Picard/RigidPushforwardRank.lean`)
proves `sectionsRankAtStalk (p_* M) t = p.fiberH0 M t` under three hypotheses
`hfin`, `hproj`, `hbc`.  Its own module docstring establishes that `hproj`
(`Module.Projective` of the Čech `H⁰`) is **load-bearing**: dropped, the
statement is false, with the counterexample `A = k[x]`,
`M = 𝒪_{ℙ¹_A}/x` recorded at `Picard/RigidPushforwardP1Sheaf.lean`:567-576.

That is true of *that* statement, and it has been read as a bound on what the
machinery can deliver.  It is not.  Reading which step consumes which
hypothesis shows `hfin` and `hproj` are used **only in step 1**, the appeal to
`Module.rankAtStalk_eq` that converts `sectionsRankAtStalk` — a
`Module.rankAtStalk`, which is a statement about the module being flat — into a
fibre dimension.  Steps 2 through 6, the entire semilinear transport

```
κ(t)-fibre of Γ(p_* M, ⊤)  ≅  κ(t) ⊗ ker d  ≅  ker (d ⊗ κ(t))
                           ≅  ker d_t       ≅  Γ(X_t, M_t)
```

consume **neither `hfin` nor `hproj`** — verified by a fresh-context review,
which reproduced the original from this theorem by adding only
`Module.rankAtStalk_eq`.  So this file states the comparison with those two
hypotheses removed:

* `fiberRank_gammaTop_eq_fiberH0` — no `hfin`, no `hproj`, only `hbc`.

**But dropping `hfin` has a cost, and it must be stated here rather than
discovered later.**  The original's docstring
(`Picard/RigidPushforwardRank.lean`:138-145) closes a junk-value hazard:
`Module.finrank` returns `0` in the infinite-dimensional case, on *both* sides,
so the identity could hold vacuously as `0 = 0`.  Its argument that this cannot
happen runs entirely through `hfin` (`ker d` finite ⟹ `κ(t) ⊗ ker d` is
finite-dimensional ⟹ steps 3-6 carry that to `Γ(X_t, M_t)`).  `hbc` does **not**
replace it: taking `d = 0 : M₀ →ₗ[A] PUnit` makes `hbc` hold for every `B`
(trivially surjective) with `ker d = M₀` arbitrary, so an infinite-dimensional
`ker d` is compatible with `hbc` and both sides then read `0`.

So the theorem below is honest but weaker than the original in a way the
hypothesis list alone does not show: **it is informative only where `ker d` is
finite-dimensional over `κ(t)`**, and it does not certify that itself.  A
consumer wanting a non-vacuous reading must supply finite-dimensionality
separately — which is *not* the same as supplying `hfin` (`Module.Finite` over
the base), and is the reason the statement is still worth having.

## What this buys for B5, and the obligation it does NOT remove

`Scheme.HasH0Semicontinuity` (`Picard/SemicontinuityH0.lean`) asks for openness
of `{t | q.fiberH0 L t ≤ n}`.  The `sectionsRankAtStalk` form cannot be an input
to it: semicontinuity is only informative where the fibre dimension *jumps*, and
`hproj` forces it locally constant (`Module.isLocallyConstant_rankAtStalk`).
The `Ideal.fiberRank` form here has no such effect, which is the point of the
restatement.

**It does not, however, already match
`Scheme.Modules.isOpen_pointRank_le`** (`Picard/PointRankSemicontinuity.lean`),
and an earlier revision of this docstring claimed it did.  Measured: the two are
*not the same term* and `rfl` between them fails.  `pointRank` unfolds (through
`pointRank_eq_chartFiberRank` at `V = ⊤`) to a `fiberRank` taken at a prime of
`Γ(Spec R, ⊤)` with the `Γ(Spec R, ⊤)`-module structure, whereas the conclusion
below uses `t.asIdeal` for `t : PrimeSpectrum R` with the `R`-module structure.
Bridging them needs a `ΓSpecIso` transport of exactly the kind steps 2 and 6
perform by hand, and the only in-tree lemma relating the two worlds,
`Scheme.Modules.rankAtStalk_sections_eq_pointRank`
(`Picard/FlatteningStratificationUniversal.lean`:204), carries
`[Module.Flat]` + `[Module.Finite]` binders — i.e. precisely what was dropped.

So B5 has **three** open obligations, not one: (a) `hbc` without
`h¹`-vanishing, (b) finite-dimensionality to defeat the junk-value reading, and
(c) this carrier bridge between `pointRank` and `Ideal.fiberRank`.  (c) was
unlisted until a fresh-context review found it.

**CORRECTED, and both corrections are against this list, not against the Lean
below.** Two of those three have since been repriced or closed:

* **(b) is CLOSED** — `Picard/TwoTermKernelSemicontinuity.lean`.  Stated on a
  two-term complex `k : K → Aⁿ` with `K` merely `Module.Finite`,
  finite-dimensionality of both fibres is *synthesised*, not supplied: it is a
  consequence of the shape, so no hypothesis defeats the junk-value reading —
  there is nothing to defeat.
* **(a) was MISPRICED, and the misprice is mine.**  The counterexample below is
  correct and `hbc` really is not free.  But `hbc` is consumed in **step 3
  only**, whose job is to cross from `ker (d ⊗ κ(t))` to `κ(t) ⊗ ker d` — that
  is, to reach *this* theorem's conclusion about `Γ(p_* M, ⊤)`.  Steps 4-6 alone
  already give `dim ker (d ⊗ κ(t)) = p.fiberH0 M t`, with no `hbc` at all;
  that is `finrank_ker_moduleSectionDiffBase_baseChange_eq_fiberH0`
  (`Picard/FiberH0CechKernel.lean`).  So `hbc` identifies the fibre of the
  *pushforward's section module*; it does **not** identify the fibre `h⁰`, and a
  route through the fibrewise Čech kernel does not owe it.

(c) stands, unchanged.  What replaces (a) is a different obligation: the Čech
difference map must be *replaced* by a complex of the engine's shape, and
`TwoTermFiniteReplacement.h0_bijective` — not `kerBaseChange` — is where the
residual cohomology-and-base-change content sits.

## What is still open

The remaining hypothesis `hbc` — bijectivity of
`AlgebraicJacobian.TwoTerm.kerBaseChange` over every algebra — is *not* free,
and it is worth being precise about why, because the temptation is to hope it
falls out of flatness.

Its only producer in the tree,
`TwoTerm.bijective_kerBaseChange_of_surjective`, needs `d` **surjective** —
i.e. `h¹`-vanishing.  Surjectivity is genuinely necessary and not an artefact
of that proof: take `A = ℤ`, `d = (2 · ·) : ℤ → ℤ`, which is injective with
both terms flat but not surjective.  Then `ker d = 0`, so `B ⊗ ker d = 0` for
every `B`, while over `B = ℤ/2` the base-changed map is zero and
`ker (d ⊗ B) = ℤ/2 ≠ 0`.  So `kerBaseChange` is not bijective, with flatness
of both terms intact.

What this file therefore does is **relocate** part of the B5 obligation, not
discharge it.  It converts "find a projectivity-free rank bridge" — impossible,
and the route the gate's own docstring prescribes — into the three named items
(a), (b), (c) above, of which (a) is the honest half of
cohomology-and-base-change (Stacks 02KG).  Correctly located; all three open.

One route not yet followed: a `TwoTermFiniteReplacement` supplies
`h0_bijective` for *every* algebra `B` with **no** surjectivity hypothesis
(it is a field of the structure, and `exists_twoTermFiniteReplacement` needs
only noetherian + flat + f.g. cohomology).  That is a comparison between the
`H⁰`s of the replacement and original complexes rather than the
`kerBaseChange` of one map, so it does not immediately give `hbc`; whether it
can be made to is the next thing to try.

## References

Stacks 02KG (cohomology and base change at `i = 0`), 00NX; Mumford,
*Abelian Varieties*, II §5; Hartshorne III 12.8, 12.11.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Module Limits TensorProduct

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- **The fibre-`h⁰` comparison, with no projectivity and no finiteness.**

For quasi-compact quasi-separated `p : X ⟶ Spec R`, quasi-coherent `M` carrying
a two-chart affine cover `𝒰`, and `t : Spec R` with affine fibre inclusion, the
`κ(t)`-fibre dimension of the base section module `Γ(p_* M, ⊤)` equals the
fibre `h⁰`, assuming only the base-change bijectivity `hbc`.

This is steps 2-6 of `rank_pushforward_eq_fiberH0` with step 1 — the only step
that consumes `hfin`/`hproj` — removed, and the conclusion restated on
`Ideal.fiberRank` rather than on `sectionsRankAtStalk`.  See the module
docstring for why that restatement is what milestone B5 needs. -/
theorem fiberRank_gammaTop_eq_fiberH0
    (p : X ⟶ Spec R) (𝒰 : X.AffineCoverMVSquare) (M : X.Modules)
    [M.IsQuasicoherent] [QuasiCompact p] [QuasiSeparated p]
    (t : PrimeSpectrum R) [IsAffineHom (p.fiberι t)]
    (hbc :
      letI := p.baseSectionsModule M 𝒰.U₁
      letI := p.baseSectionsModule M 𝒰.U₂
      letI := p.baseSectionsModule M (𝒰.U₁ ⊓ 𝒰.U₂)
      ∀ (B : Type u) [CommRing B] [Algebra Γ(Spec R, ⊤) B],
        Function.Bijective (AlgebraicJacobian.TwoTerm.kerBaseChange
          (𝒰.moduleSectionDiffBase p M) B)) :
    Module.finrank t.asIdeal.ResidueField
        (t.asIdeal.Fiber Γ((Scheme.Modules.pushforward p).obj M, (⊤ : (Spec R).Opens)))
      = p.fiberH0 M t := by
  letI m1 := p.baseSectionsModule M 𝒰.U₁
  letI m2 := p.baseSectionsModule M 𝒰.U₂
  letI m0 := p.baseSectionsModule M (𝒰.U₁ ⊓ 𝒰.U₂)
  letI mT := p.baseSectionsModule M (⊤ : X.Opens)
  letI n1 := (p.fiberToSpecResidueField t).baseSectionsModule (p.fiberModule t M)
    ((𝒰.preimage (p.fiberι t)).U₁)
  letI n2 := (p.fiberToSpecResidueField t).baseSectionsModule (p.fiberModule t M)
    ((𝒰.preimage (p.fiberι t)).U₂)
  letI n0 := (p.fiberToSpecResidueField t).baseSectionsModule (p.fiberModule t M)
    ((𝒰.preimage (p.fiberι t)).U₁ ⊓ (𝒰.preimage (p.fiberι t)).U₂)
  letI nT := (p.fiberToSpecResidueField t).baseSectionsModule (p.fiberModule t M)
    (⊤ : (p.fiber t).Opens)
  letI aRK : Algebra Γ(Spec R, ⊤) Γ(Spec ((Spec R).residueField t), ⊤) :=
    (((Spec R).fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
  have e0 : Γ((Scheme.Modules.pushforward p).obj M, (⊤ : (Spec R).Opens))
      ≃ₗ[Γ(Spec R, ⊤)] LinearMap.ker (𝒰.moduleSectionDiffBase p M) :=
    (Scheme.Modules.pushforwardTopEquivBaseSections p M) ≪≫ₗ
      (𝒰.globalSectionsEquivKerModuleSectionDiffBase p M)
  -- STEP 2 (unconditional)
  have step2 : Module.finrank t.asIdeal.ResidueField
        (t.asIdeal.Fiber Γ((Scheme.Modules.pushforward p).obj M, (⊤ : (Spec R).Opens)))
      = Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
          (TensorProduct Γ(Spec R, ⊤) Γ(Spec ((Spec R).residueField t), ⊤)
            (LinearMap.ker (𝒰.moduleSectionDiffBase p M))) := by
    refine finrank_tensor_eq_of_ringEquiv
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
      (specResidueFieldRingEquiv R t) ?_ e0.toAddEquiv ?_
    · intro r
      have h := appLE_fromSpecResidueField_apply R t
        ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm r)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm
    · intro r n
      rw [smul_gammaSpecTop ((Scheme.Modules.pushforward p).obj M) r n]
      exact e0.map_smul _ _
  have hbcK := hbc Γ(Spec ((Spec R).residueField t), ⊤)
  have step3 : Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
        (TensorProduct Γ(Spec R, ⊤) Γ(Spec ((Spec R).residueField t), ⊤)
          (LinearMap.ker (𝒰.moduleSectionDiffBase p M)))
      = Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
          (LinearMap.ker (((𝒰.moduleSectionDiffBase p M).baseChange
            Γ(Spec ((Spec R).residueField t), ⊤)))) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ hbcK)
  have step4 := finrank_ker_baseChange_residueField 𝒰 p M t
  have step5 : Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
        (LinearMap.ker ((𝒰.preimage (p.fiberι t)).moduleSectionDiffBase
          (p.fiberToSpecResidueField t) (p.fiberModule t M)))
      = Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
          Γ(p.fiberModule t M, (⊤ : (p.fiber t).Opens)) :=
    (LinearEquiv.finrank_eq ((𝒰.preimage (p.fiberι t)).globalSectionsEquivKerModuleSectionDiffBase
      (p.fiberToSpecResidueField t) (p.fiberModule t M))).symm
  have step6 : Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
        Γ(p.fiberModule t M, (⊤ : (p.fiber t).Opens))
      = p.fiberH0 M t := by
    letI := p.fiberSectionsModule t (p.fiberModule t M)
    refine finrank_eq_of_ringEquiv_addEquiv
      (Scheme.ΓSpecIso ((Spec R).residueField t)).commRingCatIsoToRingEquiv
      (AddEquiv.refl _) ?_
    intro r m
    change r • m = _
    rw [Scheme.Hom.baseSectionsModule_smul_def]
    change _ = ((p.fiberResidueMap t).hom
      ((Scheme.ΓSpecIso ((Spec R).residueField t)).commRingCatIsoToRingEquiv r)) • m
    congr 1
    simp only [Scheme.Hom.fiberResidueMap, CommRingCat.hom_comp, RingHom.comp_apply]
    have hLE : (p.fiberToSpecResidueField t).appLE ⊤ ⊤ le_top
        = (p.fiberToSpecResidueField t).appTop := Scheme.Hom.appLE_eq_app _
    rw [hLE]
    congr 1
    have h1 := congrArg (fun φ : Γ(Spec ((Spec R).residueField t), ⊤) ⟶
        Γ(Spec ((Spec R).residueField t), ⊤) => φ.hom r)
      (Scheme.ΓSpecIso ((Spec R).residueField t)).hom_inv_id
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at h1
    exact h1.symm
  rw [step2, step3, step4, step5, step6]

end AlgebraicGeometry
