/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.Pic0Et
import AlgebraicJacobian.Picard.Pic0AbelianVariety
import AlgebraicJacobian.RiemannRoch.Adelic.GenusUnconditional
import AlgebraicJacobian.Genus

/-!
# The tangent space of `Pic⁰_{C/k}` in its étale formulation

The Kleiman §5 Thm. `thm:tgtsp` dimension development for `Scheme.Pic0SchemeEt C`
— the identity component of the scheme representing the **étale-sheafified**
relative Picard functor, which is the object the Jacobian headline binds
(`picardJacobianWitness`, `AlgebraicJacobian/Jacobian.lean`).

## Why this file exists

`Picard/Pic0AbelianVariety.lean` develops the same chain for `Pic0Scheme C`, the
identity component of the scheme representing the *unsheafified* `picSharp C`.
That development carries `[HasPicScheme C]`, a class with no instance whose only
producer is the conditional `picSchemeOfHasRationalPoint` — so it is a statement
about a *pointed* curve, and the headline's dimension leaf
`smoothOfRelativeDimension_genus_pic0Et` cannot consume it.

## What this file corrects

`Jacobian.lean` priced the étale dimension leaf as needing "the comparison of the
two Picard schemes, which is available only under a section" — i.e. exactly the
hypothesis the owner decision `I-0491` forbids the headline to carry. **That
pricing is wrong, and this file is the refutation.** Every engine of the
dual-number leg is quantified over an arbitrary functor and an arbitrary
`RepresentableBy`:

* `Pic0.pointedDualNumberPointsEquivRepresentableFiber` and
  `pointedDualNumberPointsEquivAddKernel`
  (`Picard/Pic0DualNumberCocycle.lean`) take `(G, rep)` as arguments;
* `pointedDualNumberPointsEquivOfOpenImmersion` (`Picard/Pic0TangentSpace.lean`)
  takes an arbitrary morphism with open-immersion underlying map;
* `overDualNumberSectionEquivCotangentSpaceDual`
  (`Picard/TangentSpaceIdentitySection.lean`) takes an arbitrary `X` and section.

`picSharp` entered only at the two *application* sites of
`Pic0AbelianVariety.lean`. Here the same engines are applied to
`(PicSharp.etaleSheaf C).obj` with `representableEt` — which is precisely the
`(G, rep)` pair they ask for, and which needs no rational point.

## What is proved and what remains

Proved outright, with no rational point and no `[HasPicScheme C]`:
`identitySection`, `pointedDualNumberPoints_equiv_cotangentSpaceDual`,
`pointedDualNumberPoints_equiv_relPicEtKernel` (the representability leg **against
`picEt`**), `cotangentSpaceDual_equiv_relPicEtKernel`, and
`finiteDimensional_cotangentSpace`.

**What "axiom-clean" does and does not mean here**, since every declaration in this file
binds `[HasPicSchemeEt C]` and `#print axioms` on each reports only
`[propext, Classical.choice, Quot.sound]`. That is a statement about the *implications*: a
bound instance argument is never unfolded. At any real use site the unconditional
`instHasPicSchemeEt` fires, and its body is `(fgaPicardRepresentability C).1` — the
project's central `sorry`. So instantiating any declaration below at a bare curve reports
`sorryAx`. The honest phrasing, which the commit messages should have used: these add **no
new `sorry`**, and are axiom-clean *conditional on the `sorry`-backed `HasPicSchemeEt`
gate*. Nothing in this file is unconditional in the stronger sense of holding for a curve
today. Recorded after a fresh-context audit (`I-0988`).

The dimension identity itself is stated as an **implication**. Its single antecedent is
`SemilinearCotangentComparisonEt`, which is clause for clause the same *shape* as the
`picSharp` side's own open residue
`Pic0.semilinearComparison_cotangentSpaceDual_h1Cok` (`Pic0AbelianVariety.lean`, a bare
`sorry`): same `∀ S`, same `∃ i j`, same bijectivity, same intertwining. This file adds
**no `sorry` of its own**; the antecedent is a named hypothesis, not a discharged
obligation.

**It is one statement, but not the *same* statement — corrected after a fresh-context
audit (`I-0989`).** An earlier version of this paragraph said the étale formulation owes
"the same one statement the pointed formulation owes, and no more". The count is right and
the shape is right; the identification is not. The two antecedents compare **different
carriers**:

* on the `picSharp` side the kernel is a kernel of `PicSharp.relPresheaf`, whose elements
  are honest invertible-sheaf classes (a quotient of `LineBundle.OnProduct`), and the
  residue is priced there as a Čech-to-invertible-sheaves comparison at a non-affine
  scheme;
* here the kernel description lands in a kernel of `(PicSharp.etaleSheaf C).obj` — the
  **sheafification** — so its elements are sheafification classes.

Reusing the `picSharp` cocycle argument therefore needs a bridge from the sheafified
kernel back to the presheaf kernel at `Spec k[ε]`, and no such lemma exists in the
project. The two agree under a section (`picEtComparison_isIso_of_hasRationalPoint`), which
is exactly the hypothesis `I-0491` forbids and that this formulation exists to avoid. So
the étale antecedent additionally absorbs the sheafification-versus-presheaf step: not
extra `sorry`s and not a weakening, but unnamed cost inside a named hypothesis, named here.

What this file does **not** do, stated plainly because it is easy to overread:
it does not close the headline leaf `smoothOfRelativeDimension_genus_pic0Et`.
That leaf needs, over and above the dimension count, the passage from a
tangent-space dimension to Mathlib's presentation-based
`SmoothOfRelativeDimension` (characterised by `Module.rank S Ω[S⁄R]`), plus
`Pic0Et.smooth` itself. Those are recorded on the leaf and are untouched here.

## References

Kleiman, "The Picard scheme" (arXiv:math/0504020), §5 Thm. `thm:tgtsp`.
Mumford, "Abelian varieties", §II.4 (the tangent-vector scaling).
-/

set_option autoImplicit false

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

namespace Scheme

namespace Pic0Et

variable {k : Type u} [Field k]

/-! ## §1. The identity section of `Pic⁰_{C/k}` -/

/-- **The `k`-rational identity-section point of `Pic⁰_{C/k}`**, étale
formulation: the lift of the identity section of `PicSchemeEt C` through the
clopen immersion `Pic⁰_{C/k} ↪ Pic_{C/k}`.

`GroupScheme.identityComponentSection` needs `[GrpObj G]` and
`[LocallyOfFiniteType G.hom]` on `G = PicSchemeEt C`; both are available with no
hypothesis on `C(k)` — the first from `groupSchemeStructureEt` (Yoneda transport
of the étale sheaf's abelian-group structure) and the second from
`instPicSchemeEtLocallyOfFiniteType`. This is the étale counterpart of
`Pic0.identitySection`, which carries `[HasPicScheme C]`. -/
noncomputable def identitySection (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    Spec (.of k) ⟶ (Pic0SchemeEt C).left :=
  GroupScheme.identityComponentSection (PicSchemeEt C)

/-- The identity-section point is a genuine section of the structural morphism.
Transport of `GroupScheme.identityComponentSection_isSection`. -/
theorem identitySection_isSection (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    identitySection C ≫ (Pic0SchemeEt C).hom = 𝟙 (Spec (.of k)) :=
  GroupScheme.identityComponentSection_isSection (PicSchemeEt C)

/-- The residue field of the local ring at the identity of `Pic⁰_{C/k}`. -/
noncomputable abbrev identityResidueField (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :=
  ResidueField ((Pic0SchemeEt C).left.presheaf.stalk ((identitySection C).base default))

/-- The Zariski cotangent space `m_e/m_e²` at the identity of `Pic⁰_{C/k}`. -/
noncomputable abbrev identityCotangentSpace (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :=
  CotangentSpace ((Pic0SchemeEt C).left.presheaf.stalk ((identitySection C).base default))

/-! ## §2. The two legs of Kleiman §5 Thm. `thm:tgtsp`, étale formulation -/

/-- **The Stacks 0B28 dictionary at the identity**, étale formulation: pointed
dual-number points of `Pic⁰_{C/k}` at the identity biject with `κ(e)`-linear
functionals on the cotangent space `m_e/m_e²`.

Direct specialisation of `overDualNumberSectionEquivCotangentSpaceDual`
(`Picard/TangentSpaceIdentitySection.lean`) to `e = identitySection C`; that
engine is generic in the scheme and the section, so this needs nothing about
`picEt` beyond the section being a section. Étale counterpart of
`Pic0.pointedDualNumberPoints_equiv_cotangentSpaceDual`. -/
theorem pointedDualNumberPoints_equiv_cotangentSpaceDual (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    Nonempty (Pic0.pointedDualNumberPoints (Pic0SchemeEt C) (identitySection C) ≃
      Module.Dual (identityResidueField C) (identityCotangentSpace C)) := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  exact ⟨overDualNumberSectionEquivCotangentSpaceDual (Pic0SchemeEt C)
    (identitySection_isSection C) (congrArg _ (Subsingleton.elim _ _))⟩

/-- **The representability leg, against `picEt` and with no rational point** —
the declaration whose absence `Jacobian.lean` priced as a section-gated
transport.

`T_e Pic⁰_{C/k}` biject with the kernel of the restriction homomorphism
`Pic_{(C/k)ét}(Spec k[ε]) →+ Pic_{(C/k)ét}(Spec k)`. Composite of

1. the open-immersion transport `T_e Pic⁰ ≃ T_e Pic` along the clopen inclusion
   (`pointedDualNumberPointsEquivOfOpenImmersion`), and
2. the represented-functor kernel description
   (`pointedDualNumberPointsEquivAddKernel`) applied at
   `G = (PicSharp.etaleSheaf C).obj` — the `AddCommGrpCat`-valued étale Picard
   sheaf — with `rep = representableEt C`.

Step 2 is the whole point: that engine takes an arbitrary `AddCommGrpCat`-valued
`G` together with a `RepresentableBy` for `G ⋙ forget`, and by definition
`picEt C = (PicSharp.etaleSheaf C).obj ⋙ forget AddCommGrpCat`
(`Picard/PicEtSheaf.lean`), so `representableEt C` **is** that datum. No
comparison between the two Picard schemes occurs anywhere in the proof, and the
étale-sheafified functor is the one whose kernel is described.

Étale counterpart of `Pic0.pointedDualNumberPoints_equiv_relPicKernel`. Like it,
this is a bijection of **sets**: transporting `finrank` needs the `k`-linearity
bookkeeping, which stays with the dimension identity below. -/
theorem pointedDualNumberPoints_equiv_relPicEtKernel (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    Nonempty (Pic0.pointedDualNumberPoints (Pic0SchemeEt C) (identitySection C) ≃
      {a : ((PicSharp.etaleSheaf C).obj).obj (Opposite.op (overDualNumber k)) //
        (((PicSharp.etaleSheaf C).obj).map (overDualNumberZero k).op).hom a = 0}) := by
  obtain ⟨f, hopen, -⟩ :=
    GroupScheme.IdentityComponent.isOpenSubgroupScheme (PicSchemeEt C)
  haveI := hopen
  have he' : (identitySection C ≫ f.left) ≫ (PicSchemeEt C).hom = 𝟙 (Spec (.of k)) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => identitySection C ≫ t) (Over.w f)).trans
        (identitySection_isSection C))
  exact ⟨(pointedDualNumberPointsEquivOfOpenImmersion f (identitySection C)).trans
    (pointedDualNumberPointsEquivAddKernel (PicSchemeEt C)
      ((PicSharp.etaleSheaf C).obj) (representableEt C) he')⟩

/-- **The two legs composed**, étale formulation: the `κ(e)`-linear dual of the
cotangent space at the identity of `Pic⁰_{C/k}` bijects with the dual-number
kernel of `Pic_{(C/k)ét}`. Étale counterpart of
`Pic0.cotangentSpaceDual_equiv_relPicKernel`, and a bijection of sets for the
same reason. -/
theorem cotangentSpaceDual_equiv_relPicEtKernel (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    Nonempty (Module.Dual (identityResidueField C) (identityCotangentSpace C) ≃
      {a : ((PicSharp.etaleSheaf C).obj).obj (Opposite.op (overDualNumber k)) //
        (((PicSharp.etaleSheaf C).obj).map (overDualNumberZero k).op).hom a = 0}) := by
  obtain ⟨φ⟩ := pointedDualNumberPoints_equiv_cotangentSpaceDual C
  obtain ⟨ψ⟩ := pointedDualNumberPoints_equiv_relPicEtKernel C
  exact ⟨φ.symm.trans ψ⟩

/-- Finite-dimensionality of the cotangent space at the identity, from the
unconditional `Pic0Et.locallyOfFiniteType`. Needed for the duality step of the
dimension chain. -/
theorem finiteDimensional_cotangentSpace (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    FiniteDimensional (identityResidueField C) (identityCotangentSpace C) := by
  haveI : LocallyOfFiniteType (Pic0SchemeEt C).hom := locallyOfFiniteType C
  exact Pic0.finiteDimensional_cotangentSpace_of_locallyOfFiniteType (Pic0SchemeEt C) _

/-! ## §3. The dimension identity, as an implication with one named antecedent -/

/-- **The one open input of the étale dimension count**, named so that the
implication below has an auditable antecedent rather than a `sorry`.

This is the étale restatement of `Pic0.semilinearComparison_cotangentSpaceDual_h1Cok`
(`Picard/Pic0AbelianVariety.lean`, a bare `sorry`): for every 2-affine cover `S`
of `C`, an additive equivalence between the dual of the cotangent space at the
identity of `Pic⁰_{C/k}` and the concrete two-chart Čech cokernel
`S.H1Cok (toModuleKSheaf C)`, together with a bijection `i` of the two scalar
rings intertwining the actions — exactly the data
`Pic0.finrank_eq_of_addEquiv_of_bijective_smul` consumes, and no more.

`i` need only be a bijection of the underlying types, not a ring map: the
`κ(e)`-dimension of the left side is compared with the `k`-dimension of the right
side across the residue-field identification, so neither
`LinearEquiv.finrank_eq` nor `restrictScalars` applies.

**Non-vacuity.** `C` occurs three times in the body — in the cover `S`, in the cotangent
space, and in the sheaf `toModuleKSheaf C` — so this is not the `HasDivFunctor` failure
mode, where the curve did not occur at all. It is a genuine two-sided constraint: it
implies a non-trivial `finrank` identity, and it is not satisfiable by making the left
carrier trivial (an `exact?` search cannot produce `Subsingleton` for it at these
hypotheses). At `genus C = 0` the *right* carrier does become trivial — see
`subsingleton_h1Cok_of_genus_eq_zero` below — but that discharges one carrier, not the
hypothesis.

**The honest state, and what this hypothesis costs.** Two pieces of missing mathematics,
not one:

1. what `Pic0AbelianVariety.lean` records at its own residue — exhibiting the map that
   sends a dual-number kernel class to its transition unit, i.e. a
   Čech-to-invertible-sheaves comparison at a *non-affine* scheme. Nothing here reduces
   that;
2. **and, specific to this side**, the passage between the sheafified kernel this
   comparison is stated against and the `relPresheaf` kernel that argument is about. See
   the module header: the `picSharp` residue's carrier is a quotient of
   `LineBundle.OnProduct`, this one's is a sheafification class, and the project has no
   lemma relating the two without a section.

So the étale side needs one hypothesis rather than two, and needs nothing about a section —
but that hypothesis is strictly harder than its `picSharp` namesake, and clause 2 is why.
Recorded here rather than only in the inbox (`I-0989`) because a reader pricing future work
off this file would otherwise inherit the understatement.

**QUANTIFIER WEAKENED 2026-07-29 r2, and the previous form overcharged the leaf**
(`I-1059`, `work-reviewer`; the over-specification was mine). This was stated with
`∀ S : C.left.AffineCoverMVSquare`, while its only consumer
`finrank_cotangentSpace_eq_finrank_hModuleOne` instantiates it at exactly **one** cover —
the one `Adelic.exists_affineCoverMVSquare_module_finite_H1Cok` hands it — so the
universal quantifier was never used. As written, a future lane owed a semilinear
comparison at *every* 2-affine cover of `C`; it owes one at a cover of its own choosing,
and the supplied cover already carries the finiteness such a proof wants. The `∀`-form
implies this one by instantiation, so nothing that consumed the old statement is
weakened, and this is the form the theorem actually consumes. -/
def SemilinearCotangentComparisonEt (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] : Prop :=
  ∃ (S : C.left.AffineCoverMVSquare) (i : identityResidueField C → k)
      (j : Module.Dual (identityResidueField C) (identityCotangentSpace C)
            ≃+ S.H1Cok (Scheme.toModuleKSheaf C)),
    Function.Bijective i ∧ ∀ r x, j (r • x) = i r • j x

/-- **The Kleiman §5 Thm. `thm:tgtsp` dimension identity for `Pic⁰_{C/k}`, étale
formulation**: `dim_{κ(e)} m_e/m_e² = dim_k H¹(C, 𝒪_C)` at the identity, with
**no rational point and no `[HasPicScheme C]`**.

Stated as an implication from `SemilinearCotangentComparisonEt`, which is the
whole open content. The other two legs of the chain are discharged here:

* `dim_{κ(e)} m_e/m_e² = dim_{κ(e)} Dual(m_e/m_e²)` — reflexivity of
  finite-dimensional duality (`Subspace.dual_finrank_eq`, finite-dimensionality
  from `finiteDimensional_cotangentSpace` above, i.e. from the unconditional
  `Pic0Et.locallyOfFiniteType`);
* `dim_k Ȟ¹(S, 𝒪_C) = dim_k H¹(C, 𝒪_C)` — the gate-free Mayer–Vietoris
  comparison `AffineCoverMVSquare.hModuleOneEquivH1Cok_curve`, at the 2-affine
  cover supplied unconditionally by
  `Adelic.exists_affineCoverMVSquare_module_finite_H1Cok`.

Both of those legs are the *same* lemmas the pointed side uses, applied at
`Pic0SchemeEt`: they are generic in the scheme. Étale counterpart of
`Pic0.finrank_cotangentSpace_eq_finrank_hModuleOne`, which reports `sorryAx`
through its own residue. -/
theorem finrank_cotangentSpace_eq_finrank_hModuleOne (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C]
    (hcomp : SemilinearCotangentComparisonEt C) :
    Module.finrank (identityResidueField C) (identityCotangentSpace C)
      = Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  haveI := finiteDimensional_cotangentSpace C
  obtain ⟨S, i, j, hi, hc⟩ := hcomp
  calc Module.finrank (identityResidueField C) (identityCotangentSpace C)
      = Module.finrank (identityResidueField C)
          (Module.Dual (identityResidueField C) (identityCotangentSpace C)) :=
        Subspace.dual_finrank_eq.symm
    _ = Module.finrank k (S.H1Cok (Scheme.toModuleKSheaf C)) :=
        Pic0.finrank_eq_of_addEquiv_of_bijective_smul i j hi hc
    _ = Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
        (LinearEquiv.finrank_eq S.hModuleOneEquivH1Cok_curve).symm

/-- **The dimension count in the form the headline leaf needs**: the tangent
space at the identity of `Pic⁰_{C/k}` has dimension `genus C`.

Immediate from the identity above, since `genus C` is *by definition*
`dim_k H¹(C, 𝒪_C)` (`AlgebraicJacobian/Genus.lean`) — the two sides match with no
transport, exactly as on the pointed side.

This is the number `smoothOfRelativeDimension_genus_pic0Et` (`Jacobian.lean`)
needs. It is **not** that leaf: the leaf needs `Pic0Et.smooth` and the passage from
a tangent-space dimension to Mathlib's presentation-based
`SmoothOfRelativeDimension` — two inputs, as the r1 revision of this paragraph
(mine) said.

An r2 revision (also mine) replaced that with "the leaf is **one** obligation, the
smoothness half absorbed". **That is RETRACTED** — a fresh-context audit refuted it
(`I-1094`) and I reproduced the refutation before accepting; the two-input pricing
above is restored. The bullet below states the audit's reasoning, and the second
bullet is what genuinely survives from r2:

* the leaf is **one** obligation. `SmoothOfRelativeDimension n` is a
  `HasRingHomProperty` over `Locally (IsStandardSmoothOfRelativeDimension n)`, and at
  chart level the graded condition implies the ungraded one, so pinning the numeral
  supplies smoothness with it (`Pic0Et.leafB_of_chartwise`, stated with no smoothness
  hypothesis). `Pic0Et.smooth` is *absorbed*, not subtracted. **REFUTED — do not plan
  from this bullet** (`I-1094`, `I-1097`; relayed by `review-ajc` after the measuring
  lane released). `leafB_of_chartwise` is `HasRingHomProperty.iff_appLE.mpr`, the class
  definitionally *unfolded*, and the lemma named as the absorption mechanism is invoked
  by no declaration in that file; smoothness is missing from the hypothesis because the
  unfolding never mentions it. And the unfolded form is **harder** than the class — it
  demands the chart condition on every pair `(U, V, e)` where the class field asks only
  that *some* affine pair exist at each point. The second bullet below (the number
  lives in a different place) is unaffected, as is `geometricallyReduced_of_leafB`;
* the number lives in a different **place**, not merely on a different invariant.
  What the leaf asks is `Module.rank S Ω[S⁄R] = genus C` on the away-localisations of
  affine chart algebras of `Pic⁰`; what this theorem gives is a `finrank` at the
  *identity*. Nothing here computes a chart.

What this theorem does remove from the leaf's cost is the transport along a section
that its docstring used to claim to require. -/
theorem finrank_cotangentSpace_eq_genus (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [GeometricallyIntegral C.hom] [HasPicSchemeEt C]
    (hcomp : SemilinearCotangentComparisonEt C) :
    Module.finrank (identityResidueField C) (identityCotangentSpace C) = genus C :=
  finrank_cotangentSpace_eq_finrank_hModuleOne C hcomp

/-- **Half of the antecedent is free at `genus C = 0`, and the other half is not** —
recorded as a theorem so the boundary is measured rather than asserted.

At genus `0` the Čech side of `SemilinearCotangentComparisonEt` is `Subsingleton` for
*every* 2-affine cover, unconditionally: `genus C` is by definition
`dim_k H¹(C, 𝒪_C)`, so `genus C = 0` gives `Subsingleton (H¹(C, 𝒪_C))` by
`Module.finrank_zero_iff` (legitimate here because the genus carrier is a finite
`k`-module, `Adelic.instModuleFiniteHModuleOne`), and the gate-free Mayer–Vietoris
equivalence carries that to `S.H1Cok`.

**What this does not give**, and it is the reason the antecedent stays open even in the
degenerate case: the *other* side of the comparison is the dual of the cotangent space at
the identity of `Pic⁰_{C/k}`, and nothing in the tree makes that `Subsingleton` — an
`exact?` search at exactly these hypotheses fails. Making it vanish is the assertion that
`Pic⁰_{C/k}` is `0`-dimensional, which is the conclusion the comparison is *for*. So
`genus C = 0` does not inhabit the antecedent; it discharges one of its two carriers.

This is worth a declaration because the natural next move on a hypothesis like this is to
look for a degenerate instantiation, and here that move gets exactly halfway. -/
theorem subsingleton_h1Cok_of_genus_eq_zero (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] [GeometricallyIntegral C.hom]
    (hg : genus C = 0) (S : C.left.AffineCoverMVSquare) :
    Subsingleton (S.H1Cok (Scheme.toModuleKSheaf C)) := by
  have h0 : Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) = 0 := hg
  haveI : Subsingleton (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
    Module.finrank_zero_iff.mp h0
  exact Function.Injective.subsingleton
    (f := (S.hModuleOneEquivH1Cok_curve (C := C)).symm) (LinearEquiv.injective _)

/-! ## §4. The keystone: `T₀ Pic⁰_{C/k} ≅ H¹(C, 𝒪_C)` -/

/-- **The Kleiman §5 Thm. `thm:tgtsp` tangent-space isomorphism at the étale
`Pic⁰`**: the Zariski tangent space at the identity of `Pic⁰_{C/k}` is
isomorphic, as an additive group, to `H¹(C, 𝒪_C)` — over an arbitrary base
field, with no rational point.

From the dimension identity through `nonempty_cotangentSpaceAddEquiv_of_finrank_eq`
(`Picard/Pic0TangentSpace.lean`), which is generic in the scheme and the section:
for `X` locally of finite type over `Spec k`, a section `e`, and a finite
`k`-module `W`, an equality of the two dimensions yields `m_e/m_e² ≃+ W`. Its
three inputs are all unconditional here — `Pic0Et.locallyOfFiniteType`,
`identitySection_isSection`, and the genus lane's `instModuleFiniteHModuleOne`.

Étale counterpart of `Pic0.tangentSpaceIso`, and the same shape: existentially
bundled over the identity-section point, additive rather than `k`-linear (the
underlying additive structure is what the dimension corollary consumes).

Its single antecedent is the same `SemilinearCotangentComparisonEt`, so this
keystone costs nothing beyond the dimension identity. -/
theorem tangentSpaceIso (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C]
    (hcomp : SemilinearCotangentComparisonEt C) :
    Nonempty (Σ' (e : Spec (.of k) ⟶ (Pic0SchemeEt C).left),
      CotangentSpace ((Pic0SchemeEt C).left.presheaf.stalk (e.base default))
        ≃+ Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  haveI : LocallyOfFiniteType (Pic0SchemeEt C).hom := locallyOfFiniteType C
  exact (nonempty_cotangentSpaceAddEquiv_of_finrank_eq (Pic0SchemeEt C)
      (identitySection_isSection C) (Scheme.HModule k (Scheme.toModuleKSheaf C) 1)
      (finrank_cotangentSpace_eq_finrank_hModuleOne C hcomp)).map
    fun φ => ⟨identitySection C, φ⟩

end Pic0Et

end Scheme

end AlgebraicGeometry
