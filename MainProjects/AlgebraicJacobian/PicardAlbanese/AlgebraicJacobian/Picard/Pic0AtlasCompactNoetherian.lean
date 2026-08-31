/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AtlasCompactFromClass
-- Imported so that the coverage lemma this file's docstrings CITE is in its own import closure:
-- a cited name that resolves only by `grep` is a name this file cannot see, and that failure mode
-- has recurred in this project (I-1073, I-0994).  `pointwise_of_pointwise_restrictChart` is the
-- converse that makes single-index coverage equivalent to unrestricted one-chart coverage, which
-- is why `Finite ι` below is not cheap.
import AlgebraicJacobian.Picard.Pic0ChartAtlasCoupling

/-!
# The per-chart half of `hcpt` was NOT free: the charts are OPENS, and openness needs noetherianity

Three files price the atlas's `CompactSpace` input, and all three split it the same way: the
per-chart half is "free at the divisor-representability lane's own carrier", the index-finiteness
half is the obstruction.  The first half of that split is **about the wrong object**.

`Pic0AtlasFiniteType.lean`'s `Discharged` section exhibits
`CompactSpace (divSchemeOver k A B n r₁ r₂ b₁ b₂).left` by `inferInstance` and calls it "the
compactness input of `JacobianData.ofCharts`'s finite route, at the same carrier".  But the charts
of the atlas are not the representing objects.  `mixedParamChart` is
`restrictChart (abelSigmaChart …) (V i)`, whose source is `yoneda.obj ((V i : Scheme))` — an
**open subscheme** of `(D i).left`.  So `compactSpace_of_finite_atlas`'s hypothesis
`∀ i, CompactSpace (X i)` is compactness of `(V i : Scheme)`, and *that* is not an instance:

> `example … (V : (divSchemeOver …).left.Opens) : CompactSpace (V : Scheme) := by infer_instance`

fails.  Compactness does not pass to open subspaces, so the sentence three sites carry is true of
`divSchemeOver` and false of the object the hypothesis is about.

**How large the gap is depends on a claim this tree does not prove, and an earlier version of this
header asserted it as fact.**  That version said `V ≠ ⊤` is *forced*, because "the `hf` certificate
is false for the Abel chart at `V = ⊤`", citing `Pic0ChartPair.lean:134`.  That line is a
docstring assertion, not a theorem: there is **no** `¬ IsOpenImmersion.presheaf` declaration
anywhere in this project (measured by search, not by grep for one spelling).  So the honest form is
weaker — for `V = ⊤` the ambient instance would suffice and the gap would be invisible, and nothing
in Lean rules that `V` out.  What *is* certain is that the lemma below is needed for a general `V`,
which is what `mixedParamChart` quantifies over; whether `V = ⊤` is admissible is open.

## What closes it, and it is not a new hypothesis

`DivScheme` is a *noetherian* scheme, and on a noetherian space every subset is compact.

* `IsLocallyNoetherian` comes from `LocallyOfFiniteType.isLocallyNoetherian` applied to
  `locallyOfFiniteType_divSchemeOverHom` over the noetherian base `Spec k` — a field is a
  noetherian ring, so nothing is assumed of the curve.
* with `compactSpace_divScheme` that is `IsNoetherian`, hence `NoetherianSpace`, hence
  `NoetherianSpace.isCompact` applies to the carrier of any `V`.

So the per-chart half is genuinely free — but by noetherianity of the divisor scheme, not by the
instance the three sites cite.  `compactSpace_isOpen_divSchemeOver` below is that step, and
`compactSpace_glued_of_finite_mixedParamChart` feeds it to `compactSpace_of_finite_atlas`.

## What this does NOT do

**`Finite ι` is not discharged and I do not claim it is.**  Dropping it makes
`compactSpace_glued_of_finite_mixedParamChart` fail to elaborate (measured), which is the point:
after this file the atlas's compactness input costs *index finiteness alone*.  That is a strict
subtraction from the three-route picture — the class route's `hcl`
(`Pic0AtlasCompactFromClass.lean`) and the Abel image are no longer the only ways to pay it at a
finite atlas — and it is **not** a producer of `hcpt` for the classical class-indexed atlas, which
has no finiteness.

**AND FINITENESS IS NOT CHEAP FOR THE ASSEMBLY — but that caveat is about the assembly, NOT about
the compactness lemma, and an earlier version of this header attached it to both.**  A
`PUnit`-indexed atlas is `Finite` and elaborates against `jacobianDataOfFiniteMixedParamCharts`
(probed), so it looks as though finiteness could be met by simply taking one chart.  For the
*assembly* it cannot be met that way: per inbox `I-1389`, single-index coverage implies
**unrestricted one-chart coverage** through the landed converse
`pointwise_of_pointwise_restrictChart` (`Pic0ChartAtlasCoupling.lean`), and one-chart coverage is
the configuration the heterogeneous atlas exists to avoid needing
(`Pic0ChartCoveragePointwise.lean`, `Pic0ChartCoverageIndexSlack.lean`,
`Pic0ChartAtlasParamFree.lean`).  Neither those files nor `I-1389` *proves* the non-uniformity they
assert, so whether a finite atlas covers is open in both directions.

**The compactness lemma is coverage-free, which is stronger than the caveat suggested** (`I-1430`).
`compactSpace_glued_of_finite_mixedParamChart` carries the `IsLocallySurjective` instance binder
only to match the assembly's shape: the binder is **idle**, and the statement compiles with it
deleted (measured).  `glueData` does not depend on coverage — mathlib introduces that instance
only at `representableBy` (`Sites/Representability.lean`).  So `hcpt` costs `Finite ι` *and
nothing about coverage*; the I-1389 coupling bites when the assembly consumes coverage for `rep`,
not here.  The binder is kept so that a consumer holding the assembly's hypotheses can apply this
lemma without reshaping them, and this paragraph exists so nobody prices the idle binder as a cost.

No claim is made here that a finite atlas exists.

No antecedent of the seam moves.  `rep`, `IsChartUniv` and Zariski-local surjectivity are
untouched, and this file produces no `JacobianData` at any curve.

## Main declarations

* `AlgebraicGeometry.isLocallyNoetherian_divSchemeOver` — the divisor scheme is locally
  noetherian, from `LocallyOfFiniteType` over the noetherian base.
* `AlgebraicGeometry.isNoetherian_divSchemeOver` — and noetherian, with `compactSpace_divScheme`.
* `AlgebraicGeometry.compactSpace_isOpen_divSchemeOver` — **the step the three sites skipped**:
  every open of the divisor scheme is a compact space.
* `AlgebraicGeometry.compactSpace_of_representableBy` — and it is a property of the **functor**:
  compactness of a representing object transports between representations, the companion of
  `locallyOfFiniteType_of_representableBy`.
* `AlgebraicGeometry.compactSpace_glued_of_finite_mixedParamChart` — `hcpt` for a finite
  mixed-parameter atlas at the divisor-representability carrier, with **no** `hcl` and no Abel
  morphism.
* `AlgebraicGeometry.jacobianDataOfFiniteMixedParamCharts` — the assembly with `hcpt` gone and
  `Finite ι` in its place.
* `AlgebraicGeometry.quasiCompact_jacobianDataOfFiniteMixedParamCharts` — the consequence for the
  `dat-j.qcfield` row: that row's field is *discharged* at a finite atlas, so `hcl` is what pays it
  at an **infinite** one.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

noncomputable section

open Scheme

/-! ## The divisor scheme is noetherian -/

section Noetherian

variable (k : Type u) [Field k]

/-- **The divisor scheme is locally noetherian.**

`locallyOfFiniteType_divSchemeOverHom` makes the structure morphism locally of finite type, and
`Spec k` is locally noetherian because a field is a noetherian ring; `LocallyOfFiniteType.
isLocallyNoetherian` transports.  Nothing about the curve `X` is used beyond what the divisor
scheme's own construction needs.

Spelled with `@` and the named instance because `locallyOfFiniteType_divSchemeOverHom` takes `k`
*explicitly*, so it is not found by `inferInstance` at an implicit `k`.

**An earlier version of this docstring gave a different and FALSE reason** — that the
`LocallyOfFiniteType` binder "does not synthesise inside a tactic block". It does:
`exact LocallyOfFiniteType.isLocallyNoetherian (divSchemeOver …).hom` compiles in tactic mode
(measured, `I-1432`). The binder that fails to synthesise where this lemma is *consumed* is
`IsLocallyNoetherian`, which is why the consumers below introduce it with `haveI`. Corrected
rather than deleted, because a false justification in a docstring reads as audited. -/
theorem isLocallyNoetherian_divSchemeOver {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
    (A B : X.CurveDivisor) (n r₁ r₂ : ℕ)
    (b₁ : Module.Basis (Fin r₁) k ↥(divisorSections k B ⊤))
    (b₂ : Module.Basis (Fin r₂) k ↥(divisorSections k (A + B) ⊤)) :
    IsLocallyNoetherian (divSchemeOver k A B n r₁ r₂ b₁ b₂).left :=
  @LocallyOfFiniteType.isLocallyNoetherian _ _ (divSchemeOver k A B n r₁ r₂ b₁ b₂).hom
    (locallyOfFiniteType_divSchemeOverHom k A B n r₁ r₂ b₁ b₂) inferInstance

/-- **The divisor scheme is noetherian**: locally noetherian (above) and compact
(`compactSpace_divScheme`, DD-Q).

Only the `IsLocallyNoetherian` parent needs introducing — `compactSpace_divScheme` is already an
instance, so `constructor` finds the second field on its own.  Kept as a named theorem because
`IsNoetherian` is the hypothesis a reader expects behind "every open is compact", even though the
payload below no longer routes through it. -/
theorem isNoetherian_divSchemeOver {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
    (A B : X.CurveDivisor) (n r₁ r₂ : ℕ)
    (b₁ : Module.Basis (Fin r₁) k ↥(divisorSections k B ⊤))
    (b₂ : Module.Basis (Fin r₂) k ↥(divisorSections k (A + B) ⊤)) :
    IsNoetherian (divSchemeOver k A B n r₁ r₂ b₁ b₂).left := by
  haveI := isLocallyNoetherian_divSchemeOver k A B n r₁ r₂ b₁ b₂
  constructor

/-- **THE STEP THREE SITES SKIPPED**: every open subscheme of the divisor scheme is a compact
space.

This is what the atlas's per-chart hypothesis actually asks for, and it is *not* the instance
`CompactSpace (divSchemeOver …).left` that `Pic0AtlasFiniteType.lean`'s `Discharged` section
exhibits: compactness does not pass to open subspaces.

**It needs only LOCAL noetherianity**, not `IsNoetherian`: on a locally noetherian scheme the
inclusion of an open is quasi-compact (mathlib's `quasiCompact_of_noetherianSpace_source` via
`IsLocallyNoetherian`'s affine-local noetherian spaces, stacks 01OX), and
`QuasiCompact.compactSpace_of_compactSpace V.ι` then transports compactness *down* from the
ambient.  An earlier proof here went through `IsNoetherian` → `NoetherianSpace` →
`NoetherianSpace.isCompact`, two hops longer, and made the lemma look as though it needed
compactness of the ambient scheme as a hypothesis rather than as an instance already in scope
(`I-1431`).

Stated for an arbitrary `V`, with no `V ≠ ⊤` or affineness hypothesis, because the chart opens of
the atlas are arbitrary — `mixedParamChart` takes `V : ∀ i, (D i).left.Opens` unconstrained. -/
theorem compactSpace_isOpen_divSchemeOver {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
    (A B : X.CurveDivisor) (n r₁ r₂ : ℕ)
    (b₁ : Module.Basis (Fin r₁) k ↥(divisorSections k B ⊤))
    (b₂ : Module.Basis (Fin r₂) k ↥(divisorSections k (A + B) ⊤))
    (V : (divSchemeOver k A B n r₁ r₂ b₁ b₂).left.Opens) :
    CompactSpace (V : Scheme.{u}) := by
  haveI := isLocallyNoetherian_divSchemeOver k A B n r₁ r₂ b₁ b₂
  exact QuasiCompact.compactSpace_of_compactSpace V.ι

end Noetherian

/-! ## The per-chart half belongs to the FUNCTOR, not to `divSchemeOver`

The section above is stated at `divSchemeOver`, which is where the divisor-representability lane's
producers land — but that carrier is not where the property lives, and `Pic0AtlasFiniteType.lean`
had already made exactly this argument for the *other* finiteness input:
`locallyOfFiniteType_of_representableBy` proves `hD` transports between any two representations of
`divFunctor C π n`, with a header paragraph on why a carrier-specific argument is the worse one.

Compactness transports the same way and for the same reason, so the same paragraph applies.
Recorded after an audit observed that this file's correction had inherited the narrowness of the
claim it was correcting (`I-1431`, `I-1433`): the wrong-object defect was fixed at one carrier,
while the fix's own scope went unexamined. -/

section Transport

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

variable (C π) in
/-- **Compactness of a representing object is a property of the divisor functor.**

If `divFunctor C π n` is represented by `D` and by `D'`, and `D'.left` is compact, so is `D.left`.
Representing objects are isomorphic over the base (`Functor.RepresentableBy.uniqueUpToIso`), the
component `e.hom.left` is then an isomorphism of schemes, and compactness transports along the
induced homeomorphism.

The companion of `locallyOfFiniteType_of_representableBy` (`Pic0AtlasFiniteType.lean`), and stated
for the same reason: a producer of `rep` does not get to choose a representing object that fails
the per-chart half.  Uses none of the curve's geometry — smoothness, properness and geometric
irreducibility are not in scope in this section at all, which is the evidence that this is a
statement about representability rather than about the divisor scheme. -/
theorem compactSpace_of_representableBy {n : ℕ} {D D' : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (rep' : (divFunctor C π n).RepresentableBy D')
    (h : CompactSpace D'.left) :
    CompactSpace D.left := by
  have e := rep.uniqueUpToIso rep'
  have hiso : IsIso e.hom.left :=
    ⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id]; rfl,
      by rw [← Over.comp_left, e.inv_hom_id]; rfl⟩
  haveI := h
  exact (Scheme.homeoOfIso (asIso e.hom.left)).symm.compactSpace

end Transport

/-! ## `hcpt` at a finite atlas over the divisor-representability carrier -/

section Atlas

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of k))] [IsIntegral Y]
variable {A B : Y.CurveDivisor} {r₁ r₂ : ℕ}
variable {b₁ : Module.Basis (Fin r₁) k ↥(divisorSections k B ⊤)}
variable {b₂ : Module.Basis (Fin r₂) k ↥(divisorSections k (A + B) ⊤)}

variable (C π) in
/-- **`hcpt` for a finite mixed-parameter atlas at the divisor-representability carrier** — with
no `hcl`, no Abel morphism and no hypothesis on the chart opens.

`Pic0AtlasFiniteType.lean` names two routes to `hcpt` (a finite atlas, or the Abel image) and
`Pic0AtlasCompactFromClass.lean` adds a third (the `dat-j.qcfield` class hypothesis).  This is the
first route, *completed*: its per-chart input is compactness of the chart opens, which those files
record as free at this carrier and which is in fact the noetherian step above.

The `gg i` are per-index divisor-scheme parameters, deliberately unconstrained and distinct from
the chart parameters `nn i`: the seam ties them nowhere (`Pic0ChartAtlasParamFree.lean`), and
requiring `gg = nn` here would import a coupling the assembly does not have.

**`Finite ι` is load-bearing and undischarged.**  Removing it breaks elaboration, which is the
honest content: after this lemma the atlas's compactness input costs index finiteness *alone*. -/
theorem compactSpace_glued_of_finite_mixedParamChart {ι : Type u} [Finite ι] (nn : ι → ℕ)
    (gg : ι → ℕ)
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy
      (divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂).left.Opens)
    (hf : ∀ i, IsOpenImmersion.presheaf (mixedParamChart C π nn
      (fun i => divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂) rep m Z hdeg V i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn
        (fun i => divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂) rep m Z hdeg V))] :
    CompactSpace (Scheme.LocalRepresentability.glueData hf).glued :=
  compactSpace_of_finite_atlas C _ hf
    (fun i => compactSpace_isOpen_divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂ (V i))

variable (C π) in
/-- **The atlas assembly with `hcpt` replaced by `Finite ι`.**

Compare `jacobianDataOfMixedParamCharts` (`Pic0AtlasFiniteType.lean`), which carries `hcpt` as a
hypothesis its docstring calls the exposed one, and `jacobianDataOfCompactFromClass`
(`Pic0AtlasCompactFromClass.lean`), which pays it with `(lam, hcl)`.  Here neither appears.

**This produces no `JacobianData` at any curve.**  The three open antecedents are unchanged and
`Finite ι` is a fourth hypothesis, not a discharge: for the classical class-indexed atlas it is
false.  What the signature records is that at a *finite* atlas the compactness input is free —
so a lane assembling a finite atlas owes `rep`, `hf` and coverage, and nothing else.

**Do not read that as "so build a finite atlas".**  `Finite ι` interacts with the coverage
instance: at a one-element index the instance is equivalent to unrestricted one-chart coverage
(`I-1389`), which three files in this tree expect to fail.  The signature is a statement about
where the cost sits, not a recommendation of a route. -/
def jacobianDataOfFiniteMixedParamCharts {ι : Type u} [Finite ι] (nn : ι → ℕ)
    (gg : ι → ℕ)
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy
      (divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂).left.Opens)
    (hf : ∀ i, IsOpenImmersion.presheaf (mixedParamChart C π nn
      (fun i => divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂) rep m Z hdeg V i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn
        (fun i => divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂) rep m Z hdeg V))] :
    JacobianData C :=
  jacobianDataOfMixedParamCharts C π nn
    (fun i => divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂) rep m Z hdeg V hf
    (fun _ => inferInstance)
    (compactSpace_glued_of_finite_mixedParamChart C π nn gg rep m Z hdeg V hf)

variable (C π) in
/-- **The `quasiCompact` field of `JacobianData` is discharged at a finite atlas** — the form that
matters to the `dat-j.qcfield` lane, so it is stated rather than left to be read off.

`Pic0AtlasCompactFromClass.lean` proves `hcpt` and the `JacobianData.quasiCompact` field are one
statement in both directions (`compactSpace_glued_iff_quasiCompact`), and `dat-j.qcfield` prices
that field as having no producer of any shape.  At a *finite* atlas over the divisor carrier it
does: the field of the datum above is already proved, with no `hcl` and no Abel morphism.

**So `hcl` is what pays the `quasiCompact` field at an INFINITE atlas**, which is the accurate
form of "the field has no producer".  The classical class-indexed atlas is infinite, so `hcl` is
not superseded — see the finiteness caveat in this file's header. -/
theorem quasiCompact_jacobianDataOfFiniteMixedParamCharts {ι : Type u} [Finite ι] (nn : ι → ℕ)
    (gg : ι → ℕ)
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy
      (divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂).left.Opens)
    (hf : ∀ i, IsOpenImmersion.presheaf (mixedParamChart C π nn
      (fun i => divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂) rep m Z hdeg V i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn
        (fun i => divSchemeOver k A B (gg i) r₁ r₂ b₁ b₂) rep m Z hdeg V))] :
    QuasiCompact
      (jacobianDataOfFiniteMixedParamCharts C π nn gg rep m Z hdeg V hf).J.hom :=
  (jacobianDataOfFiniteMixedParamCharts C π nn gg rep m Z hdeg V hf).quasiCompact

end Atlas

end

end AlgebraicGeometry
