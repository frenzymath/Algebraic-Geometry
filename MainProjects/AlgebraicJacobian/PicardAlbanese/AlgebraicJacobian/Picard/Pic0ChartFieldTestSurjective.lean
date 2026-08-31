/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartLocalSurjectivity

/-!
# At a one-point test, Zariski-local surjectivity IS surjectivity

DAT-J's `quasiCompact` field reduces — in either coordinate system, see
`Picard/JacobianDataQcFromRep.lean` and `Picard/Pic0AtlasCompactFromClass.lean` — to one
statement `hcl`: **every point of the representing object has its class pulled back along some
field point of the divisor scheme**.  Both of those files record that `hcl` has no producer,
and the routes they name (the Abel image, finite-separable descent) are the expensive ones.

This file supplies the general fact that reprices the *first* half of that statement, and it
is not about `pic⁰` at all:

> a Zariski covering sieve of a scheme whose space is a `Subsingleton` **contains the
> identity**, so a locally surjective morphism of presheaves of types is honestly surjective
> on sections there.

`Spec K` for a field `K` is such a scheme (`Unique (PrimeSpectrum K)` in mathlib), and the
tests `hcl` quantifies over are exactly `overSpec k κ(y)`.  So on the `hcl` side, coverage —
antecedent 2 of `pic0RepresentableByOfCharts`, which the seam **already assumes** — is not
merely "locally" available at a field point: it gives a section on the nose, with no descent
step and no Abel image.

## Why the statement is about a `Subsingleton` space and not about fields

The proof looks at the space only, and it goes through for an arbitrary presheaf of types on
`Scheme`: take a cover refining the sieve (`exists_cover_of_mem_grothendieckTopology`), take
the component over the unique point, observe its base map is epi *because the target has at
most one point*, conclude it is an isomorphism (`IsOpenImmersion.isIso`), and use
`Sieve.downward_closed` along its inverse.  Nothing here mentions `pic⁰`, the curve, the
divisor scheme, or the sheaf condition.  Stated in that generality deliberately: it is the
mirror image of `Picard/Pic0ChartBotRefute.lean`'s
`not_isLocallySurjective_restrictChart_bot_of_presheaf`, which refutes the `V = ⊥` endpoint by
looking only at the *emptiness* of the space.  Empty spaces kill local surjectivity; one-point
spaces make it free.  Both are facts about the site, not about the Picard functor.

## What this does NOT do, stated because the temptation here is exactly the audited failure mode

**It does not discharge `hcl`, and it does not discharge any antecedent.**  What it gives is a
section of the Σ-sheaf over `Spec κ(y)` *in the image of the atlas*, i.e. an index `i` and a
`κ(y)`-point of the `i`-th chart source.  `hcl` asks for a point of `divSchemeOver …` whose
class is `pic0Map C q lam` for the **one fixed** class `lam`.  Two gaps remain and neither is
touched here:

* the chart source of `mixedParamChart` is `(V i : Scheme)`, an *open of* `(D i).left`, and the
  chart index `i` produced is the one coverage happens to supply — so the point obtained lies in
  a chart of the atlas, not in a single named divisor scheme;
* `hcl`'s `lam` is fixed *before* `y` is quantified, whereas coverage's index varies with the
  point.  Collapsing that quantifier order is the real content of `hcl`, and this file leaves
  it open.

So the honest reading is: **the "local" in DAT-B's local surjectivity costs nothing at the
tests DAT-J quantifies over.**  That is a subtraction from `hcl`'s price, not a payment of it.

## Main declarations

* `AlgebraicGeometry.exists_isIso_of_mem_zariskiTopology` — a covering sieve of a
  `Subsingleton`-space scheme contains an isomorphism.  The only geometric input.
* `AlgebraicGeometry.id_mem_of_mem_zariskiTopology` — hence it contains the identity, i.e. it
  is the top sieve on the nose.
* `AlgebraicGeometry.app_surjective_of_isLocallySurjective_of_subsingleton` — hence local
  surjectivity of an arbitrary morphism of presheaves of types is surjectivity on sections
  there.
* `AlgebraicGeometry.exists_chart_section_of_chartsCoverLocally_of_subsingleton` — the `pic⁰`
  reading: at a one-point test, a covering chart family hits **every** section, by a genuine
  index and a genuine point of that chart's source.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u v

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-! ## The site fact -/

/-- **A Zariski covering sieve of a scheme with at most one point contains an isomorphism.**

Take a cover refining the sieve; its component over the point `x` is an open immersion whose
base map is surjective *because the target is a subsingleton*, hence an isomorphism.

The `Subsingleton` hypothesis is on the space, and `x` witnesses that it is also nonempty —
both are needed: on the empty scheme the bottom sieve covers
(`Scheme.bot_mem_grothendieckTopology`) and contains no isomorphism at all. -/
theorem exists_isIso_of_mem_zariskiTopology {X : Scheme.{u}} [Subsingleton (X : Type u)]
    (x : X) (S : Sieve X) (hS : S ∈ Scheme.zariskiTopology X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), S.arrows g ∧ IsIso g := by
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  haveI : Epi (𝒰.f i).base := by
    rw [TopCat.epi_iff_surjective]
    exact fun z => ⟨y, Subsingleton.elim _ _⟩
  exact ⟨𝒰.X i, 𝒰.f i, hle _ _ (Presieve.ofArrows.mk i), IsOpenImmersion.isIso (𝒰.f i)⟩

/-- **A Zariski covering sieve of a scheme with at most one point contains the identity** —
so on such a scheme "covering" carries no information beyond nonemptiness.

`Sieve.downward_closed` along the inverse of the isomorphism above. -/
theorem id_mem_of_mem_zariskiTopology {X : Scheme.{u}} [Subsingleton (X : Type u)]
    (x : X) (S : Sieve X) (hS : S ∈ Scheme.zariskiTopology X) :
    S.arrows (𝟙 X) := by
  obtain ⟨Y, g, hg, hiso⟩ := exists_isIso_of_mem_zariskiTopology x S hS
  have h := S.downward_closed hg (inv g)
  rwa [IsIso.inv_hom_id] at h

/-- **Zariski-local surjectivity IS surjectivity at a one-point test.**

For an arbitrary morphism of presheaves of types on `Scheme`: the image sieve of a section is
covering by hypothesis, hence contains the identity by the previous theorem, and an identity in
the image sieve *is* a preimage of the section.

No `pic⁰`, no curve, no sheaf condition — this is the counterpart of
`not_isLocallySurjective_restrictChart_bot_of_presheaf`
(`Picard/Pic0ChartBotRefute.lean`), which refutes local surjectivity on the *empty* space by
the same kind of purely site-level argument. -/
theorem app_surjective_of_isLocallySurjective_of_subsingleton
    {F G : Scheme.{u}ᵒᵖ ⥤ Type v} (φ : F ⟶ G)
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology φ]
    {X : Scheme.{u}} [Subsingleton (X : Type u)] (x : X) :
    Function.Surjective (φ.app (op X)) := by
  intro s
  obtain ⟨t, ht⟩ :=
    id_mem_of_mem_zariskiTopology x _
      (Presheaf.imageSieve_mem Scheme.zariskiTopology φ s)
  exact ⟨t, by simpa using ht⟩

/-! ## The instances at `Spec` of a field

Recorded as `example`s rather than restated: both are mathlib instances
(`PrimeSpectrum.instUnique` for a field), and the point of listing them is that the tests
`hcl` quantifies over — `overSpec k κ(y)` — satisfy the hypotheses above with nothing to
prove. -/

section Field

variable (K : Type u) [Field K]

example : Subsingleton (Spec (CommRingCat.of K) : Type u) := inferInstance

example : Nonempty (Spec (CommRingCat.of K) : Type u) := inferInstance

end Field

/-! ## The `pic⁰` reading -/

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

/-- **At a one-point test, a covering chart family hits every section on the nose.**

Given DAT-B's coverage (`ChartsCoverLocally`, the `pic⁰` spelling a producer actually attempts)
and a test whose space has at most one point, every section `s` of the Σ-sheaf over that test
is `f i` applied to a genuine point of the `i`-th chart source — no restriction to a
neighbourhood, no refinement, no descent.

This is what makes the "local" in B-5/B-6 free at the tests DAT-J's `hcl` quantifies over
(`Picard/JacobianDataQcFromRep.lean`).  It does **not** produce `hcl`: the index `i` here is
whichever one coverage supplies at `s`, while `hcl` fixes one class `lam` on one divisor scheme
before quantifying over points.  See this file's module docstring for the two surviving gaps. -/
theorem exists_chart_section_of_chartsCoverLocally_of_subsingleton {ι : Type u}
    {X : ι → Scheme.{u}} (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (hcov : ChartsCoverLocally C f)
    {T : Scheme.{u}} [Subsingleton (T : Type u)] (t : T)
    (s : (pic0SigmaSheaf C).1.obj (op T)) :
    ∃ (i : ι) (x : T ⟶ X i), (f i).app (op T) x = s := by
  have hid := id_mem_of_mem_zariskiTopology t _ (hcov T s)
  rw [iSup, Sieve.sSup_apply] at hid
  obtain ⟨S, ⟨i, rfl⟩, x, hx⟩ := hid
  exact ⟨i, x, by simpa using hx⟩

end AlgebraicGeometry
