/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import AlgebraicJacobian.Picard.DivFamilyZero
import AlgebraicJacobian.Picard.DivPushforwardFlat

/-!
# The divisor-support quasi-finiteness binder, reduced to its geometric core

`AJC.picrep.divlocallyclosed`.

## The obligation this file is about

`Picard/DivPushforwardFlat.lean` carries, on every one of its theorems, the instance
binder

```
[LocallyQuasiFinite (schematicSupportι x.F ≫ pullback.snd π T.hom)]
```

— "the divisor `D ⊆ X_T` has finite fibres over `T`" — and says of it, in its own
module docstring, that it "has no producer in this project", that
`LocallyQuasiFinite` "occurs nowhere else in `Picard/`", and that it is
"kernel-checked NOT derivable from `DivFamily`'s other fields". All three
statements are true at HEAD and none of them is weakened here.

What *was* never measured is **how much of that binder is geometry**. This file
measures it, and the answer is that the binder is one topological statement away
from free: two of the three inputs the mathlib criteria want are supplied by
`DivFamily.properSupport`, which every family already carries.

## What is proved here

* `Scheme.Modules.locallyOfFiniteType_schematicSupportι_comp` and
  `Scheme.Modules.quasiCompact_schematicSupportι_comp` — from
  `HasProperSupport` alone, the support map is locally of finite type and
  quasi-compact. Both by synthesis once `IsProper` is in scope; recorded as named
  theorems because `HasProperSupport` is a `def`, not a class, so a consumer
  writing `haveI := hps` gets **no** instance and the synthesis silently fails
  (measured: `infer_instance` fails on both goals with the `def` in scope and
  succeeds with the `IsProper` restatement).

* `Scheme.Modules.locallyQuasiFinite_schematicSupportι_comp_iff_finite_fibers` —
  the binder **is equivalent** to finiteness of each set-theoretic fibre of the
  divisor over the base, for an arbitrary module with proper support over an
  arbitrary morphism. No curve, no smoothness, no relative dimension, no
  `DivFamily`.

* `Scheme.Modules.locallyQuasiFinite_schematicSupportι_comp_iff_isFinite_fiber` —
  the same equivalence in the scheme-theoretic form, against
  `IsFinite (…).fiberToSpecResidueField t`.

* `Scheme.Modules.locallyQuasiFinite_schematicSupportι_comp_of_finite_fibers` —
  the direction a producer needs, as a standalone implication.

* `Scheme.DivFamily.locallyQuasiFinite_of_finite_fibers` and
  `Scheme.DivFamily.locallyQuasiFinite_iff_finite_fibers` — the same statements
  at a `DivFamily`, where `properSupport` is a field, so the hypothesis list is
  *only* the fibre finiteness.

* `Scheme.Modules.locallyQuasiFinite_schematicSupportι` — for contrast, and
  because it is the fact that makes the composite's failure informative: the
  support immersion **on its own** is always locally quasi-finite, for every
  module on every scheme, by `IsPreimmersion`. So nothing about the annihilator
  or the support is what the binder is asking for; the whole content sits in the
  projection to `T`.

## What this does NOT do, stated because it is the natural over-reading

* It does **not** produce the binder for any family. The remaining obligation is
  the fibre finiteness, and that is where relative dimension one enters: on the
  curve fibre `C_t` the divisor `D_t` is the zero scheme of a regular section of
  an invertible ideal (`Picard/DivDegree.lean` has that fibre short exact
  sequence in full — `Scheme.DivFamily.isLocallyTrivial_fiber_kernel` (the bare
  name fails `#check`: it lives in the `Scheme.DivFamily` namespace, not
  `Scheme.Modules`), `mono_fiber_kernel_ι`,
  `fiberKernelIso`, `fiberCokernelIso`), hence `0`-dimensional, hence finite. That
  step is genuinely absent and is not attempted here.

* It does **not** close `AJC.picrep.divlocallyclosed`. D3′ proper is the
  `ExistsUnique` statement about the Grassmannian locus; this file is upstream of
  it.

* It does **not** inhabit `Scheme.DivFamily`. `Picard/DivFamilyZero.lean`'s
  `DivFamily.zero` is the tree's only producer, so every statement here is
  testable at exactly one family.

* It closes **no** `sorry`, and `Scheme.fgaPicardRepresentability` is untouched.
  A shorter hypothesis list on the divisor side is not progress on the seam's
  `rep`, and this file is verified with that theorem as a `sorryAx` control.

## Why the reduction is worth landing separately

The reduction is a repricing of D3′'s hypothesis: the binder is no longer an
affine-local `RingHom.QuasiFinite` condition to be attacked at each site, but one
fibre statement, with every scheme-level binder discharged from a field a family
already carries.

**"THREE ROWS" WAS AN OVERCOUNT AND IS WITHDRAWN — it is ONE row plus a partial
contribution to a gate** (fresh-context audit, `I-1618`; the earlier text here, and
this file's commit messages, said the reduction retires plumbing for D3′, D4′ and
the local-constancy gate at once).

* **D3′** — yes. This is that row's binder.
* **D4′** — no. D4′ consumes D3′ and never binds `LocallyQuasiFinite` itself, so
  counting it separately double-counts a single discharge.
* **`Scheme.HasLocallyConstantDivDeg`** (`Picard/DivDegree.lean`) — partially. Its
  own docstring names **two** inputs, "the finiteness/rank half of the campaign's
  B3 rigid-pushforward engine **plus** relative-dimension-1 quasi-finiteness", and
  its content is local constancy of a rank function. This file supplies at most the
  second input.

## References

Blueprint: the campaign's D3′ node.
Source: [Kleiman], "The Picard scheme" (arXiv:math/0504020), §3 Def. `df:red`,
Ex. `ex:DivC`. Mathlib: `AlgebraicGeometry/Morphisms/QuasiFinite.lean`
(`locallyQuasiFinite_iff_finite_preimage_singleton`,
`locallyQuasiFinite_iff_isFinite_fiber`,
`LocallyQuasiFinite.of_finite_preimage_singleton`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

variable {S X : Scheme.{u}}

/-! ## §1. The support immersion alone is always quasi-finite

This section exists to locate the content of the binder. A reader pricing
`LocallyQuasiFinite (schematicSupportι F ≫ pullback.snd π T.hom)` might expect the
difficulty to be about the annihilator ideal sheaf or the schematic support, both
of which are project-local primitives with a thin API
(`Picard/QuotScheme.lean` records that `annihilator_ideal` itself is blocked on the
QCoh localisation bridge). It is not: the support immersion is quasi-finite
outright. -/

/-- **The schematic-support immersion is always locally quasi-finite** — for every
sheaf of modules on every scheme, with no hypothesis whatever.

`schematicSupportι F` is `IdealSheafData.subschemeι` of the annihilator ideal
sheaf, and mathlib registers `IsPreimmersion` for every `subschemeι`
(`AlgebraicGeometry/IdealSheaf/Subscheme.lean`) together with a low-priority
`IsPreimmersion ⟹ LocallyQuasiFinite` instance.

**The `inferInstanceAs` is load-bearing and is not cosmetic**, and the mechanism is
worth stating exactly, because two wrong versions of it have stood here. Measured,
three spellings in one probe:

* `LocallyQuasiFinite F.annihilator.subschemeι` — plain `infer_instance`
  **succeeds**;
* `LocallyQuasiFinite (schematicSupportι F)` — plain `infer_instance` **fails**;
* the same after `unfold Scheme.Modules.schematicSupportι` — still **fails**, and
  `pp.explicit` shows why: the goal becomes
  `@LocallyQuasiFinite (@schematicSupport X F) X (@IdealSheafData.subschemeι X
  (@annihilator X F))`. Unfolding rewrote the **morphism** to the annihilator form
  but left the **source scheme** as `schematicSupport X F`, so the instance —
  indexed on `IdealSheafData.subscheme` as the source — does not apply.

So the obstruction is the *source-object* index, not reducibility of the morphism,
and it is not a missing instance: converting the goal wholesale with
`inferInstanceAs` fixes it. (An earlier revision of this paragraph blamed
"unfolding replaces the reducible definition by the `annihilator`-projection form
that the instance is not indexed on", which has the direction backwards; a
fresh-context audit then reported that the annihilator spelling *also* fails, which
the first probe above refutes. Both are recorded because the two errors point
opposite ways and a reader who inherits either will look in the wrong place.)
Stated as a theorem so downstream sites cite a name rather than rediscover this. -/
theorem locallyQuasiFinite_schematicSupportι (F : X.Modules) :
    LocallyQuasiFinite (schematicSupportι F) :=
  inferInstanceAs (LocallyQuasiFinite F.annihilator.subschemeι)

/-- **The schematic-support immersion is a preimmersion**, hence injective on
points. Same `inferInstanceAs` remark as above. Used below only through
`Scheme.Hom.isEmbedding`. -/
theorem isPreimmersion_schematicSupportι (F : X.Modules) :
    IsPreimmersion (schematicSupportι F) :=
  inferInstanceAs (IsPreimmersion F.annihilator.subschemeι)

/-! ## §2. Two of the three inputs are free from `properSupport` -/

section Composite

variable {T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)

/-- **The support map is locally of finite type, from proper support alone.**

`HasProperSupport f F` is by definition `IsProper (schematicSupportι F ≫ f)`
(`Picard/QuotScheme.lean`), and mathlib derives `LocallyOfFiniteType` from
`IsProper` by synthesis.

**The restatement of the hypothesis as an `IsProper` instance is required.**
`HasProperSupport` is a plain `def`, not a class, so `haveI := hps` registers
nothing that instance search can use: `infer_instance` on this very goal
**fails** with the `def` in scope and **succeeds** after
`haveI : IsProper _ := hps` (measured both ways).

**But the word "synthesis" overstates the step, and the gloss that stood here —
that the failure "reads as *mathlib lacks `IsProper ⟹ LocallyOfFiniteType`*" — is
withdrawn** (fresh-context audit, `I-1620`, reproduced by its author).
`LocallyOfFiniteType` is a **structure parent** of `IsProper`, so this theorem is
`hps.toLocallyOfFiniteType`: a field access, not an instance search, and no lemma
is missing anywhere. `quasiCompact_schematicSupportι_comp` is one hop further
(`hps.toUniversallyClosed`). The `def`-versus-class friction is real and worth a
name; describing it as a synthesis gap sent the reader hunting a reducibility bug
that does not exist. -/
theorem locallyOfFiniteType_schematicSupportι_comp
    (hps : HasProperSupport f F) :
    LocallyOfFiniteType (schematicSupportι F ≫ f) :=
  haveI : IsProper (schematicSupportι F ≫ f) := hps
  inferInstance

/-- **The support map is quasi-compact, from proper support alone.** Same route
and same `def`-versus-class caveat as
`locallyOfFiniteType_schematicSupportι_comp`. -/
theorem quasiCompact_schematicSupportι_comp
    (hps : HasProperSupport f F) :
    QuasiCompact (schematicSupportι F ≫ f) :=
  haveI : IsProper (schematicSupportι F ≫ f) := hps
  inferInstance

/-! ## §3. The binder is exactly the fibre finiteness -/

/-- **The quasi-finiteness binder of the divisor side IS finiteness of the
fibres**, for an arbitrary module with proper support over an arbitrary
morphism of schemes.

Both mathlib criteria that could give this want binders the caller does not
obviously have: `locallyQuasiFinite_iff_finite_preimage_singleton` needs
`LocallyOfFiniteType` *and* `QuasiCompact`. §2 supplies both from
`HasProperSupport`, so the equivalence holds with **no** hypothesis beyond proper
support.

What this buys, and it is the point of the file: a lane producing the binder does
not need to touch `LocallyQuasiFinite`, the annihilator ideal sheaf, the
schematic support, or affine-local `RingHom.QuasiFinite` conditions at all. It
needs one topological statement about the fibres of `D → T`. On a relative curve
that statement is that a nonempty effective Cartier divisor on a `1`-dimensional
fibre is a finite set of points — which is where the relative-dimension-one
hypothesis genuinely enters, and it is *not* proved here. -/
theorem locallyQuasiFinite_schematicSupportι_comp_iff_finite_fibers
    (hps : HasProperSupport f F) :
    LocallyQuasiFinite (schematicSupportι F ≫ f) ↔
      ∀ t : T, ((schematicSupportι F ≫ f) ⁻¹' {t}).Finite :=
  haveI : IsProper (schematicSupportι F ≫ f) := hps
  locallyQuasiFinite_iff_finite_preimage_singleton

/-- **The scheme-theoretic form of the same equivalence**: the binder holds iff
every scheme-theoretic fibre of the divisor over the base is a finite scheme over
the residue field.

Stated alongside the point-set form because the two feed different producers. A
route through the fibre short exact sequence of `Picard/DivDegree.lean`
(`fiberCokernelIso`, which identifies `(O_D)_t` with the cokernel of the fibre
ideal inclusion) lands naturally on *this* shape, since it produces a statement
about the fibre as a scheme rather than about a preimage set. -/
theorem locallyQuasiFinite_schematicSupportι_comp_iff_isFinite_fiber
    (hps : HasProperSupport f F) :
    LocallyQuasiFinite (schematicSupportι F ≫ f) ↔
      ∀ t : T, IsFinite ((schematicSupportι F ≫ f).fiberToSpecResidueField t) :=
  haveI : IsProper (schematicSupportι F ≫ f) := hps
  locallyQuasiFinite_iff_isFinite_fiber

/-- **The producer direction, standalone.** Given proper support, finiteness of
the fibres *gives* the binder. Split out from the `iff` because a producer only
ever uses this half, and because it is the form that lets a use site avoid
naming `HasProperSupport` twice. -/
theorem locallyQuasiFinite_schematicSupportι_comp_of_finite_fibers
    (hps : HasProperSupport f F)
    (hfib : ∀ t : T, ((schematicSupportι F ≫ f) ⁻¹' {t}).Finite) :
    LocallyQuasiFinite (schematicSupportι F ≫ f) :=
  haveI : IsProper (schematicSupportι F ≫ f) := hps
  LocallyQuasiFinite.of_finite_preimage_singleton _ hfib

/-- **A fibre of the divisor injects into the corresponding fibre of the ambient
family.** The support immersion is a preimmersion, hence injective on points, and
the fibre of the composite is by definition the preimage of the ambient fibre.

Recorded because it is the shape in which the missing geometry will be consumed:
it reduces fibre finiteness for `D → T` to finiteness of a *subset* of the curve
fibre `C_t`, so a producer never has to reason about `D` as a scheme in its own
right. Note the hypothesis is finiteness of the ambient fibre, which for a
relative curve is **false** — so this lemma is a reduction tool for a cut-down
subset, not a route to the binder by itself. -/
theorem finite_fiber_schematicSupportι_comp_of_finite
    {t : T} (hfin : (f ⁻¹' {t}).Finite) :
    ((schematicSupportι F ≫ f) ⁻¹' {t}).Finite := by
  haveI := isPreimmersion_schematicSupportι F
  have hpre : ((schematicSupportι F ≫ f) ⁻¹' {t})
      = (schematicSupportι F).base ⁻¹' (f ⁻¹' {t}) := rfl
  rw [hpre]
  exact hfin.preimage (schematicSupportι F).isEmbedding.injective.injOn

/-- **The binder is FIBREWISE, and this form needs no proper support at all.**

`LocallyQuasiFinite.of_fiberToSpecResidueField` reduces the binder to
quasi-finiteness of each scheme-theoretic fibre of the divisor over the residue
field of the base point, and it wants **neither** `LocallyOfFiniteType` **nor**
`QuasiCompact`. So for an arbitrary module — no properness assumption whatever —
this reduction has a shorter hypothesis list than
`locallyQuasiFinite_schematicSupportι_comp_of_finite_fibers`.

**THAT ADVANTAGE IS EMPTY AT A `DivFamily`, AND THE CLAIM THAT IT IS "STRICTLY
WEAKER" THERE IS WITHDRAWN** (fresh-context audit, `I-1619`, reproduced by its
author). At a family `properSupport` is a *field*, so the two forms are
**interderivable**: fibrewise gives point-set by composing with
`locallyQuasiFinite_schematicSupportι_comp_iff_finite_fibers`, and point-set gives
fibrewise via `LocallyQuasiFinite.of_finite_preimage_singleton` and then
`inferInstance` per fibre — both directions measured, both close. Since a producer
will stand at a family, the ordering buys a *spelling* exactly where it was
advertised as buying strength. The hypothesis-count fact above is true only for a
module with no proper support, which is not the consuming site.

**Which form to aim at, then, is about proof shape and not about strength.** The
relative-curve geometry is fibrewise by nature (`D_t` is the zero scheme of a
regular section of an invertible ideal on the `1`-dimensional `C_t`), so an
argument of that shape lands here without a detour; an argument holding global
information about `D` lands on the point-set forms. Both are named so a lane picks
by what its argument produces — but neither is a weaker hypothesis than the other
at the site that matters, and `isFinite_support_of_fibers` records a second
obligation this form's antecedent carries. -/
theorem locallyQuasiFinite_schematicSupportι_comp_of_fibers
    (h : ∀ t : T, LocallyQuasiFinite
      ((schematicSupportι F ≫ f).fiberToSpecResidueField t)) :
    LocallyQuasiFinite (schematicSupportι F ≫ f) :=
  LocallyQuasiFinite.of_fiberToSpecResidueField _ h

/-- **The binder holds outright when the support is empty**, with no proper-support
hypothesis at all — a morphism out of an empty scheme is finite, hence locally
quasi-finite, by synthesis.

This is the degenerate producer, and it is what makes the reduction of §3
*testable* rather than a statement about an uninhabited situation: it fires at
`DivFamily.zero` (`Picard/DivFamilyZero.lean`), whose support is empty by
`isEmpty_schematicSupport_of_isZero`.

**What it does not show.** Emptiness is exactly the case where the fibre statement
carries no geometry, so this producer is evidence of satisfiability and not of
content — the pattern `I-1494` warns about. The non-degenerate case is a *nonempty*
effective Cartier divisor on a relative curve, and nothing here reaches it. Stated
anyway, because a reduction nobody can instantiate even once is worth less than one
that is instantiated at the tree's only family. -/
theorem locallyQuasiFinite_schematicSupportι_comp_of_isEmpty
    (he : IsEmpty (schematicSupport F)) :
    LocallyQuasiFinite (schematicSupportι F ≫ f) :=
  haveI := he
  inferInstance

end Composite

end Modules

/-! ## §4. At a `DivFamily`, where proper support is a field -/

namespace DivFamily

variable {S X : Scheme.{u}} {π : X ⟶ S} {T : Over S}

/-- **The binder at a divisor family: only the fibre finiteness remains.**

`DivFamily.properSupport` is a structure field, so instantiating §3 at a family
removes the proper-support hypothesis entirely. This is the statement a lane
closing the divisor side should aim at, and its hypothesis list is one item long.

Non-vacuity: the tree has exactly one `DivFamily` producer,
`DivFamily.zero` (`Picard/DivFamilyZero.lean`), whose support is **empty**
(`isEmpty_schematicSupport_of_isZero`), so at that family the fibre hypothesis is
satisfiable and the conclusion is a real instance rather than a statement about
an uninhabited carrier. That is a remark about testability, not evidence that the
hypothesis is weak at a nonempty divisor. -/
theorem locallyQuasiFinite_of_finite_fibers (x : DivFamily π T)
    (hfib : ∀ t : (T.left : Scheme.{u}),
      ((Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) ⁻¹' {t}).Finite) :
    LocallyQuasiFinite (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) :=
  Modules.locallyQuasiFinite_schematicSupportι_comp_of_finite_fibers _ _
    x.properSupport hfib

/-- **The binder at a divisor family is equivalent to the fibre finiteness.**

The `iff` form, so that a lane can also read the binder *backwards*: any
consumer of `DivPushforwardFlat`'s theorems is entitled to finiteness of the
divisor's fibres, which is a usable fact in its own right and was not previously
extractable from the binder without redoing the mathlib plumbing. -/
theorem locallyQuasiFinite_iff_finite_fibers (x : DivFamily π T) :
    LocallyQuasiFinite (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) ↔
      ∀ t : (T.left : Scheme.{u}),
        ((Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) ⁻¹' {t}).Finite :=
  Modules.locallyQuasiFinite_schematicSupportι_comp_iff_finite_fibers _ _
    x.properSupport

/-- **The scheme-theoretic form at a family.** Same content as
`locallyQuasiFinite_iff_finite_fibers`, in the shape the fibre short exact
sequence of `Picard/DivDegree.lean` produces. -/
theorem locallyQuasiFinite_iff_isFinite_fiber (x : DivFamily π T) :
    LocallyQuasiFinite (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) ↔
      ∀ t : (T.left : Scheme.{u}),
        IsFinite ((Modules.schematicSupportι x.F ≫
          pullback.snd π T.hom).fiberToSpecResidueField t) :=
  Modules.locallyQuasiFinite_schematicSupportι_comp_iff_isFinite_fiber _ _
    x.properSupport

/-- **The support map of a family is locally of finite type**, from the
`properSupport` field. Exposed because `DivPushforwardFlat`'s finiteness tower
spends exactly this, and because the `def`-versus-class trap of §2 bites at every
site that tries to synthesise it. -/
theorem locallyOfFiniteType_support (x : DivFamily π T) :
    LocallyOfFiniteType (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) :=
  Modules.locallyOfFiniteType_schematicSupportι_comp _ _ x.properSupport

/-- **The support map of a family is quasi-compact**, from the `properSupport`
field. -/
theorem quasiCompact_support (x : DivFamily π T) :
    QuasiCompact (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) :=
  Modules.quasiCompact_schematicSupportι_comp _ _ x.properSupport

/-- **The fibrewise reduction at a family**, which is the form the relative-curve
argument should consume: `properSupport` is not even mentioned, because
`Modules.locallyQuasiFinite_schematicSupportι_comp_of_fibers` does not need it.

This is the recommended target for whoever closes the row's geometry: one
statement per fibre, over a field, about the zero scheme of a regular section of
an invertible ideal on a curve. -/
theorem locallyQuasiFinite_of_fibers (x : DivFamily π T)
    (h : ∀ t : (T.left : Scheme.{u}), LocallyQuasiFinite
      ((Modules.schematicSupportι x.F ≫
        pullback.snd π T.hom).fiberToSpecResidueField t)) :
    LocallyQuasiFinite (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) :=
  Modules.locallyQuasiFinite_schematicSupportι_comp_of_fibers _ _ h

/-- **The binder upgrades the support map from proper to FINITE**, which is what
`Picard/DivPushforwardFlat.lean` actually spends it on.

That file's reduction reads "a proper *quasi-finite* morphism is finite
(`IsFinite.of_isProper_of_locallyQuasiFinite`), hence affine, and
`Scheme.CoherentSheafFlat` transfers along an affine pushforward". This states the
first step as a named theorem at a `DivFamily`, so the two inputs — the
`properSupport` field and the binder — are visibly the whole cost of `IsFinite`,
and a consumer citing "the divisor is finite over the base" has a name instead of
an inlined `haveI`.

Stated because the finiteness, not the quasi-finiteness, is what the downstream
`Module.Finite` tower consumes (`IsFinite.finite_app` in that file's own account
of where the hypothesis is spent). -/
theorem isFinite_support (x : DivFamily π T)
    (hqf : LocallyQuasiFinite (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom)) :
    IsFinite (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) :=
  haveI : IsProper (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) :=
    x.properSupport
  haveI := hqf
  IsFinite.of_isProper_of_locallyQuasiFinite _

/-- **THE BINDER HAS A PRODUCER: it holds at the empty divisor, for an arbitrary
`π` and an arbitrary test object.**

So `Picard/DivPushforwardFlat.lean`'s theorems are no longer statements nobody can
instantiate: composing this with `DivFamily.zero` discharges their binder.

**TWO CLAIMS THAT STOOD HERE ARE WITHDRAWN, both refuted by measurement**
(fresh-context audit, `I-1621`, both reproduced by their author).

*"their conclusions become facts about an actual family rather than an implication
with an unwitnessed antecedent"* — the conclusions were **already** free at
`DivFamily.zero`, independently of the binder: `CoherentSheafFlat (𝟙 T.left)` of
the pushforward closes by `Modules.coherentSheafFlat_of_isZero`, and finite
presentation by `isFinitePresentation_of_isZero`, both from
`Picard/DivFamilyZero.lean` and neither needing this file. So discharging the
binder at zero delivers nothing downstream that was not already one line away.

*That this file is what makes the binder inhabited* — with only the pre-existing
`isEmpty_schematicSupport_of_isZero` in scope, plain `infer_instance` closes
**both** `LocallyQuasiFinite` and `IsFinite` of the support map at zero. The
producer was already reachable; what this file adds at zero is a name, not access.

**Read the strength of this correctly, since the natural over-reading is
available.** The empty divisor is the case where fibre finiteness is *free*, so
this is a satisfiability witness, not the geometry. It does two things and no
more: it shows the binder is not vacuous-by-uninhabitability, and it lets a
reader check that the reduction of
`Modules.locallyQuasiFinite_schematicSupportι_comp_iff_finite_fibers` composes in
the intended direction at a real object. The obligation that remains — a nonempty
effective Cartier divisor on a relative curve has finite fibres — is untouched,
and is the whole content of the row.

Stated with `π` and `T` fully general because `DivFamily.zero` is
(`Picard/DivFamilyZero.lean`: no properness, smoothness or separatedness on `π`),
so there is no curve hypothesis to be double-counted here. -/
theorem locallyQuasiFinite_zero :
    LocallyQuasiFinite (Modules.schematicSupportι (DivFamily.zero π T).F
      ≫ pullback.snd π T.hom) :=
  Modules.locallyQuasiFinite_schematicSupportι_comp_of_isEmpty _ _
    (Scheme.Modules.isEmpty_schematicSupport_of_isZero (Limits.isZero_zero _))

/-- **The whole chain in one step: fibrewise quasi-finiteness gives a FINITE
divisor over the base.**

The composite of `locallyQuasiFinite_of_fibers` with `isFinite_support`: hypothesis
a statement per fibre over a field, conclusion the finiteness that
`Picard/DivPushforwardFlat.lean`'s `Module.Finite` tower consumes.

**THE SENTENCE THAT STOOD HERE — "the divisor side's remaining distance is exactly
the antecedent here, and nothing between it and finiteness is unbuilt" — IS FALSE
AND IS WITHDRAWN** (fresh-context audit, `I-1618`, reproduced by its author before
accepting). There is a **second, unnamed** obligation between this antecedent and
the `DivDegree.lean` fibre sequence a producer would reach for, and it is a carrier
mismatch:

* this antecedent quantifies over `Hom.fiber (schematicSupportι x.F ≫ pullback.snd
  π T.hom) t` — the **fibre of the support**;
* `DivDegree.lean`'s fibre short exact sequence (`fiberCokernelIso`,
  `Scheme.DivFamily.isLocallyTrivial_fiber_kernel`, `mono_fiber_kernel_ι`,
  `fiberKernelIso`) is about `Hom.fiberModule (pullback.snd π T.hom) t x.F`, whose
  support is `schematicSupport (fiberModule …)` — the **support of the fibre**.

Measured: `rfl` **fails** between the two carriers. And the bridge is not in the
tree — `Picard/QuotSupportBaseChange.lean` proves only
`annihilator F ≤ (annihilator (g'^* F)).map g'`, the inclusion that yields
properness of the *larger* support; the reverse inclusion, which is what
identifying the two carriers needs, is nowhere in the project.

So a lane aiming at this antecedent owes **two** things, not one: the geometric
fibre statement, and that support-versus-fibre comparison. Recorded at the
declaration rather than in a footnote, because the withdrawn sentence was
specifically an instruction about where to aim. -/
theorem isFinite_support_of_fibers (x : DivFamily π T)
    (h : ∀ t : (T.left : Scheme.{u}), LocallyQuasiFinite
      ((Modules.schematicSupportι x.F ≫
        pullback.snd π T.hom).fiberToSpecResidueField t)) :
    IsFinite (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) :=
  x.isFinite_support (x.locallyQuasiFinite_of_fibers h)

/-- **The empty divisor is finite over the base**, for an arbitrary `π` and
test object — the producer chain run to its end. Composed rather than reproved so
that the two links are exercised at the tree's one family. -/
theorem isFinite_support_zero :
    IsFinite (Modules.schematicSupportι (DivFamily.zero π T).F
      ≫ pullback.snd π T.hom) :=
  (DivFamily.zero π T).isFinite_support locallyQuasiFinite_zero

end DivFamily

end Scheme

end AlgebraicGeometry
