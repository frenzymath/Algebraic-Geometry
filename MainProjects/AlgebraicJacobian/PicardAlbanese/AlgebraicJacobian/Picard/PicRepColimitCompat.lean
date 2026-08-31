/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ThetaAssembly
import AlgebraicJacobian.Picard.PicRepDatum

/-!
# β1 — Pic⁰ commutes with the base-field colimit `K_s = colim k''` (DAT-G0 probe)

**Deliverable of the DAT-G0 β1 feasibility probe** (mini-spec `informal/spec-datg0.md`
§4.3, landing note I-0259).  β1 is the SOLE avatar-less brick gating the DAT-G0 route:
*does the degree-zero Picard functor `pic0` commute with the filtered colimit
`K_s = colim_{k''} k''` of the base field (`k''` ranging over finite separable
subextensions of `K_s/k'`)?*  This file states β1 precisely against the landed
`pic0Subgroup`/`pic0TypeFunctor` API, records the **verdict**, and lands the load-bearing
**reduction** to a single pinned residual.

## Verdict: **YES — provable-in-tree (L), route-pinned; NOT obstructed, NOT the fallback**

The hard search DOWNGRADES β1 from "XL, no landed avatar" to "L, reduction fully landed,
one analytic residual", because the base-field-change functoriality of `pic0` is **already
a landed NATURAL ISOMORPHISM**:

* `pic0Theta` / `pic0ThetaType` (`Picard/Pic0ThetaAssembly.lean`):
  `pic0Functor (C_L) ≅ (Over.map σ).op ⋙ pic0Functor C`, for an **arbitrary** field
  extension `k → L` (`σ = Spec.map (algebraMap k L)`), with **no** finiteness / separability
  / Galois content.  I.e. the Pic⁰ functor over the base-changed field `L` is the FIXED
  challenge-base functor `pic0Functor C` precomposed with the pushforward `(Over.map σ).op`.

This collapses β1 onto the **single fixed functor** `pic0TypeFunctor C` over the challenge
base `k`.  After rebasing every stage by `pic0Theta`, the varying-field colimit
`colim_{k''} pic0(C_{k''})(T''_{k''}) → pic0(C_{K_s})(T''_{K_s})` becomes an internal
statement in the single category `Over (Spec (.of k))`:

> **β1 (fixed-base form, the honest content):** the fixed functor `pic0TypeFunctor C`
> sends the cofiltered limit of test schemes `S_{K_s} = lim_{k''} S_{k''}`
> (`S_{k''} := (Over.map σ_{k''}).obj T''_{k''}`, all `k`-schemes, affine transition maps
> since `Spec k''' → Spec k''` is affine, qcqs) to the filtered colimit of its values.

The reduction *(raw base-field colimit)  ⟸  (fixed-base cofiltered-limit preservation)*
is **fully mechanical from landed + mathlib machinery**:
`pic0ThetaType` (the componentwise natural iso) + mathlib's colimit transport across a
natural iso (`CategoryTheory.Limits.preservesColimit_of_natIso`,
`IsColimit.equivOfNatIsoOfIso`).  See `pic0TypeFunctor_baseChange_iso` and
`Pic0PreservesFilteredBaseColimit` below.

### The sole pinned residual (the analytic heart, avatar in hand)

`Pic0PreservesFilteredBaseColimit C` — that `pic0TypeFunctor C` (FIXED base `k`) is
locally of finite presentation *as a functor*.  On **affine** tests `overSpec k A` this is
exactly:

> the affine relative-Picard plus construction `PicEtAff C A` (hence its degree-zero
> subgroup `pic0Subgroup C (overSpec k A)`) **commutes with filtered colimits of the test
> algebra `A`**,

which rides **finite presentation of the proper smooth curve `C/k`**.  Named avatars
(mathlib, `.lake-packages/mathlib` v4.31.0, verified this pass):

* `CommRingCat.preservesColimit_coyoneda_of_finitePresentation`
  (`Algebra/Category/Ring/FinitePresentation.lean:144`) — `Hom_R(S,−)` preserves filtered
  colimits for finitely-presented `S`;
* `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` (`:81`, existence /
  surjectivity) + `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit` (`:45`,
  uniqueness / injectivity);
* scheme level: `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
  (`AlgebraicGeometry/AffineTransitionLimit.lean:1177`, EXISTENCE) +
  `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType` (`:686`, UNIQUENESS) +
  `Scheme.exists_isAffineOpen_preimage_eq` (`:1058`) / `exists_isOpenCover_and_isAffine`
  (`:1078`) for spreading the affine opens & sections of `S_{K_s} = lim S_{k''}` back to a
  finite stage.

This residual is **`divRep`-free** (it is intrinsic to `C/k`, needing neither the Jacobian
nor `rep_{K_s}`), sized M–L; it is NOT a one-probe proof, hence the probe verdict is
**YES-PINNED** rather than **YES-LANDED**.  What DAT-G0's β brick now consumes:
`Pic0PreservesFilteredBaseColimit C` (this file) ⟹ β1 ⟹ (with α + the LANDED
`AffineTransitionLimit`/`Ring.FinitePresentation` spreading) β2's descent of `rep_{K_s}` to
a finite stage `k'`.

## Main declarations

* `pic0TypeFunctor_baseChange_iso` — the landed rebasing: `pic0TypeFunctor (C_L)` is the
  fixed-base functor precomposed with the pushforward (a repackaging of `pic0ThetaType`,
  machine-checked here in the exact form the colimit argument consumes).
* `Pic0PreservesFilteredBaseColimit` — the β1 residual, as a named `Prop` over the FIXED
  base: `pic0TypeFunctor C` preserves the colimit (in `(Over (Spec k))ᵒᵖ`) of every
  cofiltered limit of qcqs test schemes with affine transition maps.  The pinned target of
  the DAT-G0 implementation lane.
* `pic0_baseField_preserves_of_fixedBase` — the reduction: the residual for the fixed base
  `C` transports along `pic0ThetaType` to base-field-colimit preservation for `C_L`,
  i.e. β1 for the base-changed curve follows from the fixed-base residual.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-! ## The landed rebasing: `pic0` over `L` is the fixed-base functor pushed forward -/

variable (L : Type u) [Field L] [Algebra k L]

/-- **The base-field rebasing of `pic0` (landed).**  The Type-valued degree-zero Picard
functor over the base-changed field `L` is the FIXED challenge-base functor
`pic0TypeFunctor C` precomposed with the pushforward `(Over.map σ).op`
(`σ = Spec.map (algebraMap k L)`) — verbatim the landed natural isomorphism
`pic0ThetaType`.  This is the identity that collapses the β1 base-field colimit onto the
single fixed functor `pic0TypeFunctor C`: every stage `pic0(C_{k''})` is `pic0 C` read on
the pushed-forward test, so the varying-field colimit is a cofiltered *limit of test
schemes* over the fixed base `k`. -/
noncomputable def pic0TypeFunctor_baseChange_iso :
    pic0TypeFunctor ((baseChange k L).obj C)
      ≅ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).op
          ⋙ pic0TypeFunctor C :=
  pic0ThetaType k L C

/-! ## The β1 residual (pinned) and the reduction to the fixed base -/

/-- **The β1 residual** — the sole avatar-less analytic heart this probe pins.  The FIXED
challenge-base functor `pic0TypeFunctor C` is *locally of finite presentation as a functor*:
it sends the colimit (in `(Over (Spec k))ᵒᵖ`) of every cofiltered limit of qcqs test
schemes with affine transition maps to the filtered colimit of its values.  Equivalently,
on affine tests, `PicEtAff C A` commutes with filtered colimits of the test algebra `A`
(finite presentation of `C/k`).  Named avatars: see the module docstring
(`preservesColimit_coyoneda_of_finitePresentation`,
`exists_π_app_comp_eq_of_locallyOfFinitePresentation`).  Pinned target of the DAT-G0
implementation lane; `divRep`-free, intrinsic to `C/k`. -/
def Pic0PreservesFilteredBaseColimit : Prop :=
  ∀ ⦃J : Type u⦄ [SmallCategory J] [IsCofiltered J] (S : J ⥤ Over (Spec (.of k))),
    (∀ ⦃i j : J⦄ (f : i ⟶ j), IsAffineHom (S.map f).left) →
    (∀ i, CompactSpace (S.obj i).left) →
    (∀ i, QuasiSeparatedSpace (S.obj i).left) →
    ∀ [HasLimit S], PreservesColimit S.op (pic0TypeFunctor C)

/-- **The β1 reduction (load-bearing core, LANDED).**  The base-field-colimit
compatibility of `pic0` at `L` follows, for *any* diagram `K` of `L`-tests, from the SAME
compatibility of the FIXED challenge-base functor read on the pushed-forward tests — because
`pic0TypeFunctor (C_L)` is `(Over.map σ).op ⋙ pic0TypeFunctor C` up to the landed natural
iso `pic0ThetaType`, and colimit preservation transports along a natural iso
(`preservesColimit_of_natIso`).  This is the step that carries the fixed-base residual
`Pic0PreservesFilteredBaseColimit` to β1 for the base-changed curve `C_{K_s}`. -/
theorem preservesColimit_pic0TypeFunctor_baseChange {J : Type u} [Category.{u} J]
    (K : J ⥤ (Over (Spec (.of L)))ᵒᵖ)
    [PreservesColimit K ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).op
        ⋙ pic0TypeFunctor C)] :
    PreservesColimit K (pic0TypeFunctor ((baseChange k L).obj C)) :=
  preservesColimit_of_natIso K (pic0TypeFunctor_baseChange_iso C L).symm

end AlgebraicGeometry
