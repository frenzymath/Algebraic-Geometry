/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.EpsChartSquare
import AlgebraicJacobian.Tangent.ChartTrivialityGeo

/-!
# `hchart` DISCHARGED at the Wave-5 charts (W5-T3, closing worksheet §7.9 item (4))

`Tangent/TwoChartKernelComparison.lean`'s `twoChartKernelEquiv` — the bijection of the two
`ε`-kernels, (T3-3) — takes one hypothesis, clause (iii-c2):

```
hchart : ∀ L, CechPic.map f L = 1 → ∀ s, CechPic.map (V s).ι L = 1
```

Three docstrings in this directory say that hypothesis "has a producer at the Wave-5 instance",
naming `Scheme.Opens.cechPicMap_ι_eq_one_of_map_eq_one` (`Tangent/ChartTrivialityGeo.lean`) plus
`Tangent/EpsChartSquare.lean`. Worksheet §7.9 item (4) verified every step of that claim by hand and
recorded the honest residue in its own words:

> *"What I did NOT do is instantiate the composite of the two, so «`hchart` is discharged at the
> instance» remains an argument with every step verified rather than a landed declaration."*

**This file is that declaration** (`chartTrivial_of_map_eq_one`). The consumer grep that dates the
gap: before this file, the producer had **four** occurrences outside its defining file and **all
four were prose** — `EpsChartSquare.lean:64/:89/:100` and `TwoChartKernelComparison.lean:35`.
Zero in a proof term. (`I-0711`/`I-0630` island shape, pointed at this lane's own Wave-5 surface.)

## The obstacle was the §8.0 cast, and it is the SAME cast — measured, not assumed

The producer, at `g := relCurveMap C k[ε] k` and `O := fst_{k[ε]} ⁻¹ᵁ W`, wants `e'` at the open
`g ⁻¹ᵁ O = relCurveMap ⁻¹ᵁ fst_{k[ε]} ⁻¹ᵁ W`, and states its `hsq` through
`(g.appLE O (g ⁻¹ᵁ O) le_rfl).hom`. But `EpsChartSquare`'s two exports live at `fst_k ⁻¹ᵁ W`:
`epsChartDown` is `Γ(relCurve C k, fst_k ⁻¹ᵁ W) ≃+* Γ(C.left, W)`, and its
`relSectionsMap_eq_fstRingHom_comp` is stated through `relSectionsMap`, which is `appLE` at *that*
pair of opens. Those two opens are equal only propositionally — `relCurveMap_preimage`, the
`rfl`-failure quoted in `Tangent/EpsReductionSquare.lean`'s docstring. So §7.9's "every step
verified" was verified about statements that do not compose until the transport is supplied; the
missing piece was never a mathematical one.

## Why `resRingEquivOfEq` is built from `resHom` and not from `▸`

The first draft defined the open-equality transport as `h ▸ RingEquiv.refl _`. It typechecks, and
`epsChartDownAt` built from it typechecks — but then `hsq_at`'s proof cannot proceed: the
`rw [relSectionsMap, RingEquiv.symm_apply_eq, resRingEquivOfEq]` chain does not advance the goal,
because nothing rewrites under a `▸`-transport whose motive is opaque. Rebuilt from
`X.resHom (le_of_eq h)` in both directions, the same proof closes: `Scheme.resHom_resHom` and
`Scheme.resHom_self` fire, and the two `@[simp]` projection lemmas below give `rw` a handle.

> **CORRECTION (2026-07-29, review `I-0831`) — and it corrects this file's own first version.** The
> paragraph above originally called that a *"silent no-op … with **no error** reported"*, and
> generalised it into a rule about rewrites that fail without a message. **That is false**, and
> it was checked by rebuilding the `▸` draft verbatim: `rw` **does** report,
> *"Tactic 'rewrite' failed: Did not find an occurrence of the pattern `(RingEquiv.symm ?e) ?x = ?y`
> … the target expression is not type-correct under the 'instances' transparency level."* I had
> observed the unchanged goal (via `lean_goal` on the surrounding proof) and inferred the absence of
> a diagnostic instead of reading one. The mechanism and the fix are unchanged; the "no error
> message" claim is withdrawn, along with the "mirror image of §7.7" framing built on it.
>
> **What survives is the ordinary lesson, already on record as `I-0685`/`I-0817`:** a `▸`-transport
> is opaque to `rw`, and the error message names transparency rather than the definition. Prefer a
> transport assembled from the API's own restriction maps whenever lemmas about them exist, which
> for `Scheme.resHom` they do — this is `presheafCongr`'s design in
> `Cohomology/RelThetaTransportCore.lean`, arrived at independently.

## Scope

`W` is an arbitrary affine open of `C.left`, and that is the **only** hypothesis: the affineness of
the two base-changed opens is produced here (`isAffineOpen_fst_preimage`,
`isAffineOpen_relCurveMap_fst_preimage`), not assumed. ~~carried as hypotheses (`hO`, `hgO`) — the
producer needs them and this file does not manufacture them.~~ **That sentence described this file's
first version and was the defect `I-0829` found**: with both as binders the headline was true as a
statement and unusable as a tool, since neither had a reachable producer.

Nothing here is two-chart: `chartTrivial_of_map_eq_one` is per-chart, which is exactly the
shape `hchart`'s `∀ s : Bool` quantifier consumes. This file does **not** instantiate
`twoChartKernelEquiv` itself; that needs the two surjectivity binders as well
(`Tangent/TwoChartHonestGenus.lean`, `Tangent/EpsZeroSurjective.lean`).

## Main declarations

* `AlgebraicGeometry.resRingEquivOfEq` — the section-ring transport along an equality of opens,
  with its two projection lemmas.
* `AlgebraicGeometry.epsChartDownAt` — `epsChartDown` at the open the producer wants (the `e'`).
* `AlgebraicGeometry.appLE_relCurveMap_eq` — `appLE` at the transported pair is `relSectionsMap`
  followed by the transport.
* `AlgebraicGeometry.hsq_at` — `EpsChartSquare`'s square, restated as the producer's `hsq`.
* `AlgebraicGeometry.isAffineOpen_fst_preimage` / `isAffineOpen_relCurveMap_fst_preimage` — the two
  affineness inputs the producer needs, **produced** (they were binders in this file's first
  version; `I-0829`).
* `AlgebraicGeometry.chartTrivial_of_map_eq_one` — **(iii-c2) at the Wave-5 charts**: a class killed
  by `ε ↦ 0` is trivial on each thickened affine chart. Takes `hW` alone.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §§7.9, 8.2, 8.3.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open TruncExpCech DualNumber TrivSqZeroExt

namespace AlgebraicGeometry

open scoped TruncExpCech.EpsilonReduction

attribute [local instance] Scheme.overModule Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))

/-! ## The section-ring transport along an equality of opens -/

/-- **Restriction along an equality of opens, as a ring equivalence.** Built from
`X.resHom (le_of_eq …)` in both directions and **not** from `h ▸ RingEquiv.refl _` — see the module
docstring for the measured reason (the `▸` version makes `hsq_at`'s `rw` a silent no-op). -/
noncomputable def resRingEquivOfEq {X : Scheme.{u}} {U U' : X.Opens} (h : U = U') :
    Γ(X, U) ≃+* Γ(X, U') where
  toFun := X.resHom (le_of_eq h.symm)
  invFun := X.resHom (le_of_eq h)
  left_inv s := by rw [Scheme.resHom_resHom, Scheme.resHom_self]
  right_inv s := by rw [Scheme.resHom_resHom, Scheme.resHom_self]
  map_mul' a b := map_mul _ a b
  map_add' a b := map_add _ a b

@[simp]
theorem resRingEquivOfEq_apply {X : Scheme.{u}} {U U' : X.Opens} (h : U = U') (s : Γ(X, U)) :
    resRingEquivOfEq h s = X.resHom (le_of_eq h.symm) s :=
  rfl

@[simp]
theorem resRingEquivOfEq_symm_apply {X : Scheme.{u}} {U U' : X.Opens} (h : U = U') (s : Γ(X, U')) :
    (resRingEquivOfEq h).symm s = X.resHom (le_of_eq h) s :=
  rfl

/-! ## The producer's `e'` and `hsq` at the transported open -/

/-- **The `e'` the producer takes**: `EpsChartSquare.epsChartDown` moved to the open
`relCurveMap ⁻¹ᵁ fst_{k[ε]} ⁻¹ᵁ W` that `Opens.cechPicMap_ι_eq_one_of_map_eq_one` asks for. -/
noncomputable def epsChartDownAt {W : C.left.Opens} (hW : IsAffineOpen W) :
    Γ(relCurve C k, relCurveMap C (DualNumber k) k ⁻¹ᵁ
        ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W)) ≃+* Γ(C.left, W) :=
  (resRingEquivOfEq (relCurveMap_preimage C (DualNumber k) k W)).trans (epsChartDown C hW)

/-- **`appLE` at the transported pair of opens is `relSectionsMap` followed by the transport.**
The bridge between the producer's spelling of the `ε ↦ 0` section map and this directory's.
`Scheme.Hom.appLE_map`: `appLE` then a restriction is one `appLE`, the witnesses being
proof-irrelevant. -/
theorem appLE_relCurveMap_eq {W : C.left.Opens}
    (s : Γ(relCurve C (DualNumber k), (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W)) :
    ((relCurveMap C (DualNumber k) k).appLE
        ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W)
        (relCurveMap C (DualNumber k) k ⁻¹ᵁ
          ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W)) le_rfl).hom s
      = (resRingEquivOfEq (relCurveMap_preimage C (DualNumber k) k W)).symm
          (relSectionsMap C (DualNumber k) k W s) := by
  rw [relSectionsMap, resRingEquivOfEq_symm_apply]
  exact (congr((CommRingCat.Hom.hom $(Scheme.Hom.appLE_map (relCurveMap C (DualNumber k) k)
    (le_of_eq (relCurveMap_preimage C (DualNumber k) k W).symm)
    (homOfLE (le_of_eq (relCurveMap_preimage C (DualNumber k) k W))).op)) s)).symm

/-- **`EpsChartSquare`'s square, restated as the producer's `hsq`.** The content is entirely
`relSectionsMap_eq_fstRingHom_comp`; what this adds is the transport, and the two restrictions
cancel by `resHom_resHom`/`resHom_self`. -/
theorem hsq_at {W : C.left.Opens} (hW : IsAffineOpen W) :
    ((epsChartDownAt C hW : Γ(relCurve C k, relCurveMap C (DualNumber k) k ⁻¹ᵁ
          ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W)) →+* Γ(C.left, W))).comp
        ((relCurveMap C (DualNumber k) k).appLE
          ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W)
          (relCurveMap C (DualNumber k) k ⁻¹ᵁ
            ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W)) le_rfl).hom
      = (TruncExpCech.fstRingHom (R := Γ(C.left, W))).comp
          ((Over.dualNumberSectionsOfIsAffineOpen C hW).symm :
            Γ((C ⊗ overSpec k (DualNumber k)).left,
              (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W) →+* DualNumber Γ(C.left, W)) := by
  rw [← relSectionsMap_eq_fstRingHom_comp C hW]
  ext s
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom]
  rw [appLE_relCurveMap_eq C s, epsChartDownAt, RingEquiv.trans_apply,
    resRingEquivOfEq_symm_apply, resRingEquivOfEq_apply, Scheme.resHom_resHom,
    Scheme.resHom_self]
  rfl

/-! ## The two affineness inputs, PRODUCED rather than assumed

A fresh-context review (inbox `I-0829`) found that the first version of this file carried both
affineness facts as hypotheses of `chartTrivial_of_map_eq_one` and called them routine in its
docstring — while no reachable producer existed for either, so the headline was true as a statement
and unusable as a tool (`I-0688`: every explicit binder needs a producer). Both are one line from
`IsAffineOpen.preimage`, and the second needs the same `relCurveMap_preimage` rewrite as everything
else in this file. -/

/-- **The base-changed chart is affine.** `IsAffineOpen.preimage` along the first projection, whose
`IsAffineHom` instance is `Over.isAffineHom_fst_left`. -/
theorem isAffineOpen_fst_preimage {W : C.left.Opens} (hW : IsAffineOpen W) :
    IsAffineOpen ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W) :=
  hW.preimage (fst C (overSpec k (DualNumber k))).left

/-- **The `ε ↦ 0` preimage of the base-changed chart is affine.** Rewrite by
`relCurveMap_preimage` — the propositional equality of opens this whole file is about — and it is
the `k`-side base-changed chart, affine by the same `IsAffineOpen.preimage`. -/
theorem isAffineOpen_relCurveMap_fst_preimage {W : C.left.Opens} (hW : IsAffineOpen W) :
    IsAffineOpen (relCurveMap C (DualNumber k) k ⁻¹ᵁ
      ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W)) := by
  rw [relCurveMap_preimage]
  exact hW.preimage (fst C (overSpec k k)).left

/-! ## (iii-c2) at the Wave-5 charts -/

/-- **`hchart` DISCHARGED, per chart** (clause (iii-c2) at the Wave-5 instance): a Čech Picard class
on the thickened curve killed by `ε ↦ 0` is trivial on the thickened affine chart over `W`.

This is the composite worksheet §7.9 item (4) named and did not write: the geometric producer
`Opens.cechPicMap_ι_eq_one_of_map_eq_one` at `g := relCurveMap C k[ε] k`, with `e'` and `hsq`
supplied by `epsChartDownAt`/`hsq_at` above, and its `htriv` obtained from the kernel hypothesis by
`rw [hker, map_one]` — the one-line implication §7.9 had already probed.

Per-chart, hence exactly the shape `twoChartKernelEquiv`'s `hchart : ∀ s : Bool, …` consumes.

**It takes `hW` alone.** The two affineness facts the geometric producer needs are discharged above
rather than assumed — see that section's note and `I-0829` for why the first version of this file
was wrong to carry them as binders. -/
theorem chartTrivial_of_map_eq_one {W : C.left.Opens} (hW : IsAffineOpen W)
    (L : (relCurve C (DualNumber k)).CechPic)
    (hker : Scheme.CechPic.map (relCurveMap C (DualNumber k) k) L = 1) :
    Scheme.CechPic.map ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W).ι L = 1 :=
  Scheme.Opens.cechPicMap_ι_eq_one_of_map_eq_one (relCurveMap C (DualNumber k) k)
    ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W)
    (isAffineOpen_fst_preimage C hW) (isAffineOpen_relCurveMap_fst_preimage C hW) L Γ(C.left, W)
    (Over.dualNumberSectionsOfIsAffineOpen C hW).symm (epsChartDownAt C hW) (hsq_at C hW)
    (by rw [hker, map_one])

end AlgebraicGeometry
