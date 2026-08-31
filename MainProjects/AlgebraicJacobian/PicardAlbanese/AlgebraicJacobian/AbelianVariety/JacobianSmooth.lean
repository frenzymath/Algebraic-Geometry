/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianData

/-!
# Smoothness of the Jacobian (W5-S2), and the shape of the relative-dimension assembly

Brick S2 of the Wave-5 abelian-variety package (roadmap `AJCR.w5-av.s2`):
`Smooth d.J.hom` for the pinned representability datum `(d : JacobianData C)`,
via mathlib's group-scheme smoothness criterion.

## Why this is one line, and what it costs

`smooth_of_grpObj` (`Mathlib/AlgebraicGeometry/Group/Smooth.lean:64`) needs three
hypotheses on `f`, and the datum supplies two of them outright:

* `[LocallyOfFiniteType f]` — `d.locallyOfFiniteType`, a construction certificate;
* `[GrpObj (Over.mk f)]` — `d.grpObj`. Note the **keying**: instance search does
  not unfold `Over.mk` on its own, so the group structure must be ascribed at the
  `Over.mk d.J.hom` spelling. This is pure defeq (`Over.mk d.J.hom` *is* `d.J` by
  structure eta) and `Picard/JacobianData.lean` machine-checks exactly this as its
  η-defeq smoke test 2;
* `[GeometricallyReduced f]` — brick **S1**, which is *not* proved here. It stays
  an instance argument, so this file is unconditional in the datum and every
  consumer sees the S1 dependency in its own signature.

Geometric (rather than bare) reducedness is intrinsic to mathlib's route, not an
artefact: the proof base-changes to `AlgebraicClosure k`, runs the homogeneity
argument there — translating the smooth locus by `GrpObj.mulRight` until it meets
any prescribed closed point — and descends along
`@Surjective ⊓ @Flat ⊓ @QuasiCompact`. That is also why S1 is naturally stated
geometrically; see `informal/w5-s-worksheet.md` §1–§2.

## Main declarations

* `AlgebraicGeometry.JacobianData.smooth` — `Smooth d.J.hom`, given S1.
* `AlgebraicGeometry.JacobianData.smooth_of_smoothOfRelativeDimension` — the
  degradation direction of the frozen numeral, recorded so that S3's consumers
  need not re-derive `Smooth` from `SmoothOfRelativeDimension (genus C)`.

The S3 assembly itself (`SmoothOfRelativeDimension (genus C) d.J.hom`) is
**worksheet-first** and its route is frozen in `informal/w5-s-worksheet.md` §3;
the short version is that mathlib's `SmoothOfRelativeDimension` is a *pointwise,
local-at-source* condition, so no "relative dimension is locally constant"
theorem is needed — translation homogeneity (X2) transports the identity count
(T5) to the other points. No Lean is written for S3 here: its numeral waits on
T3/T4.

Reference: Kleiman, "The Picard scheme", §5 `cor:sm` (arXiv:math/0504020);
Milne, "Abelian varieties", Prop. 2.1.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace JacobianData

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- **S2: the Jacobian is smooth over `k`** (Kleiman §5 `cor:sm`). A group scheme
locally of finite type and geometrically reduced over a field is smooth
(`smooth_of_grpObj`); the first two hypotheses come from the datum, and geometric
reducedness is brick S1, taken here as an instance argument. -/
theorem smooth (d : JacobianData C) [GeometricallyReduced d.J.hom] : Smooth d.J.hom :=
  letI := d.locallyOfFiniteType
  letI : GrpObj (Over.mk d.J.hom) := d.grpObj
  smooth_of_grpObj d.J.hom

/-- The frozen numeral degrades to bare smoothness: if the Jacobian is smooth of
relative dimension `genus C` (brick S3) then it is smooth. Recorded here so
consumers of the S3 instance need not rediscover
`SmoothOfRelativeDimension.smooth`, and so that the two statements of the
smoothness leg sit side by side. -/
theorem smooth_of_smoothOfRelativeDimension (d : JacobianData C)
    [SmoothOfRelativeDimension (genus C) d.J.hom] : Smooth d.J.hom :=
  SmoothOfRelativeDimension.smooth (n := genus C) d.J.hom

end JacobianData

end AlgebraicGeometry
