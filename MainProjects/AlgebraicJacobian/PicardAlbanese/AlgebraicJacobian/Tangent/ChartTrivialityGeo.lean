/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.ChartClassNaturality
import AlgebraicJacobian.Tangent.PicEpsKernelTrivial

/-!
# (iii-c2-aff-geo) IS CLOSED (W5-T4): an ε-kernel class is trivial on a thickened affine chart

`informal/w5-t4-worksheet.md` has carried **(iii-c2-aff-geo)** as T4's last mathematical residue
since §6.17 — *"the chart module of an `ε`-kernel class base-changes to the chart module of its
restriction"* — and it was the `hcyc` binder of
`Scheme.Opens.cechPicMap_ι_eq_one_of_dualNumberChart_of_cyclic`
(`Tangent/DualNumberChartPic.lean`). This file discharges it.

`Opens.cechPicMap_ι_eq_one_of_map_eq_one`: given `g : X ⟶ Z`, an affine open `O` of `Z` with
affine preimage, and presentations `Γ(Z, O) ≃+* A[ε]`, `Γ(X, g⁻¹O) ≃+* A` intertwining `g.appLE`
with `ε ↦ 0`, a Čech–Picard class on `Z` trivial on `g⁻¹O` is trivial on `O`.

## What was actually missing was TWO links, not one

§6.17 correctly diagnosed the residue as a naturality square. It was that **plus** a ring-level
composition that three module docstrings had described without writing down:

1. **The square** — `Opens.cechPicClass_map` (`Tangent/ChartClassNaturality.lean`).
2. **`fst` versus the ε-quotient** — `TruncExpCech.pic_eq_one_of_mapRingHom_fst`
   (`Tangent/PicEpsKernelTrivial.lean`). The geometry delivers triviality of the base change along
   `fst`; the landed module tower consumes freeness of the base change along `A[ε] ⧸ (ε)`.

Given both, this file is four `refine`/`rw` lines. No dual-number *arithmetic* appears anywhere in
it — that was all spent upstream.

## `hsq` is a SQUARE, not a factoring — and the type error is the honest signal

The first version of this statement asked only for `e : Γ(Z, O) ≃+* A[ε]` and
`g.appLE O (g⁻¹O) = fstRingHom ∘ e`. That **does not typecheck**: `g.appLE` lands in
`Γ(X, g ⁻¹ᵁ O)`, while `fstRingHom ∘ e` lands in `A`. So the downstairs chart needs its own
presentation `e'`, and the hypothesis is the commuting square of the two. Worth recording because
the failure was informative rather than an obstacle: a mis-stated intertwining announced itself as
a type mismatch naming exactly the two rings that had been conflated.

## Why the split across three modules — for readability, NOT for a technical reason

The ring half lives in `Tangent/PicEpsKernelTrivial.lean` and the square in
`Tangent/ChartClassNaturality.lean` because they are about different things (`A[ε]` and the affine
dictionary respectively) and neither needs the other. **An earlier draft of this docstring claimed
the split was forced** — that importing the square into the ring file flipped an instance and broke
it. That claim is RETRACTED: it was measured with a hand-rolled `lean` call missing the project's
own `maxSynthPendingDepth = 3`, and with the option supplied the combined import set elaborates
fine (verified). The split is a choice; a later session may merge the files if it prefers, and
should not expect a wall. See `PicEpsKernelTrivial`'s docstring for the option trap itself, which
is real and worth reading before trusting any lock-free check.

## One error the LSP could not have caught, and the reason

The proofs here were developed in a single scratch file and were green in the LSP with zero
diagnostics. Split into these three modules, the *first* version put `namespace TruncExpCech`
inside `namespace AlgebraicGeometry` — it is top-level (`Tangent/TruncExpUnits.lean:60`) — and the
LSP could report only `Imports are out of date`, because the new imports had no oleans yet. A
kernel check against a scratch olean root found nine errors in twelve seconds.

> **After splitting verified proofs into a NEW module that imports another NEW module, the LSP is
> blind to it.** `lean_diagnostic_messages` answering with one import complaint is not a pass;
> kernel-check the chain in dependency order (with the lakefile's options, per above) before
> believing the split preserved what the scratch file proved.

## What this does NOT close

*This section described the state when this file landed (`93f84ed2`). All three items it listed
were discharged later the same session; kept with its resolutions so the file is not read as
open work.*

**The two named consumer inputs of T4** — `V₀ ≠ ⊥ ∧ V₀ ≠ ⊤` and `Surjective f.base` at the
`ε ↦ 0` map (`Tangent/TwoChartSelector.lean`'s `surjective_selector_comp` relocated the latter to
a topological fact about a map of one-point spaces) — were **both witnessed**:
`Tangent/EpsZeroSurjective.lean` (`2755a58e`, over an arbitrary ring) and
`Tangent/TwoChartHonest.lean` (`80e6da8e`, which reduced *both* chart conditions to the single
hypothesis `¬ IsAffine Y`). `Tangent/TwoChartHonestGenus.lean` (`2d46afeb`) then made even that
unnecessary: `¬ IsAffine` was a chosen sufficient condition, and `g ≠ 0` discharges what it was
wanted for. Inbox `I-0729` records the `¬ IsAffine` route and its price, but it is not on the
critical path.

**The ring equivalences and the square this file's hypotheses take are also built**, in
`Tangent/EpsChartSquare.lean` (`aaa4627bb`): `e` is `Over.dualNumberSectionsOfIsAffineOpen`, `e'`
its `ε ↦ 0` reduction, and `relSectionsMap_eq_fstRingHom_comp` is the square `hsq`, instantiated at
`A = Γ(C.left, W)`. The original note here — that `hsq` was "the next consumer-side obligation,
named rather than built" — priced work that was three quarters landed; see worksheet §6.28.

The standing lesson of inbox `I-0630`/`I-0679`/`I-0711` still applies to how this file is read: a
carrier with no producers reads as an island exactly like one with no consumers, and the two need
opposite repairs. So does `I-0687`: a retraction that misses a docstring has not landed.

## Main declarations

* `AlgebraicGeometry.Scheme.Opens.cechPicMap_ι_eq_one_of_map_eq_one` — **(iii-c2-aff-geo)**.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §§6.17, 6.27.
-/

set_option autoImplicit false

universe u

open CategoryTheory TrivSqZeroExt DualNumber

namespace AlgebraicGeometry

namespace Scheme

variable {X Z : Scheme.{u}} (g : X ⟶ Z)

/-- **(iii-c2-aff-geo): an `ε`-kernel Čech–Picard class is trivial on a thickened affine chart.**

For `g : X ⟶ Z` (at the tangent computation: the `ε ↦ 0` immersion of the curve into its
thickening), an affine open `O ⊆ Z` whose preimage is affine, and ring equivalences presenting the
two section rings as `A[ε]` upstairs and `A` downstairs **compatibly with `g`** (`hsq`), a class
`L` whose pullback is trivial on `g ⁻¹ᵁ O` is itself trivial on `O`.

Proof: `Opens.cechPicClass_map` turns the geometric hypothesis into triviality of the base change
of the chart class along `g.appLE`; `hsq` rewrites that base change as `fst` after `e`; and
`TruncExpCech.pic_eq_one_of_mapRingHom_fst` with `CommRing.Pic.eq_one_of_mapRingEquiv` bring
triviality back to `O`.

`A` is an arbitrary commutative ring: no curve, no base field and no finiteness enter. -/
theorem Opens.cechPicMap_ι_eq_one_of_map_eq_one
    (O : Z.Opens) (hO : IsAffineOpen O) (hgO : IsAffineOpen (g ⁻¹ᵁ O))
    (L : Z.CechPic) (A : Type u) [CommRing A] (e : Γ(Z, O) ≃+* DualNumber A)
    (e' : Γ(X, g ⁻¹ᵁ O) ≃+* A)
    (hsq : (e' : Γ(X, g ⁻¹ᵁ O) →+* A).comp (g.appLE O (g ⁻¹ᵁ O) le_rfl).hom
      = (TruncExpCech.fstRingHom (R := A)).comp (e : Γ(Z, O) →+* DualNumber A))
    (htriv : Scheme.CechPic.map (g ⁻¹ᵁ O).ι (Scheme.CechPic.map g L) = 1) :
    Scheme.CechPic.map O.ι L = 1 := by
  refine Opens.cechPicMap_ι_eq_one_of_cechPicClass_eq_one hO ?_
  refine CommRing.Pic.eq_one_of_mapRingEquiv e ?_
  refine TruncExpCech.pic_eq_one_of_mapRingHom_fst _ ?_
  rw [CommRing.Pic.mapRingHom_mapRingHom, ← hsq,
    ← CommRing.Pic.mapRingHom_mapRingHom, ← Opens.cechPicClass_map g O hO hgO L,
    Opens.cechPicClass, htriv, map_one, map_one, map_one]

end Scheme

end AlgebraicGeometry
