/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EffectivityMoving
import AlgebraicJacobian.Tangent.CyclicQuotientGenerator

/-!
# Chart triviality at the Picard-group level (W5-T4, clause (iii-c2-aff), steps 1–2)

`Tangent/DualNumberChartTriviality.lean` proves the *module* statement — an invertible
`A[ε]`-module cyclic mod `(ε)` is free. This file lifts it to the two statements a **Čech
Picard class on an affine chart** needs, so that clause (iii-c2-aff) reduces to producing the
generator:

* `CommRing.Pic.eq_one_of_cyclic_mod_eps` — a `Pic A[ε]` class whose `AsModule` is cyclic mod
  `(ε)` is trivial;
* `CommRing.Pic.eq_one_of_mapRingEquiv` — triviality transports back along a ring **equivalence**
  of the coefficient ring;
* `AlgebraicGeometry.Scheme.Opens.cechPicMap_ι_eq_one_of_dualNumberChart` — the two composed with
  the tree's affine dictionary: a class trivial after transport to `A[ε]` restricts trivially to
  the chart;
* `AlgebraicGeometry.Scheme.Opens.cechPicMap_ι_eq_one_of_dualNumberChart_of_cyclic` — the same
  with the generator **produced** from cyclicity of the reduction rather than assumed, which is
  the form (iii-c2-aff) actually consumes.

## The sheaf→module step is already in the tree — do not rebuild it

`informal/w5-t4-worksheet.md` §6.11 step 3 flagged the sheaf→module crossing as the honest risk
of this clause, citing inbox `I-0533` (a sibling project was flagged for eliding it). Measured:
**the crossing does not have to be built here.** `Scheme.Opens.cechPicClass`
(`Picard/EffectivityMoving.lean`) already presents a `CechPic` class on an affine open as an
element of `CommRing.Pic Γ(Z, O)` — a *ring*-level object — and mathlib's
`CommRing.Pic.AsModule` / `mk_eq_self` / `mk_eq_one_iff_free` complete the passage to modules.
`EffectivityMoving.cechPicClass_basicOpen_eq_one_of_free` already uses exactly this pattern, so
it is in use and not merely available. See worksheet §6.15.

## Implementation notes

`CommRing.Pic.eq_one_of_mapRingEquiv` is `EffectivityMoving`'s `private
pic_eq_one_of_mapRingHom` specialised to an equivalence, re-derived from public API in three
lines (`mapRingHom_mapRingHom`, `RingEquiv.symm_apply_apply`, `mapAlgebra_self_apply`). `private`
hides the name, not the proof — the standing lesson of inbox `I-0567`; no upstream change is
needed for it.

## What is still owed of (iii-c2-aff)

**Not the generator — that is now produced rather than assumed.**
`Tangent/CyclicQuotientGenerator.lean` (ported from the sibling project, cross-project thread
`I-0495`) shows the "fixed `m`" binder *is* cyclicity of the reduction `M ⧸ (ε)·M`, with the
converse, so
`cechPicMap_ι_eq_one_of_dualNumberChart_of_cyclic` below consumes cyclicity directly.

What remains is the **geometric** input, and only it: identifying *"`L` restricts trivially along
`ε ↦ 0`"* with *"the chart module's reduction is cyclic"* — i.e. freeness of the restriction on
the chart. Nothing in this file or in `CyclicQuotientGenerator.lean` supplies that, and neither
may be read as closing (iii-c2-aff).

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §§6.11, 6.15.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TrivSqZeroExt DualNumber

namespace CommRing.Pic

/-! ## Step 1: the algebra core at the Picard-group level -/

/-- **A `Pic A[ε]` class cyclic mod `(ε)` is trivial.** The Picard-group form of
`DualNumber.free_of_cyclic_mod_eps`: pass to `AsModule`, apply the module statement, and come
back by `mk_eq_self`.

This is clause (i) of the W5-T4 decomposition in the shape the affine dictionary hands it over:
`Scheme.Opens.cechPicClass` produces a `CommRing.Pic` element, not a module. -/
theorem eq_one_of_cyclic_mod_eps {A : Type u} [CommRing A] (M : CommRing.Pic (DualNumber A))
    (m : M.AsModule)
    (h : ∀ x : M.AsModule, ∃ r : DualNumber A,
      x - r • m ∈ Ideal.span {(ε : DualNumber A)} • (⊤ : Submodule (DualNumber A) M.AsModule)) :
    M = 1 := by
  rw [← CommRing.Pic.mk_eq_self (M := M), CommRing.Pic.mk_eq_one_iff_free]
  exact DualNumber.free_of_cyclic_mod_eps A M.AsModule m h

/-! ## Step 2: transport of triviality along a coefficient equivalence -/

/-- **Triviality transports back along a ring equivalence of coefficients.** If the image of
`M : Pic R` under `Pic.mapRingHom e` is trivial for a ring *equivalence* `e : R ≃+* S`, then `M`
is trivial.

Needed because the affine dictionary produces the class over `Γ(Z, O)`, while the dual-number
statement lives over `A[ε]`, and the identification between them is an equivalence
(`Over.dualNumberSectionsOfIsAffineOpen`) rather than an equality.

This is `Picard/EffectivityMoving.lean`'s `private pic_eq_one_of_mapRingHom` at an equivalence.
It re-derives from public API in three lines, so the `private` marker is not an obstruction —
inbox `I-0567`. -/
theorem eq_one_of_mapRingEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    {M : CommRing.Pic R} (h : CommRing.Pic.mapRingHom (e : R →+* S) M = 1) : M = 1 := by
  have h2 := congrArg (CommRing.Pic.mapRingHom (e.symm : S →+* R)) h
  rw [map_one, CommRing.Pic.mapRingHom_mapRingHom] at h2
  rw [show (e.symm : S →+* R).comp (e : R →+* S) = RingHom.id R from by
    ext x; exact e.symm_apply_apply x] at h2
  rw [← Algebra.algebraMap_self (R := R), CommRing.Pic.mapRingHom_algebraMap,
    CommRing.Pic.mapAlgebra_self_apply] at h2
  exact h2

end CommRing.Pic

namespace AlgebraicGeometry

namespace Scheme

variable {Z : Scheme.{u}}

/-! ## The two composed with the affine dictionary -/

/-- **Chart triviality from a dual-number presentation of the chart's sections.** For an affine
open `O` of `Z` whose section ring is identified with `A[ε]` by a ring equivalence `e`, a Čech
Picard class `L` whose transported chart class is cyclic mod `(ε)` restricts trivially to `O`.

This is clause (iii-c2-aff) *modulo its generator*: steps 1 and 2 of worksheet §6.15 together
with the tree's affine dictionary
(`Opens.cechPicClass`, `Opens.cechPicMap_ι_eq_one_of_cechPicClass_eq_one`). The remaining
obligation — producing `m` and its cyclicity from "`L` is trivial on `C`" — is the hypothesis
`hcyc` here, deliberately left as a hypothesis rather than a `sorry` (w5-worksheet §0(4): never
register a staged fact).

`A` is an arbitrary commutative ring: nothing here needs the curve, the base field, or
finiteness of the sections. -/
theorem Opens.cechPicMap_ι_eq_one_of_dualNumberChart {O : Z.Opens} (hO : IsAffineOpen O)
    (L : Z.CechPic) (A : Type u) [CommRing A] (e : Γ(Z, O) ≃+* DualNumber A)
    (m : (CommRing.Pic.mapRingHom (e : Γ(Z, O) →+* DualNumber A)
      (O.cechPicClass hO L)).AsModule)
    (hcyc : ∀ x : (CommRing.Pic.mapRingHom (e : Γ(Z, O) →+* DualNumber A)
        (O.cechPicClass hO L)).AsModule,
      ∃ r : DualNumber A, x - r • m ∈ Ideal.span {(ε : DualNumber A)} •
        (⊤ : Submodule (DualNumber A)
          (CommRing.Pic.mapRingHom (e : Γ(Z, O) →+* DualNumber A)
            (O.cechPicClass hO L)).AsModule)) :
    Scheme.CechPic.map O.ι L = 1 :=
  Opens.cechPicMap_ι_eq_one_of_cechPicClass_eq_one hO
    (CommRing.Pic.eq_one_of_mapRingEquiv e
      (CommRing.Pic.eq_one_of_cyclic_mod_eps _ m hcyc))

/-- **Chart triviality from cyclicity of the reduction** — the form clause (iii-c2-aff) consumes,
with the generator produced rather than chosen.

Same statement as `cechPicMap_ι_eq_one_of_dualNumberChart` except that the hypothesis is
*"`M ⧸ (ε)·M` is cyclic"*, which is what "the restriction of `L` to `C` is trivial on this chart"
delivers — a trivialising section, not a choice of generator. The generator is then supplied by
`Submodule.exists_sub_smul_mem_of_quotient_cyclic`
(`Tangent/CyclicQuotientGenerator.lean`, ported from the sibling project per `I-0495`), whose
converse makes the two hypotheses equivalent.

The remaining obligation of (iii-c2-aff) is therefore exactly the geometric one: produce the
cyclicity from triviality along `ε ↦ 0`. -/
theorem Opens.cechPicMap_ι_eq_one_of_dualNumberChart_of_cyclic {O : Z.Opens}
    (hO : IsAffineOpen O) (L : Z.CechPic) (A : Type u) [CommRing A]
    (e : Γ(Z, O) ≃+* DualNumber A)
    (hcyc : ∃ y : (CommRing.Pic.mapRingHom (e : Γ(Z, O) →+* DualNumber A)
        (O.cechPicClass hO L)).AsModule ⧸
          (Ideal.span {(ε : DualNumber A)} • (⊤ : Submodule (DualNumber A)
            (CommRing.Pic.mapRingHom (e : Γ(Z, O) →+* DualNumber A)
              (O.cechPicClass hO L)).AsModule)),
      ∀ z, ∃ r : DualNumber A, z = r • y) :
    Scheme.CechPic.map O.ι L = 1 := by
  obtain ⟨m, hm⟩ := Submodule.exists_sub_smul_mem_of_quotient_cyclic _ hcyc
  exact Opens.cechPicMap_ι_eq_one_of_dualNumberChart hO L A e m hm

end Scheme

end AlgebraicGeometry
