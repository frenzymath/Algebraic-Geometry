/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RelThetaTransportCore
import AlgebraicJacobian.Tangent.DualNumberCarrierCoboundary

/-!
# (T3-5): the downstairs `k → k` Čech `Ȟ¹` translation (W5-T3)

The seam `informal/w5-t4-worksheet.md` §7.6 found by printing the types of the arrows T3's
composition has to join. (T3-2) (`Tangent/EpsArrowIdentification.lean`) matched their **sources**;
their **targets** are sections of *different schemes*:

```
engine  (TwoCover.unitsReduction C.left U₀ U₁) lands on   Γ(C.left,       U₀ ⊓ U₁)ˣ ⧸ …
geometry (pullbackOverlapQuot (relCurveMap …))  lands on   Γ(relCurve C k, fst⁻¹U₀ ⊓ fst⁻¹U₁)ˣ ⧸ …
```

This file is the `MulEquiv` between them — the `k → k` analogue of
`Over.dualNumberCechH1Equiv`, built the same way from the same two inputs.

## What it is built over, and why NOT the object this lane coined for the job

`Tangent/EpsChartSquare.lean`'s `epsChartDown` is a ring equivalence of the right shape, but at
**one** open and under `IsAffineOpen`. The right input is **`sectionsCollapse`**
(`Cohomology/RelThetaTransportCore.lean:41`), landed for the relative-theta work: a `k`-linear
equivalence `Γ(C.left, V) ≃ₗ[k] Γ(relCurve C k, fst ⁻¹ᵁ V)` at **arbitrary** `V` with only
compact/quasi-separated hypotheses, **no affineness**, and shipping exactly the two auxiliary lemmas
this construction needs:

* `sectionsCollapse_mul` (:116) — multiplicativity, hence the units form;
* `sectionsCollapse_resHom` (:235) — naturality in the open, hence the coboundary image.

Worksheet §7.6 records that the first draft of that section priced this seam by `epsChartDown` and
called the downstairs side one-third equipped. **Searching the object's shape across the project
rather than the name this lane coined found a stronger input with both lemmas already proved.**

## Implementation notes — one real wall, and it was not an instance

`QuotientGroup.congr _ _ e he` is how `Over.dualNumberCechH1Equiv` is built, and copying that
spelling here fails with *"failed to synthesize instance … `.Normal`"*. Three attempts to supply the
instance were wasted: a `haveI`, a project-local `Subgroup.normal_of_isMulCommutative` instance, and
dropping `Scheme.overModule` from the local instances. **None of them was the problem.**
Measured: the
`Normal` instance for the exact subgroup synthesizes by `inferInstance` in a standalone probe,
and so
does the quotient *type*. The failure came from the two positional `_`s — with the subgroups left as
metavariables, elaboration reaches the `[Normal]` argument before they are solved. Naming **both**
subgroups explicitly in the `congr` call closes it with no instance work at all.

> The upstairs file gets away with `_ _` because its own elaboration order happens to solve them
> first. A spelling that works in one file is not thereby a spelling; and *"failed to synthesize
> instance"* is not always about instances — check whether the instance's arguments are still
> metavariables. (`I-0685` family; the reverse of `measure-the-instance-surface`.)

## Scope

Everything here is over the **identity** base change `k → k`. It says nothing about a general
coefficient extension, and it is not the dual-number side (that is
`Tangent/DualNumberCarrier*.lean`). It does not compose the chain: (T3-6), the composite
`H¹(C,𝒪) ≃+ ker(CechPic(C_ε) → CechPic(C))`, is still unwritten, and whether it comes out
**additive** without extra work is unmeasured — see worksheet §7.6.

## Main declarations

* `AlgebraicGeometry.collapseRingEquiv` / `collapseUnits` — the ring and units forms of
  `sectionsCollapse`.
* `AlgebraicGeometry.unitsMap_resHom_collapseUnits` — naturality of the units form in the open.
* `AlgebraicGeometry.range_collapseUnits_comp` — the per-chart range identification.
* `AlgebraicGeometry.map_cechCoboundaryUnits_collapseUnits` — the coboundary subgroup image.
* `AlgebraicGeometry.collapseCechH1Equiv` — **(T3-5)**: the two-chart Čech `Ȟ¹`-of-units groups of
  `C.left` and of `relCurve C k` agree.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §7.6.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open TruncExpCech

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))

/-! ## The ring and units forms of `sectionsCollapse` -/

/-- **`sectionsCollapse` as a ring equivalence.** It is `k`-linear by construction and
multiplicative by `sectionsCollapse_mul`, so the two combine into a `≃+*` with no new content. -/
noncomputable def collapseRingEquiv (V : C.left.Opens)
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) :
    Γ(C.left, V) ≃+* Γ(relCurve C k, (fst C (overSpec k k)).left ⁻¹ᵁ V) where
  __ := sectionsCollapse C V hV hV'
  map_mul' := sectionsCollapse_mul C V hV hV'

/-- **The induced isomorphism of unit groups** — the form the Čech cocycle engine consumes, since a
two-chart `Ȟ¹` is a quotient of a group of *units*. -/
noncomputable def collapseUnits (V : C.left.Opens)
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) :
    Γ(C.left, V)ˣ ≃* Γ(relCurve C k, (fst C (overSpec k k)).left ⁻¹ᵁ V)ˣ :=
  Units.mapEquiv (collapseRingEquiv C V hV hV').toMulEquiv

/-- **Naturality of the units form in the open**: restricting downstairs then collapsing agrees with
collapsing then restricting on the relative curve. `Units.ext` plus `sectionsCollapse_resHom`. -/
theorem unitsMap_resHom_collapseUnits {W V : C.left.Opens} (hWV : W ≤ V)
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left))
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (u : Γ(C.left, V)ˣ) :
    Units.map ((relCurve C k).resHom
        (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left hWV)).toMonoidHom
        (collapseUnits C V hV hV' u)
      = collapseUnits C W hW hW' (Units.map (C.left.resHom hWV).toMonoidHom u) := by
  ext
  exact (sectionsCollapse_resHom C hWV hW hW' hV hV' (u : Γ(C.left, V))).symm

variable {V : Bool → C.left.Opens}

/-! ## The coboundary subgroup, one chart at a time -/

/-- **The per-chart range identification.** The collapsed image of the chart units of `Γ(C.left,
W)`,
restricted to the overlap, is exactly the image of the *relative* chart units restricted to the
relative overlap.

Both inclusions come from `unitsMap_resHom_collapseUnits`, read forwards and applied at
`(collapseUnits …).symm v`. Same proof shape as
`Over.range_dualNumberSectionsUnits_comp` on the dual-number side. -/
theorem range_collapseUnits_comp {W W' : C.left.Opens}
    (hW : IsCompact ((W : Set C.left))) (hW' : IsQuasiSeparated ((W : Set C.left)))
    (hI : IsCompact ((W' : Set C.left))) (hI' : IsQuasiSeparated ((W' : Set C.left)))
    (h : W' ≤ W) :
    MonoidHom.range ((collapseUnits C W' hI hI').toMonoidHom.comp
        (Units.map (C.left.resHom h).toMonoidHom))
      = MonoidHom.range (Units.map ((relCurve C k).resHom
          (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left h)).toMonoidHom) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨v, rfl⟩
    exact ⟨collapseUnits C W hW hW' v, unitsMap_resHom_collapseUnits C h hI hI' hW hW' v⟩
  · rintro x ⟨v, rfl⟩
    refine ⟨(collapseUnits C W hW hW').symm v, ?_⟩
    have := unitsMap_resHom_collapseUnits C h hI hI' hW hW' ((collapseUnits C W hW hW').symm v)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm

/-- **The collapse carries the two-chart Čech coboundary subgroup ONTO the relative one.** As on the
dual-number side, `cechCoboundaryUnits` is a join of two ranges and `Subgroup.map` distributes over
`⊔`, so this is one range identification per chart and no `Bool` case analysis.

An equality rather than a containment, for the reason
`Tangent/DualNumberCarrierCoboundary.lean` records: a containment lets the map descend but does not
identify the quotients, and a kernel comparison needs the identification. -/
theorem map_cechCoboundaryUnits_collapseUnits
    (hc : ∀ s, IsCompact ((V s : Set C.left))) (hq : ∀ s, IsQuasiSeparated ((V s : Set C.left)))
    (hci : IsCompact (((V false ⊓ V true : C.left.Opens) : Set C.left)))
    (hqi : IsQuasiSeparated (((V false ⊓ V true : C.left.Opens) : Set C.left))) :
    Subgroup.map (collapseUnits C (V false ⊓ V true) hci hqi).toMonoidHom
        (cechCoboundaryUnits
          (C.left.resHom (inf_le_left : V false ⊓ V true ≤ V false))
          (C.left.resHom (inf_le_right : V false ⊓ V true ≤ V true)))
      = cechCoboundaryUnits
          ((relCurve C k).resHom (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left
            (inf_le_left : V false ⊓ V true ≤ V false)))
          ((relCurve C k).resHom (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left
            (inf_le_right : V false ⊓ V true ≤ V true))) := by
  rw [cechCoboundaryUnits, cechCoboundaryUnits, Subgroup.map_sup, MonoidHom.map_range,
    MonoidHom.map_range,
    range_collapseUnits_comp C (hc false) (hq false) hci hqi inf_le_left,
    range_collapseUnits_comp C (hc true) (hq true) hci hqi inf_le_right]
  rfl

/-! ## (T3-5): the descended equivalence -/

/-- **(T3-5): the two-chart Čech `Ȟ¹`-of-units groups of `C.left` and of `relCurve C k` agree.**

The seam worksheet §7.6 found between the truncated-exponential engine (which computes on `C.left`)
and the geometric comparison (which lands on `relCurve C k`). `QuotientGroup.congr` of
`collapseUnits` and the subgroup equality above — and, per the module docstring, **both subgroups
must be named explicitly** in that call; leaving them as `_` produces a spurious `.Normal`
synthesis failure. -/
noncomputable def collapseCechH1Equiv
    (hc : ∀ s, IsCompact ((V s : Set C.left))) (hq : ∀ s, IsQuasiSeparated ((V s : Set C.left)))
    (hci : IsCompact (((V false ⊓ V true : C.left.Opens) : Set C.left)))
    (hqi : IsQuasiSeparated (((V false ⊓ V true : C.left.Opens) : Set C.left))) :
    (Γ(C.left, V false ⊓ V true)ˣ ⧸ cechCoboundaryUnits
        (C.left.resHom (inf_le_left : V false ⊓ V true ≤ V false))
        (C.left.resHom (inf_le_right : V false ⊓ V true ≤ V true))) ≃*
      (Γ(relCurve C k, (fst C (overSpec k k)).left ⁻¹ᵁ (V false ⊓ V true))ˣ ⧸
        cechCoboundaryUnits
          ((relCurve C k).resHom (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left
            (inf_le_left : V false ⊓ V true ≤ V false)))
          ((relCurve C k).resHom (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left
            (inf_le_right : V false ⊓ V true ≤ V true)))) :=
  QuotientGroup.congr
    (cechCoboundaryUnits
      (C.left.resHom (inf_le_left : V false ⊓ V true ≤ V false))
      (C.left.resHom (inf_le_right : V false ⊓ V true ≤ V true)))
    (cechCoboundaryUnits
      ((relCurve C k).resHom (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left
        (inf_le_left : V false ⊓ V true ≤ V false)))
      ((relCurve C k).resHom (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left
        (inf_le_right : V false ⊓ V true ≤ V true))))
    (collapseUnits C (V false ⊓ V true) hci hqi)
    (map_cechCoboundaryUnits_collapseUnits C hc hq hci hqi)

@[simp]
theorem collapseCechH1Equiv_mk
    (hc : ∀ s, IsCompact ((V s : Set C.left))) (hq : ∀ s, IsQuasiSeparated ((V s : Set C.left)))
    (hci : IsCompact (((V false ⊓ V true : C.left.Opens) : Set C.left)))
    (hqi : IsQuasiSeparated (((V false ⊓ V true : C.left.Opens) : Set C.left)))
    (u : Γ(C.left, V false ⊓ V true)ˣ) :
    collapseCechH1Equiv C hc hq hci hqi (QuotientGroup.mk u)
      = QuotientGroup.mk (collapseUnits C (V false ⊓ V true) hci hqi u) :=
  rfl

end AlgebraicGeometry
