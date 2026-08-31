/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.DualNumberCarrier
import AlgebraicJacobian.Tangent.TruncExpCech

/-!
# The carrier translation matches the two Čech coboundary subgroups (W5-T4, item (2))

`Tangent/DualNumberCarrier.lean` builds the carrier translation
`Γ(C, W)[ε] ≃+* Γ(C_ε, fst⁻¹ W)` and proves it natural in the open. That makes the two Čech `Ȟ¹`
*carriers* isomorphic — and, as inbox `I-0571` records and `I-0630` re-found in this file's
neighbour, an isomorphism of the two ends of a map says nothing about the map, while the Wave-5
computation is a **kernel**. This file closes that gap on the coboundary side:

```
Subgroup.map (dualNumberSectionsUnits C) (cechCoboundaryUnits (mapRingHom res₀) (mapRingHom res₁))
  = cechCoboundaryUnits res₀' res₁'
```

(`Over.map_cechCoboundaryUnits_dualNumberSectionsUnits`), where the primed restrictions are those of
the **thickened** charts. With that equality the translation descends to a `MulEquiv` of the two
two-chart Čech `Ȟ¹`-of-units groups (`Over.dualNumberCechH1Equiv`) — the object the `ε`-kernel
computation consumes, rather than the two carriers at its ends.

## Why an equality and not a containment

A containment would let the map descend but would not identify the quotients: the descended map
could have a kernel arising from the target subgroup being strictly larger. Since both inclusions
come from the *same* square applied to the equivalence and to its inverse, the equality costs one
extra `le_antisymm` branch — and settling for `≤` would leave exactly the gap `I-0630`(2) named
("the two `H¹` carriers are still only abstractly isomorphic").

## Implementation notes

`cechCoboundaryUnits` is a join of two `MonoidHom.range`s, and `Subgroup.map` distributes over `⊔`
(`Subgroup.map_sup`, `MonoidHom.map_range`), so the whole statement reduces to **one range
identification per chart** and no case analysis on `Bool` ever appears. Each range identification is
`Over.unitsMap_resHom_dualNumberSectionsUnits` — the landed naturality-in-the-open square — read
forwards for `≤` and applied to the preimage of a thickened chart unit (via
`MulEquiv.apply_symm_apply`) for `≥`.

**One spelling trap, measured.** `Over.unitsMap_resHom_dualNumberSectionsUnits` is stated with
`Over.resAlgHom C h` coerced to a `RingHom`, whereas `cechCoboundaryUnits` at the two-chart datum is
stated with `C.left.resHom h`. The two are equal by `rfl`, and `exact` accepts either — but `rw`
cannot see through the coercion, failing with *"the target expression is not type-correct under the
`instances` transparency level"*. So `range_dualNumberSectionsUnits_comp` is **stated in the
`resHom` spelling** (the consumer's), not the `resAlgHom` one; with that choice the subgroup
equality is a single `rw` chain. Same family as the seam recorded in
`Tangent/TwoChartQuotientNaturality.lean`.

## Main declarations

* `AlgebraicGeometry.Over.range_dualNumberSectionsUnits_comp` — the per-chart range identification.
* `AlgebraicGeometry.Over.map_cechCoboundaryUnits_dualNumberSectionsUnits` — **item (2)**: the
  translation carries the thickened coboundary subgroup **onto** the base one.
* `AlgebraicGeometry.Over.dualNumberCechH1Equiv` — the induced isomorphism of two-chart Čech
  `Ȟ¹`-of-units groups, with `dualNumberCechH1Equiv_mk`.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §6.20(2).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open TruncExpCech DualNumber TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

attribute [local instance] Over.sectionsAlgebra

namespace Over

variable {V W : C.left.Opens}

/-- **The per-chart range identification.** The translated image of the chart units of `Γ(C, V)[ε]`,
restricted to the overlap `W`, is exactly the image of the *thickened* chart units of
`Γ(C_ε, fst⁻¹ V)` restricted to `fst⁻¹ W`.

This is the whole content of item (2): `cechCoboundaryUnits` is a join of two such ranges, so the
subgroup statement follows by `Subgroup.map_sup` with no `Bool` case analysis.

`≤` is `Over.unitsMap_resHom_dualNumberSectionsUnits` read forwards; `≥` is that same square applied
to `(dualNumberSectionsUnits C hV hV').symm v`, whose image is `v` by `MulEquiv.apply_symm_apply`.

Stated in the `C.left.resHom` spelling rather than `Over.resAlgHom` — see the module docstring: the
two are `rfl`-equal, but only this one is `rw`-usable at the consumer. -/
theorem range_dualNumberSectionsUnits_comp
    (hV : IsCompact ((V : Set C.left))) (hV' : IsQuasiSeparated ((V : Set C.left)))
    (hW : IsCompact ((W : Set C.left))) (hW' : IsQuasiSeparated ((W : Set C.left)))
    (h : W ≤ V) :
    MonoidHom.range
        ((Over.dualNumberSectionsUnits C hW hW').toMonoidHom.comp
          (Units.map (mapRingHom (C.left.resHom h)).toMonoidHom))
      = MonoidHom.range
          (Units.map ((C ⊗ overSpec k (DualNumber k)).left.resHom
            (Scheme.Hom.preimage_mono
              (fst C (overSpec k (DualNumber k))).left h)).toMonoidHom) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨v, rfl⟩
    exact ⟨Over.dualNumberSectionsUnits C hV hV' v,
      Over.unitsMap_resHom_dualNumberSectionsUnits C hV hV' hW hW' h v⟩
  · rintro x ⟨v, rfl⟩
    refine ⟨(Over.dualNumberSectionsUnits C hV hV').symm v, ?_⟩
    have := Over.unitsMap_resHom_dualNumberSectionsUnits C hV hV' hW hW' h
      ((Over.dualNumberSectionsUnits C hV hV').symm v)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm

/-- **ITEM (2): the carrier translation carries the thickened Čech coboundary subgroup ONTO the
base one.** This is what upgrades `Tangent/DualNumberCarrier.lean`'s equivalence of *carriers* to an
equivalence of the two Čech `Ȟ¹` **quotients**, and it is what inbox `I-0630`(2) found missing:
`resHom_dualNumberSections` made it provable, but nobody had proved it, so the two `H¹` groups were
only abstractly isomorphic — worthless to a kernel computation (`I-0571`).

Proof: `Subgroup.map` distributes over the join `cechCoboundaryUnits` is built from, leaving one
range identification per chart (`range_dualNumberSectionsUnits_comp`). No dual-number algebra, no
case split. -/
theorem map_cechCoboundaryUnits_dualNumberSectionsUnits {V : Bool → C.left.Opens}
    (hc : ∀ s, IsCompact ((V s : Set C.left))) (hq : ∀ s, IsQuasiSeparated ((V s : Set C.left)))
    (hci : IsCompact (((V false ⊓ V true : C.left.Opens) : Set C.left)))
    (hqi : IsQuasiSeparated (((V false ⊓ V true : C.left.Opens) : Set C.left))) :
    Subgroup.map (Over.dualNumberSectionsUnits C hci hqi).toMonoidHom
        (cechCoboundaryUnits
          (mapRingHom (C.left.resHom (inf_le_left : V false ⊓ V true ≤ V false)))
          (mapRingHom (C.left.resHom (inf_le_right : V false ⊓ V true ≤ V true))))
      = cechCoboundaryUnits
          ((C ⊗ overSpec k (DualNumber k)).left.resHom
            (Scheme.Hom.preimage_mono (fst C (overSpec k (DualNumber k))).left
              (inf_le_left : V false ⊓ V true ≤ V false)))
          ((C ⊗ overSpec k (DualNumber k)).left.resHom
            (Scheme.Hom.preimage_mono (fst C (overSpec k (DualNumber k))).left
              (inf_le_right : V false ⊓ V true ≤ V true))) := by
  rw [cechCoboundaryUnits, cechCoboundaryUnits, Subgroup.map_sup, MonoidHom.map_range,
    MonoidHom.map_range,
    range_dualNumberSectionsUnits_comp C (hc false) (hq false) hci hqi inf_le_left,
    range_dualNumberSectionsUnits_comp C (hc true) (hq true) hci hqi inf_le_right]

/-- **The two-chart Čech `Ȟ¹`-of-units groups agree across the carrier translation.** The
truncated-exponential engine of `Tangent/TruncExpCech.lean` computes with the left-hand quotient
(`DualNumber` of the *original* overlap sections); the two-chart comparison
`Scheme.twoChartClass` consumes the right-hand one (units of the *thickened* overlap sections). This
is the isomorphism between them, at quotient level.

`QuotientGroup.congr` of the carrier translation and the subgroup equality above. Because it is
built from that equality rather than asserted, a consumer may transport a **kernel** across it —
which the carrier equivalence alone did not license. -/
noncomputable def dualNumberCechH1Equiv {V : Bool → C.left.Opens}
    (hc : ∀ s, IsCompact ((V s : Set C.left))) (hq : ∀ s, IsQuasiSeparated ((V s : Set C.left)))
    (hci : IsCompact (((V false ⊓ V true : C.left.Opens) : Set C.left)))
    (hqi : IsQuasiSeparated (((V false ⊓ V true : C.left.Opens) : Set C.left))) :
    ((DualNumber Γ(C.left, V false ⊓ V true))ˣ ⧸ cechCoboundaryUnits
        (mapRingHom (C.left.resHom (inf_le_left : V false ⊓ V true ≤ V false)))
        (mapRingHom (C.left.resHom (inf_le_right : V false ⊓ V true ≤ V true)))) ≃*
      (Γ((C ⊗ overSpec k (DualNumber k)).left,
          (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ (V false ⊓ V true))ˣ ⧸
        cechCoboundaryUnits
          ((C ⊗ overSpec k (DualNumber k)).left.resHom
            (Scheme.Hom.preimage_mono (fst C (overSpec k (DualNumber k))).left
              (inf_le_left : V false ⊓ V true ≤ V false)))
          ((C ⊗ overSpec k (DualNumber k)).left.resHom
            (Scheme.Hom.preimage_mono (fst C (overSpec k (DualNumber k))).left
              (inf_le_right : V false ⊓ V true ≤ V true)))) :=
  QuotientGroup.congr _ _ (Over.dualNumberSectionsUnits C hci hqi)
    (map_cechCoboundaryUnits_dualNumberSectionsUnits C hc hq hci hqi)

@[simp]
theorem dualNumberCechH1Equiv_mk {V : Bool → C.left.Opens}
    (hc : ∀ s, IsCompact ((V s : Set C.left))) (hq : ∀ s, IsQuasiSeparated ((V s : Set C.left)))
    (hci : IsCompact (((V false ⊓ V true : C.left.Opens) : Set C.left)))
    (hqi : IsQuasiSeparated (((V false ⊓ V true : C.left.Opens) : Set C.left)))
    (u : (DualNumber Γ(C.left, V false ⊓ V true))ˣ) :
    dualNumberCechH1Equiv C hc hq hci hqi (QuotientGroup.mk u)
      = QuotientGroup.mk (Over.dualNumberSectionsUnits C hci hqi u) :=
  rfl

end Over

end AlgebraicGeometry
