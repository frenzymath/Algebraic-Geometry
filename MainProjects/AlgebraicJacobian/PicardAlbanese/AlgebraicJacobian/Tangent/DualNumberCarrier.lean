/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.DualNumberBaseChange
import AlgebraicJacobian.Cohomology.RelativeSectionsLinear

/-!
# The carrier translation at `Spec k[ε]` (W5-T4 step (b))

The truncated-exponential engine of `Tangent/TruncExpCech.lean` computes the Čech `Ȟ¹` of
units of `Γ(C, V₀ ⊓ V₁)[ε]` — the `DualNumber` of the **original** sections. The two-chart
comparison of `Tangent/TwoChartCechPic.lean` consumes `Γ(C_ε, V₀' ⊓ V₁')ˣ` — the **thickened**
sections of the base-changed curve. This file identifies the two:

```
Γ(C, W)[ε]  ≃+*  Γ(C_ε, fst⁻¹ W)                  (`Over.dualNumberSections`)
```

for any qcqs open `W ⊆ C.left`, and proves the two compatibility laws a cocycle-level consumer
needs: naturality in the open (`Over.resHom_dualNumberSections`) and naturality of the
underlying algebra comparison in the coefficient ring (`TruncExpCech.baseChangeAlgEquiv_symm_map`).

## Why this file exists, and what it does *not* yet do

`informal/w5-t4-worksheet.md` §6.10 recorded — from a fresh-context review (inbox `I-0573`) —
that "clause (ii) is landed" was true of the *algebra* equivalence
`TruncExpCech.baseChangeAlgEquiv` and **false of the cover-level translation**: only a docstring
asserted the composite, and no declaration built it. This file builds it, so the assertion now
rests on a theorem.

**Still owed, and named here so it is not mistaken for landed** (worksheet §6.13): the
identification of the section map induced by the `ε ↦ 0` test-object morphism
`overDualNumberZero` with `TrivSqZeroExt.fstHom` across this equivalence. That is a statement
about the *coefficient* direction, and the tree's existing coefficient-naturality tool
(`AlgebraicGeometry.relSectionsMap`) does not apply off the shelf: it wants
`[Algebra R R'] [IsScalarTower k R R']`, and at `R := k[ε]`, `R' := k` the instance
`Algebra k[ε] k` does **not** exist — the reduction `fstRingHom` is a `k`-algebra map but it is
not registered as an algebra structure, and registering it globally would be a diamond with
`Algebra k k`. `baseChangeAlgEquiv_symm_map` below is the algebra half of that statement, proved
here in the general form (an arbitrary `f : A →ₐ[k] B`), which is what a future session should
compose with a scheme-level coefficient square rather than re-deriving.

## Implementation notes

The equivalence is `TruncExpCech.baseChangeAlgEquiv` (inverted, so that the dual numbers are the
*source*) followed by `Over.sectionsBaseChange`. Both directions matter: the engine produces
`DualNumber`-side data, the comparison consumes scheme-side data.

`Over.resHom_dualNumberSections` is exactly `Over.sectionsBaseChange_naturality` composed with
`baseChangeAlgEquiv_symm_map` at `f := Over.resAlgHom` — no new geometry, which is the point of
factoring the coefficient naturality out as its own lemma.

## Main declarations

* `AlgebraicGeometry.Over.dualNumberSections` — the carrier translation
  `Γ(C, W)[ε] ≃+* Γ(C_ε, fst⁻¹ W)`, with `Over.dualNumberSections_apply`.
* `AlgebraicGeometry.Over.dualNumberSectionsOfIsAffineOpen` — the affine-open form, which is
  the one the two-chart cover supplies.
* `TruncExpCech.baseChangeAlgEquiv_symm_map` — naturality of the algebra comparison in the
  coefficient ring, in `symm` form.
* `AlgebraicGeometry.Over.resHom_dualNumberSections` — naturality of the carrier translation in
  the open.
* `AlgebraicGeometry.Over.dualNumberSectionsUnits` — the induced isomorphism of **unit**
  groups, which is the form the Čech cocycle engine consumes, with its own restriction law
  `Over.unitsMap_resHom_dualNumberSectionsUnits`.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §§6.10, 6.13.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open TruncExpCech DualNumber TensorProduct

namespace TruncExpCech

variable {k : Type u} [Field k]

/-- **Naturality of the dual-number base-change comparison in the coefficient ring**, in the
form the carrier translation consumes (`symm` on the outside): for a `k`-algebra map
`f : A →ₐ[k] B`, reducing coefficients commutes with the comparison
`A ⊗[k] k[ε] ≃ₐ[A] A[ε]`.

Proved by `TensorProduct.induction_on`; the pure-tensor case is `baseChangeAlgEquiv_tmul` on
both sides plus `TrivSqZeroExt.ext`, and `fst_mapRingHom` / `snd_mapRingHom` do the rest.

Stated for an arbitrary `f` on purpose. The Wave-5 consumer needs two instances — the
restriction `Over.resAlgHom` along an inclusion of opens (used in
`AlgebraicGeometry.Over.resHom_dualNumberSections` below) and the reduction
`ε ↦ 0`; keeping the lemma general means the second one costs nothing here when a scheme-level
coefficient square lands. -/
theorem baseChangeAlgEquiv_symm_map (A B : Type u) [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (f : A →ₐ[k] B) (x : DualNumber A) :
    (baseChangeAlgEquiv k B).symm (mapRingHom (f : A →+* B) x)
      = Algebra.TensorProduct.map f (AlgHom.id k (DualNumber k))
          ((baseChangeAlgEquiv k A).symm x) := by
  apply (baseChangeAlgEquiv k B).injective
  rw [AlgEquiv.apply_symm_apply]
  have key : ∀ y : A ⊗[k] DualNumber k,
      baseChangeAlgEquiv k B (Algebra.TensorProduct.map f (AlgHom.id k (DualNumber k)) y)
        = mapRingHom (f : A →+* B) (baseChangeAlgEquiv k A y) := by
    intro y
    induction y with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul a y =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, baseChangeAlgEquiv_tmul,
        baseChangeAlgEquiv_tmul]
      refine TrivSqZeroExt.ext ?_ ?_ <;>
        simp [TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, smul_eq_mul, fst_mapRingHom,
          snd_mapRingHom]
  rw [key, AlgEquiv.apply_symm_apply]

end TruncExpCech

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

attribute [local instance] Over.sectionsAlgebra

/-! ## The carrier translation -/

/-- **The carrier translation at the dual numbers**: for a qcqs open `W ⊆ C.left`, the sections
of the base-changed curve `C_ε` over the preimage of `W` are the dual numbers of the sections
of `C` over `W`:

```
Γ(C, W)[ε]  ≃+*  Γ(C_ε, fst⁻¹ W).
```

This is the composite the worksheet's §6.10 box found asserted in a docstring and absent as a
declaration: `TruncExpCech.baseChangeAlgEquiv` inverted (putting the dual numbers on the left,
where the truncated-exponential engine produces them) followed by the landed
`Over.sectionsBaseChange`. -/
noncomputable def Over.dualNumberSections {W : C.left.Opens}
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left)) :
    DualNumber Γ(C.left, W) ≃+*
      Γ((C ⊗ overSpec k (DualNumber k)).left,
        (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W) :=
  (baseChangeAlgEquiv k Γ(C.left, W)).symm.toRingEquiv.trans
    (Over.sectionsBaseChange C (DualNumber k) hW hW')

/-- The carrier translation, unfolded: base-change the tensor form of the dual number.
Definitional; the workhorse normal form for the laws below. -/
theorem Over.dualNumberSections_apply {W : C.left.Opens}
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left))
    (x : DualNumber Γ(C.left, W)) :
    Over.dualNumberSections C hW hW' x
      = Over.sectionsBaseChange C (DualNumber k) hW hW'
          ((baseChangeAlgEquiv k Γ(C.left, W)).symm x) :=
  rfl

/-- The carrier translation at an **affine** open — the form the two-chart cover supplies, since
`Cohomology/RelativeTwoCover.lean`'s `relCover` provides affine thickened charts (and an affine
overlap). Affine opens are qcqs. -/
noncomputable def Over.dualNumberSectionsOfIsAffineOpen {W : C.left.Opens}
    (hW : IsAffineOpen W) :
    DualNumber Γ(C.left, W) ≃+*
      Γ((C ⊗ overSpec k (DualNumber k)).left,
        (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W) :=
  Over.dualNumberSections C hW.isCompact hW.isQuasiSeparated

/-! ## Naturality in the open -/

/-- **The carrier translation commutes with restriction of opens**: restricting a thickened
section along `W' ≤ W` is translating the coefficient-wise restriction of the dual number.

This is the law a *cocycle*-level consumer needs — the two-chart engine restricts overlap units
to refinements constantly — and it is `Over.sectionsBaseChange_naturality` composed with
`TruncExpCech.baseChangeAlgEquiv_symm_map` at `f := Over.resAlgHom`, with no new geometry. -/
theorem Over.resHom_dualNumberSections {W W' : C.left.Opens}
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left))
    (hV : IsCompact (W' : Set C.left)) (hV' : IsQuasiSeparated (W' : Set C.left))
    (h : W' ≤ W) (x : DualNumber Γ(C.left, W)) :
    (C ⊗ overSpec k (DualNumber k)).left.resHom
        (Scheme.Hom.preimage_mono (fst C (overSpec k (DualNumber k))).left h)
        (Over.dualNumberSections C hW hW' x)
      = Over.dualNumberSections C hV hV'
          (mapRingHom (Over.resAlgHom C h : Γ(C.left, W) →+* Γ(C.left, W')) x) := by
  rw [Over.dualNumberSections_apply, Over.dualNumberSections_apply,
    TruncExpCech.baseChangeAlgEquiv_symm_map]
  exact Over.sectionsBaseChange_naturality C (DualNumber k) hW hW' hV hV' h _

/-! ## The unit-group form, which is what the Čech engine consumes -/

/-- **The carrier translation on units**: `(Γ(C, W)[ε])ˣ ≃* Γ(C_ε, fst⁻¹ W)ˣ`. The two-chart
Čech comparison consumes overlap *units*, and the truncated-exponential engine produces them
(`truncExpUnit`), so this is the shape the intertwining actually needs. -/
noncomputable def Over.dualNumberSectionsUnits {W : C.left.Opens}
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left)) :
    (DualNumber Γ(C.left, W))ˣ ≃*
      Γ((C ⊗ overSpec k (DualNumber k)).left,
        (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W)ˣ :=
  Units.mapEquiv (Over.dualNumberSections C hW hW').toMulEquiv

@[simp]
theorem Over.dualNumberSectionsUnits_coe {W : C.left.Opens}
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left))
    (u : (DualNumber Γ(C.left, W))ˣ) :
    (Over.dualNumberSectionsUnits C hW hW' u :
        Γ((C ⊗ overSpec k (DualNumber k)).left,
          (fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W))
      = Over.dualNumberSections C hW hW' (u : DualNumber Γ(C.left, W)) :=
  rfl

/-- The unit-level carrier translation commutes with restriction — the unit form of
`Over.resHom_dualNumberSections`, obtained by `Units.ext` from it.

Stated with `Units.map` of the section-restriction ring map rather than with
`Scheme.unitsRestrict`: the latter lives in `Picard/UnitsCocycle.lean`, which is not in this
file's import cone, and the two are equal by definition
(`AlgebraicGeometry.Scheme.unitsMap_resHom`, `Tangent/TwoChartCechPic.lean`) — so a consumer
downstream of both may rewrite freely between them. -/
theorem Over.unitsMap_resHom_dualNumberSectionsUnits {W W' : C.left.Opens}
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left))
    (hV : IsCompact (W' : Set C.left)) (hV' : IsQuasiSeparated (W' : Set C.left))
    (h : W' ≤ W) (u : (DualNumber Γ(C.left, W))ˣ) :
    Units.map ((C ⊗ overSpec k (DualNumber k)).left.resHom
          (Scheme.Hom.preimage_mono (fst C (overSpec k (DualNumber k))).left h)).toMonoidHom
        (Over.dualNumberSectionsUnits C hW hW' u)
      = Over.dualNumberSectionsUnits C hV hV'
          (Units.map (mapRingHom
            (Over.resAlgHom C h : Γ(C.left, W) →+* Γ(C.left, W'))).toMonoidHom u) :=
  Units.ext (Over.resHom_dualNumberSections C hW hW' hV hV' h (u : DualNumber Γ(C.left, W)))

end AlgebraicGeometry
