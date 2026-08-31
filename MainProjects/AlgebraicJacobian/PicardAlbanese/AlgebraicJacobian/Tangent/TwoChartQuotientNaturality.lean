/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TwoChartNaturality

/-!
# Naturality of the DESCENDED two-chart comparison (W5-T4, intertwining item (1))

`Tangent/TwoChartNaturality.lean` proves the reduction square for `twoChartClassHom` — the map
**before** the Čech quotient. The truncated-exponential engine of `Tangent/TruncExpCech.lean`
works between the quotients (`TruncExpCech.cechUnitsReduction`), so the square the kernel
computation consumes is the one for the descended `twoChartClass`. This file proves it.

## Why the hom-level square was not enough (inbox `I-0630`)

A fresh-context reviewer found that `map_twoChartClassHom`'s generality — no
`Function.Surjective sel`, no affineness — is a property of *that declaration*, and does not carry
to its consumer: `twoChartClass` exists only given `hsel`, so the quotient-level square needs
`hsel` at **both** ends (`sel` and `sel ∘ f.base`). Recorded as the standing rule at
`informal/w5-t4-worksheet.md` §6.18: *a generality claim is scoped to the declaration it is written
on, not to the chain.*

What was genuinely missing is one containment: that pulling back along `f` carries the Čech
coboundary subgroup of `Y` into that of `X`. Without it the pullback does not descend to the
quotients at all, so no square can be stated.

## Implementation notes

The containment (`cechCoboundaryUnits_le_comap_unitsAppLE`) is **not** a cohomological statement.
A coboundary is `ρ₀ˣ(v₀) · ρ₁ˣ(v₁)` for chart units `vₛ : Γ(Y, V s)ˣ`, and the two `unitsAppLE`
functoriality lemmas already in the tree move the pullback past the restriction in both directions:

* `Scheme.Hom.map_unitsAppLE` — pullback after restriction, which retypes the generator as the
  pullback of the *chart* unit;
* `Scheme.Hom.unitsAppLE_map` — restriction after pullback, which puts it back on the overlap.

Both are `@[simp]`, so after `Scheme.resHom` is unfolded to `X.presheaf.map` — the spelling those
two lemmas are stated in — `simp` closes each factor. Unfolding `resHom` is what the proof actually
needs: with `resHom` folded, `rw` fails with *"the target expression is not type-correct under the
`instances` transparency level"*, the familiar symptom of the `Γ`/`presheaf.obj` coercion seam
recorded elsewhere in this directory. Neither `rfl` nor a hand-directed `rw` chain closes it; the
one-line `simp [Scheme.resHom]` does.

The square itself is then free: `QuotientGroup.map_mk` and `twoChartClass_mk` reduce both sides to
the landed `map_twoChartClassHom`.

## Main declarations

* `AlgebraicGeometry.Scheme.cechCoboundaryUnits_le_comap_unitsAppLE` — the containment: pullback
  carries two-chart Čech coboundaries to coboundaries.
* `AlgebraicGeometry.Scheme.pullbackOverlapQuot` — the induced map of two-chart Čech `Ȟ¹`
  quotients.
* `AlgebraicGeometry.Scheme.map_twoChartClass` — **the quotient-level reduction square**, the form
  the `ε`-kernel computation consumes.
* `AlgebraicGeometry.Scheme.map_twoChartClass_eq_one_iff` — its kernel form.

Reference: Kleiman, "The Picard scheme", §5, proof of Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §6.20(1).
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}} {V : Bool → Y.Opens}

/-! ## The containment: pullback carries Čech coboundaries to Čech coboundaries -/

/-- **Pullback along `f` carries a two-chart Čech coboundary to a two-chart Čech coboundary.**

A coboundary on `Y` is a product `ρ₀ˣ(v₀) · ρ₁ˣ(v₁)` of restrictions of *chart* units. Pulling
back commutes with restriction (`Hom.map_unitsAppLE`, then `Hom.unitsAppLE_map`), so the image is
the corresponding product of restrictions of the pulled-back chart units — a coboundary for the
preimage charts.

This is the statement whose absence blocked the quotient-level square (inbox `I-0630`): without
it, `pullbackOverlapUnit` does not descend to the Čech `Ȟ¹` quotients. It is pure `unitsAppLE`
functoriality — no cocycles, no cohomology, no affineness, and no surjectivity of the selector. -/
theorem cechCoboundaryUnits_le_comap_unitsAppLE (f : X ⟶ Y) :
    TruncExpCech.cechCoboundaryUnits
        (Y.resHom (inf_le_left : V false ⊓ V true ≤ V false))
        (Y.resHom (inf_le_right : V false ⊓ V true ≤ V true)) ≤
      (TruncExpCech.cechCoboundaryUnits
        (X.resHom (inf_le_left : f ⁻¹ᵁ V false ⊓ f ⁻¹ᵁ V true ≤ f ⁻¹ᵁ V false))
        (X.resHom (inf_le_right : f ⁻¹ᵁ V false ⊓ f ⁻¹ᵁ V true ≤ f ⁻¹ᵁ V true))).comap
        (f.unitsAppLE (V false ⊓ V true) (f ⁻¹ᵁ V false ⊓ f ⁻¹ᵁ V true) le_rfl) := by
  intro u hu
  obtain ⟨v₀, v₁, rfl⟩ := TruncExpCech.mem_cechCoboundaryUnits.mp hu
  refine Subgroup.mem_comap.mpr (TruncExpCech.mem_cechCoboundaryUnits.mpr
    ⟨f.unitsAppLE (V false) (f ⁻¹ᵁ V false) le_rfl v₀,
      f.unitsAppLE (V true) (f ⁻¹ᵁ V true) le_rfl v₁, ?_⟩)
  rw [map_mul]
  congr 1 <;> simp [Scheme.resHom]

/-! ## The induced map of Čech `Ȟ¹` quotients -/

/-- **The pullback of two-chart Čech `Ȟ¹`-of-units classes** along `f`, i.e.
`pullbackOverlapUnit` descended to the quotients. Well defined by
`cechCoboundaryUnits_le_comap_unitsAppLE`. -/
noncomputable def pullbackOverlapQuot (f : X ⟶ Y) :
    (Γ(Y, V false ⊓ V true)ˣ ⧸ TruncExpCech.cechCoboundaryUnits
        (Y.resHom (inf_le_left : V false ⊓ V true ≤ V false))
        (Y.resHom (inf_le_right : V false ⊓ V true ≤ V true))) →*
      (Γ(X, (fun s ↦ f ⁻¹ᵁ V s) false ⊓ (fun s ↦ f ⁻¹ᵁ V s) true)ˣ ⧸
        TruncExpCech.cechCoboundaryUnits
          (X.resHom (inf_le_left : (fun s ↦ f ⁻¹ᵁ V s) false ⊓ (fun s ↦ f ⁻¹ᵁ V s) true
            ≤ (fun s ↦ f ⁻¹ᵁ V s) false))
          (X.resHom (inf_le_right : (fun s ↦ f ⁻¹ᵁ V s) false ⊓ (fun s ↦ f ⁻¹ᵁ V s) true
            ≤ (fun s ↦ f ⁻¹ᵁ V s) true))) :=
  QuotientGroup.map _ _ (f.unitsAppLE (V false ⊓ V true) (f ⁻¹ᵁ V false ⊓ f ⁻¹ᵁ V true) le_rfl)
    (cechCoboundaryUnits_le_comap_unitsAppLE f)

@[simp]
theorem pullbackOverlapQuot_mk (f : X ⟶ Y) (u : Γ(Y, V false ⊓ V true)ˣ) :
    pullbackOverlapQuot f (QuotientGroup.mk u)
      = QuotientGroup.mk (pullbackOverlapUnit f u) :=
  rfl

/-! ## The quotient-level reduction square -/

/-- **THE QUOTIENT-LEVEL REDUCTION SQUARE.** The descended comparison `twoChartClass` is natural
in the scheme: pulling back a two-chart Čech `Ȟ¹` class and then comparing to `CechPic` is
comparing and then pulling back.

Unlike the hom-level `map_twoChartClassHom`, this needs `Function.Surjective sel` at **both** ends
— the source and the target of `twoChartClass` each exist only given it. That is exactly the
correction of inbox `I-0630`; see the module docstring.

This is the square the `ε`-kernel computation consumes, because the truncated-exponential engine's
`TruncExpCech.cechUnitsReduction` is a map between these quotients, not between the unit groups. -/
theorem map_twoChartClass (f : X ⟶ Y) (sel : Y → Bool) (hmem : ∀ y, y ∈ V (sel y))
    (hsel : Function.Surjective sel)
    (hsel' : Function.Surjective (fun x ↦ sel (f.base x)))
    (q : Γ(Y, V false ⊓ V true)ˣ ⧸ TruncExpCech.cechCoboundaryUnits
      (Y.resHom (inf_le_left : V false ⊓ V true ≤ V false))
      (Y.resHom (inf_le_right : V false ⊓ V true ≤ V true))) :
    Scheme.CechPic.map f (twoChartClass V sel hmem hsel q)
      = twoChartClass (fun s ↦ f ⁻¹ᵁ V s) (fun x ↦ sel (f.base x))
          (fun x ↦ hmem (f.base x)) hsel' (pullbackOverlapQuot f q) := by
  induction q using QuotientGroup.induction_on with
  | H u =>
    rw [twoChartClass_mk, pullbackOverlapQuot_mk, twoChartClass_mk, map_twoChartClassHom]

/-- **The kernel form of the quotient-level square**: a two-chart Čech class dies in `X.CechPic`
after pullback exactly when its pulled-back class does. This is the shape the `ε`-kernel
computation reads, since `twoChartClass` is injective (`twoChartClass_injective`) and so the
`CechPic`-level kernel is computed by the `Ȟ¹`-level one. -/
theorem map_twoChartClass_eq_one_iff (f : X ⟶ Y) (sel : Y → Bool) (hmem : ∀ y, y ∈ V (sel y))
    (hsel : Function.Surjective sel)
    (hsel' : Function.Surjective (fun x ↦ sel (f.base x)))
    (q : Γ(Y, V false ⊓ V true)ˣ ⧸ TruncExpCech.cechCoboundaryUnits
      (Y.resHom (inf_le_left : V false ⊓ V true ≤ V false))
      (Y.resHom (inf_le_right : V false ⊓ V true ≤ V true))) :
    Scheme.CechPic.map f (twoChartClass V sel hmem hsel q) = 1
      ↔ pullbackOverlapQuot f q = 1 := by
  rw [map_twoChartClass f sel hmem hsel hsel' q]
  constructor
  · intro h
    exact (injective_iff_map_eq_one _).mp
      (twoChartClass_injective (fun s ↦ f ⁻¹ᵁ V s) (fun x ↦ sel (f.base x))
        (fun x ↦ hmem (f.base x)) hsel') _ h
  · intro h
    rw [h, map_one]

end Scheme

end AlgebraicGeometry
