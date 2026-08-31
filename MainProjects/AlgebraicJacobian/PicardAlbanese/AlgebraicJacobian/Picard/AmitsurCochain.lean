/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EtaleSeparatedness
import AlgebraicJacobian.Descent.UnitDescent

/-!
# The Amitsur toolkit for étale separatedness (sub-brick ζ2·P)

This file collects the three reusable groups of lemmas consumed by the coherent-witness
step (ζ2·i) of the (C1) étale-separatedness assembly
(`informal/c1-etale-separatedness-assembly.md`, section "ζ2 … global-unit correction
route"). All three revolve around units and the "only global units cross the projection
`p`" insight.

## (P1) Global gluing of coboundary-trivial unit families

`AlgebraicGeometry.Scheme.exists_global_unit_of_compatible`: a unit `0`-cochain
`β : ∀ x, Γ(X, 𝒰.opens x)ˣ` on a pointed cover whose members agree on overlaps glues to a
single global unit `w : Γ(X, ⊤)ˣ` restricting to each `β x`. This is the `𝒪ˣ`-sheaf gluing
of `Scheme.exists_unitsRestrict_eq` specialized to the tautological cover `V = ⊤`,
`W = 𝒰.opens` (which covers `⊤` because `x ∈ 𝒰.opens x`). The separation companion
`global_unit_ext` is the matching uniqueness statement.

## (P2a) The three cofaces on the triple tensor

Extending ζ1's `tensorInl`/`tensorInr` idiom, `AlgebraicGeometry.tensorFace₁₂`,
`tensorFace₁₃`, `tensorFace₂₃ : B ⊗[A] B →ₐ[k] B ⊗[A] (B ⊗[A] B)` are the `k`-restrictions
of the `A`-linear cofaces `Module.descentFace₁₂/₁₃/₂₃` of
`AlgebraicJacobian.Descent.UnitDescent`. The three simplicial coincidence lemmas record
that the six composites `faceᵢⱼ ∘ inl/inr : B →ₐ[k] B ⊗[A] (B ⊗[A] B)` collapse onto the
three "insert-in-position" maps `x ↦ x⊗1⊗1`, `x ↦ 1⊗x⊗1`, `x ↦ 1⊗1⊗x`.

## (P2b) Global-units descent along the projection at `⊤`

`AlgebraicGeometry.Over.unitsSndTopEquiv`: the ε1 descent equivalence `unitsSndEquiv`
specialized to `V = ⊤` (both `Spec R` sides being affine), giving
`Γ((overSpec k R).left, ⊤)ˣ ≃* Γ((C ⊗ overSpec k R).left, ⊤)ˣ`, whose forward map is
pullback of global units along the second projection (`unitsSndTopEquiv_apply`, phrased via
`Units.map … appTop`). The surjectivity/injectivity faces `appTop_units_surjective`,
`appTop_units_injective` and the naturality `unitsSndTopEquiv_naturality` along
`overSpecMap φ` (`φ : R →ₐ[k] R'`) are what let ζ2·i descend global units and compare them
across `R₂ → R₃`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## (P1) Global gluing of coboundary-trivial unit families -/

namespace Scheme

variable {X : Scheme.{u}}

/-- **Global gluing of a compatible unit family (P1).** A unit `0`-cochain `β` on a pointed
cover `𝒰` whose members agree on pairwise overlaps glues to a single global unit
`w : Γ(X, ⊤)ˣ` restricting to each `β x`. This is `Scheme.exists_unitsRestrict_eq` at the
tautological cover `V = ⊤`, `W = 𝒰.opens`, which covers `⊤` since `x ∈ 𝒰.opens x`. -/
theorem exists_global_unit_of_compatible {𝒰 : X.PointedCover}
    (β : ∀ x, Γ(X, 𝒰.opens x)ˣ)
    (hβ : ∀ x y, X.unitsRestrict (inf_le_left : 𝒰.opens x ⊓ 𝒰.opens y ≤ 𝒰.opens x) (β x)
        = X.unitsRestrict inf_le_right (β y)) :
    ∃ w : Γ(X, ⊤)ˣ, ∀ x, X.unitsRestrict le_top w = β x :=
  exists_unitsRestrict_eq (V := ⊤) (W := 𝒰.opens) (fun _ ↦ le_top)
    (fun w _ ↦ Opens.mem_iSup.mpr ⟨w, 𝒰.mem_opens w⟩) β hβ

/-- **Separation companion of (P1).** Two global units agreeing on every member of a
pointed cover are equal — the `V = ⊤` case of `Scheme.unitsRestrict_eq_of_locally_eq`. -/
theorem global_unit_ext {𝒰 : X.PointedCover} (w w' : Γ(X, ⊤)ˣ)
    (h : ∀ x : X, X.unitsRestrict (le_top : 𝒰.opens x ≤ ⊤) w
        = X.unitsRestrict le_top w') : w = w' :=
  unitsRestrict_eq_of_locally_eq (W := 𝒰.opens) (fun _ ↦ le_top)
    (fun w _ ↦ Opens.mem_iSup.mpr ⟨w, 𝒰.mem_opens w⟩) w w' h

/-! ## A `⊤`-restriction lemma for `unitsAppLE`. -/

/-- On the top open, `unitsAppLE` is `Units.map` of the top-section pullback `appTop`: both
sides act as `f.appTop` on unit sections. Used to phrase the `⊤`-descent equivalence of
(P2b) through the `appTop`-map the consumer expects. -/
lemma Hom.unitsAppLE_top {Y : Scheme.{u}} (f : X ⟶ Y) (u : Γ(Y, ⊤)ˣ) :
    f.unitsAppLE ⊤ (f ⁻¹ᵁ ⊤) le_rfl u = Units.map f.appTop.hom.toMonoidHom u := by
  apply Units.ext
  simp only [Scheme.Hom.coe_unitsAppLE, Units.coe_map]
  rw [Scheme.Hom.appLE_eq_app]
  rfl

end Scheme

/-! ## (P2a) The three cofaces on the triple tensor -/

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

/-- The coface `B ⊗[A] B →ₐ[k] B ⊗[A] (B ⊗[A] B)` hitting tensor positions `1, 2`,
`x ⊗ y ↦ x ⊗ (y ⊗ 1)` — the `k`-restriction of the `A`-linear `Module.descentFace₁₂`. -/
noncomputable abbrev tensorFace₁₂ : B ⊗[A] B →ₐ[k] B ⊗[A] (B ⊗[A] B) :=
  (Module.descentFace₁₂ A B).restrictScalars k

/-- The coface `B ⊗[A] B →ₐ[k] B ⊗[A] (B ⊗[A] B)` hitting tensor positions `1, 3`,
`x ⊗ y ↦ x ⊗ (1 ⊗ y)` — the `k`-restriction of the `A`-linear `Module.descentFace₁₃`. -/
noncomputable abbrev tensorFace₁₃ : B ⊗[A] B →ₐ[k] B ⊗[A] (B ⊗[A] B) :=
  (Module.descentFace₁₃ A B).restrictScalars k

/-- The coface `B ⊗[A] B →ₐ[k] B ⊗[A] (B ⊗[A] B)` hitting tensor positions `2, 3`,
`w ↦ 1 ⊗ w` — the `k`-restriction of the `A`-linear `Module.descentFace₂₃`. -/
noncomputable abbrev tensorFace₂₃ : B ⊗[A] B →ₐ[k] B ⊗[A] (B ⊗[A] B) :=
  (Module.descentFace₂₃ A B).restrictScalars k

/-- **Simplicial identity, position `1`.** Both `tensorFace₁₂ ∘ tensorInl` and
`tensorFace₁₃ ∘ tensorInl` are the insertion `x ↦ x ⊗ (1 ⊗ 1)`. -/
lemma tensorFace₁₂_comp_tensorInl :
    (tensorFace₁₂ (k := k) (A := A) (B := B)).comp tensorInl
      = (tensorFace₁₃ (k := k) (A := A) (B := B)).comp (tensorInl (A := A) (B := B)) := by
  ext b; rfl

/-- **Simplicial identity, position `2`.** Both `tensorFace₁₂ ∘ tensorInr` and
`tensorFace₂₃ ∘ tensorInl` are the insertion `x ↦ 1 ⊗ (x ⊗ 1)`. -/
lemma tensorFace₁₂_comp_tensorInr :
    (tensorFace₁₂ (k := k) (A := A) (B := B)).comp tensorInr
      = (tensorFace₂₃ (k := k) (A := A) (B := B)).comp (tensorInl (A := A) (B := B)) := by
  ext b; rfl

/-- **Simplicial identity, position `3`.** Both `tensorFace₁₃ ∘ tensorInr` and
`tensorFace₂₃ ∘ tensorInr` are the insertion `x ↦ 1 ⊗ (1 ⊗ x)`. -/
lemma tensorFace₁₃_comp_tensorInr :
    (tensorFace₁₃ (k := k) (A := A) (B := B)).comp tensorInr
      = (tensorFace₂₃ (k := k) (A := A) (B := B)).comp (tensorInr (A := A) (B := B)) := by
  ext b; rfl

/-! ## (P2b) Global-units descent along the projection at `⊤` -/

namespace Over

variable (C : Over (Spec (.of k)))
  [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

/-- **The `⊤`-descent equivalence for global units (P2b).** Specializing the projection
descent `unitsSndEquiv` to `V = ⊤` (both `Spec R` sides affine), pullback of global units
along the second projection is a group isomorphism
`Γ((overSpec k R).left, ⊤)ˣ ≃* Γ((C ⊗ overSpec k R).left, ⊤)ˣ`. The codomain open
`(snd …).left ⁻¹ᵁ ⊤` is `⊤` on the nose (`Scheme.Hom.preimage_top`). -/
noncomputable def unitsSndTopEquiv (R : Type u) [CommRing R] [Algebra k R] :
    Γ((overSpec k R).left, ⊤)ˣ ≃* Γ((C ⊗ overSpec k R).left, ⊤)ˣ :=
  unitsSndEquiv C (overSpec k R) (isAffineOpen_top_overSpec k R)

/-- The forward map of `unitsSndTopEquiv` is pullback of global units along the second
projection, `Units.map … appTop` — the form ζ2·i consumes. -/
@[simp]
lemma unitsSndTopEquiv_apply (R : Type u) [CommRing R] [Algebra k R]
    (v : Γ((overSpec k R).left, ⊤)ˣ) :
    unitsSndTopEquiv C R v
      = Units.map (snd C (overSpec k R)).left.appTop.hom.toMonoidHom v := by
  rw [← Scheme.Hom.unitsAppLE_top]
  exact unitsSndEquiv_apply C (overSpec k R) (isAffineOpen_top_overSpec k R) v

/-- **Surjectivity of global-unit pullback (P2b).** Every global unit on the product
descends to a global unit on the base. -/
theorem appTop_units_surjective (R : Type u) [CommRing R] [Algebra k R]
    (w : Γ((C ⊗ overSpec k R).left, ⊤)ˣ) :
    ∃ χ : Γ((overSpec k R).left, ⊤)ˣ,
      Units.map (snd C (overSpec k R)).left.appTop.hom.toMonoidHom χ = w :=
  ⟨(unitsSndTopEquiv C R).symm w, by
    rw [← unitsSndTopEquiv_apply, MulEquiv.apply_symm_apply]⟩

/-- **Injectivity of global-unit pullback (P2b).** Global units are separated by the
projection `p`, so `p^#` is injective on global units. -/
theorem appTop_units_injective (R : Type u) [CommRing R] [Algebra k R] :
    Function.Injective
      (Units.map (snd C (overSpec k R)).left.appTop.hom.toMonoidHom) := by
  intro a b hab
  refine (unitsSndTopEquiv C R).injective ?_
  rw [unitsSndTopEquiv_apply, unitsSndTopEquiv_apply, hab]

/-- **Naturality of the `⊤`-descent along `overSpecMap φ` (P2b).** For a `k`-algebra map
`φ : R →ₐ[k] R'`, descending a global unit on `overSpec k R` and pulling it back along
`C ◁ overSpecMap φ` equals first pulling back along `overSpecMap φ` and then descending —
the square that lets ζ2·i compare descended units across `R₂ → R₃`. It rests on the base
square `snd_left_naturality`. -/
theorem unitsSndTopEquiv_naturality {R R' : Type u} [CommRing R] [Algebra k R]
    [CommRing R'] [Algebra k R'] (φ : R →ₐ[k] R') (χ : Γ((overSpec k R).left, ⊤)ˣ) :
    unitsSndTopEquiv C R'
        (Units.map (overSpecMap φ).left.appTop.hom.toMonoidHom χ)
      = Units.map (C ◁ overSpecMap φ).left.appTop.hom.toMonoidHom
          (unitsSndTopEquiv C R χ) := by
  rw [← Scheme.Hom.unitsAppLE_top, ← Scheme.Hom.unitsAppLE_top]
  -- All the opens of `unitsSndEquiv_naturality` at `V = ⊤` are `⊤` on the nose
  -- (`Scheme.Hom.preimage_top` is `rfl`), so ε1's naturality closes the goal by defeq.
  exact unitsSndEquiv_naturality C (overSpecMap φ)
    (isAffineOpen_top_overSpec k R) (isAffineOpen_top_overSpec k R') χ

end Over

end AlgebraicGeometry
