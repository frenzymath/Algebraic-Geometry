/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Std.Tactic.BVDecide.LRAT.Internal.Clause

/-!
# Tangent-space substrate: dual-number points of a scheme at a point (A.3.iii substrate)

Scheme-level substrate for the Kleiman §5 tangent-space theorem
`thm:pic0_tangent_space_iso` (`Picard/Pic0AbelianVariety.lean`,
`Scheme.Pic0.tangentSpaceIso`), bridging Mathlib's
`AlgebraicGeometry.SpecToEquivOfLocalRing` to the local-algebra substrate of
`Picard/TangentSpaceDualNumbers.lean`.

## Main declarations

- `AlgebraicGeometry.isLocalHom_dualNumber_iff` — a ring homomorphism from a
  local ring to the dual numbers `k[ε]` over a field is a *local*
  homomorphism iff its constant component kills the maximal ideal. The
  right-hand side is exactly the side condition
  `∀ x ∈ maximalIdeal R, fst (f x) = 0` used throughout
  `TangentSpaceDualNumbers.lean`.
- `AlgebraicGeometry.specToEquivOfLocalRingAt` — the fiber form of Mathlib's
  `SpecToEquivOfLocalRing`: for a local ring `R` and a *fixed* point `x : X`,
  morphisms `Spec R ⟶ X` sending the closed point to `x` correspond to local
  ring homomorphisms `𝒪_{X,x} ⟶ R`.
- `AlgebraicGeometry.specDualNumberAtEquiv` — the two combined: dual-number
  points of `X` at `x` correspond to ring homomorphisms `𝒪_{X,x} → k[ε]`
  whose constant component kills the maximal ideal.

Combined with `localDualNumberHomEquivCotangentSpaceDual`
(`TangentSpaceDualNumbers.lean`), this identifies the dual-number points of
`X` at a `k`-rational point `x` with the dual of the cotangent space
`m_x/m_x²`, once the `k`-algebra structure on the stalk (from the structure
morphism of a `k`-scheme) is threaded through — the remaining step towards
`thm:pic0_tangent_space_iso`.

Blueprint: `blueprint/src/chapters/Picard_Pic0AbelianVariety.tex`,
§ `sec:pic0_tangent_space` (`lem:tangent_dual_number_local_iff`,
`lem:tangent_spec_local_ring_at`, `cor:tangent_spec_dual_number_at`).
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

section DualNumberLocalHom

open TrivSqZeroExt

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [IsLocalRing R]

/-- A ring homomorphism from a local ring to the dual numbers `k[ε]` over a
field is local iff its constant component kills the maximal ideal. The
right-hand side is the side condition on dual-number points used in
`TangentSpaceDualNumbers.lean`. -/
lemma isLocalHom_dualNumber_iff (f : R →+* DualNumber k) :
    IsLocalHom f ↔ ∀ x ∈ maximalIdeal R, fst (f x) = 0 := by
  constructor
  · intro hf x hx
    by_contra h0
    have hu : IsUnit (f x) := isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h0)
    exact mem_nonunits_iff.mp ((mem_maximalIdeal x).mp hx) (hf.map_nonunit x hu)
  · intro h
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal R := (mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr hna)
    have h0 : fst (f a) = 0 := h a hm
    have := isUnit_iff_isUnit_fst.mp ha
    rw [h0] at this
    exact not_isUnit_zero this

end DualNumberLocalHom

section SpecAtPoint

variable (X : Scheme.{u}) (R : CommRingCat.{u}) [IsLocalRing R]

/-- **Fiber form of `SpecToEquivOfLocalRing`.** For a local ring `R`, a scheme
`X` and a fixed point `x : X`, morphisms `Spec R ⟶ X` sending the closed
point to `x` correspond to local ring homomorphisms `𝒪_{X,x} ⟶ R`. -/
noncomputable def specToEquivOfLocalRingAt (x : X) :
    {f : Spec R ⟶ X // f.base (closedPoint R) = x} ≃
      {φ : X.presheaf.stalk x ⟶ R // IsLocalHom φ.hom} where
  toFun f :=
    ⟨(X.presheaf.stalkCongr (Inseparable.of_eq f.2.symm)).hom ≫
        Scheme.stalkClosedPointTo f.1,
     haveI : IsLocalHom ((X.presheaf.stalkCongr
         (Inseparable.of_eq f.2.symm)).hom).hom := isLocalHom_of_isIso _
     CommRingCat.isLocalHom_comp _ _⟩
  invFun φ :=
    haveI := φ.2
    ⟨Spec.map φ.1 ≫ X.fromSpecStalk x, by
      rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]⟩
  left_inv := by
    rintro ⟨f, rfl⟩
    refine Subtype.ext ?_
    dsimp only
    have hcongr : (X.presheaf.stalkCongr
        (Inseparable.of_eq (rfl : f.base (closedPoint R) = f.base (closedPoint R)).symm)).hom
          = 𝟙 _ := by
      simp [TopCat.Presheaf.stalkCongr]
    rw [hcongr, Category.id_comp]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk f
  right_inv := by
    rintro ⟨φ, hφ⟩
    haveI := hφ
    refine Subtype.ext ?_
    dsimp only
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ ?_
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_assoc,
      Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk]

end SpecAtPoint

section DualNumberPoints

open TrivSqZeroExt

variable {k : Type u} [Field k]

/-- **Dual-number points of a scheme at a point, as stalk data.** For a field
`k`, a scheme `X` and a point `x : X`, morphisms
`Spec k[ε] ⟶ X` sending the closed point to `x` correspond to ring
homomorphisms `𝒪_{X,x} → k[ε]` whose constant component kills the maximal
ideal — the interface consumed by
`localDualNumberHomEquivCotangentSpaceDual`. -/
noncomputable def specDualNumberAtEquiv (X : Scheme.{u}) (x : X) :
    {f : Spec (CommRingCat.of (DualNumber k)) ⟶ X //
        f.base (closedPoint (DualNumber k)) = x} ≃
      {φ : X.presheaf.stalk x ⟶ CommRingCat.of (DualNumber k) //
        ∀ a ∈ maximalIdeal (X.presheaf.stalk x), fst (φ.hom a) = 0} :=
  (specToEquivOfLocalRingAt X (CommRingCat.of (DualNumber k)) x).trans
    (Equiv.subtypeEquivRight fun φ => isLocalHom_dualNumber_iff φ.hom)

end DualNumberPoints

end AlgebraicGeometry
