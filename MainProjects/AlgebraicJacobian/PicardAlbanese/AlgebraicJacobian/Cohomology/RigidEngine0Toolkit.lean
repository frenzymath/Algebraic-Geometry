/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.QcohSections
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# RE-0: the `QcohOn ⟹ IsLocalizedModule` bridge

This file is the lattice toolkit's keystone (w4-3 worksheet §2.3): the bridge from the
landed quasi-coherence packaging `AlgebraicGeometry.Scheme.QcohOn` (`QcohSections.lean`,
the (P1) ambient-section action + the two (P2) localization axioms) to mathlib's
`IsLocalizedModule`. It lets any packaged sheaf `F` on the pinned relative cover be read as
the two-lattice pair the rigid engine consumes, with `ι₀`/`ι₁` the chart-to-overlap
restrictions and their `IsLocalizedModule (Submonoid.powers t)` instances produced here.

## Main declarations

* `AlgebraicGeometry.Scheme.QcohOn.moduleOfLE` — the `Γ(X, U)`-module structure on `F`-
  sections over `V ≤ U` induced by the (P1) action `qsmul`. A `def` used only as a *local*
  instance (the bare-`qsmul` packaging deliberately avoids a global `Module Γ(X, U)` tower;
  see the design note in `QcohSections.lean`).
* `AlgebraicGeometry.Scheme.QcohOn.secResₗ` — section restriction promoted to a
  `Γ(X, U)`-linear map for the `moduleOfLE` structures (linearity is the packaging's
  restriction naturality `secRes_qsmul`).
* `AlgebraicGeometry.Scheme.QcohOn.isLocalizedModule_secResₗ` — **the bridge**: on an
  affine open `U` with `[QcohOn F U]`, if `g : Γ(X, U)` acts invertibly on the overlap
  sections `F(U ⊓ D(g))`, then the restriction `F(U) → F(U ⊓ D(g))` is an
  `IsLocalizedModule (Submonoid.powers g)`. The three axioms are the term-for-term images
  of the packaging data (worksheet §2.3): `map_units` from the unit hypothesis, `surj`
  from (P2) denominator clearing, `exists_of_eq` from (P2) defect annihilation.
* `AlgebraicGeometry.Scheme.QcohOn.isLocalizedModule_secResₗ_moduleKSheaf` — the structure-
  sheaf specialization, **unconditional**: `g` is always a unit on `D(g)`, so `map_units`
  is discharged for free. This is `Γ(X, D(g)) = Γ(X, U)_g` in packaging vocabulary, the
  instance the 𝒪-section lattices of the pair consume directly.

## Consumption

The abstract bridge is the deliverable the cbc lane and the sheaf-assembly brick (RE-4)
share for any packaged-sheaf computation on the pinned cover: RE-4 feeds it a glued twisted
sheaf `F` with `[QcohOn F Vᵢᴿ]`, taking `t := t₀` (the pulled-back chart coordinate, a unit
on the overlap `= basicOpen t₀ᴿ`) to obtain the pair's `ι₀`/`ι₁` localization instances.
The unit hypothesis of the abstract form is exactly the pair's "`t` acts invertibly on `N`"
datum; for the structure sheaf it needs no supplier.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.QcohOn

open Scheme.QcohOn

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {U : X.Opens}
variable {F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k)}
  [Scheme.QcohOn F U]

/-- The `Γ(X, U)`-module structure on `F`-sections over `V ≤ U` coming from the `qsmul`
action of the ambient section ring (the (P1) mixin). A `def`, used as a *local* instance
only: making it a global instance would pollute every `F`-section type with a second module
tower (over `Γ(X, U)`, alongside the coefficient ring `k`), defeating keyed rewriting —
exactly the diamond the bare-`qsmul` packaging was designed to avoid. -/
@[reducible]
noncomputable def moduleOfLE {V : X.Opens} (hVU : V ≤ U) :
    Module Γ(X, U) (F.obj.obj (op V)) where
  smul r m := qsmul hVU r m
  one_smul := one_qsmul hVU
  mul_smul := mul_qsmul hVU
  smul_zero := qsmul_zero hVU
  smul_add := qsmul_add hVU
  add_smul := add_qsmul hVU
  zero_smul m := by
    have h : qsmul hVU (0 : Γ(X, U)) m + qsmul hVU 0 m = qsmul hVU 0 m + 0 := by
      rw [add_zero, ← add_qsmul, add_zero]
    exact add_left_cancel h

/-- Section restriction `F(W) → F(V)` (`hVW : V ≤ W`) promoted to a `Γ(X, U)`-linear map
for the `moduleOfLE` structures; `Γ(X, U)`-linearity is the packaging's restriction
naturality `secRes_qsmul`. -/
noncomputable def secResₗ {V W : X.Opens} (hVW : V ≤ W) (hWU : W ≤ U) :
    letI := moduleOfLE (F := F) hWU
    letI := moduleOfLE (F := F) (hVW.trans hWU)
    F.obj.obj (op W) →ₗ[Γ(X, U)] F.obj.obj (op V) :=
  letI := moduleOfLE (F := F) hWU
  letI := moduleOfLE (F := F) (hVW.trans hWU)
  { toFun := secRes F hVW
    map_add' := (secRes F hVW).map_add
    map_smul' := fun r m => secRes_qsmul hVW hWU r m }

/-- **RE-0 bridge (abstract form).** Let `U` be an affine open of a scheme `X`, let `F`
carry the quasi-coherence packaging `QcohOn F U`, and let `g : Γ(X, U)`. If `g` acts
invertibly on the sections `F(U ⊓ D(g))` (for the `Γ(X, U)`-action of the packaging — the
"`t` acts invertibly on `N`" datum of the two-lattice pair, discharged for the structure
sheaf by `g` being a unit on `D(g)`), then the restriction `F(U) → F(U ⊓ D(g))` exhibits
`F(U ⊓ D(g))` as the localization of `F(U)` at the powers of `g`, i.e. it is an
`IsLocalizedModule (Submonoid.powers g)`.

The three `IsLocalizedModule` axioms are the term-for-term images of the packaging data
(worksheet §2.3): `map_units` from the unit hypothesis (powers of a unit are units),
`surj` from (P2) denominator clearing `exists_secRes_eq_qsmul_pow`, and `exists_of_eq`
from (P2) defect annihilation `exists_qsmul_pow_eq_zero`. -/
theorem isLocalizedModule_secResₗ (hU : IsAffineOpen U) (g : Γ(X, U))
    (hg : letI := moduleOfLE (F := F) (inf_le_left : U ⊓ X.basicOpen g ≤ U)
      IsUnit (algebraMap Γ(X, U)
        (Module.End Γ(X, U) (F.obj.obj (op (U ⊓ X.basicOpen g)))) g)) :
    letI := moduleOfLE (F := F) (le_refl U)
    letI := moduleOfLE (F := F) (inf_le_left : U ⊓ X.basicOpen g ≤ U)
    IsLocalizedModule (Submonoid.powers g)
      (secResₗ (F := F) (inf_le_left : U ⊓ X.basicOpen g ≤ U) (le_refl U)) := by
  letI iU := moduleOfLE (F := F) (le_refl U)
  letI iW := moduleOfLE (F := F) (inf_le_left : U ⊓ X.basicOpen g ≤ U)
  refine ⟨?_, ?_, ?_⟩
  · -- `map_units`: powers of the unit `g` are units.
    rintro ⟨_, n, rfl⟩
    change IsUnit (algebraMap Γ(X, U) _ (g ^ n))
    rw [map_pow]
    exact hg.pow n
  · -- `surj`: (P2) denominator clearing.
    intro y
    obtain ⟨N, e, he⟩ := exists_secRes_eq_qsmul_pow (F := F) hU (le_refl U) g y
    exact ⟨⟨e, ⟨g ^ N, N, rfl⟩⟩, he.symm⟩
  · -- `exists_of_eq`: (P2) defect annihilation.
    intro x₁ x₂ he
    have he' : secRes F (inf_le_left : U ⊓ X.basicOpen g ≤ U) x₁ =
        secRes F (inf_le_left : U ⊓ X.basicOpen g ≤ U) x₂ := he
    have h0 : secRes F (inf_le_left : U ⊓ X.basicOpen g ≤ U) (x₁ - x₂) = 0 := by
      rw [map_sub, he', sub_self]
    obtain ⟨M, hM⟩ := exists_qsmul_pow_eq_zero (F := F) hU (le_refl U) g (x₁ - x₂) h0
    refine ⟨⟨g ^ M, M, rfl⟩, ?_⟩
    rw [qsmul_sub] at hM
    exact sub_eq_zero.mp hM

/-- **RE-0 bridge, structure-sheaf specialization (unconditional).** For the structure
sheaf `X.moduleKSheaf k` on an affine open `U` and any `g : Γ(X, U)`, the restriction
`Γ(X, U) → Γ(X, U ⊓ D(g))` exhibits the target as the localization of `Γ(X, U)` at the
powers of `g`. The `map_units` hypothesis of `isLocalizedModule_secResₗ` is discharged for
free: `g` restricts to a *unit* on `D(g) ≥ U ⊓ D(g)` (`RingedSpace.isUnit_res_basicOpen`),
so its `Γ(X, U)`-action (multiplication by `resHom g`) is invertible.

This recovers, in the packaging vocabulary, the classical fact `Γ(X, D(g)) = Γ(X, U)_g`,
and is the instance the 𝒪-section lattices `M₀ = Γ(V₀)`, `N = Γ(overlap)` of the two-
lattice pair consume directly (worksheet §2.3). -/
theorem isLocalizedModule_secResₗ_moduleKSheaf [X.Over (Spec (.of k))] (hU : IsAffineOpen U)
    (g : Γ(X, U)) :
    letI := moduleOfLE (F := X.moduleKSheaf k) (le_refl U)
    letI := moduleOfLE (F := X.moduleKSheaf k) (inf_le_left : U ⊓ X.basicOpen g ≤ U)
    IsLocalizedModule (Submonoid.powers g)
      (secResₗ (F := X.moduleKSheaf k) (inf_le_left : U ⊓ X.basicOpen g ≤ U) (le_refl U)) := by
  letI iW := moduleOfLE (F := X.moduleKSheaf k) (inf_le_left : U ⊓ X.basicOpen g ≤ U)
  apply isLocalizedModule_secResₗ hU g
  -- `map_units` for `g`: `g` is a unit on `U ⊓ D(g)`.
  have hu : IsUnit (X.resHom (inf_le_left : U ⊓ X.basicOpen g ≤ U) g) := by
    have h1 : IsUnit (X.resHom (X.basicOpen_le g) g) :=
      X.toRingedSpace.isUnit_res_basicOpen g
    have h2 : X.resHom (inf_le_left : U ⊓ X.basicOpen g ≤ U) g =
        X.resHom (inf_le_right : U ⊓ X.basicOpen g ≤ X.basicOpen g)
          (X.resHom (X.basicOpen_le g) g) := by
      rw [resHom_resHom]
    rw [h2]
    exact (X.resHom (inf_le_right : U ⊓ X.basicOpen g ≤ X.basicOpen g)).isUnit_map h1
  have hE : ⇑(algebraMap Γ(X, U)
        (Module.End Γ(X, U) ((X.moduleKSheaf k).obj.obj (op (U ⊓ X.basicOpen g)))) g) =
      fun m : Γ(X, U ⊓ X.basicOpen g) ↦ X.resHom (inf_le_left : U ⊓ X.basicOpen g ≤ U) g * m := by
    funext m
    rw [Module.algebraMap_end_apply]
    exact Scheme.moduleKSheaf_qsmul_eq _ g m
  rw [Module.End.isUnit_iff, hE]
  change Function.Bijective
    fun m : Γ(X, U ⊓ X.basicOpen g) ↦ X.resHom (inf_le_left : U ⊓ X.basicOpen g ≤ U) g * m
  obtain ⟨v, hv⟩ := hu
  rw [← hv]
  refine Function.bijective_iff_has_inverse.mpr ⟨fun m ↦ ↑v⁻¹ * m, ?_, ?_⟩
  · exact fun m ↦ Units.inv_mul_cancel_left v m
  · exact fun m ↦ Units.mul_inv_cancel_left v m

end Scheme.QcohOn

end AlgebraicGeometry
