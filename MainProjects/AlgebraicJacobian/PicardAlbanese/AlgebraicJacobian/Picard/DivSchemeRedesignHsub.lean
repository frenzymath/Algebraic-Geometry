/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignJFlat

/-!
# DD-4 — the carve fibre non-collapse `hsub`, and its equivalence with `hinj`

The sole remaining XL wall of the DD-4 seam is the **carve rank-`g` fibre non-collapse**

`hsub z p : Function.Injective ((D.sideColengthSubmodule z).subtype.rTensor κ(p))`

— at every base prime `p`, the side-component submodule `N z = D.sideColengthSubmodule z`
of the colength `Γ(D(h z)) ⧸ (eqn z)` stays injective in the residue fibre (no fibre
collapse).  `hsub` feeds brick-1's `forall_flat_colength_quotient_of_hsub`
(`Picard/DivSchemeRedesignJFlat.lean`) → `Module.Flat R (colength z ⧸ N z)` → RD-N.

## What this file lands

The **converse** of the landed reduction
`hinj_of_forall_sideColengthSubmodule_subtype_rTensor_injective` (`hsub ⟹ hinj`,
`Picard/DivSchemeUnivFibreHinj.lean`), completing the equivalence

`hsub ⟺ hinj ⟺ hspan`

(the middle equivalence is `liftQ_rTensor_injective_of_ker_rTensor_le` /
`hspan_of_forall_liftQ_rTensor_injective`).

* `ThetaGeneratorSeed.hsub_of_forall_liftQ_rTensor_injective` — **`hinj ⟹ hsub`**: the
  fibre non-collapse `hsub` follows from the induced-map fibre injectivity `hinj`
  (injectivity of the residue fibre of `f̄_z : K ⧸ ker f_z → colength z`).
* `ThetaGeneratorSeed.forall_sideColengthSubmodule_subtype_rTensor_injective_iff` — the
  packaged `hsub ⟺ hinj`.

Because `f̄_z = N z.subtype ∘ ē` corestricts through the equivalence
`ē : K ⧸ ker f_z ≃ₗ N z`, the two fibre-injectivity statements differ only by the (always
injective/surjective) equivalence `ē ⊗ κ(p)`, so `hsub` and `hinj` are interchangeable.
This lets the genuine carve rank-`g` argument target `f̄_z` — the induced map whose image is
the fibre window `divUniversalFibreKM` (corank `g`, `finrank_divUniversalFibreKM_add`,
`Picard/DivSchemeSeedUnivAssembleKappa.lean`) and onto which the reading is an isomorphism
(the pin from `divUniversal_carve_residueField`, `Picard/DivSchemeFamilyUniv.lean`) — and
still discharge `hsub`.

## The anti-circularity ordering (BINDING — recorded for the seam)

`hsub`/`hinj`/`hspan` here are stated for a generic `ThetaGeneratorSeed D`.  Their statements
mention `D.piece z = (relCurve C R).basicOpen (D.h z)` (through `D.kColengthMap z`) and
`D.eqn z = read (D.sec z)`, so **at the concrete redesigned universal seed the piece-level
`hsub` depends on the ann-cutter `D.h z`** (through `piece z`).  Since the redesign's `h z`
(`Picard/DivSchemeRedesignFibreCut.lean`) is produced by RD-N, which consumes brick-1's
`Module.Flat R (colength z ⧸ N z)` (`forall_flat_colength_quotient_of_hsub`), which consumes
`hsub`, the *piece-level* `hsub` at the concrete seed is **circular**.

The non-circular route (independent of `h z`): the universal carve
`divUniversal_carve_residueField` is `h z`-free (it is a law on every residue field of the
pair chart ring), and the RD-N input it must feed is the **chart-level** `J`-flatness
(the base ideal `J = ⟨read ψ : ψ ∈ K⟩` over the whole pinned chart `V = relPinnedChart`,
`le_rfl`, `Γ(V) ⧸ J` flat), which is also `h z`-free.  So the carve wiring of `hsub` must be
performed at the chart level `V` (`le_rfl`), and the piece-level `hsub` proper follows by
localizing to the basic open `D(h z) ⊆ V` *after* `h z` is chosen.  The equivalences of this
file and of `Picard/DivSchemeUnivFibreHinj.lean` are pure linear algebra and hold at either
level; the carve pin (`hinj`) is the residual, and it must be stated at the chart level to be
non-circular.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}
variable {K : Submodule R (relThetaSections C R π a)}

namespace ThetaGeneratorSeed

variable (D : ThetaGeneratorSeed C R π a K)

/-! ## The `hinj ⟹ hsub` converse: `hsub` and `hinj` are equivalent -/

set_option maxHeartbeats 1600000 in
-- the heavy relCurve section-ring colength drives the `rTensor` factorisation defeq past
-- the default budget (matched to `hinj_of_forall_sideColengthSubmodule_subtype_rTensor_injective`)
set_option synthInstance.maxHeartbeats 400000 in
/-- **`hinj ⟹ hsub`**: the carve fibre non-collapse `hsub` — injectivity, at every base
prime `p`, of the residue fibre of the side-component submodule inclusion
`N z = D.sideColengthSubmodule z ↪ colength z` — follows from the induced-map fibre
injectivity `hinj`, the residue-fibre injectivity of the injectivization
`f̄_z = (ker f_z).liftQ f_z : K ⧸ ker f_z → colength z`.

Together with `hinj_of_forall_sideColengthSubmodule_subtype_rTensor_injective` (`hsub ⟹ hinj`)
this shows `hsub` and `hinj` are **equivalent** — either discharges the (c4) flat-cokernel
producer `forall_flat_colength_quotient_of_hsub`.

Proof: `f̄_z` corestricts to a linear equivalence `ē : K ⧸ ker f_z ≃ₗ N z` with
`N z.subtype ∘ ē = f̄_z`, so `f̄_z ⊗ κ(p) = (N z.subtype ⊗ κ(p)) ∘ (ē ⊗ κ(p))` with
`ē ⊗ κ(p)` surjective (an equivalence).  Any `w` with `(N z.subtype ⊗ κ(p)) w = 0` lifts to
`u` with `w = (ē ⊗ κ(p)) u`; then `(f̄_z ⊗ κ(p)) u = (N z.subtype ⊗ κ(p)) w = 0`, so `u = 0`
by `hinj`, whence `w = (ē ⊗ κ(p)) 0 = 0`. -/
theorem hsub_of_forall_liftQ_rTensor_injective
    (hinj : ∀ (z : relCurve C R) (p : PrimeSpectrum R),
      Function.Injective
        (((LinearMap.ker ((D.kColengthMap z).comp K.subtype)).liftQ
            ((D.kColengthMap z).comp K.subtype) le_rfl).rTensor p.asIdeal.ResidueField)) :
    ∀ (z : relCurve C R) (p : PrimeSpectrum R),
      Function.Injective
        ((D.sideColengthSubmodule z).subtype.rTensor p.asIdeal.ResidueField) := by
  intro z p
  set f := (D.kColengthMap z).comp K.subtype with hf
  set fbar := (LinearMap.ker f).liftQ f le_rfl with hfbar
  have hfbar_inj : Function.Injective fbar := by
    rw [← LinearMap.ker_eq_bot, hfbar]
    exact Submodule.ker_liftQ_eq_bot' _ f rfl
  have hrange : LinearMap.range fbar = D.sideColengthSubmodule z := by
    rw [hfbar, Submodule.range_liftQ, hf, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  -- corestrict `fbar` to `N z`; the corestriction `g` is bijective
  set g := fbar.codRestrict (D.sideColengthSubmodule z)
    (fun x => hrange ▸ LinearMap.mem_range_self fbar x) with hg
  have hgcomp : (D.sideColengthSubmodule z).subtype ∘ₗ g = fbar :=
    LinearMap.subtype_comp_codRestrict _ _ _
  have hg_inj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, hg, LinearMap.ker_codRestrict, LinearMap.ker_eq_bot]
    exact hfbar_inj
  have hg_surj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, hg, LinearMap.range_codRestrict, hrange,
      Submodule.comap_subtype_eq_top]
  -- `ē : K ⧸ ker f ≃ₗ N z` (`ebar.toLinearMap` is defeq to `g`)
  set ebar := LinearEquiv.ofBijective g ⟨hg_inj, hg_surj⟩ with hebar
  -- `fbar ⊗ κ = (N z.subtype ⊗ κ) ∘ (g ⊗ κ)`
  have hfactor : fbar.rTensor p.asIdeal.ResidueField
      = (D.sideColengthSubmodule z).subtype.rTensor p.asIdeal.ResidueField ∘ₗ
          g.rTensor p.asIdeal.ResidueField := by
    rw [← LinearMap.rTensor_comp, hgcomp]
  -- `g ⊗ κ` is surjective (an equivalence's `rTensor`)
  have hg_rTensor_surj : Function.Surjective (g.rTensor p.asIdeal.ResidueField) := by
    change Function.Surjective (ebar.toLinearMap.rTensor p.asIdeal.ResidueField)
    rw [← LinearEquiv.coe_rTensor]
    exact (LinearEquiv.rTensor p.asIdeal.ResidueField ebar).surjective
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨u, rfl⟩ := hg_rTensor_surj w
  have hfu : fbar.rTensor p.asIdeal.ResidueField u = 0 := by
    rw [hfactor, LinearMap.comp_apply]; exact hw
  have hu0 : u = 0 :=
    (injective_iff_map_eq_zero (fbar.rTensor p.asIdeal.ResidueField)).mp (hinj z p) u hfu
  rw [hu0, map_zero]

/-- **`hsub ⟺ hinj`**: the carve fibre non-collapse `hsub` (injectivity of the residue
fibre of `N z ↪ colength z`) is equivalent to the induced-map fibre injectivity `hinj`
(injectivity of the residue fibre of `f̄_z : K ⧸ ker f_z → colength z`).  Packages the
landed forward direction
`hinj_of_forall_sideColengthSubmodule_subtype_rTensor_injective` with the converse
`hsub_of_forall_liftQ_rTensor_injective`; either may discharge the flat-cokernel producer. -/
theorem forall_sideColengthSubmodule_subtype_rTensor_injective_iff :
    (∀ (z : relCurve C R) (p : PrimeSpectrum R),
        Function.Injective
          ((D.sideColengthSubmodule z).subtype.rTensor p.asIdeal.ResidueField))
      ↔ ∀ (z : relCurve C R) (p : PrimeSpectrum R),
        Function.Injective
          (((LinearMap.ker ((D.kColengthMap z).comp K.subtype)).liftQ
              ((D.kColengthMap z).comp K.subtype) le_rfl).rTensor p.asIdeal.ResidueField) :=
  ⟨D.hinj_of_forall_sideColengthSubmodule_subtype_rTensor_injective,
    D.hsub_of_forall_liftQ_rTensor_injective⟩

end ThetaGeneratorSeed

end AlgebraicGeometry
