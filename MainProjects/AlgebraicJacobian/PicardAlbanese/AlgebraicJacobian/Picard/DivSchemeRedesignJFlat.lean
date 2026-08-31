/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeUnivFibreHinj

/-!
# DD-4 redesign, brick 1 — the `R_Z`-flatness of the reading-map cokernel (`J`-flat)

The XL foundational flatness of the DD-4 seed redesign (`informal/spec-dd4-redesign.md`
§1.4 / §3 row 1; landing note I-0289).  Everything downstream — the relative-local-BPF
stalk Nakayama `RD-N` (§1.3, brick 3) and the non-circular certificate (brick 6) — rides on

`Module.Flat R_Z (colength z ⧸ N z)`,

the certificate-clause-(c4) cokernel of the `K`-side-component **reading map**
`f_z = kColengthMap z ∘ K.subtype : ↥K → colength z`, where
`colength z = Γ(D(h z)) ⧸ (eqn z)` and `N z = sideColengthSubmodule z = range f_z` is the
piece image of the base ideal `J = ⟨read ψ : ψ ∈ K⟩`.  Since `eqn z = read (sec z) ∈ J`,
`colength z ⧸ N z ≅ Γ(D(h z)) ⧸ J·Γ(D(h z))` — this **is** the piecewise `Γ/J`-flatness of
the spec's §1.4 (from which `J` itself is `R_Z`-flat as `ker(Γ ↠ Γ/J)` with `Γ` flat).

## What this file lands

The flat conclusion is exposed as a **standalone reusable keystone**, reduced along the
landed chain to the single genuine carve input.  It rides on the G-4 flattening keystone

* `Module.Flat.quotient_range_of_forall_ker_rTensor_residueField_le` (c4,
  `Picard/SlicingFlatKernel.lean:296`, I-0240): for `f : M → N` (`M` finite, `N` finite
  flat) and `L ≤ ker f` with `hspan : ∀ p, ker (f ⊗ κ(p)) ≤ range (L.subtype ⊗ κ(p))`,
  the cokernel `N ⧸ range f` is flat — the `k[ε]`-trap ruled out by the fibrewise spanning.

fed at `L = ker f_z` through the **landed** reductions

* `hspan_of_forall_liftQ_rTensor_injective` (I-0282, `DivSchemeUnivFibreKerSpan.lean:190`):
  `hinj ⟹ hspan`;
* `hinj_of_forall_sideColengthSubmodule_subtype_rTensor_injective` (I-0286,
  `DivSchemeUnivFibreHinj.lean:129`): `hsub ⟹ hinj`.

* `flat_colength_quotient_of_hspan` — single-point c4 cokernel flatness from the fibrewise
  spanning `hspan`;
* `forall_flat_colength_quotient_of_hspan` — the `∀ z` package (the exact `hflat` shape
  `RD-N` / the certificate consume), from `hspan` + the landed `hcolFin`/`hcolFlat`;
* `forall_flat_colength_quotient_of_hsub` — the same, reduced all the way to the **cleanest
  carve statement** `hsub` (the fibre non-collapse `N z ⊗ κ(p) ↪ colength z ⊗ κ(p)`, the
  rank-`g` pinning delivered by `divUniversal_carve_residueField`).

Unlike the false-at-`seedUniv` `FibreInjective` route (`flat_colength_quotient`,
`DivSchemeUnivFibreKerInj.lean` — `f_z ⊗ κ(p)` is *never* injective, it always kills the
seed section), the `hspan`/`hsub` route divides the kernel out first, so its fibre input is
the genuine carve rank-`g` content, never contradicted by the seed section.

## The precisely-scoped residual (the honest XL wall — NOT in this file)

The carve input `hsub`/`hspan` at the concrete redesigned universal seed is the genuine
size-XL content: wiring `divUniversal_carve_residueField` (`DivSchemeFamilyUniv.lean:135`,
`carvePairArrow = 0` fibrewise) — transported by `ker_baseChange_mkQ`
(`DivCarveKit.lean:91`), the fibre-window span law `divUniversalFibreKM_eq_span`
(`DivSchemeSeedUnivRes.lean:376`) and the corank-`g` count `finrank_divUniversalFibreKM_add`
(`DivSchemeSeedUnivAssembleKappa.lean:207`) — to the seed's colength side-reading `f_z`.
That needs the section→functionField germ bridge (`relThetaResSide` on `D(h')` ↔
`thetaFieldRead`) identifying the piece colength fibre with the fibre-window reading (I-0286
residual), which in turn depends on the redesigned `(sec z, h z)` (bricks 2–4).  This file
takes `hsub`/`hspan` as hypotheses so the flat conclusion is non-circular and stable under
that redesign; the carve wiring instantiates them downstream.
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

set_option maxHeartbeats 800000 in
-- the colength `Γ(D(h z)) ⧸ (eqn z)` is the heavy relCurve section-ring quotient; deriving
-- the module instances for its quotient by `N z` re-elaborates that type past the default
-- budget (as in `sideColengthSubmodule_finite` / `flat_colength_quotient`)
set_option synthInstance.maxHeartbeats 400000 in
/-- **Brick 1, single point — the (c4) cokernel flatness from the fibrewise spanning**:
the per-point colength quotient `(Γ(D(h z)) ⧸ (eqn z)) ⧸ N z` is `R`-flat as soon as the
fibrewise-kernel-spanning law `hspan` holds at `z` (plus `K` finite and the colength
finite/flat over `R`).  `N z = sideColengthSubmodule z = range (kColengthMap z ∘ K.subtype)`
is the range of the `K`-side-component reading map, so this is exactly the (c4) keystone
`Module.Flat.quotient_range_of_forall_ker_rTensor_residueField_le` at `L = ker f_z`
(`hle = le_rfl`) — the direct `hflat` producer of the DD-4 capstone
`dvd_of_flat_quotient_of_field_vanishing`, on the *sound* fibrewise-spanning route (never the
false `FibreInjective`). -/
theorem flat_colength_quotient_of_hspan (z : relCurve C R) [Module.Finite R ↥K]
    [Module.Finite R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z})]
    [Module.Flat R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z})]
    (hspan : ∀ p : PrimeSpectrum R,
      LinearMap.ker (((D.kColengthMap z).comp K.subtype).rTensor p.asIdeal.ResidueField)
        ≤ LinearMap.range
          ((LinearMap.ker ((D.kColengthMap z).comp K.subtype)).subtype.rTensor
            p.asIdeal.ResidueField)) :
    Module.Flat R ((Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z})
      ⧸ D.sideColengthSubmodule z) := by
  have hrange : D.sideColengthSubmodule z
      = LinearMap.range ((D.kColengthMap z).comp K.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
  rw [hrange]
  exact Module.Flat.quotient_range_of_forall_ker_rTensor_residueField_le
    ((D.kColengthMap z).comp K.subtype)
    (LinearMap.ker ((D.kColengthMap z).comp K.subtype)) le_rfl hspan

set_option maxHeartbeats 800000 in
-- deriving the colength `Module.Finite`/quotient instances re-elaborates the heavy relCurve
-- section-ring quotient type past the default budget (as in `forall_flat_colength_quotient`)
set_option synthInstance.maxHeartbeats 400000 in
/-- **Brick 1, `∀ z` package — the `hflat` argument from the fibrewise spanning `hspan`**:
from the landed per-piece colength finiteness/flatness (`hcolFin`/`hcolFlat`) and the
fibrewise-kernel-spanning law `hspan` at every point, produces
`∀ z, Module.Flat R ((Γ(D(h z)) ⧸ (eqn z)) ⧸ N z)` — the exact `hflat` argument of
`dvd_of_flat_quotient_of_field_vanishing` and the flat prerequisite (iii) of `RD-N`. -/
theorem forall_flat_colength_quotient_of_hspan [Module.Finite R ↥K]
    (hcolFin : ∀ z : relCurve C R,
      Module.Finite R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}))
    (hcolFlat : ∀ z : relCurve C R,
      Module.Flat R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}))
    (hspan : ∀ (z : relCurve C R) (p : PrimeSpectrum R),
      LinearMap.ker (((D.kColengthMap z).comp K.subtype).rTensor p.asIdeal.ResidueField)
        ≤ LinearMap.range
          ((LinearMap.ker ((D.kColengthMap z).comp K.subtype)).subtype.rTensor
            p.asIdeal.ResidueField)) :
    ∀ z : relCurve C R,
      Module.Flat R ((Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z})
        ⧸ D.sideColengthSubmodule z) := fun z => by
  haveI := hcolFin z
  haveI := hcolFlat z
  exact D.flat_colength_quotient_of_hspan z (hspan z)

/-- **Brick 1, `∀ z` package from the cleanest carve statement `hsub`**: the same
`hflat` conclusion, reduced all the way to the fibre non-collapse of the side-component
inclusion — at every base prime `p`, `N z ⊗ κ(p) ↪ colength z ⊗ κ(p)` is injective.  This
is the rank-`g` pinning delivered by `divUniversal_carve_residueField`: no fibre of the
`K`-side-component submodule `N z` collapses.  Composes the landed reductions
`hsub ⟹ hinj` (`hinj_of_forall_sideColengthSubmodule_subtype_rTensor_injective`) and
`hinj ⟹ hspan` (`hspan_of_forall_liftQ_rTensor_injective`) with the (c4) keystone; it is the
brick-1 flat producer downstream `RD-N` / the certificate consume, parameterized by the one
honest carve obligation. -/
theorem forall_flat_colength_quotient_of_hsub [Module.Finite R ↥K]
    (hcolFin : ∀ z : relCurve C R,
      Module.Finite R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}))
    (hcolFlat : ∀ z : relCurve C R,
      Module.Flat R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}))
    (hsub : ∀ (z : relCurve C R) (p : PrimeSpectrum R),
      Function.Injective
        ((D.sideColengthSubmodule z).subtype.rTensor p.asIdeal.ResidueField)) :
    ∀ z : relCurve C R,
      Module.Flat R ((Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z})
        ⧸ D.sideColengthSubmodule z) :=
  D.forall_flat_colength_quotient_of_hspan hcolFin hcolFlat
    (D.hspan_of_forall_liftQ_rTensor_injective
      (D.hinj_of_forall_sideColengthSubmodule_subtype_rTensor_injective hsub))

end ThetaGeneratorSeed

end AlgebraicGeometry
