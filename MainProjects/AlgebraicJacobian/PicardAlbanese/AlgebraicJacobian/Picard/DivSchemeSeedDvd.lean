/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeed
import AlgebraicJacobian.Picard.DivSchemeRelDivisor
import AlgebraicJacobian.Picard.SlicingFlatKernel

/-!
# DD-4 — the `hdvd` reduction: divisibility from fibre vanishing (links 1+3 assembled)

The divisor-first `hdvd` (`IsGenerator.dvd`, the Nakayama-neighbourhood clause) reduced to
its single honest input — **link 2**, the fibre-vanishing `N ⊗ κ(p) = 0` at every base
point.  Everything else (the germwise closer, the local-ring unit descent) is discharged
here from landed engines:

* `Scheme.mem_span_singleton_of_forall_germ` (`Picard/DivisorStalkIdeal.lean`) reduces the
  global membership on the piece to a germ-level membership at every point;
* at a point `y` the germ lands in the **local ring** stalk `𝒪_y`, so the
  `Picard/DivSchemeRelDivisor.lean` stalk-form consumer
  `mem_span_singleton_map_of_subsingleton_tmul_residueField_localRing` discharges the germ
  from the fibre vanishing at the base point `basePrime (germ_y)` — no structure-map
  geometry, the local ring supplies the unit descent (link 3);
* germ regularity of the equation (the germ closer's `hb`) is the seed's fibre-regularity
  law, supplied as `hreg` (the P-fib nonvanishing route of `isGenerator_of_fibre_ne_zero`).

The submodule `N z = sideColengthSubmodule` is the honest **image of the `K`-side
components** in the colength `Γ(D(h z)) ⧸ (eqn z)`; `hdvd` says it is the zero submodule,
which the Nakayama neighbourhood delivers from `N z ⊗ κ(p) = 0` at every base point.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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

/-- The `R`-linear map sending a global theta section to the class of its side component
in the colength `Γ(D(h z)) ⧸ (eqn z)`. -/
noncomputable def kColengthMap (z : relCurve C R) :
    relThetaSections C R π a →ₗ[R]
      (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}) :=
  (Ideal.Quotient.mkₐ R (Ideal.span {D.eqn z})).toLinearMap.comp
    (relThetaResSide a (D.side z) (D.piece_le z))

/-- **The `K`-side-component submodule `N z`** of the colength: the image of `K` under the
map "side component, then mod `eqn z`".  `hdvd` at `z` is exactly `N z = 0`. -/
noncomputable def sideColengthSubmodule (z : relCurve C R) :
    Submodule R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}) :=
  Submodule.map (D.kColengthMap z) K

set_option synthInstance.maxHeartbeats 400000 in
-- the colength `Γ(D(h z)) ⧸ (eqn z)` is the heavy relCurve section-ring quotient; deriving
-- its `IsNoetherian` module instance re-elaborates that type past the default budget
/-- **Link 1** (`N` finite): the side-component submodule `N z` is a finite `R`-module as
soon as the ambient colength `Γ(D(h z)) ⧸ (eqn z)` is finite over `R` (the
`SupportTubeFinite` output, I-0244) and `R` is Noetherian — a submodule of a finite module
over a Noetherian ring is finite.  Discharges the `hfin` hypothesis of the reduction. -/
theorem sideColengthSubmodule_finite [IsNoetherianRing R] (z : relCurve C R)
    [Module.Finite R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z})] :
    Module.Finite R (D.sideColengthSubmodule z) := by
  haveI : _root_.IsNoetherian R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}) :=
    isNoetherian_of_isNoetherianRing_of_finite R _
  exact Module.Finite.iff_fg.mpr (_root_.IsNoetherian.noetherian (D.sideColengthSubmodule z))

lemma mk_relThetaResSide_mem_sideColengthSubmodule (z : relCurve C R)
    {ψ : relThetaSections C R π a} (hψ : ψ ∈ K) :
    Ideal.Quotient.mk (Ideal.span {D.eqn z})
        (relThetaResSide a (D.side z) (D.piece_le z) ψ) ∈ D.sideColengthSubmodule z :=
  ⟨ψ, hψ, rfl⟩

/-- **The `hdvd` reduction**: the seed satisfies its divisibility clause as soon as, at
every point `y` of every piece `D(h z)`,
* `hreg` — the germ of the equation is a nonzerodivisor (the fibre-regularity law), and
* `hfib` — the fibre `N z ⊗ κ(basePrime germ_y) = 0` vanishes (**link 2**), with `N z`
  finite over `R` (**link 1**, `hfin`).

The germ closer glues the pointwise memberships; each is the stalk-form Nakayama descent. -/
theorem dvd_of_forall_subsingleton_tmul_residueField
    (hreg : ∀ (z : relCurve C R) (y : relCurve C R) (hy : y ∈ D.piece z),
      ((relCurve C R).presheaf.germ (D.piece z) y hy).hom (D.eqn z)
        ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk y))
    (hfin : ∀ z : relCurve C R, Module.Finite R (D.sideColengthSubmodule z))
    (hfib : ∀ (z : relCurve C R) (y : relCurve C R) (hy : y ∈ D.piece z),
      Subsingleton (↥(D.sideColengthSubmodule z) ⊗[R]
        (basePrime (R := R)
          ((relCurve C R).presheaf.germ (D.piece z) y hy).hom).asIdeal.ResidueField)) :
    ∀ (z : relCurve C R) ⦃ψ : relThetaSections C R π a⦄, ψ ∈ K →
      relThetaResSide a (D.side z) (D.piece_le z) ψ ∈ Ideal.span {D.eqn z} := by
  intro z ψ hψ
  refine Scheme.mem_span_singleton_of_forall_germ (fun y hy => hreg z y hy)
    (fun y hy => ?_)
  haveI := hfin z
  exact mem_span_singleton_map_of_subsingleton_tmul_residueField_localRing
    ((relCurve C R).presheaf.germ (D.piece z) y hy).hom (D.sideColengthSubmodule z)
    (hfib z y hy) (D.mk_relThetaResSide_mem_sideColengthSubmodule z hψ)

/-- **The `hdvd` wall, crispest form**: the seed satisfies its divisibility clause given
exactly the two carve-specific fibre facts (plus the landed finiteness and regularity):

* `hflat` — the colength quotient `(Γ(D(h z)) ⧸ (eqn z)) ⧸ N z` is `R`-flat (the carve's
  flat rank-`g` structure, `SlicingFlatKernel`);
* `hfield` — every element of `N z` dies in the residue-field fibre at the base point
  (`x ⊗ₜ 1 = 0`), i.e. the `K`-side components are divisible by the fibre equation `e_p`
  (the `d_p` fibre achiever, `exists_coeffAt_eq_baseDivisorAt`).

Composes the reduction with the flat-cokernel link-2 half
`subsingleton_tmul_residueField_of_flat_quotient`: `hflat` + `hfield` build the honest
module fibre `N z ⊗ κ(p) = 0` at every base point, which the reduction turns into `dvd`.
This is the single remaining wall of the divisor-first `hdvd`, isolated to the carve's own
fibre geometry. -/
theorem dvd_of_flat_quotient_of_field_vanishing [IsNoetherianRing R]
    (hreg : ∀ (z : relCurve C R) (y : relCurve C R) (hy : y ∈ D.piece z),
      ((relCurve C R).presheaf.germ (D.piece z) y hy).hom (D.eqn z)
        ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk y))
    (hfin : ∀ z : relCurve C R, Module.Finite R (D.sideColengthSubmodule z))
    (hflat : ∀ z : relCurve C R,
      Module.Flat R ((Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z})
        ⧸ D.sideColengthSubmodule z))
    (hfield : ∀ (z : relCurve C R) (y : relCurve C R) (hy : y ∈ D.piece z)
        (x : ↥(D.sideColengthSubmodule z)),
        ((x : Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}) ⊗ₜ[R]
            (1 : (basePrime (R := R)
              ((relCurve C R).presheaf.germ (D.piece z) y hy).hom).asIdeal.ResidueField))
          = 0) :
    ∀ (z : relCurve C R) ⦃ψ : relThetaSections C R π a⦄, ψ ∈ K →
      relThetaResSide a (D.side z) (D.piece_le z) ψ ∈ Ideal.span {D.eqn z} :=
  D.dvd_of_forall_subsingleton_tmul_residueField hreg hfin (fun z y hy => by
    haveI := hflat z
    exact _root_.subsingleton_tmul_residueField_of_flat_quotient (D.sideColengthSubmodule z)
      (basePrime (R := R) ((relCurve C R).presheaf.germ (D.piece z) y hy).hom)
      (fun x => hfield z y hy x))

set_option maxHeartbeats 800000 in
-- deriving the colength `IsNoetherian`/`Module.Finite` instances re-elaborates the heavy
-- relCurve section-ring quotient type past the default budget (as in
-- `sideColengthSubmodule_finite`)
set_option synthInstance.maxHeartbeats 400000 in
/-- **The `hdvd` wall, fibre-kernel form** (the sharpened single obligation, replacing the
per-point flat-quotient input of `dvd_of_flat_quotient_of_field_vanishing` by the more
primitive fibrewise-kernel data): the seed satisfies its divisibility clause given

* `hcolFin`/`hcolFlat` — each colength `Γ(D(h z)) ⧸ (eqn z)` is **finite and flat** over
  `R` (the slicing criterion
  `Module.Flat.quotient_span_singleton_of_forall_tmul_residueField` from the seed's
  fibre-regularity + the `SupportTube` finiteness — both landed, per piece);
* `hspan` — **the fibrewise-kernel-spanning law**: at every base prime `p` the fibre
  kernel of the `K`-side-component map `K → Γ(D(h z)) ⧸ (eqn z)` is spanned by the base
  change of its global kernel (the fibrewise carve `divUniversal_carve_residueField`;
  exactly the certificate-clause-(c4) input);
* `hfield` — every `K`-side component dies in the ambient residue-field fibre
  (`x ⊗ₜ 1 = 0`), i.e. is divisible by the fibre equation `e_p` (the `d_p` achiever
  `exists_coeffAt_eq_baseDivisorAt`, transported by `pieceQuotBaseChangeAlg`).

`hspan` (with `K` finite and the colength finite/flat) yields the per-point flatness of
`(Γ(D(h z)) ⧸ (eqn z)) ⧸ N z` through the flattening keystone (c4)
`Module.Flat.quotient_range_of_forall_ker_rTensor_residueField_le` — `N z` is the range of
the `K`-side-component map — and that flatness plus `hfield` is exactly the input of
`dvd_of_flat_quotient_of_field_vanishing`.  This isolates the divisor-first `hdvd` to the
single fibrewise-kernel obligation `hspan`: **no glued↔per-point flatness bridge**, and,
contra the module-fibre "supply `hfib` directly" route, the flatness the `k[ε]` trap
demands (needed to turn `hfield` into `Subsingleton (N z ⊗ κ(p))`) is supplied here by
`hspan` + `hcolFlat`, never by `hfield` alone. -/
theorem dvd_of_fibrewise_ker_span_of_field_vanishing [IsNoetherianRing R]
    [Module.Finite R ↥K]
    (hreg : ∀ (z : relCurve C R) (y : relCurve C R) (hy : y ∈ D.piece z),
      ((relCurve C R).presheaf.germ (D.piece z) y hy).hom (D.eqn z)
        ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk y))
    (hcolFin : ∀ z : relCurve C R,
      Module.Finite R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}))
    (hcolFlat : ∀ z : relCurve C R,
      Module.Flat R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}))
    (hspan : ∀ (z : relCurve C R) (p : PrimeSpectrum R),
      LinearMap.ker (((D.kColengthMap z).comp K.subtype).rTensor p.asIdeal.ResidueField)
        ≤ LinearMap.range
          ((LinearMap.ker ((D.kColengthMap z).comp K.subtype)).subtype.rTensor
            p.asIdeal.ResidueField))
    (hfield : ∀ (z : relCurve C R) (y : relCurve C R) (hy : y ∈ D.piece z)
        (x : ↥(D.sideColengthSubmodule z)),
        ((x : Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}) ⊗ₜ[R]
            (1 : (basePrime (R := R)
              ((relCurve C R).presheaf.germ (D.piece z) y hy).hom).asIdeal.ResidueField))
          = 0) :
    ∀ (z : relCurve C R) ⦃ψ : relThetaSections C R π a⦄, ψ ∈ K →
      relThetaResSide a (D.side z) (D.piece_le z) ψ ∈ Ideal.span {D.eqn z} := by
  refine D.dvd_of_flat_quotient_of_field_vanishing hreg
    (fun z => by haveI := hcolFin z; exact D.sideColengthSubmodule_finite z)
    (fun z => ?_) hfield
  haveI := hcolFin z
  haveI := hcolFlat z
  have hrange : D.sideColengthSubmodule z
      = LinearMap.range ((D.kColengthMap z).comp K.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
  rw [hrange]
  exact Module.Flat.quotient_range_of_forall_ker_rTensor_residueField_le
    ((D.kColengthMap z).comp K.subtype)
    (LinearMap.ker ((D.kColengthMap z).comp K.subtype)) le_rfl (hspan z)

end ThetaGeneratorSeed

end AlgebraicGeometry
