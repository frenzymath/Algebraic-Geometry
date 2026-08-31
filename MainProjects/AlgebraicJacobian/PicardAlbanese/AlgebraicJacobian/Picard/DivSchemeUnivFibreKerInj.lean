/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedDvd

/-!
# DD-4 — the carve fibre-injective lift `ψ_z` and per-point colength flatness

The remaining seed-close wall of the divisor-first `hdvd`, in its **fibre-injective**
form (I-0278 FINDING 1, the "cleanest route to `hdvd`, skipping `hspan`").  For the seed
`K`-side-component map

`f_z := (kColengthMap z) ∘ K.subtype : ↥K → colength z`, with
`colength z = Γ(D(h z)) ⧸ (eqn z)` and `N z = sideColengthSubmodule z = range f_z`,

the carve supplies a **fibre-injective lift `ψ_z`**: at every base prime `p` the fibre map
`f_z ⊗ κ(p)` is injective — the `K`-side components (the `H⁰(N − d_p)` fibre windows) inject
into the fibre colength.  That is exactly the hypothesis consumed by the landed engine

* `Module.Flat.quotient_range_of_forall_rTensor_residueField_injective`
  (`Picard/SlicingFlatKernel.lean:192`): for `ψ : P → N` with `P` finite, `N` finite flat
  and `ψ ⊗ κ(p)` injective at every prime, the cokernel `N ⧸ range ψ` is flat,

giving `Module.Flat R (colength z ⧸ N z)` per point (`flat_colength_quotient` /
`forall_flat_colength_quotient`).  Fed into the DD-4 capstone
`dvd_of_flat_quotient_of_field_vanishing` (`Picard/DivSchemeSeedDvd.lean:128`) together with
the fibre-vanishing `hfield`, this closes `hdvd` on the fibre-injective route
(`dvd_of_fibreInjective_of_field_vanishing`) — no `hspan`, no glued↔per-point flatness
bridge.

**Shared engine (I-0278 FINDING 2).**  The abstract flat-cokernel content is *entirely* the
`SlicingFlatKernel` `FibrewiseInjective` engine (`:192`); there is no further abstract lemma
to factor.  The RD3/CertUniv flat-cokernel clauses (the `IsCertified` `flat_coker_incl` /
`flat_coker_diff` of `Picard/DivisorFamily.lean`) consume the *same* engine on
`deltaLeft − deltaRight`, each consumer supplying its own carve fibre-injective lift.  The
genuine remaining content is per-consumer geometry — here, the fibre-injectivity
`FibreInjective` of `f_z`, whose proof identifies the fibre window `divUniversalFibreKM`
with `H⁰(N − d_p)` (`Picard/DivSchemeSeedUnivAssembleKappa.lean:157`) transported by the
colength base change `pieceQuotBaseChangeAlg` (`Picard/DivisorFamilyPullback.lean:384`), and
is entangled with the concrete seed `seedUniv`.
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

/-- **The carve fibre-injective law `ψ_z`** at a point `z` (the seed-close wall, fibre form):
the `K`-side-component map `f_z = (kColengthMap z) ∘ K.subtype : ↥K → colength z` is injective
after base change to the residue field `κ(p)` at every base prime `p` — equivalently, the
fibre kernel of `K → colength z` is trivial.  Geometrically the `K`-side components are the
`H⁰(N − d_p)` fibre windows sitting inside the fibre colength, injectively.  This is exactly
the hypothesis the flat-cokernel engine
`Module.Flat.quotient_range_of_forall_rTensor_residueField_injective` consumes. -/
def FibreInjective (z : relCurve C R) : Prop :=
  ∀ p : PrimeSpectrum R,
    Function.Injective
      (((D.kColengthMap z).comp K.subtype).rTensor p.asIdeal.ResidueField)

/-- **`ψ_z ⟹ Flat(colength ⧸ N z)`** at a single point: from the carve fibre-injective law
`FibreInjective z` (plus the colength finite and flat over `R`, and `K` finite over `R`) the
engine `Module.Flat.quotient_range_of_forall_rTensor_residueField_injective` yields flatness
of the per-point colength quotient `(Γ(D(h z)) ⧸ (eqn z)) ⧸ N z`, since
`N z = sideColengthSubmodule z = range ((kColengthMap z) ∘ K.subtype)`.  This is the direct
`hflat` producer of the DD-4 capstone `dvd_of_flat_quotient_of_field_vanishing`. -/
theorem flat_colength_quotient (z : relCurve C R) [Module.Finite R ↥K]
    [Module.Finite R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z})]
    [Module.Flat R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z})]
    (hinj : D.FibreInjective z) :
    Module.Flat R ((Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z})
      ⧸ D.sideColengthSubmodule z) := by
  have hrange : D.sideColengthSubmodule z
      = LinearMap.range ((D.kColengthMap z).comp K.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
  rw [hrange]
  exact Module.Flat.quotient_range_of_forall_rTensor_residueField_injective
    ((D.kColengthMap z).comp K.subtype) hinj

set_option synthInstance.maxHeartbeats 400000 in
-- the colength `Γ(D(h z)) ⧸ (eqn z)` is the heavy relCurve section-ring quotient; deriving
-- its module instances for the quotient by `N z` re-elaborates that type past the default budget
/-- **`ψ_z ⟹ Flat(colength ⧸ N z)` at every point** — the `hflat` package of the DD-4
capstone.  From the per-point colength finiteness/flatness (`hcolFin`/`hcolFlat`, both
landed at the seed) and the carve fibre-injective law `FibreInjective z` at every point,
produces `∀ z, Module.Flat R ((Γ(D(h z)) ⧸ (eqn z)) ⧸ N z)` — exactly the `hflat` argument
of `dvd_of_flat_quotient_of_field_vanishing`. -/
theorem forall_flat_colength_quotient [IsNoetherianRing R] [Module.Finite R ↥K]
    (hcolFin : ∀ z : relCurve C R,
      Module.Finite R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}))
    (hcolFlat : ∀ z : relCurve C R,
      Module.Flat R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}))
    (hinj : ∀ z : relCurve C R, D.FibreInjective z) :
    ∀ z : relCurve C R,
      Module.Flat R ((Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z})
        ⧸ D.sideColengthSubmodule z) := fun z => by
  haveI := hcolFin z
  haveI := hcolFlat z
  exact D.flat_colength_quotient z (hinj z)

set_option synthInstance.maxHeartbeats 400000 in
-- deriving the colength `Module.Finite`/quotient instances re-elaborates the heavy relCurve
-- section-ring quotient type past the default budget (as in `sideColengthSubmodule_finite`)
/-- **The `hdvd` wall, fibre-injective form** (I-0278 FINDING 1 "cleanest route", skipping
`hspan`): the seed satisfies its divisibility clause given

* `hreg` — the germ of the equation is a nonzerodivisor (the seed's fibre-regularity law);
* `hcolFin`/`hcolFlat` — each colength `Γ(D(h z)) ⧸ (eqn z)` is finite and flat over `R`
  (the `SupportTube` finiteness + the slicing flatness, both landed per piece);
* `hinj` — the carve fibre-injective law `FibreInjective z` at every point (the `ψ_z`
  lift: `f_z ⊗ κ(p)` injective at every base prime);
* `hfield` — every `K`-side component dies in the ambient residue-field fibre (`x ⊗ₜ 1 = 0`),
  i.e. is divisible by the fibre equation `e_p` (the `d_p` achiever, transported by
  `pieceQuotBaseChangeAlg`).

`hinj` (with `K` finite and the colength finite/flat) yields the per-point flatness of
`(Γ(D(h z)) ⧸ (eqn z)) ⧸ N z` through the fibrewise-injective engine
`Module.Flat.quotient_range_of_forall_rTensor_residueField_injective`, and that flatness plus
`hfield` is exactly the input of `dvd_of_flat_quotient_of_field_vanishing`.  This isolates the
divisor-first `hdvd` to the single fibre-injective obligation `hinj` — no `hspan`, no glued↔
per-point flatness bridge. -/
theorem dvd_of_fibreInjective_of_field_vanishing [IsNoetherianRing R] [Module.Finite R ↥K]
    (hreg : ∀ (z : relCurve C R) (y : relCurve C R) (hy : y ∈ D.piece z),
      ((relCurve C R).presheaf.germ (D.piece z) y hy).hom (D.eqn z)
        ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk y))
    (hcolFin : ∀ z : relCurve C R,
      Module.Finite R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}))
    (hcolFlat : ∀ z : relCurve C R,
      Module.Flat R (Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}))
    (hinj : ∀ z : relCurve C R, D.FibreInjective z)
    (hfield : ∀ (z : relCurve C R) (y : relCurve C R) (hy : y ∈ D.piece z)
        (x : ↥(D.sideColengthSubmodule z)),
        ((x : Γ(relCurve C R, D.piece z) ⧸ Ideal.span {D.eqn z}) ⊗ₜ[R]
            (1 : (basePrime (R := R)
              ((relCurve C R).presheaf.germ (D.piece z) y hy).hom).asIdeal.ResidueField))
          = 0) :
    ∀ (z : relCurve C R) ⦃ψ : relThetaSections C R π a⦄, ψ ∈ K →
      relThetaResSide a (D.side z) (D.piece_le z) ψ ∈ Ideal.span {D.eqn z} :=
  D.dvd_of_flat_quotient_of_field_vanishing hreg
    (fun z => by haveI := hcolFin z; exact D.sideColengthSubmodule_finite z)
    (D.forall_flat_colength_quotient hcolFin hcolFlat hinj) hfield

end ThetaGeneratorSeed

end AlgebraicGeometry
