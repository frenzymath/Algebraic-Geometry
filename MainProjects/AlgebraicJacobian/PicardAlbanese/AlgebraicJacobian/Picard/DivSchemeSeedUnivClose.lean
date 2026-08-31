/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedDvd

/-!
# DD-4 — the seed section is a fibre kernel witness of the `K`-side-component map

For any theta generator seed `D` the candidate generator `sec z` lies in `K` (`sec_mem`)
and its side component **is** the equation `eqn z`, so its class in the colength
`Γ(D(h z)) ⧸ (eqn z)` is zero: `kColengthMap z (sec z) = 0`.  Hence `sec z` is a nonzero
element of `K` (nonzero in the fibre by the seed construction) that is killed by
`f_z := kColengthMap z ∘ K.subtype`.

This is the structural witness that `f_z` is **never fibrewise injective** when `sec z`
survives fibrewise — i.e. `ThetaGeneratorSeed.FibreInjective z` is *false* for any seed
whose seed section has nonzero residue-field fibre.  See the landing note (SEED CLOSE:
`FibreInjective` route is unsound; the correct route is
`dvd_of_fibrewise_ker_span_of_field_vanishing`, the `hspan`/`c4` keystone).
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

/-- **The seed section lies in the fibre kernel of the `K`-side-component map**: its side
component is by definition the equation `eqn z`, so its colength class vanishes,
`kColengthMap z (sec z) = 0`.  Combined with `sec_mem` (`sec z ∈ K`) this exhibits a
distinguished element of `K` that `f_z = kColengthMap z ∘ K.subtype` always kills — the
obstruction to fibrewise injectivity of `f_z` whenever `sec z` survives in the fibre. -/
@[simp]
theorem kColengthMap_sec_eq_zero (z : relCurve C R) :
    D.kColengthMap z (D.sec z) = 0 := by
  change Ideal.Quotient.mk (Ideal.span {D.eqn z})
      (relThetaResSide a (D.side z) (D.piece_le z) (D.sec z)) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self (D.eqn z))

/-- The seed section, viewed in `K`, is in the kernel of `f_z = kColengthMap z ∘ K.subtype`.
The class of `⟨sec z, sec_mem z⟩` under `f_z` is `kColengthMap z (sec z) = 0`. -/
theorem sec_mem_ker_kColengthMap_comp_subtype (z : relCurve C R) :
    (⟨D.sec z, D.sec_mem z⟩ : ↥K) ∈
      LinearMap.ker ((D.kColengthMap z).comp K.subtype) := by
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply]
  exact D.kColengthMap_sec_eq_zero z

/-- **`IsGenerator` on the sound `hspan` (`c4`) route** — the correct seed-close assembly
(replacing the *unsound* `FibreInjective` route: `f_z = kColengthMap z ∘ K.subtype`
kills the fibre-nonzero section `sec z ∈ K`, so `f_z ⊗ κ(p)` is never injective and
`FibreInjective z` is false).  Composes the sharpened divisibility capstone
`dvd_of_fibrewise_ker_span_of_field_vanishing` (`Picard/DivSchemeSeedDvd.lean:180`, the
`hspan`/`c4` `Module.Flat.quotient_range_of_forall_ker_rTensor_residueField_le` route)
with the fibre-regularity discharge `isGenerator_of_fibre_ne_zero`
(`Picard/DivSchemeSeed.lean:188`).  Reduces the whole DDR-3 close of the seed to the six
route-independent fibre facts:

* `hreg` — germ regularity of the equation (fibre-regularity law);
* `hcolFin`/`hcolFlat` — each colength `Γ(D(h z)) ⧸ (eqn z)` finite/flat over `R`;
* `hspan` — the fibre kernel of the `K`-side-component map is spanned by the base change
  of its global kernel (the genuine carve flat rank-`g` content, the `c4` clause);
* `hfield` — every `K`-side component dies in the ambient residue-field fibre;
* `hfib` — the compared chart component of the seed section is fibrewise nonzero.

`D.localEquations (this)` is then the DDR-3 `relDivisor`. -/
theorem isGenerator_of_fibrewise_ker_span_of_field_vanishing [IsNoetherianRing R]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
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
          = 0)
    (hfib : ∀ (z : relCurve C R) (p : PrimeSpectrum R),
      ((relCurve C p.asIdeal.ResidueField).basicOpen
          (relPinnedSectionsMap C R p.asIdeal.ResidueField π (D.side z) (D.h z)) :
        (relCurve C p.asIdeal.ResidueField).Opens) ≠ ⊥ →
      relPinnedSectionsMap C R p.asIdeal.ResidueField π (D.side z)
        (relThetaResSide a (D.side z) le_rfl (D.sec z)) ≠ 0) :
    D.IsGenerator :=
  D.isGenerator_of_fibre_ne_zero
    (D.dvd_of_fibrewise_ker_span_of_field_vanishing hreg hcolFin hcolFlat hspan hfield)
    hfib

end ThetaGeneratorSeed

end AlgebraicGeometry
