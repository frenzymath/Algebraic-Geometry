/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartLocusGeneralTest
import AlgebraicJacobian.Picard.Pic0ChartTwistSplit

/-!
# `IsSplitWitnessIsoInvariant` DISCHARGED — CHART-U(b) at a general test, unconditionally

`Picard/Pic0ChartLocusGeneralTest.lean` proves CHART-U(b) over a general test *modulo one
hypothesis*: `IsSplitWitnessIsoInvariant C`, the transport of `IsSplitWitness` along an
**isomorphism** of reading fields.  That was the single input standing between the landed
affine openness and `isOpen_chartLocus` over a general test, and its own docstring priced it as
"`PicEtAff.map_map` plus `map_id`, not geometry".

**This file proves it, and the price was almost that.**  The route is:

1. the residue-field extension a morphism of tests induces is a `k`-algebra map
   (`Over.testPointFieldMap_comp_algebraMap`) — this was *not* recorded anywhere, and it is what
   lets the extension be read as an `AlgHom`/`AlgEquiv` at all.  It is `Spec.preimage` applied to
   the naturality square `Over.testPoint_comp_left`, plus the two `Over` triangles;
2. an invertible extension is therefore a `k`-algebra **equivalence**
   (`Over.testPointFieldAlgEquiv`);
3. `IsSplitWitness` is invariant along such an equivalence
   (`isSplitWitness_map_overSpecMap_iff`);
4. the naturality square in the `overSpecMap` spelling (`Over.testPoint_comp`) turns (3) into
   `IsSplitWitnessIsoInvariant`.

## What step (3) actually costs, and where the prediction was right

The prediction was `map_map` + `map_id`; what it *is* is `PicEtAff.map_map` in the
`mapAlg`-into-a-common-target form (`PicEtAff.map_mapAlg_eq_map`) plus
`picEtAffineEquiv_naturality`, and the witness clause is carried through untouched.  So the class
side is indeed pure functoriality.

**What the prediction did not mention is the instance side, and that is the real content.**
`IsSplitWitness C μ` existentially quantifies a splitting field `L` *together with seven
instances*, four of them about `L` over the reading field: `Algebra K L`, `IsScalarTower k K L`,
`Module.Finite K L`, `Algebra.IsSeparable K L`.  Transporting the predicate along `e : K ≃ₐ[k] K'`
keeps **the same `L`** but must re-derive all four over `K'`, along `e.symm`.  Two of them are
mathlib transports found by name (`Module.Finite.of_equiv_equiv`,
`Algebra.IsSeparable.of_equiv_equiv`, both stated for exactly this square) and two are
`IsScalarTower.of_algebraMap_eq`.  A one-line `rw` this is not; but it is bookkeeping, and no
geometry enters — in particular nothing about the curve, the twist, or `H¹` is touched.

## Why the forward direction genuinely needs an EQUIVALENCE, not an `AlgHom`

`isSplitWitness_map_overSpecMap` is stated for `e : K ≃ₐ[k] K'` and the `≃` is load-bearing at a
precise point: the transported `Algebra K' L` is `algebraMap K L ∘ e.symm`, which needs `e`
*surjective*.  Along a non-invertible `K → K'` there is no `K'`-algebra structure on the old `L`
at all, and one would have to base-change `L` — which is the separable-extension route
(`exists_witness_of_separable_extension`), a different and strictly harder lemma.  So the `IsIso`
hypothesis of `IsSplitWitnessIsoInvariant` is not packaging; it is what makes the same `L` work.

## Main declarations

* `AlgebraicGeometry.Over.testPointFieldMap_comp_algebraMap` — the induced residue-field
  extension is a `k`-algebra map.
* `AlgebraicGeometry.Over.testPointFieldAlgHom` / `Over.testPointFieldAlgEquiv` — that extension
  as an `AlgHom`, and as an `AlgEquiv` when it is invertible.
* `AlgebraicGeometry.Over.testPoint_comp` — the `Pic0ChartTestPoint` naturality square as an
  equality of morphisms **in the slice**, through `Over.overSpecMap`.
* `AlgebraicGeometry.PicEtAff.map_mapAlg_eq_map` — `map_map` in the form this needs: an explicit
  `k`-algebra map into a common target is absorbed by `PicEtAff.map`.
* `AlgebraicGeometry.isSplitWitness_map_overSpecMap_iff` — `IsSplitWitness` is invariant along a
  `k`-algebra equivalence of the reading field.
* **`AlgebraicGeometry.isSplitWitnessIsoInvariant_holds`** — the hypothesis of
  `Pic0ChartLocusGeneralTest`, discharged.
* `AlgebraicGeometry.chartLocus_fromSpecAffine_eq_preimage'`,
  `AlgebraicGeometry.isOpen_chartLocus_of_affineLocal'` — the general-test statements with the
  hypothesis removed.  **`isOpen_chartLocus_of_affineLocal'` is CHART-U(b) at a general test with
  no residue**, which is what `c9b` consumes as the `V` of `restrictChart`.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

namespace Over

/-! ## The residue-field extension is a `k`-algebra map

`testPointFieldMap` is defined as a bare `CommRingCat` morphism (`Scheme.Hom.residueFieldMap`),
and `Pic0ChartTestPoint` records only its `Algebra` reading via `testPointFieldAlgebra`, which
makes `κ(t)` a `κ(f t)`-algebra *without* saying anything about `k`.  For the plus-class
transport that is not enough: `PicEtAff.mapAlg` consumes a `k`-**algebra** map, so the fact that
the extension is one over `k` has to be proved.  It is exactly the two `Over` triangles read
through `Spec.preimage`. -/

/-- **The residue-field extension induced by a morphism of tests is a `k`-algebra map.**

`testPointFieldMap f t : κ(f t) → κ(t)` commutes with the two `k`-algebra structures of
`Pic0ChartTestPoint`, both of which are `Spec.preimage` of a composite down to `Spec k`.  The
proof is the naturality square `testPoint_comp_left` composed with `T.hom`, pushed through
`Spec.preimage` (a bijection on homs out of an affine, so it turns the commuting square of
schemes into the commuting square of rings). -/
theorem testPointFieldMap_comp_algebraMap {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (t : T'.left) :
    (testPointFieldMap f t).hom.comp
        (algebraMap k (testPointField (T := T) (f.left.base t)))
      = algebraMap k (testPointField (T := T') t) := by
  have hw : (testPoint t).left ≫ T'.hom
      = Spec.map (testPointFieldMap f t)
          ≫ ((testPoint (T := T) (f.left.base t)).left ≫ T.hom) := by
    rw [← Category.assoc, ← testPoint_comp_left f t, Category.assoc, Over.w f,
      Over.w (testPoint t)]
  have hpre := congrArg (fun g => (Spec.preimage g).hom) hw
  simp only [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp] at hpre
  exact hpre.symm

/-- The residue-field extension at a point, as a `k`-algebra map. -/
def testPointFieldAlgHom {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T'.left) :
    testPointField (T := T) (f.left.base t) →ₐ[k] testPointField (T := T') t :=
  { (testPointFieldMap f t).hom with
    commutes' := fun r => congrFun (congrArg DFunLike.coe
      (testPointFieldMap_comp_algebraMap f t)) r }

/-- **An invertible residue-field extension is a `k`-algebra equivalence.**  This is the shape
the `IsSplitWitness` transport consumes, and the `IsIso` hypothesis of
`IsSplitWitnessIsoInvariant` exists precisely to supply it. -/
def testPointFieldAlgEquiv {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T'.left)
    [IsIso (testPointFieldMap f t)] :
    testPointField (T := T) (f.left.base t) ≃ₐ[k] testPointField (T := T') t :=
  { (asIso (testPointFieldMap f t)).commRingCatIsoToRingEquiv with
    commutes' := (testPointFieldAlgHom f t).commutes }

/-- **The naturality square of the bridge, in the slice.**  `Pic0ChartTestPoint.testPoint_comp_left`
states it for the underlying scheme morphisms; every class-level transport needs it for the
`Over`-morphisms themselves, since `picEtMap` is indexed by those.  Faithfulness of
`Over.forget` (`Over.OverMorphism.ext`) is the whole content. -/
theorem testPoint_comp {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T'.left) :
    testPoint t ≫ f
      = overSpecMap (testPointFieldAlgHom f t) ≫ testPoint (T := T) (f.left.base t) :=
  Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, Over.overSpecMap_left]
    exact testPoint_comp_left f t)

end Over

namespace PicEtAff

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- **`map_map` in the form the transport needs**: an explicit `k`-algebra map `e : K → K'` that
is compatible with two towers into a common `L` is absorbed by `PicEtAff.map`.

`PicEtAff.map_map` is stated for a chain of `Algebra` instances; here the middle step is an
explicit `AlgHom`, so the `Algebra K K'` it needs is manufactured from `e` and the
`IsScalarTower K K' L` from `halg`.  This is the class-side half of the whole iso-invariance,
and it is pure functoriality — no field, separability or finiteness hypothesis appears. -/
theorem map_mapAlg_eq_map {K K' L : Type u} [CommRing K] [Algebra k K]
    [CommRing K'] [Algebra k K'] [CommRing L] [Algebra k L]
    [Algebra K L] [Algebra K' L] [IsScalarTower k K L] [IsScalarTower k K' L]
    (e : K →ₐ[k] K') (halg : ∀ x : K, algebraMap K' L (e x) = algebraMap K L x)
    (a : PicEtAff C K) :
    PicEtAff.map C L (PicEtAff.mapAlg C e a) = PicEtAff.map C L a :=
  letI : Algebra K K' := e.toRingHom.toAlgebra
  haveI : IsScalarTower k K K' := .of_algebraMap_eq fun x => (e.commutes x).symm
  haveI : IsScalarTower K K' L := .of_algebraMap_eq fun x => (halg x).symm
  PicEtAff.map_map C K' L a

end PicEtAff

/-! ## Iso-invariance of the split predicate -/

variable (C) in
/-- **`IsSplitWitness` transports along a `k`-algebra equivalence of the reading field**
(forward direction).

The splitting field `L` is **not changed**: along `e : K ≃ₐ[k] K'` the same `L` presents the
transported class, via the `K'`-algebra structure `algebraMap K L ∘ e.symm`.  That is where the
`≃` is used and cannot be weakened — for a non-invertible `K → K'` no such structure exists and
one must base-change `L` instead (`exists_witness_of_separable_extension`, a strictly harder
statement).

The four instances about `L/K` are re-derived over `K'`: `Algebra K' L` and
`IsScalarTower k K' L` by `of_algebraMap_eq`, and `Module.Finite K' L`,
`Algebra.IsSeparable K' L` by mathlib's transports along the same commuting square
(`Module.Finite.of_equiv_equiv`, `Algebra.IsSeparable.of_equiv_equiv`).  The class equation is
`picEtAffineEquiv_naturality` plus `PicEtAff.map_mapAlg_eq_map`, and the witness clause `(W, hW,
hW1)` is carried through **untouched** — it lives over `L`, which did not move. -/
theorem isSplitWitness_map_overSpecMap {K K' : Type u} [Field K] [Algebra k K]
    [Field K'] [Algebra k K'] (e : K ≃ₐ[k] K') (nu : picEt C (overSpec k K))
    (h : IsSplitWitness C nu) :
    IsSplitWitness C (picEtMap C (Over.overSpecMap e.toAlgHom) nu) := by
  obtain ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, M, hM, W, hW, hW1⟩ := h
  letI := hLfield
  letI := hkL
  letI := hKL
  haveI := htow
  haveI := hfin
  haveI := hsep
  -- the SAME `L`, now a `K'`-algebra along `e.symm`
  letI hK'L : Algebra K' L := ((algebraMap K L).comp e.symm.toRingHom).toAlgebra
  have halg : ∀ x : K, algebraMap K' L (e x) = algebraMap K L x := fun x => by
    change (algebraMap K L) (e.symm (e x)) = _
    rw [e.symm_apply_apply]
  haveI htow' : IsScalarTower k K' L := .of_algebraMap_eq fun x => by
    change algebraMap k L x = (algebraMap K L) (e.symm (algebraMap k K' x))
    rw [show e.symm (algebraMap k K' x) = algebraMap k K x from
      (e.symm.commutes x).trans rfl, ← IsScalarTower.algebraMap_apply k K L]
  -- the commuting square both mathlib transports are stated against
  have hcomp : ((algebraMap K' L).comp (e.toRingEquiv : K →+* K'))
      = ((RingEquiv.refl L : L →+* L)).comp (algebraMap K L) :=
    RingHom.ext fun x => halg x
  haveI hfin' : Module.Finite K' L :=
    Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl L) hcomp
  haveI hsep' : Algebra.IsSeparable K' L :=
    Algebra.IsSeparable.of_equiv_equiv e.toRingEquiv (RingEquiv.refl L) hcomp
  refine isSplitWitness_of_presenting_witness C _ M ?_ W hW hW1
  rw [picEtAffineEquiv_naturality, PicEtAff.map_mapAlg_eq_map e.toAlgHom halg]
  exact hM

variable (C) in
/-- **Iso-invariance of `IsSplitWitness`, as an `iff`.**  The reverse direction is the forward
one at `e.symm`, since `overSpecMap` is functorial and `e.symm ∘ e = id`.  An `iff` is what the
locality assembly needs: a one-sided containment would not give openness. -/
theorem isSplitWitness_map_overSpecMap_iff {K K' : Type u} [Field K] [Algebra k K]
    [Field K'] [Algebra k K'] (e : K ≃ₐ[k] K') (nu : picEt C (overSpec k K)) :
    IsSplitWitness C (picEtMap C (Over.overSpecMap e.toAlgHom) nu)
      ↔ IsSplitWitness C nu := by
  refine ⟨fun h => ?_, isSplitWitness_map_overSpecMap C e nu⟩
  have hid : Over.overSpecMap (k := k) e.symm.toAlgHom ≫ Over.overSpecMap e.toAlgHom
      = 𝟙 (overSpec k K) := by
    rw [← Over.overSpecMap_comp, show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id k K from
      AlgHom.ext fun x => e.symm_apply_apply x, Over.overSpecMap_id]
  have hback := isSplitWitness_map_overSpecMap C e.symm _ h
  rwa [← picEtMap_comp, hid, picEtMap_id] at hback

variable (C) in
/-- **`IsSplitWitnessIsoInvariant` — DISCHARGED.**

The hypothesis `Picard/Pic0ChartLocusGeneralTest.lean` carries, and the only input standing
between the landed affine openness of `chartLocus` and CHART-U(b) at a general test.  With it,
`isOpen_chartLocus_of_affineLocal'` below is unconditional.

The assembly is the naturality square in the slice (`Over.testPoint_comp`): reading the class at
`κ(t)` after restricting along `f` equals restricting along `Spec` of the residue-field
extension, which under the `IsIso` hypothesis is `Spec` of a `k`-algebra **equivalence** — and
along one of those `IsSplitWitness` is invariant. -/
theorem isSplitWitnessIsoInvariant_holds : IsSplitWitnessIsoInvariant C := by
  intro T T' f t hiso mu
  haveI := hiso
  have hfac : picEtMap C (Over.testPoint t) (picEtMap C f mu)
      = picEtMap C (Over.overSpecMap (Over.testPointFieldAlgHom f t))
          (picEtMap C (Over.testPoint (T := T) (f.left.base t)) mu) := by
    rw [← picEtMap_comp, ← picEtMap_comp, Over.testPoint_comp f t]
  rw [hfac, show Over.testPointFieldAlgHom f t
      = (Over.testPointFieldAlgEquiv f t).toAlgHom from AlgHom.ext fun _ => rfl]
  exact isSplitWitness_map_overSpecMap_iff C (Over.testPointFieldAlgEquiv f t) _

/-! ## CHART-U(b) at a general test, with the hypothesis removed -/

variable (C) in
/-- `chartLocus_fromSpecAffine_eq_preimage` with its hypothesis discharged. -/
theorem chartLocus_fromSpecAffine_eq_preimage' (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (U : T.left.affineOpens) (lam : picEt C T) :
    chartLocus C m Z (picEtMap C (Over.fromSpecAffine T U) lam)
      = (Over.fromSpecAffine T U).left.base ⁻¹' chartLocus C m Z lam :=
  chartLocus_fromSpecAffine_eq_preimage C (isSplitWitnessIsoInvariant_holds C) m Z T U lam

variable (C) in
/-- **CHART-U(b) AT A GENERAL TEST, UNCONDITIONALLY.**

If `chartLocus` is open over each affine-open test object of `T`, it is open over `T` — with no
remaining hypothesis.  This is the `V` that `c9b`'s `restrictChart` needs, and the statement
`Pic0ChartLocusIsOpen`'s docstring promised. -/
theorem isOpen_chartLocus_of_affineLocal' (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (T : Over (Spec (.of k))) (lam : picEt C T)
    (haff : ∀ U : T.left.affineOpens,
      IsOpen (chartLocus C m Z (picEtMap C (Over.fromSpecAffine T U) lam))) :
    IsOpen (chartLocus C m Z lam) :=
  isOpen_chartLocus_of_affineLocal C (isSplitWitnessIsoInvariant_holds C) m Z T lam haff

end

end AlgebraicGeometry
