/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartTestPoint
import AlgebraicJacobian.Picard.Pic0RankOneLocus
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentationSplit

/-!
# Split witnesses from rank-one presentations at a field (Task-C steps D0 + D1)

Two converse-direction bricks for the rank-one openness lane.

* `AlgebraicGeometry.Over.exists_overSpecMap_testPoint_comp` (D0) — **testPoint naturality
  in the slice**: for `f : T' ⟶ T` over `Spec k` and a point `t` of `T'.left`, the
  naturality square of the residue-field bridge (`Over.testPoint_comp_left`) is promoted
  to an equation of slice morphisms through a `k`-algebra map of the two residue fields.
  The algebra-map upgrade of `testPointFieldMap` is not done by hand: it is delegated to
  `exists_algHom_eq_of_overSpec_hom_of_commRing`, whose `Spec.preimage` performs it once.

* `AlgebraicGeometry.PicRankOneLocalPresentation.isSplitWitness` (D1) — **the field
  converse of the presentation contract**: a `PicRankOneLocalPresentation` of a
  genus-degree class over a field `K` yields `IsSplitWitness` for that class.  The
  splitting field is a finite separable single-factor refinement of the presentation's
  étale cover (`Algebra.EtaleCover.exists_finiteSeparableField_algHom`); the presenting
  equation is the plus-class field collapse (`PicEtAff.map_mk_eq_unit_of_algHom`) read
  through `P.datum_class`; the witness divisor comes from the presentation's own
  `H¹`-vanishing through the datum dictionary
  (`BasicOpenCocycleDatum.hasWitnessH1Vanishing_iff_subsingleton`).

* `AlgebraicGeometry.isSplitWitness_of_mem_picRankOneOpen_field` — membership of a field
  class in `PicRankOneOpen` implies `IsSplitWitness`, by testing with the identity.
  Together with the landed `mem_picRankOneOpen_of_isSplitWitness` this is the fibrewise
  characterization of the rank-one locus at fields.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## D0: testPoint naturality in the slice -/

/-- **testPoint naturality as an equation of slice morphisms** (Task-C D0).  For a
morphism of tests `f : T' ⟶ T` over `Spec k` and a point `t : T'.left`, there is a
`k`-algebra map `φ : κ(f t) →ₐ[k] κ(t)` through which the field point of `t` composed
with `f` is the field point of `f t`.

This is `Over.testPoint_comp_left` upgraded from the underlying schemes to the slice: the
underlying map of the connecting morphism is `Spec` of `Over.testPointFieldMap f t`, and
its `k`-algebra structure is recovered by `exists_algHom_eq_of_overSpec_hom_of_commRing`
rather than assembled by hand. -/
theorem Over.exists_overSpecMap_testPoint_comp
    {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (t : T'.left) :
    ∃ φ : Over.testPointField (T := T) (f.left.base t) →ₐ[k]
        Over.testPointField (T := T') t,
      Over.testPoint t ≫ f
        = Over.overSpecMap φ ≫ Over.testPoint (T := T) (f.left.base t) := by
  have hw : Spec.map (Over.testPointFieldMap f t)
        ≫ (overSpec k (Over.testPointField (T := T) (f.left.base t))).hom
      = (overSpec k (Over.testPointField (T := T') t)).hom := by
    calc Spec.map (Over.testPointFieldMap f t)
          ≫ (overSpec k (Over.testPointField (T := T) (f.left.base t))).hom
        = Spec.map (Over.testPointFieldMap f t)
            ≫ ((Over.testPoint (T := T) (f.left.base t)).left ≫ T.hom) := by
          rw [Over.w (Over.testPoint (T := T) (f.left.base t))]
      _ = ((Over.testPoint t).left ≫ f.left) ≫ T.hom := by
          rw [← Category.assoc, ← Over.testPoint_comp_left f t]
      _ = (Over.testPoint t).left ≫ T'.hom := by
          rw [Category.assoc, Over.w f]
      _ = (overSpec k (Over.testPointField (T := T') t)).hom :=
          Over.w (Over.testPoint t)
  obtain ⟨φ, hφ⟩ := exists_algHom_eq_of_overSpec_hom_of_commRing (k := k)
    (Over.testPointField (T := T) (f.left.base t))
    (Over.testPointField (T := T') t)
    (Over.homMk (Spec.map (Over.testPointFieldMap f t)) hw)
  refine ⟨φ, ?_⟩
  apply Over.OverMorphism.ext
  have key : (Over.overSpecMap φ).left = Spec.map (Over.testPointFieldMap f t) :=
    congrArg Over.Hom.left hφ.symm
  rw [Over.comp_left, Over.comp_left, key]
  exact Over.testPoint_comp_left f t

/-! ## D1: presentation at a field ⇒ split witness -/

/-- Triviality of a module is preserved by any coefficient extension: a tensor product
with a subsingleton factor is a subsingleton. -/
private theorem subsingleton_tensorProduct_of_subsingleton_left
    {R X Y : Type u} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (h : Subsingleton X) :
    Subsingleton (X ⊗[R] Y) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z with
  | zero => rfl
  | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
  | add u v hu hv => rw [hu, hv, add_zero]

set_option maxHeartbeats 1600000 in
-- The plus-class field collapse through the base-changed étale carrier needs the larger
-- budget (same as `isSplitWitness_map_overSpecMap_of_algHom`).
/-- **The field converse of the rank-one presentation contract** (Task-C D1): a
`PicRankOneLocalPresentation` of a genus-degree class over a field `K` makes that class a
split witness.

The splitting field `L` is a finite separable single-factor refinement of the
presentation's étale cover.  The presenting Čech class is the image of the presentation's
own `P.datum.cechPicClass` under the carrier-to-`L` refinement, by the plus-class field
collapse; its witness divisor with vanishing `H¹` exists because the presentation's
`h1_vanishing` field survives the coefficient extension to `L` (`0 ⊗ = 0`), which is
exactly the datum dictionary's condition at `L`. -/
theorem PicRankOneLocalPresentation.isSplitWitness
    {pi : C.left ⟶ P1 k} [IsFinite pi]
    {K : Type u} [Field K] [Algebra k K]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k K)}
    (P : PicRankOneLocalPresentation pi lam) :
    IsSplitWitness C lam.1 := by
  obtain ⟨L, hLf, hKL, hLfin, hLsep, ⟨ψ⟩⟩ :=
    P.cover.exists_finiteSeparableField_algHom
  letI := hLf
  letI := hKL
  letI := hLfin
  letI := hLsep
  letI hkL : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  haveI htowkKL : IsScalarTower k K L := .of_algebraMap_eq fun _ => rfl
  letI hBL : Algebra P.cover.Carrier L := ψ.toRingHom.toAlgebra
  haveI htowKBL : IsScalarTower K P.cover.Carrier L :=
    .of_algebraMap_eq fun x => (ψ.commutes x).symm
  haveI htowkBL : IsScalarTower k P.cover.Carrier L := .of_algebraMap_eq fun x => by
    change algebraMap k L x = ψ (algebraMap k P.cover.Carrier x)
    rw [IsScalarTower.algebraMap_apply k K P.cover.Carrier, ψ.commutes,
      ← IsScalarTower.algebraMap_apply k K L]
  have hcurve : Over.Hom.left (C ◁ Over.overSpecMap (AlgHom.restrictScalars k ψ))
      = relCurveMap C P.cover.Carrier L := by
    refine congrArg (fun g : overSpec k L ⟶ overSpec k P.cover.Carrier => (C ◁ g).left) ?_
    exact Over.OverMorphism.ext rfl
  have hM : PicEtAff.map C L (picEtAffineEquiv C K lam.1)
      = PicEtAff.unit C L (relPicMk C (overSpec k L)
          (Scheme.CechPic.map (relCurveMap C P.cover.Carrier L)
            P.datum.cechPicClass)) := by
    rw [← P.represents, PicEtAff.map_mk_eq_unit_of_algHom C P.representative ψ,
      P.datum_class, relPicAlgMap_mk, hcurve]
    rfl
  have hsub : Subsingleton ((datumPair P.datum).H1 ⊗[P.cover.Carrier] L) :=
    subsingleton_tensorProduct_of_subsingleton_left
      ((subsingleton_datumPair_h1_iff P.datum).mpr P.h1_vanishing)
  obtain ⟨W, hW, hW1⟩ :=
    (P.datum.hasWitnessH1Vanishing_iff_subsingleton L).mpr hsub
  exact isSplitWitness_of_presenting_witness C lam.1
    (Scheme.CechPic.map (relCurveMap C P.cover.Carrier L) P.datum.cechPicClass)
    hM W hW hW1

/-- **Membership of a field class in the public rank-one locus implies the split-witness
condition** — the converse of `mem_picRankOneOpen_of_isSplitWitness`, obtained by testing
the membership contract with the identity of `overSpec k K`.  Together the two theorems
characterize the rank-one locus fibrewise at fields. -/
theorem isSplitWitness_of_mem_picRankOneOpen_field
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    {K : Type u} [Field K] [Algebra k K]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k K)}
    (h : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k K))) :
    IsSplitWitness C lam.1 := by
  obtain ⟨P⟩ := (mem_picRankOneOpen_iff pi lam).mp h K (𝟙 (overSpec k K))
  have e : ((picDegLayerFunctor C (genus C : ℤ)).map
        (𝟙 (overSpec k K)).op lam).1 = lam.1 :=
    picEtMap_id C lam.1
  have hsplit := P.isSplitWitness
  exact e ▸ hsplit

end

end AlgebraicGeometry
