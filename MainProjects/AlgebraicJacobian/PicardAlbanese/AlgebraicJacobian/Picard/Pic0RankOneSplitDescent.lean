/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartTwistSplit
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentationDatum

/-!
# Descent of the split-witness condition along a field embedding

`isSplitWitness_map_overSpecMap_of_algHom` (`Picard/Pic0RankOneNativePresentationField`)
transports a split witness *up* an arbitrary extension of its reading field.  This file
proves the converse: if the pullback of a class `ν` over `K` along a field embedding
`e : K →ₐ[k] K'` is a split witness, then `ν` itself already is.  Together the two make
the split-witness condition on a field class *intrinsic to the underlying point*, which
is exactly what lets the rank-one split locus be computed on any carrier and transported
down cover maps.

The proof splits `ν` over a finite separable `L/K` and destructures the hypothesis'
splitting `L'/K'`, presents both Čech classes by basic-open cocycle data, and compares
them over a common finite separable extension `P/L'`: a field factor of the base change
to `L'` of the field cover `L/K`.  Over `P` the two presenting classes agree — both
present the pushforward of `ν`, and the plus unit (étale separatedness, C1) together
with `relPicMk`-injectivity at a one-point base identifies them at the Čech level — so
the witness `H¹`-vanishing predicates of the two data coincide there, and field-location
invariance walks the witness from `L'` down to `L`.

The auxiliary finite map `pi` is used only to choose the basic-open cocycle data through
which the `H¹` witness is transported.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

set_option maxHeartbeats 1600000 in
-- Two instance towers (one per splitting field) and the compositum transport need the
-- larger budget, exactly as in the upward-transport template.
/-- **Split-witness descent along an arbitrary field embedding** — the converse of
`isSplitWitness_map_overSpecMap_of_algHom`: if the pullback of `ν` along
`Spec K' → Spec K` is a split witness then so is `ν`.

No finiteness, separability, or algebraicity assumption is imposed on `e`.  The witness
is not read off over the hypothesis' splitting field directly: both splittings are
compared over a finite separable field factor of the base change of the `ν`-side
splitting field, where étale separatedness identifies the presenting Čech classes, and
the witness then descends by field-location invariance of the `H¹` predicate. -/
theorem isSplitWitness_of_overSpecMap
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    {K K' : Type u} [Field K] [Algebra k K] [Field K'] [Algebra k K']
    (e : K →ₐ[k] K') (nu : picEt C (overSpec k K))
    (h : IsSplitWitness C (picEtMap C (Over.overSpecMap e) nu)) :
    IsSplitWitness C nu := by
  -- split `ν` over a finite separable `L/K`, and present the splitting by a datum
  obtain ⟨L, hLf, hkL, hKL, htowkKL, hLfin, hLsep, M, hM⟩ :=
    exists_splitting_of_picEt C nu
  letI := hLf
  letI := hkL
  letI := hKL
  letI := htowkKL
  letI := hLfin
  letI := hLsep
  obtain ⟨D, hD⟩ :=
    BasicOpenCocycleDatum.exists_cechPicClass_eq (C := C) (B := L) (π := pi) M
  -- destructure the split witness of the pullback, and present its splitting too
  obtain ⟨L', hL'f, hkL', hK'L', htowkK'L', hL'fin, hL'sep, M', hM', W', hW'cl, hW'1⟩ := h
  letI := hL'f
  letI := hkL'
  letI := hK'L'
  letI := htowkK'L'
  letI := hL'fin
  letI := hL'sep
  obtain ⟨D', hD'⟩ :=
    BasicOpenCocycleDatum.exists_cechPicClass_eq (C := C) (B := L') (π := pi) M'
  -- the `K`-algebra structures on `K'` and `L'`, through `e`
  letI hKK' : Algebra K K' := e.toRingHom.toAlgebra
  haveI htowkKK' : IsScalarTower k K K' :=
    .of_algebraMap_eq fun x => (e.commutes x).symm
  letI hKL' : Algebra K L' := ((algebraMap K' L').comp e.toRingHom).toAlgebra
  haveI htowKK'L' : IsScalarTower K K' L' := .of_algebraMap_eq fun _ => rfl
  haveI htowkKL' : IsScalarTower k K L' := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply k K' L']
    change algebraMap K' L' (algebraMap k K' x)
      = algebraMap K' L' (e (algebraMap k K x))
    rw [e.commutes]
  -- the common field `P`: a finite separable field factor of `L' ⊗[K] L` over `L'`
  obtain ⟨P, hPf, hL'P, hPfin, hPsep, ⟨q⟩⟩ :=
    ((Algebra.EtaleCover.ofField (K := K) L).baseChange
      L').exists_finiteSeparableField_algHom
  letI := hPf
  letI := hL'P
  letI := hPfin
  letI := hPsep
  letI hkP : Algebra k P := ((algebraMap L' P).comp (algebraMap k L')).toAlgebra
  haveI htowkL'P : IsScalarTower k L' P := .of_algebraMap_eq fun _ => rfl
  letI hK'P : Algebra K' P := ((algebraMap L' P).comp (algebraMap K' L')).toAlgebra
  haveI htowK'L'P : IsScalarTower K' L' P := .of_algebraMap_eq fun _ => rfl
  haveI htowkK'P : IsScalarTower k K' P := .of_algebraMap_eq fun x => by
    change algebraMap L' P (algebraMap k L' x)
      = algebraMap L' P (algebraMap K' L' (algebraMap k K' x))
    rw [← IsScalarTower.algebraMap_apply k K' L']
  letI hKP : Algebra K P := ((algebraMap L' P).comp (algebraMap K L')).toAlgebra
  haveI htowKL'P : IsScalarTower K L' P := .of_algebraMap_eq fun _ => rfl
  haveI htowkKP : IsScalarTower k K P := .of_algebraMap_eq fun x => by
    change algebraMap L' P (algebraMap k L' x)
      = algebraMap L' P (algebraMap K L' (algebraMap k K x))
    rw [← IsScalarTower.algebraMap_apply k K L']
  haveI htowKK'P : IsScalarTower K K' P := .of_algebraMap_eq fun _ => rfl
  -- the embedding of the `ν`-side splitting field into `P`
  set sigma : L →ₐ[K] P :=
    ((q.restrictScalars K).comp
        ((Algebra.EtaleCover.ofField (K := K) L).baseChangeInclude L')).comp
      (Algebra.EtaleCover.ofFieldEquiv (K := K) L).symm.toAlgHom with hsigma
  letI hLP : Algebra L P := sigma.toRingHom.toAlgebra
  haveI htowKLP : IsScalarTower K L P :=
    .of_algebraMap_eq fun x => (sigma.commutes x).symm
  haveI htowkLP : IsScalarTower k L P := .of_algebraMap_eq fun x => by
    change algebraMap k P x = sigma (algebraMap k L x)
    rw [IsScalarTower.algebraMap_apply k K L, sigma.commutes,
      ← IsScalarTower.algebraMap_apply k K P]
  -- both data present their own classes at their own base fields
  have hidL : Scheme.CechPic.map (relCurveMap C L L) D.cechPicClass
      = D.cechPicClass := by
    have hmap : relCurveMap C L L = 𝟙 (relCurve C L) := by
      rw [relCurveMap]
      have hbase : overSpecMap (k := k) L L = 𝟙 (overSpec k L) :=
        Over.OverMorphism.ext (by simp)
      rw [hbase, MonoidalCategory.whiskerLeft_id]
      rfl
    rw [hmap, Scheme.CechPic.map_id]
    rfl
  have hidL' : Scheme.CechPic.map (relCurveMap C L' L') D'.cechPicClass
      = D'.cechPicClass := by
    have hmap : relCurveMap C L' L' = 𝟙 (relCurve C L') := by
      rw [relCurveMap]
      have hbase : overSpecMap (k := k) L' L' = 𝟙 (overSpec k L') :=
        Over.OverMorphism.ext (by simp)
      rw [hbase, MonoidalCategory.whiskerLeft_id]
      rfl
    rw [hmap, Scheme.CechPic.map_id]
    rfl
  -- the hypothesis' witness, read as the fibre predicate of `D'` at `L'`
  have hWitL' : D'.HasWitnessH1Vanishing L' :=
    ⟨W', by rw [hidL', hD', hW'cl], hW'1⟩
  -- push both presenting equations to `P`
  have hMP : PicEtAff.map C P (picEtAffineEquiv C K nu)
      = PicEtAff.unit C P
          (relPicMk C (overSpec k P) (Scheme.CechPic.map (relCurveMap C L P) M)) := by
    have hmap := congrArg (PicEtAff.map C P) hM
    rw [PicEtAff.map_map, PicEtAff.map_unit, relPicAlgMap_mk] at hmap
    exact hmap
  have hM'P : PicEtAff.map C P
        (picEtAffineEquiv C K' (picEtMap C (Over.overSpecMap e) nu))
      = PicEtAff.unit C P
          (relPicMk C (overSpec k P)
            (Scheme.CechPic.map (relCurveMap C L' P) M')) := by
    have hmap := congrArg (PicEtAff.map C P) hM'
    rw [PicEtAff.map_map, PicEtAff.map_unit, relPicAlgMap_mk] at hmap
    exact hmap
  -- over `P` both present the same class: the pushforward of `ν`
  have hnat : PicEtAff.map C P
        (picEtAffineEquiv C K' (picEtMap C (Over.overSpecMap e) nu))
      = PicEtAff.map C P (picEtAffineEquiv C K nu) := by
    rw [picEtAffineEquiv_naturality]
    change PicEtAff.map C P (PicEtAff.map C K' (picEtAffineEquiv C K nu)) = _
    rw [PicEtAff.map_map]
  -- étale separatedness + `relPicMk`-injectivity: Čech-level agreement over `P`
  haveI : Subsingleton (overSpec k P).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum P))
  have hclP : Scheme.CechPic.map (relCurveMap C L P) M
      = Scheme.CechPic.map (relCurveMap C L' P) M' :=
    relPicMk_injective_of_subsingleton C (overSpec k P)
      (PicEtAff.unit_injective C P (hMP.symm.trans (hnat.symm.trans hM'P)))
  have hclD : Scheme.CechPic.map (relCurveMap C L P) D.cechPicClass
      = Scheme.CechPic.map (relCurveMap C L' P) D'.cechPicClass := by
    rw [hD, hD']
    exact hclP
  -- chain the witness: `L' → P` (up), congr across the class identity, `P → L` (down)
  have hWitP : D.HasWitnessH1Vanishing P :=
    (D.hasWitnessH1Vanishing_congr_of_cechPicClass_eq D' P hclD).mpr
      ((D'.hasWitnessH1Vanishing_iff_of_fieldExtension L' P).mp hWitL')
  obtain ⟨W, hWcl, hW1⟩ :=
    (D.hasWitnessH1Vanishing_iff_of_fieldExtension L P).mpr hWitP
  refine isSplitWitness_of_presenting_witness C nu M hM W ?_ hW1
  rw [hWcl, hidL, hD]

end

end AlgebraicGeometry
