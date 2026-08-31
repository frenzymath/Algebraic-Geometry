/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartTwistSplit
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentationDatum

/-!
# Field-extension stability for rank-one presentation witnesses

The rank-one layer delivered by the translated-cover construction is a class over a field.
Testing its pullback over an arbitrary affine algebra reads that class at residue fields, which
are arbitrary extensions of the original field.  This file proves that the split-witness
condition survives every such extension.

The proof does not reuse the original splitting field directly.  If `N / K` is the finite
separable splitting supplied by the witness and `L / K` is arbitrary, a field factor `P / L`
of `L \otimes[K] N` is finite separable over `L` and receives `N`.  The presenting Cech class
and its `H^1` witness are then transported from `N` to `P`.
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
-- Constructing and transporting through a field factor of `L ⊗[K] N` needs the larger budget.
/-- A split witness remains a split witness after an arbitrary extension of its reading field.

The output splitting field is not the original one: it is a finite-separable field factor of
the base change of the original field cover.  Consequently no finiteness, separability, or
algebraicity assumption is imposed on the reading-field extension itself.  The auxiliary finite
map `pi` is used only to choose a basic-open cocycle datum through which the `H¹` witness is
transported. -/
theorem isSplitWitness_map_overSpecMap_of_algHom
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    {K L : Type u} [Field K] [Algebra k K] [Field L] [Algebra k L]
    (e : K →ₐ[k] L) (nu : picEt C (overSpec k K))
    (h : IsSplitWitness C nu) :
    IsSplitWitness C (picEtMap C (Over.overSpecMap e) nu) := by
  obtain ⟨N, hNf, hkN, hKN, htowkKN, hNfin, hNsep, M, hM, W, hW, hW1⟩ := h
  letI := hNf
  letI := hkN
  letI := hKN
  letI := htowkKN
  letI := hNfin
  letI := hNsep
  letI hKL : Algebra K L := e.toRingHom.toAlgebra
  haveI htowkKL : IsScalarTower k K L :=
    .of_algebraMap_eq fun x => (e.commutes x).symm
  obtain ⟨P, hPf, hLP, hPfin, hPsep, ⟨q⟩⟩ :=
    ((Algebra.EtaleCover.ofField (K := K) N).baseChange L).exists_finiteSeparableField_algHom
  letI := hPf
  letI := hLP
  letI := hPfin
  letI := hPsep
  letI hkP : Algebra k P := ((algebraMap L P).comp (algebraMap k L)).toAlgebra
  haveI htowkLP : IsScalarTower k L P := .of_algebraMap_eq fun _ => rfl
  letI hKP : Algebra K P := ((algebraMap L P).comp e.toRingHom).toAlgebra
  haveI htowKLP : IsScalarTower K L P := .of_algebraMap_eq fun _ => rfl
  haveI htowkKP : IsScalarTower k K P := .of_algebraMap_eq fun x => by
    change algebraMap L P (algebraMap k L x) = algebraMap L P (e (algebraMap k K x))
    rw [e.commutes]
  set sigma : N →ₐ[K] P :=
    ((q.restrictScalars K).comp
        ((Algebra.EtaleCover.ofField (K := K) N).baseChangeInclude L)).comp
      (Algebra.EtaleCover.ofFieldEquiv (K := K) N).symm.toAlgHom with hsigma
  letI hNP : Algebra N P := sigma.toRingHom.toAlgebra
  haveI htowKNP : IsScalarTower K N P :=
    .of_algebraMap_eq fun x => (sigma.commutes x).symm
  haveI htowkNP : IsScalarTower k N P := .of_algebraMap_eq fun x => by
    change algebraMap k P x = sigma (algebraMap k N x)
    rw [IsScalarTower.algebraMap_apply k K N, sigma.commutes,
      ← IsScalarTower.algebraMap_apply k K P]
  obtain ⟨D, hD⟩ :=
    BasicOpenCocycleDatum.exists_cechPicClass_eq (C := C) (B := N) (π := pi) M
  have hid : Scheme.CechPic.map (relCurveMap C N N) D.cechPicClass
      = D.cechPicClass := by
    have hmap : relCurveMap C N N = 𝟙 (relCurve C N) := by
      rw [relCurveMap]
      have hbase : overSpecMap (k := k) N N = 𝟙 (overSpec k N) :=
        Over.OverMorphism.ext (by simp)
      rw [hbase, MonoidalCategory.whiskerLeft_id]
      rfl
    rw [hmap, Scheme.CechPic.map_id]
    rfl
  have hWitnessN : D.HasWitnessH1Vanishing N :=
    ⟨W, by rw [hid, hD, hW], hW1⟩
  obtain ⟨W', hW', hW1'⟩ :=
    (D.hasWitnessH1Vanishing_iff_of_fieldExtension N P).mp hWitnessN
  have hMP : PicEtAff.map C P (picEtAffineEquiv C K nu)
      = PicEtAff.unit C P
          (relPicMk C (overSpec k P) (Scheme.CechPic.map (relCurveMap C N P) M)) := by
    have hmap := congrArg (PicEtAff.map C P) hM
    rw [PicEtAff.map_map, PicEtAff.map_unit, relPicAlgMap_mk] at hmap
    exact hmap
  refine isSplitWitness_of_presenting_witness C _
    (Scheme.CechPic.map (relCurveMap C N P) M) ?_ W' ?_ hW1'
  · rw [picEtAffineEquiv_naturality]
    change PicEtAff.map C P (PicEtAff.map C L (picEtAffineEquiv C K nu)) = _
    rw [PicEtAff.map_map]
    exact hMP
  · rw [hW', hD]

/-- A native datum for the arbitrary-affine pullback of a split field class has the required
residue-field `H¹` witnesses.

This is a field-origin specialization, not a claim for an arbitrary affine Picard class.  The
map to each residue field factors through the affine algebra and the chosen etale cover, so the
single split witness over `K` supplies all pointwise witnesses needed by the datum. -/
theorem PicRankOneNativeDatum.residueH1Witness_of_fieldPullback
    {K A : Type u} [Field K] [Algebra k K] [CommRing A] [Algebra k A]
    {pi : C.left ⟶ P1 k} [IsFinite pi]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (P : PicRankOneNativeDatum pi lam)
    (e : K →ₐ[k] A) (nu : picEt C (overSpec k K))
    (hlam : lam.1 = picEtMap C (Over.overSpecMap e) nu)
    (hsplit : IsSplitWitness C nu) :
    ∀ p : PrimeSpectrum P.cover.Carrier,
      P.datum.HasWitnessH1Vanishing p.asIdeal.ResidueField := by
  apply P.residueH1Witness_of_isSplitWitness
  intro t
  let iota : A →ₐ[k] P.cover.Carrier :=
    (Algebra.ofId A P.cover.Carrier).restrictScalars k
  let rho : P.cover.Carrier →ₐ[k]
      Over.testPointField (T := overSpec k P.cover.Carrier) t :=
    IsScalarTower.toAlgHom k P.cover.Carrier _
  let phi : K →ₐ[k]
      Over.testPointField (T := overSpec k P.cover.Carrier) t :=
    rho.comp (iota.comp e)
  have hcover :
      picEtMap C (Over.overSpecMap iota) lam.1 =
        relPicToPicEt C (overSpec k P.cover.Carrier)
          (P.representative : relPic C (overSpec k P.cover.Carrier)) :=
    picEtMap_eq_relPicToPicEt_of_affineRepresentative
      C lam.1 P.cover P.representative P.represents.symm
  have hpoint : Over.testPoint t = Over.overSpecMap rho := by
    rw [testPoint_eq_overSpecMap]
    apply Over.OverMorphism.ext
    rfl
  have hmaps :
      (Over.testPoint t ≫ Over.overSpecMap iota) ≫ Over.overSpecMap e =
        Over.overSpecMap phi := by
    rw [Category.assoc, hpoint, ← Over.overSpecMap_comp, ← Over.overSpecMap_comp]
  have hclass :
      picEtMap C (Over.testPoint t)
          (relPicToPicEt C (overSpec k P.cover.Carrier)
            (P.representative : relPic C (overSpec k P.cover.Carrier))) =
        picEtMap C (Over.overSpecMap phi) nu := by
    calc
      _ = picEtMap C (Over.testPoint t)
          (picEtMap C (Over.overSpecMap iota) lam.1) := by rw [hcover]
      _ = picEtMap C
          (Over.testPoint t ≫ Over.overSpecMap iota) lam.1 :=
        (picEtMap_comp (C := C) (Over.overSpecMap iota)
          (Over.testPoint t) lam.1).symm
      _ = picEtMap C (Over.testPoint t ≫ Over.overSpecMap iota)
          (picEtMap C (Over.overSpecMap e) nu) := by rw [hlam]
      _ = picEtMap C
          ((Over.testPoint t ≫ Over.overSpecMap iota) ≫
            Over.overSpecMap e) nu :=
        (picEtMap_comp (C := C) (Over.overSpecMap e)
          (Over.testPoint t ≫ Over.overSpecMap iota) nu).symm
      _ = picEtMap C (Over.overSpecMap phi) nu :=
        congrArg (fun f => picEtMap C f nu) hmaps
  rw [hclass]
  exact isSplitWitness_map_overSpecMap_of_algHom
    (C := C) pi phi nu hsplit

end

end AlgebraicGeometry
