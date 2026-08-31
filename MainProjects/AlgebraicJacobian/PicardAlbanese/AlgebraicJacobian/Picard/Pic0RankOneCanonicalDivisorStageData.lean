/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOnePresentation
import AlgebraicJacobian.Cohomology.DatumDescent
import AlgebraicJacobian.Cohomology.RankOneFamilyCertificatesFiniteStage

/-!
# A finite stage for a rank-one presentation

The cocycle datum of a rank-one presentation over an arbitrary etale carrier descends to a
finitely generated stage.  Refining once more makes the actual datum-pair `H^1` vanish there.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

/-- A Noetherian coefficient stage whose datum pulls back to a rank-one presentation datum. -/
structure PicRankOneNoetherianStage
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (P : PicRankOneLocalPresentation pi lam) where
  B0 : Subalgebra k P.cover.Carrier
  hB0fg : B0.FG
  D0 : BasicOpenCocycleDatum C (B0 : Type u) pi
  hD0 : D0.baseChange (B' := P.cover.Carrier) = P.datum
  A0 : Subalgebra (B0 : Type u) P.cover.Carrier
  hAnoeth : IsNoetherianRing A0
  hpair : Subsingleton (datumPair (D0.baseChange A0)).H1
  hbase : (D0.baseChange A0).baseChange P.cover.Carrier = P.datum

set_option maxHeartbeats 2000000 in
-- The two nested subalgebra stages carry dependent scalar-tower and datum equalities.
set_option synthInstance.maxHeartbeats 800000 in
/-- A finite Noetherian stage exists for every rank-one presentation. -/
theorem PicRankOneLocalPresentation.nonempty_noetherianStage
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (P : PicRankOneLocalPresentation pi lam)
    (hpi : pi ≫ P1.structureMap k = C.hom) :
    Nonempty (PicRankOneNoetherianStage P) := by
  classical
  have hpair : Subsingleton (datumPair P.datum).H1 :=
    (subsingleton_datumPair_h1_iff P.datum).mpr P.h1_vanishing
  obtain ⟨B0, hB0fg, D0, hD0⟩ := P.datum.exists_fg_subalgebra_baseChange_eq
  have hpairBase : Subsingleton
      (datumPair (D0.baseChange (B' := P.cover.Carrier))).H1 := by
    rw [hD0]
    exact hpair
  have htensor : Subsingleton ((datumPair D0).H1 ⊗[B0] P.cover.Carrier) :=
    D0.subsingleton_h1_tensor_of_baseChange P.cover.Carrier hpairBase
  obtain ⟨A0, -, -, hAnoeth, hpairA0, hAA⟩ :=
    BasicOpenCocycleDatum.exists_fg_pairH1_vanishing_stage
      (C := C) (pi := pi) B0 hB0fg D0 hpi htensor
  exact ⟨{
    B0 := B0
    hB0fg := hB0fg
    D0 := D0
    hD0 := hD0
    A0 := A0
    hAnoeth := hAnoeth
    hpair := hpairA0
    hbase := hAA.trans hD0 }⟩

end AlgebraicGeometry
