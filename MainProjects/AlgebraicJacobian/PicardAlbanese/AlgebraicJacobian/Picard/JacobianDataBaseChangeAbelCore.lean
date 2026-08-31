/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtCrossBaseGraph
import AlgebraicJacobian.Picard.JacobianDataBaseChangeAbel
import AlgebraicJacobian.Picard.Pic0ThetaAssembly

/-!
# The A-1 core: θ carries the Abel class across the base-field shuffle (Wave 7, W7-A1)

`Picard/JacobianDataBaseChangeAbel.lean` reduced the datum-level Abel–Jacobi base-change
compatibility (`baseChange_ofCurve_data_of_core`) to a single hypothesis `hCore`, stated at
the `pic0Subgroup` level.  This file discharges the *transport* half of `hCore` and isolates
what genuinely remains, which is smaller than the worksheet predicted.

## The re-pricing (worksheet §3 vs. what the reduction actually costs)

`informal/w7-k1-worksheet.md` §3 prices the A-1 core as an identity to be closed "by
`abelPicEt_map` + `graphLocalEquations_base_change`", i.e. as a computation about graph
divisors.  Measured here: the `pic0Subgroup`/`picEt` layers strip off *without* touching the
graph API at all, because both sides are unit images and the base-field shuffle commutes with
the étale unit at a general test — that is exactly `picEtCrossBase_relPicToPicEt`
(`Picard/PicEtCrossBaseGraph.lean`, landed for A-1 and until now unconsumed).  What is left
after the strip is a **Čech-class** identity on `((baseChange k L).obj C ⊗ T).left`, one
level below where the worksheet expected the boundary.

## Main declarations

* `AlgebraicGeometry.picEtCrossBase_picEtMap_abelPicEt` — **the transport law**: the
  base-field shuffle of the restriction of the Abel class along any `f` out of a pushed test
  is the unit image of the cross-base transport of the restricted Abel Čech class.  Landed
  and axiom-clean; no graph geometry, no hypotheses beyond the standing curve pack.
* `AlgebraicGeometry.abelCrossBaseCechCore` — the residual Čech-class obligation, named so
  the remaining gap has one address instead of being spelled out at each consumer.
* `AlgebraicGeometry.pic0CrossBaseEquiv_symm_abel_of_cech` — **the `hCore` supplier**: the
  committed `hCore` of `JacobianDataBaseChangeAbel.lean` follows from
  `abelCrossBaseCechCore`.  This is the theorem that makes `baseChange_ofCurve_data_of_core`
  applicable, so A-1's residue is now exactly `abelCrossBaseCechCore` and nothing else.
* `AlgebraicGeometry.baseChange_ofCurve_data_of_cech` — **the consumer**: the worksheet §3
  datum-level A-1 statement, off `abelCrossBaseCechCore` alone.
* `AlgebraicGeometry.abelCrossBaseCechCore_of_graph` — the residue **split into its two graph
  factors**: it suffices that the cross-base transport carries the diagonal graph class to
  the diagonal graph class and the constant graph class to the constant one.  This is the
  form `Over.graphLocalEquations_base_change` speaks about, and it is what a future session
  should attack; it needs no `abelCechClass` unfolding.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.Scheme (CechPic)

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {L : Type u} [Field L] [Algebra k L]

/-! ## The transport law -/

/-- **The Abel class transports through the base-field shuffle** (the A-1 transport half):
for any `L`-test `T` and any point `f` of `C` on the pushed-forward test, the base-field
shuffle of the restriction of the Abel class is the unit image of the cross-base transport
of the restricted Abel Čech class.

Proof: `abelPicEt` is a unit image, restriction commutes with the unit
(`picEtMap_relPicToPicEt`) and with `relPicMk` (`relPicMap_mk`), and the shuffle commutes
with the unit at a general test (`picEtCrossBase_relPicToPicEt`).  Nothing here inspects the
graph divisor — the graph API enters only in the residual Čech identity below. -/
theorem picEtCrossBase_picEtMap_abelPicEt (T : Over (Spec (.of L)))
    (f : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T ⟶ C)
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    picEtCrossBase k L C T (picEtMap C f (abelPicEt C P))
      = relPicToPicEt ((baseChange k L).obj C) T
          (relPicMk ((baseChange k L).obj C) T
            (CechPic.map (crossBaseIso k L C T).hom
              (CechPic.map (C ◁ f).left (abelCechClass C P)))) := by
  rw [abelPicEt, picEtMap_relPicToPicEt, relPicMap_mk, picEtCrossBase_relPicToPicEt]

/-! ## The residual obligation -/

/-- **The residual Čech-class obligation of A-1** — one level below the worksheet's boundary.
The cross-base transport of the Abel Čech class of `C`, restricted along the
`Over.mapPullbackAdj` counit, is the Abel Čech class of the base-changed curve at the
base-changed point.

This is *all* that stands between the landed reduction
(`baseChange_ofCurve_data_of_core`, `Picard/JacobianDataBaseChangeAbel.lean`) and the frozen
`Jacobian.baseChange_ofCurve`. -/
def abelCrossBaseCechCore (k : Type u) [Field k] (L : Type u) [Field L] [Algebra k L]
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) : Prop :=
  CechPic.map (crossBaseIso k L C ((baseChange k L).obj C)).hom
      (CechPic.map (C ◁ (Over.mapPullbackAdj
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).counit.app C).left
          (abelCechClass C P))
    = abelCechClass ((baseChange k L).obj C)
        (Functor.LaxMonoidal.ε (baseChange k L) ≫ (baseChange k L).map P)

/-- **The `hCore` supplier**: the `pic0Subgroup`-level core hypothesis of
`baseChange_ofCurve_data_of_core` follows from the Čech-level `abelCrossBaseCechCore`.

The `pic0Subgroup` and `picEt` layers strip by `Subtype.ext` plus the two `rfl`-grade
coercion anchors (`pic0CrossBaseEquiv_symm_apply_coe`, `abelElement_coe`) and the transport
law above.  Term-mode throughout: the counit's codomain is spelled `(𝟭 _).obj C`, so `rw`
cannot abstract the `picEtMap` pattern (the R4/R5 spelling friction of I-0216 — measured
here, not assumed). -/
theorem pic0CrossBaseEquiv_symm_abel_of_cech (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    (h : abelCrossBaseCechCore k L C P) :
    (pic0CrossBaseEquiv k L C ((baseChange k L).obj C)).symm
        (pic0Map C
          ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).counit.app C)
          (abelElement C P))
      = abelElement ((baseChange k L).obj C)
          (Functor.LaxMonoidal.ε (baseChange k L) ≫ (baseChange k L).map P) :=
  Subtype.ext
    ((picEtCrossBase_picEtMap_abelPicEt ((baseChange k L).obj C)
        ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).counit.app C)
        P).trans
      (congrArg
        (fun z => relPicToPicEt ((baseChange k L).obj C) ((baseChange k L).obj C)
          (relPicMk ((baseChange k L).obj C) ((baseChange k L).obj C) z)) h))

/-! ## The residue, split into graph factors -/

/-- **The residue splits along the two graph factors of the Abel class.**  Since
`abelCechClass` is `𝒪(Δ) · 𝒪(P × C)⁻¹` and Čech transport is a group homomorphism, it
suffices that the cross-base transport carries each graph factor to its counterpart
downstairs.  Both hypotheses are statements purely about `Over.graphPicClass`, i.e. in the
language of `Over.graphLocalEquations_base_change` — which is where the worksheet's §3 route
was aiming, reached now without any `abelCechClass` bookkeeping. -/
theorem abelCrossBaseCechCore_of_graph (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    (hdiag : CechPic.map (crossBaseIso k L C ((baseChange k L).obj C)).hom
        (Over.graphPicClass C
          ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).counit.app C))
      = Over.graphPicClass ((baseChange k L).obj C) (𝟙 ((baseChange k L).obj C)))
    (hconst : CechPic.map (crossBaseIso k L C ((baseChange k L).obj C)).hom
        (Over.graphPicClass C
          (toUnit ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj
            ((baseChange k L).obj C)) ≫ P))
      = Over.graphPicClass ((baseChange k L).obj C)
          (toUnit ((baseChange k L).obj C)
            ≫ (Functor.LaxMonoidal.ε (baseChange k L) ≫ (baseChange k L).map P))) :
    abelCrossBaseCechCore k L C P :=
  -- The counit's codomain is spelled `(𝟭 _).obj C`, so `rw` cannot abstract the
  -- `CechPic.map (C ◁ ·)` pattern (I-0216 notes 1–2, measured again here): term-mode only.
  ((congrArg (CechPic.map (crossBaseIso k L C ((baseChange k L).obj C)).hom)
      (cechPicMap_abelCechClass
        ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).counit.app C)
        P)).trans
    ((map_mul _ _ _).trans
      (((congrArg (· * _) hdiag).trans
        (congrArg (_ * ·) ((map_inv _ _).trans (congrArg (·⁻¹) hconst)))))))

/-! ## The downstream consumer: A-1's datum-level statement off the Čech residue -/

/-- **A-1 at the datum level, off the Čech residue** — this file's supplier composed with the
landed reduction `baseChange_ofCurve_data_of_core`
(`Picard/JacobianDataBaseChangeAbel.lean`).  This is the worksheet §3 statement
`baseChange_ofCurve_data`, now depending on `abelCrossBaseCechCore` alone; at
`d := jacobianData C`, `dL := jacobianData C_L` it is the frozen
`Jacobian.baseChange_ofCurve` (`Challenge.lean:278`).

Its existence is the point: A-1 is no longer a reduction plus a prose note about what is
missing, but a single named hypothesis with one producer obligation and a consumer that
actually applies it, both in Lean. -/
theorem baseChange_ofCurve_data_of_cech (d : JacobianData C)
    (dL : JacobianData ((baseChange k L).obj C)) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    (h : abelCrossBaseCechCore k L C P) :
    (baseChange k L).map (d.homEquiv.symm (abelElement C P))
        ≫ (baseChangeIsoOfData d dL).hom.hom.hom
      = dL.homEquiv.symm
          (abelElement _ (Functor.LaxMonoidal.ε (baseChange k L) ≫ (baseChange k L).map P)) :=
  baseChange_ofCurve_data_of_core d dL P (pic0CrossBaseEquiv_symm_abel_of_cech P h)

end AlgebraicGeometry
