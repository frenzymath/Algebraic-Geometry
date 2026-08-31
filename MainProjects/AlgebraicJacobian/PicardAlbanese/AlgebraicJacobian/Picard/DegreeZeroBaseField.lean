/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DegreeZero
import AlgebraicJacobian.Picard.PicEtAffMap

/-!
# Base-field invariance of the plus-class degree (`w4-datb` §1.2 step 2, the missing brick)

`PicEtAff.degAff` reads the degree of a plus class over a field; `PicEtAff.map` restricts a
plus class along a base extension of the affine test.  This file proves the one compatibility
between them that the tree lacked:

  `degAff L (PicEtAff.map C L a) = degAff K a`   for **any** field extension `L/K` over `k`.

`Picard/Pic0ChartCoverageDegree.lean` records (issue I-0614) that COV-1 / `w4-datb` §1.2 step 2
is *not* discharged precisely because this statement is absent — the coverage argument holds the
plus-class degree at the fibre field `K` while the presenting Čech class lives over the splitting
field `L`, and nothing equated the two readings.  That docstring predicts a lemma "shaped like
the landed `degAff_baseFieldShuffle`".

## Two corrections to that prediction, both of which make the brick *cheaper*

1. **No hypotheses on `L/K`.**  Not finite, not separable, not algebraic.  The prediction's
   model (`degAff_baseFieldShuffle`, `Picard/Pic0ThetaAssembly.lean:67`) compares two classes
   over one field; here the two *fields* differ, which sounds harder and is not: the
   degree of a relative Picard class is invariant along **any** `k`-algebra map of fields
   (`relPicDeg_relPicAlgMap`, E-iv-alg descended), so the `L/K` step itself is free.
2. **No use of the descent keystone.**  One expects `relPicAlgMap_congr` to reconcile two
   different `K`-algebra maps out of the cover carrier.  It is not needed: the two maps are
   *literally equal*, by `Algebra.EtaleCover.baseChangeMap_comp_baseChangeInclude`.

## The route

`degAff` is only *readable* on a finite separable field refinement of the representing cover
(`degAff_mk`), so each side needs its own reading field, and the two readings must be compared
inside a single field.  That field cannot be chosen freely: for `K = ℚ`, `N = ℚ(i)`, `L = ℝ` no
`K`-embedding `N → P` into a finite separable `P/L` exists unless `P` is *built* from `N`.  So:

* `N/K` finite separable with `ℓ : E.Carrier →ₐ[K] N` — field cofinality at `K`;
* `P/L` finite separable with `q : ((ofField N).baseChange L).Carrier →ₐ[L] P` — field
  cofinality applied to the **base-changed field cover**, i.e. `P` is a field factor of
  `L ⊗[K] N`.  This is what supplies both `σ : N →ₐ[K] P` and a reading of the `L`-side.

Then `j := q ∘ baseChangeMap L ℓ'` reads the `L`-side, and
`(j|_K) ∘ E.baseChangeInclude L = σ ∘ ℓ` on the nose, so both sides are `relPicDeg P` of the
*same* class and the residual `P`-to-`N` step is E-iv-alg.

## Main declarations

* `AlgebraicGeometry.PicEtAff.degAff_map` — **the brick**: `degAff` is invariant under
  `PicEtAff.map` along an arbitrary field extension of the test.
* `AlgebraicGeometry.PicEtAff.degAff_map_eq_zero_iff` — the degree-zero locus is stable both
  ways, the form the coverage argument spends.
-/

set_option autoImplicit false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

noncomputable section

set_option maxHeartbeats 1600000 in
-- Three composite `letI` algebra structures (`k → N`, `k → P`, `K → P`) are in scope while the
-- goal mentions `overSpec k`-carriers built from base-changed étale carriers; each instance
-- slot of `degAff_mk` is rechecked against those composites.  Same budget as
-- `Pic0ChartSplit.exists_splitting_of_picEtAff`, which builds one such composite.
/-- **Base-field invariance of the plus-class degree** (`w4-datb` §1.2 step 2; the brick
issue I-0614 named as absent).  For an arbitrary field extension `L/K` in a tower `k → K → L`,
restricting a plus class along `K → L` does not change its degree.

No finiteness, separability or algebraicity of `L/K` is assumed — see the file header for why
the statement is *cheaper* than its prediction, and for the two reading fields the proof
constructs (`N/K` from cofinality at `K`, and `P/L` a field factor of `L ⊗[K] N`, which is what
makes a `K`-embedding `N → P` exist at all). -/
theorem PicEtAff.degAff_map {K : Type u} [Field K] [Algebra k K]
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (a : PicEtAff C K) :
    PicEtAff.degAff L (PicEtAff.map C L a) = PicEtAff.degAff K a := by
  induction a using PicEtAff.ind with
  | mk E x =>
    -- (1) the `K`-side reading field: cofinality of field covers at `K`
    obtain ⟨N, hNf, hNa, hNfin, hNsep, ⟨ℓ⟩⟩ := E.exists_finiteSeparableField_algHom
    letI := hNf
    letI := hNa
    letI := hNfin
    letI := hNsep
    letI hkN : Algebra k N := ((algebraMap K N).comp (algebraMap k K)).toAlgebra
    haveI : IsScalarTower k K N := .of_algebraMap_eq fun _ => rfl
    -- (2) the common field: a field factor of `L ⊗[K] N`, obtained by cofinality applied to
    -- the base change of the field cover of `N`.  This is the step that cannot be replaced by
    -- an arbitrary finite separable `P/L`.
    obtain ⟨P, hPf, hPa, hPfin, hPsep, ⟨q⟩⟩ :=
      ((Algebra.EtaleCover.ofField (K := K) N).baseChange L).exists_finiteSeparableField_algHom
    letI := hPf
    letI := hPa
    letI := hPfin
    letI := hPsep
    letI hkP : Algebra k P := ((algebraMap L P).comp (algebraMap k L)).toAlgebra
    haveI htowL : IsScalarTower k L P := .of_algebraMap_eq fun _ => rfl
    letI hKP : Algebra K P := ((algebraMap L P).comp (algebraMap K L)).toAlgebra
    haveI htowKLP : IsScalarTower K L P := .of_algebraMap_eq fun _ => rfl
    haveI htowkKP : IsScalarTower k K P := .of_algebraMap_eq fun r => by
      change algebraMap L P (algebraMap k L r)
        = algebraMap L P (algebraMap K L (algebraMap k K r))
      rw [← IsScalarTower.algebraMap_apply k K L r]
    -- (3) the refinement of the field cover of `N`, and the `K`-embedding `N → P` it carries
    set ℓ' : E.Carrier →ₐ[K] (Algebra.EtaleCover.ofField (K := K) N).Carrier :=
      (Algebra.EtaleCover.ofFieldEquiv (K := K) N).symm.toAlgHom.comp ℓ with hℓ'
    set σ : N →ₐ[K] P :=
      ((q.restrictScalars K).comp
          ((Algebra.EtaleCover.ofField (K := K) N).baseChangeInclude L)).comp
        (Algebra.EtaleCover.ofFieldEquiv (K := K) N).symm.toAlgHom with hσ
    -- (4) the `L`-side reading map, and the square that makes the two readings the same class
    set j : (E.baseChange L).Carrier →ₐ[L] P :=
      q.comp (Algebra.EtaleCover.baseChangeMap L ℓ') with hj
    have hsquare : (j.restrictScalars K).comp (E.baseChangeInclude L) = σ.comp ℓ := by
      have hbc := Algebra.EtaleCover.baseChangeMap_comp_baseChangeInclude
        (A := K) (A' := L) ℓ'
      have hstep : ((Algebra.EtaleCover.baseChangeMap L ℓ').restrictScalars K).comp
            (E.baseChangeInclude L)
          = ((Algebra.EtaleCover.ofField (K := K) N).baseChangeInclude L).comp ℓ' := hbc
      ext y
      have := AlgHom.congr_fun hstep y
      change q (Algebra.EtaleCover.baseChangeMap L ℓ' (E.baseChangeInclude L y)) = _
      rw [show Algebra.EtaleCover.baseChangeMap L ℓ' (E.baseChangeInclude L y)
          = ((Algebra.EtaleCover.ofField (K := K) N).baseChangeInclude L) (ℓ' y) from this]
      simp [hσ, hℓ']
    -- (5) read both sides at `P`, and cross the `P`/`N` step by E-iv-alg
    have hK : PicEtAff.degAff K (PicEtAff.mk C E x)
        = relPicDeg N (relPicAlgMap C (ℓ.restrictScalars k)
            (x : relPic C (overSpec k E.Carrier))) :=
      PicEtAff.degAff_mk E x N ℓ
    have hL : PicEtAff.degAff L (PicEtAff.map C L (PicEtAff.mk C E x))
        = relPicDeg P (relPicAlgMap C (j.restrictScalars k)
            (descentBaseChange C L E x : relPic C (overSpec k (E.baseChange L).Carrier))) := by
      rw [PicEtAff.map_mk]
      exact PicEtAff.degAff_mk (E.baseChange L) (descentBaseChange C L E x) P j
    rw [hL, hK, descentBaseChange_coe, ← relPicAlgMap_comp,
      show (j.restrictScalars k).comp ((E.baseChangeInclude L).restrictScalars k)
          = (σ.restrictScalars k).comp (ℓ.restrictScalars k) from
        AlgHom.ext fun y => AlgHom.congr_fun hsquare y,
      relPicAlgMap_comp]
    exact relPicDeg_relPicAlgMap (σ.restrictScalars k) _

/-- The degree-zero locus of the plus group is stable in **both** directions along a base
extension of the test by a field: a plus class over `K` has degree zero iff its restriction to
`L` does.  This is the form the coverage argument spends — it is where degree-zero-ness of the
`λ` factor is turned into a vanishing `classDeg` over the splitting field. -/
theorem PicEtAff.degAff_map_eq_zero_iff {K : Type u} [Field K] [Algebra k K]
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (a : PicEtAff C K) :
    PicEtAff.degAff L (PicEtAff.map C L a) = 0 ↔ PicEtAff.degAff K a = 0 := by
  rw [PicEtAff.degAff_map]

end

end AlgebraicGeometry
