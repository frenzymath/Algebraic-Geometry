/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedUnivRes
import AlgebraicJacobian.Picard.DivSchemeSeed

/-!
# G-4 — the seed reading bridge: compared side components of window sections

The `hfib`-side of the universal seed (worksheet §1.5, I-0247 step (c)): the compared
chart components of relative theta window sections are the chart components of the
fibre window sections (the G-2 crux triangle in the side-uniform
`relPinnedSectionsMap`/`relThetaResSide` spelling), and a nonzero fibre window vector
has nonzero compared side component on any nonempty pinned chart — exactly the
nonvanishing clause `ThetaGeneratorSeed.isGenerator_of_fibre_ne_zero` consumes.

* `relThetaSections_eq_zero_of_relThetaResSide_eq_zero` — **the component crossing**
  on the integral fibre curve: a global theta section with vanishing side component on
  a nonempty pinned chart is zero (the reading is the germ at `η` of a component, `η`
  lies in every nonempty open, and the theta cocycle matches the components);
* `relPinnedSectionsMap_relThetaResSide_windowEquiv` — **the compared-side triangle**:
  the fibre comparison of the side component of `relThetaWindowEquiv x` is the side
  component of `relThetaWindowEquiv (windowCompare x)` (the G-2 crux triangle
  `resHom_relThetaWindowEquiv_cancelBaseChange_fst/snd`, side-uniform);
* `relPinnedSectionsMap_relThetaResSide_ne_zero` — **the nonvanishing bridge**: if the
  fibre comparison of a window vector is nonzero, its compared side component is
  nonzero on any nonempty pinned chart — the seed's `hfib` clause at each `κ(q)`.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

/-! ## The component crossing on the integral fibre curve -/

section Crossing

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]
variable (a : ℕ)
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- (Implementation) Germs commute with `resHom`. -/
private lemma germ_resHom_read {X : Scheme.{u}} {W V : X.Opens} (h : W ≤ V) (z : X)
    (hz : z ∈ W) (t : Γ(X, V)) :
    (X.presheaf.germ W z hz).hom (X.resHom h t)
      = (X.presheaf.germ V z (h hz)).hom t :=
  X.presheaf.germ_res_apply (homOfLE h) z hz t

/-- (Implementation) A nonbottom open of the fibre curve contains the generic point. -/
private lemma genericPoint_mem_of_ne_bot {X : Scheme.{u}} [IsIntegral X]
    {V : X.Opens} (hV : V ≠ ⊥) : genericPoint X ∈ V :=
  Scheme.genericPoint_mem_of_nonempty (Set.nonempty_iff_ne_empty.mpr fun h =>
    hV (TopologicalSpace.Opens.ext (h.trans (TopologicalSpace.Opens.coe_bot).symm)))

set_option maxHeartbeats 800000 in
-- mixed `relCurve`/product defeq checks at the fibre germ computations are heavy
set_option synthInstance.maxHeartbeats 400000 in
/-- **The component crossing** on the integral fibre curve: a global theta section
whose side component vanishes on a nonempty pinned chart is zero.  The reading is the
germ at `η` of the component of the chart containing `η`; `η` lies in every nonempty
open, and on the (nonempty) chart overlap the components match through the theta
cocycle unit, so the vanishing side kills the reading. -/
theorem relThetaSections_eq_zero_of_relThetaResSide_eq_zero (b : Bool)
    (hb : relPinnedChart C K π b ≠ ⊥) {s : relThetaSections C K π a}
    (h0 : relThetaResSide a b le_rfl s = 0) : s = 0 := by
  -- the germ at `η` of the side component vanishes, restricted anywhere below the side
  have hread : thetaFieldRead C K π a s = 0 := by
    by_cases hη : genericPoint (relCurve C K) ∈ (relCover C K (fiberTwoCover π)).V₀
    · rw [thetaFieldRead_eq_germ_fst C K π a hη s]
      cases b with
      | false =>
        -- the reading is the germ of the vanishing side component itself
        have h1 : ((relCurve C K).presheaf.germ
            (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₀) (genericPoint (relCurve C K))
            ⟨trivial, hη⟩).hom s.val.1
            = ((relCurve C K).presheaf.germ (relPinnedChart C K π false)
                (genericPoint (relCurve C K)) hη).hom
              (relThetaResSide a false le_rfl s) := by
          rw [relThetaResSide_false]
          exact (germ_resHom_read (le_inf le_top le_rfl) _ hη s.val.1).symm
        rw [h1, h0, map_zero]
      | true =>
        -- cross the overlap: the chart-0 component is the unit times the vanishing side
        have hη₁ : genericPoint (relCurve C K) ∈ relPinnedChart C K π true :=
          genericPoint_mem_of_ne_bot hb
        have hηW : genericPoint (relCurve C K)
            ∈ relPinnedChart C K π false ⊓ relPinnedChart C K π true := ⟨hη, hη₁⟩
        have hmatch := relThetaResSide_matching a false true
          (le_rfl : relPinnedChart C K π false ⊓ relPinnedChart C K π true ≤ _) s
        have h2 : relThetaResSide a true
            ((le_rfl : relPinnedChart C K π false ⊓ relPinnedChart C K π true
              ≤ _).trans inf_le_right) s = 0 := by
          rw [← resHom_relThetaResSide a true le_rfl inf_le_right s, h0, map_zero]
        have h3 : relThetaResSide a false
            ((le_rfl : relPinnedChart C K π false ⊓ relPinnedChart C K π true
              ≤ _).trans inf_le_left) s = 0 := by
          rw [hmatch, h2, mul_zero]
        have h4 : ((relCurve C K).presheaf.germ
            (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₀) (genericPoint (relCurve C K))
            ⟨trivial, hη⟩).hom s.val.1
            = ((relCurve C K).presheaf.germ
                (relPinnedChart C K π false ⊓ relPinnedChart C K π true)
                (genericPoint (relCurve C K)) hηW).hom
              (relThetaResSide a false
                ((le_rfl : relPinnedChart C K π false ⊓ relPinnedChart C K π true
                  ≤ _).trans inf_le_left) s) := by
          rw [relThetaResSide_false]
          exact (germ_resHom_read (le_inf le_top (le_rfl.trans inf_le_left)) _ hηW
            s.val.1).symm
        rw [h4, h3, map_zero]
    · rw [thetaFieldRead_eq_germ_snd C K π a hη s]
      have hη₁ : genericPoint (relCurve C K) ∈ (relCover C K (fiberTwoCover π)).V₁ :=
        mem_V₁_of_notMem_V₀ C K π hη
      cases b with
      | true =>
        have h1 : ((relCurve C K).presheaf.germ
            (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₁) (genericPoint (relCurve C K))
            ⟨trivial, hη₁⟩).hom s.val.2
            = ((relCurve C K).presheaf.germ (relPinnedChart C K π true)
                (genericPoint (relCurve C K)) hη₁).hom
              (relThetaResSide a true le_rfl s) := by
          rw [relThetaResSide_true]
          exact (germ_resHom_read (le_inf le_top le_rfl) _ hη₁ s.val.2).symm
        rw [h1, h0, map_zero]
      | false =>
        have hη₀ : genericPoint (relCurve C K) ∈ relPinnedChart C K π false :=
          genericPoint_mem_of_ne_bot hb
        have hηW : genericPoint (relCurve C K)
            ∈ relPinnedChart C K π true ⊓ relPinnedChart C K π false := ⟨hη₁, hη₀⟩
        have hmatch := relThetaResSide_matching a true false
          (le_rfl : relPinnedChart C K π true ⊓ relPinnedChart C K π false ≤ _) s
        have h2 : relThetaResSide a false
            ((le_rfl : relPinnedChart C K π true ⊓ relPinnedChart C K π false
              ≤ _).trans inf_le_right) s = 0 := by
          rw [← resHom_relThetaResSide a false le_rfl inf_le_right s, h0, map_zero]
        have h3 : relThetaResSide a true
            ((le_rfl : relPinnedChart C K π true ⊓ relPinnedChart C K π false
              ≤ _).trans inf_le_left) s = 0 := by
          rw [hmatch, h2, mul_zero]
        have h4 : ((relCurve C K).presheaf.germ
            (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₁) (genericPoint (relCurve C K))
            ⟨trivial, hη₁⟩).hom s.val.2
            = ((relCurve C K).presheaf.germ
                (relPinnedChart C K π true ⊓ relPinnedChart C K π false)
                (genericPoint (relCurve C K)) hηW).hom
              (relThetaResSide a true
                ((le_rfl : relPinnedChart C K π true ⊓ relPinnedChart C K π false
                  ≤ _).trans inf_le_left) s) := by
          rw [relThetaResSide_true]
          exact (germ_resHom_read (le_inf le_top (le_rfl.trans inf_le_left)) _ hηW
            s.val.2).symm
        rw [h4, h3, map_zero]
  exact thetaFieldRead_injective C K π a (by rw [hread, map_zero])

end Crossing

/-! ## The compared-side triangle and the nonvanishing bridge -/

section Bridge

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (K : Type u) [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance instOverCleftSeedRead : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable (a : ℕ)
variable (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)

set_option maxHeartbeats 800000 in
-- the G-2 crux triangle crosses the mixed `relCurve`/product spellings
set_option synthInstance.maxHeartbeats 400000 in
set_option linter.unusedSectionVars false in
/-- **The compared-side triangle** (the G-2 crux, side-uniform): the fibre comparison
of the side component of a relative window section is the side component of the fibre
window section of the compared vector. -/
theorem relPinnedSectionsMap_relThetaResSide_windowEquiv (b : Bool)
    (x : R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) :
    relPinnedSectionsMap C R K π b
        (relThetaResSide a b le_rfl (relThetaWindowEquiv C R π a hH1 x))
      = relThetaResSide a b le_rfl
          (relThetaWindowEquiv C K π a hH1 (windowCompare R K x)) := by
  rw [windowCompare_eq_cancelBaseChange]
  cases b with
  | false =>
    exact (resHom_relThetaWindowEquiv_cancelBaseChange_fst C R K π a hH1 x).symm
  | true =>
    exact (resHom_relThetaWindowEquiv_cancelBaseChange_snd C R K π a hH1 x).symm

variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

set_option maxHeartbeats 800000 in
-- the G-2 crux triangle crosses the mixed `relCurve`/product spellings
set_option synthInstance.maxHeartbeats 400000 in
set_option linter.unusedSectionVars false in
/-- **The nonvanishing bridge** (the seed's `hfib` clause at `κ(q)`): a window vector
with nonzero fibre comparison has nonzero compared side component on any nonempty
pinned chart of the fibre curve. -/
theorem relPinnedSectionsMap_relThetaResSide_ne_zero (b : Bool)
    {x : R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)}
    (hx : windowCompare R K x ≠ 0) (hb : relPinnedChart C K π b ≠ ⊥) :
    relPinnedSectionsMap C R K π b
        (relThetaResSide a b le_rfl (relThetaWindowEquiv C R π a hH1 x)) ≠ 0 := by
  rw [relPinnedSectionsMap_relThetaResSide_windowEquiv C R K π a hH1 b x]
  intro h0
  refine hx ((relThetaWindowEquiv C K π a hH1).injective ?_)
  rw [map_zero]
  exact relThetaSections_eq_zero_of_relThetaResSide_eq_zero C K π a b hb h0

end Bridge

end AlgebraicGeometry
