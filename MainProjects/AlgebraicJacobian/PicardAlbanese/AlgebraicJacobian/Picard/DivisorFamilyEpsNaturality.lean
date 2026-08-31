/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyWindowTriangle
import AlgebraicJacobian.Picard.DivisorThetaFibreData
import AlgebraicJacobian.Picard.DivSchemeEps
import AlgebraicJacobian.Picard.DivCarveKit

/-!
# G-2 (DD-4 Task 7) — ε-naturality: the base-change square of the window pair

The keystone `divFamEps_mapAlg` (`informal/spec-w4-gates.md` §G-2): along an arbitrary
test change `R → R'` (`[Algebra R R'] [IsScalarTower k R R']`, the `DivFam.mapAlg`
instance form), the embedding `ε` of the divisor functor commutes with base change,

`divFamEps hπ g (DivFam.mapAlg R' g F) = (windowBaseChange R' ε.1, windowBaseChange R' ε.2)`

where **`windowBaseChange R' N := Submodule.map (cancelBaseChange k R R' R' H) (N.baseChange R')`
is the ONE recorded orientation seam** (spec-dd-3 §0 discipline): it is definitionally the
right-hand side of `ker_baseChangeMkQ_eq_map_baseChange` (`Picard/DivCarveKit.lean`), so
the DDR-9/G-5 consumers (`informal/w4-g5-worksheet.md` §2 step (e), §3.2 W3, §4) convert
mathlib's `Module.Grassmannian.map`-kernels to it with no transport lemma.

* `AlgebraicGeometry.windowBaseChange` — the pinned pushforward of a window submodule.
* `windowBaseChange_divisorWindow_le` — **the `⊇` (formal) half**: equations pull back to
  equations; the compared window vector's germs land in the pulled stalk ideals, by the
  crux triangle (`resHom_relThetaWindowEquiv_cancelBaseChange_fst/snd`,
  `Picard/DivisorFamilyWindowBaseChange.lean`) and germ/`stalkMap` transport.
* `windowBaseChangeGr` — the pushed-forward window as a Grassmannian point (the quotient
  clauses via `Module.Grassmannian.baseChangeMkQEquiv`).
* `divisorWindow_pulledEquations_eq` — **the `⊆` (certificate) half**: both windows have
  finite projective rank-`g` quotients (the G-1 keystones
  `IsCertified.thetaGluedEval_surjective` + the (c2)-twisted clauses, transported to `R'`
  by `isCertified_pullback`), so the containment is an equality by the DDR-5 rank engine
  (`divisorWindow_eq_of_le_of_isCertified`, `Picard/DivSchemeEps.lean`).  NO Noetherian
  hypothesis on `R'` (nor on `R`).
* `divFamEps_mapAlg` — **the keystone**; `divFamEps_mapAlg_awayMap` — the localization
  corollary at a basic open, in `DivFamZar`'s pinned `IsLocalization.Away` instance pack.

The curve normalization hypotheses `hO : h⁰(𝒪) = 1` and `hχ : χ(𝒪) = 1 − g` are the
standing genus inputs of the G-1 keystones (`Picard/DivisorThetaFibreData.lean`), threaded
here verbatim.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## The pinned window pushforward -/

section WindowBaseChange

variable {k : Type u} [Field k]
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable {H : Type u} [AddCommGroup H] [Module k H]

/-- **The window pushforward along `R → R'`** (the G-2 orientation seam, recorded once):
the `cancelBaseChange`-image of the scalar extension of the window submodule.  This is
definitionally the right-hand side of `ker_baseChangeMkQ_eq_map_baseChange`
(`Picard/DivCarveKit.lean`), i.e. the submodule of mathlib's
`Module.Grassmannian.map`. -/
noncomputable def windowBaseChange (N : Submodule R (TensorProduct k R H)) :
    Submodule R' (TensorProduct k R' H) :=
  Submodule.map
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' H).toLinearMap
    (N.baseChange R')

variable {R'}

/-- The elementwise generator of the window pushforward: the compared ambient vector
`cancelBaseChange (1 ⊗ₜ x)` of a window vector `x` lies in the pushed window. -/
lemma cancelBaseChange_one_tmul_mem_windowBaseChange {N : Submodule R (TensorProduct k R H)}
    {x : TensorProduct k R H} (hx : x ∈ N) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' H (1 ⊗ₜ x)
      ∈ windowBaseChange R' N :=
  Submodule.mem_map_of_mem (Submodule.tmul_mem_baseChange_of_mem 1 hx)

/-- The le-criterion for the window pushforward: it suffices to test the compared
generators. -/
lemma windowBaseChange_le_iff {N : Submodule R (TensorProduct k R H)}
    {P : Submodule R' (TensorProduct k R' H)} :
    windowBaseChange R' N ≤ P ↔ ∀ x ∈ N,
      TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' H (1 ⊗ₜ x) ∈ P := by
  constructor
  · exact fun h x hx => h (cancelBaseChange_one_tmul_mem_windowBaseChange hx)
  · intro h
    rw [windowBaseChange, Submodule.map_le_iff_le_comap, Submodule.baseChange_eq_span,
      Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    have h1 : (TensorProduct.mk R R' (TensorProduct k R H) 1) m = (1 : R') ⊗ₜ[R] m := rfl
    rw [SetLike.mem_coe, Submodule.mem_comap, h1]
    exact h m hm

variable (R')

/-- **The window pushforward is the kernel of the base-changed quotient map** — the
`Module.Grassmannian.map` spelling, `ker_baseChangeMkQ_eq_map_baseChange` reversed.  The
projective-quotient hypothesis is the engine-fed certificate clause. -/
lemma windowBaseChange_eq_ker_baseChangeMkQ (N : Submodule R (TensorProduct k R H))
    [Module.Projective R (TensorProduct k R H ⧸ N)] :
    windowBaseChange R' N
      = LinearMap.ker (Module.Grassmannian.baseChangeMkQ R' N) :=
  (Grassmannian.ker_baseChangeMkQ_eq_map_baseChange R' N).symm

/-- **The pushed-forward window as a Grassmannian point**: given the finite projective
rank-`n` certificate for the quotient over `R`, the pushed window is a point of the
affine Grassmannian functor over `R'` (quotient clauses through
`Module.Grassmannian.baseChangeMkQEquiv` — the same fields as mathlib's
`Module.Grassmannian.map`, but on the ambient instance tower `[Algebra R R']`
`[IsScalarTower k R R']` rather than a `toAlgebra` transport). -/
noncomputable def windowBaseChangeGr (N : Submodule R (TensorProduct k R H)) (n : ℕ)
    [Module.Finite R (TensorProduct k R H ⧸ N)]
    [Module.Projective R (TensorProduct k R H ⧸ N)]
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (TensorProduct k R H ⧸ N) p = n) :
    Grassmannian.grFunctorAff k H n R' :=
  haveI e : (TensorProduct k R' H ⧸ windowBaseChange R' N) ≃ₗ[R']
      R' ⊗[R] (TensorProduct k R H ⧸ N) :=
    (Submodule.quotEquivOfEq _ _ (windowBaseChange_eq_ker_baseChangeMkQ R' N)).trans
      (Module.Grassmannian.baseChangeMkQEquiv N)
  { toSubmodule := windowBaseChange R' N
    finite_quotient := Module.Finite.equiv e.symm
    projective_quotient := Module.Projective.of_equiv e.symm
    rankAtStalk_eq := fun p => by
      rw [congrFun (Module.rankAtStalk_eq_of_equiv e) p,
        Module.rankAtStalk_baseChange]
      exact hrank _ }

@[simp]
lemma windowBaseChangeGr_coe (N : Submodule R (TensorProduct k R H)) (n : ℕ)
    [Module.Finite R (TensorProduct k R H ⧸ N)]
    [Module.Projective R (TensorProduct k R H ⧸ N)]
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (TensorProduct k R H ⧸ N) p = n) :
    (windowBaseChangeGr R' N n hrank).toSubmodule = windowBaseChange R' N :=
  rfl

end WindowBaseChange

/-! ## Germ transport along the relative-curve comparison -/

section GermTransport

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']

/-- (Implementation) The germ of an `appLE`-compared section is the stalk image of the
germ. -/
private lemma germ_appLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {W : X.Opens} (e : W ≤ f ⁻¹ᵁ U) (s : Γ(Y, U)) (z : X) (hz : z ∈ W) :
    (X.presheaf.germ W z hz).hom ((f.appLE U W e).hom s)
      = (f.stalkMap z).hom ((Y.presheaf.germ U (f.base z) (e hz)).hom s) := by
  have h1 : (f.appLE U W e).hom s
      = (X.presheaf.map (homOfLE e).op).hom ((f.app U).hom s) := rfl
  rw [h1, TopCat.Presheaf.germ_res_apply]
  exact (f.germ_stalkMap_apply U z (e hz) s).symm

/-- **The stalk ideal of the pulled system absorbs stalk images** (the `⊇`-half
transport): the `stalkMap`-image of the stalk ideal of `d` at the base point lies in
the stalk ideal of the pulled system. -/
lemma stalkMap_mem_stalkIdeal_pullback {d : (relCurve C R).LocalEquations}
    (hreg : ∀ (y z : relCurve C R')
      (hz : z ∈ (d.cover.pullback (relCurveMap C R R')).opens y),
      ((relCurve C R').presheaf.germ ((d.cover.pullback (relCurveMap C R R')).opens y)
        z hz).hom (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d y)
        ∈ nonZeroDivisors ((relCurve C R').presheaf.stalk z))
    (z : relCurve C R')
    {α : (relCurve C R).presheaf.stalk ((relCurveMap C R R').base z)}
    (hα : α ∈ d.stalkIdeal ((relCurveMap C R R').base z)) :
    ((relCurveMap C R R').stalkMap z).hom α
      ∈ (d.pullback (relCurveMap C R R') hreg).stalkIdeal z := by
  -- the germ of the pulled tautological equation is the stalk image of the germ
  have hzmem : z ∈ (d.cover.pullback (relCurveMap C R R')).opens z :=
    (d.cover.pullback (relCurveMap C R R')).mem_opens z
  have hgen : ((relCurve C R').presheaf.germ
      ((d.cover.pullback (relCurveMap C R R')).opens z) z hzmem).hom
      ((d.pullback (relCurveMap C R R') hreg).eqn z)
      = ((relCurveMap C R R').stalkMap z).hom
          (((relCurve C R).presheaf.germ (d.cover.opens ((relCurveMap C R R').base z))
            ((relCurveMap C R R').base z)
            (d.cover.mem_opens ((relCurveMap C R R').base z))).hom
            (d.eqn ((relCurveMap C R R').base z))) := by
    exact germ_appLE_apply (relCurveMap C R R') le_rfl
      (d.eqn ((relCurveMap C R R').base z)) z hzmem
  -- decompose `α` over the generator of the stalk ideal
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hα
  rw [hc, map_mul]
  refine Ideal.mul_mem_right _ _ ?_
  rw [Scheme.LocalEquations.stalkIdeal, ← hgen]
  exact Ideal.subset_span rfl

/-- (Implementation) Membership in a base-changed chart transports along the
relative-curve comparison. -/
private lemma relCurveMap_base_mem_preimage {V : C.left.Opens} {z : relCurve C R'}
    (hz : z ∈ (fst C (overSpec k R')).left ⁻¹ᵁ V) :
    (relCurveMap C R R').base z ∈ (fst C (overSpec k R)).left ⁻¹ᵁ V := by
  have h : z ∈ relCurveMap C R R' ⁻¹ᵁ ((fst C (overSpec k R)).left ⁻¹ᵁ V) := by
    rw [relCurveMap_preimage]
    exact hz
  exact h

end GermTransport

/-! ## The two halves and the keystone -/

section Keystone

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance instOverCleftEpsNat : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [IsDominant π] [IsIntegral C.left]
variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

variable (a : ℕ)

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
set_option linter.unusedSectionVars false in
/-- **The `⊇` (formal) half of G-2**: the pushed-forward window submodule lands inside
the window of the pulled-back system — equations pull back to equations.  Elementwise:
the compared window vector's chart components have all germs in the pulled stalk
ideals, by the crux triangle and germ/`stalkMap` transport. -/
theorem windowBaseChange_divisorWindow_le {d : (relCurve C R).LocalEquations}
    (hreg : ∀ (y z : relCurve C R')
      (hz : z ∈ (d.cover.pullback (relCurveMap C R R')).opens y),
      ((relCurve C R').presheaf.germ ((d.cover.pullback (relCurveMap C R R')).opens y)
        z hz).hom (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d y)
        ∈ nonZeroDivisors ((relCurve C R').presheaf.stalk z))
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    windowBaseChange R' (divisorWindow d hH1)
      ≤ divisorWindow (d.pullback (relCurveMap C R R') hreg) hH1 := by
  rw [windowBaseChange_le_iff]
  intro x hx
  rw [mem_divisorWindow_iff] at hx ⊢
  obtain ⟨h₀, h₁⟩ := hx
  constructor
  · -- chart-0 germs
    intro z hz
    -- the germ of the component is the germ of its chart restriction
    have hres : ((relCurve C R').presheaf.germ
        (⊤ ⊓ (relCover C R' (fiberTwoCover π)).V₀) z hz).hom
        ((relThetaWindowEquiv C R' π a hH1
          (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _
            (1 ⊗ₜ x))).val.1)
        = ((relCurve C R').presheaf.germ
            ((relCover C R' (fiberTwoCover π)).V₀) z hz.2).hom
            ((relCurve C R').resHom (le_inf le_top le_rfl)
              ((relThetaWindowEquiv C R' π a hH1
                (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _
                  (1 ⊗ₜ x))).val.1)) :=
      (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    rw [hres, resHom_relThetaWindowEquiv_cancelBaseChange_fst C R R' π a hH1 x]
    have hgerm : ((relCurve C R').presheaf.germ
        ((relCover C R' (fiberTwoCover π)).V₀) z hz.2).hom
        ((relSectionsMap C R R' (fiberTwoCover π).V₀)
          ((relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R π a hH1 x).val.1)))
        = ((relCurveMap C R R').stalkMap z).hom
            (((relCurve C R).presheaf.germ
              ((fst C (overSpec k R)).left ⁻¹ᵁ (fiberTwoCover π).V₀)
              ((relCurveMap C R R').base z)
              (relCurveMap_base_mem_preimage C R' hz.2)).hom
              ((relCurve C R).resHom (le_inf le_top le_rfl)
                ((relThetaWindowEquiv C R π a hH1 x).val.1))) :=
      germ_appLE_apply (relCurveMap C R R')
        (le_of_eq (relCurveMap_preimage C R R' (fiberTwoCover π).V₀).symm) _ z hz.2
    rw [hgerm]
    -- the base-point germ is in the stalk ideal of `d`
    have hbase : ((relCurveMap C R R').base z)
        ∈ (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ : (relCurve C R).Opens) :=
      ⟨trivial, relCurveMap_base_mem_preimage C R' hz.2⟩
    have hmem : ((relCurve C R).presheaf.germ
        ((fst C (overSpec k R)).left ⁻¹ᵁ (fiberTwoCover π).V₀)
        ((relCurveMap C R R').base z)
        (relCurveMap_base_mem_preimage C R' hz.2)).hom
        ((relCurve C R).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C R π a hH1 x).val.1))
        ∈ d.stalkIdeal ((relCurveMap C R R').base z) := by
      have hswap : ((relCurve C R).presheaf.germ
          ((fst C (overSpec k R)).left ⁻¹ᵁ (fiberTwoCover π).V₀)
          ((relCurveMap C R R').base z)
          (relCurveMap_base_mem_preimage C R' hz.2)).hom
          ((relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R π a hH1 x).val.1))
          = ((relCurve C R).presheaf.germ
              (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀)
              ((relCurveMap C R R').base z) hbase).hom
              ((relThetaWindowEquiv C R π a hH1 x).val.1) :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      rw [hswap]
      exact h₀ _ hbase
    exact stalkMap_mem_stalkIdeal_pullback C R' hreg z hmem
  · -- chart-1 germs (mirror)
    intro z hz
    have hres : ((relCurve C R').presheaf.germ
        (⊤ ⊓ (relCover C R' (fiberTwoCover π)).V₁) z hz).hom
        ((relThetaWindowEquiv C R' π a hH1
          (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _
            (1 ⊗ₜ x))).val.2)
        = ((relCurve C R').presheaf.germ
            ((relCover C R' (fiberTwoCover π)).V₁) z hz.2).hom
            ((relCurve C R').resHom (le_inf le_top le_rfl)
              ((relThetaWindowEquiv C R' π a hH1
                (TensorProduct.AlgebraTensorModule.cancelBaseChange k R R' R' _
                  (1 ⊗ₜ x))).val.2)) :=
      (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    rw [hres, resHom_relThetaWindowEquiv_cancelBaseChange_snd C R R' π a hH1 x]
    have hgerm : ((relCurve C R').presheaf.germ
        ((relCover C R' (fiberTwoCover π)).V₁) z hz.2).hom
        ((relSectionsMap C R R' (fiberTwoCover π).V₁)
          ((relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R π a hH1 x).val.2)))
        = ((relCurveMap C R R').stalkMap z).hom
            (((relCurve C R).presheaf.germ
              ((fst C (overSpec k R)).left ⁻¹ᵁ (fiberTwoCover π).V₁)
              ((relCurveMap C R R').base z)
              (relCurveMap_base_mem_preimage C R' hz.2)).hom
              ((relCurve C R).resHom (le_inf le_top le_rfl)
                ((relThetaWindowEquiv C R π a hH1 x).val.2))) :=
      germ_appLE_apply (relCurveMap C R R')
        (le_of_eq (relCurveMap_preimage C R R' (fiberTwoCover π).V₁).symm) _ z hz.2
    rw [hgerm]
    have hbase : ((relCurveMap C R R').base z)
        ∈ (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁ : (relCurve C R).Opens) :=
      ⟨trivial, relCurveMap_base_mem_preimage C R' hz.2⟩
    have hmem : ((relCurve C R).presheaf.germ
        ((fst C (overSpec k R)).left ⁻¹ᵁ (fiberTwoCover π).V₁)
        ((relCurveMap C R R').base z)
        (relCurveMap_base_mem_preimage C R' hz.2)).hom
        ((relCurve C R).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C R π a hH1 x).val.2))
        ∈ d.stalkIdeal ((relCurveMap C R R').base z) := by
      have hswap : ((relCurve C R).presheaf.germ
          ((fst C (overSpec k R)).left ⁻¹ᵁ (fiberTwoCover π).V₁)
          ((relCurveMap C R R').base z)
          (relCurveMap_base_mem_preimage C R' hz.2)).hom
          ((relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R π a hH1 x).val.2))
          = ((relCurve C R).presheaf.germ
              (⊤ ⊓ (relCover C R (fiberTwoCover π)).V₁)
              ((relCurveMap C R R').base z) hbase).hom
              ((relThetaWindowEquiv C R π a hH1 x).val.2) :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      rw [hswap]
      exact h₁ _ hbase
    exact stalkMap_mem_stalkIdeal_pullback C R' hreg z hmem

variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
/-- **The two halves assembled at one window** (adaptation form): for a certified
adaptation over `R` and a ledger window `a ≥ M`, the window of the pulled-back system
IS the pushed-forward window.  `⊇` is `windowBaseChange_divisorWindow_le`; `⊆` is the
DDR-5 rank engine on the two finite projective rank-`g` quotients, with all certificate
slots discharged by the G-1 keystones over `R` and the transported certificate over
`R'`.  No Noetherian hypotheses. -/
theorem divisorWindow_pulledEquations_eq {d : (relCurve C R).LocalEquations}
    {A : DivisorAdaptation C R π d} {g : ℕ} (hc : A.IsCertified g)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hMa : windowM_choice π hπ g ≤ a) :
    divisorWindow (A.pulledEquations R' hc.projective_colength) ha1
      = windowBaseChange R' (divisorWindow d ha1) := by
  -- the `R`-level window quotient is finite projective of rank `g`
  have hsurjR : Function.Surjective (A.thetaGluedEval a) :=
    hc.thetaGluedEval_surjective (C := C) (π := π) hπ hO hχ ha1 hMa
  haveI hfinR : Module.Finite R
      ((TensorProduct k R
          ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) :=
    haveI := hc.finite_thetaGlued a
    Module.Finite.equiv (windowQuotEquiv A ha1 hsurjR).symm
  haveI hprojR : Module.Projective R
      ((TensorProduct k R
          ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) :=
    haveI := hc.projective_thetaGlued a
    Module.Projective.of_equiv (windowQuotEquiv A ha1 hsurjR).symm
  have hrankR : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk
        ((TensorProduct k R
            ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d ha1) p = g := fun p => by
    rw [congrFun (Module.rankAtStalk_eq_of_equiv (windowQuotEquiv A ha1 hsurjR)) p]
    exact hc.rankAtStalk_thetaGlued a p
  -- the transported certificate over `R'` and its surjectivity
  have hc' : (A.pullback R' hc.projective_colength).IsCertified g :=
    A.isCertified_pullback R' hc
  have hsurj' : Function.Surjective
      ((A.pullback R' hc.projective_colength).thetaGluedEval a) :=
    hc'.thetaGluedEval_surjective (C := C) (π := π) hπ hO hχ ha1 hMa
  -- the rank engine closes the containment
  exact divisorWindow_eq_of_le_of_isCertified
    (A.pullback R' hc.projective_colength) hc' ha1
    (windowBaseChangeGr R' (divisorWindow d ha1) g hrankR) hsurj'
    (windowBaseChange_divisorWindow_le C R' π a
      (A.germ_pullbackEqn_mem_nonZeroDivisors R' hc.projective_colength) ha1)

variable (g : ℕ)

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
/-- **G-2 keystone — ε-naturality** (`informal/spec-w4-gates.md` §G-2, DD-4 Task 7):
along an arbitrary test change `R → R'`, the embedding `ε` of the divisor functor
commutes with base change — the window pair of the pulled-back family is the pinned
`windowBaseChange`-pushforward of the window pair.  `hO`/`hχ` are the standing genus
normalization of the curve (the G-1 inputs); no Noetherian hypotheses. -/
theorem divFamEps_mapAlg
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (F : DivFam C R π g) :
    divFamEps hπ g (DivFam.mapAlg R' g F)
      = (windowBaseChange R' (divFamEps hπ g F).1,
         windowBaseChange R' (divFamEps hπ g F).2) := by
  induction F using Quotient.inductionOn with
  | h G =>
    refine Prod.ext ?_ ?_
    · exact divisorWindow_pulledEquations_eq C R' π (windowM_choice π hπ g) hπ
        G.certified hO hχ (relThetaPairH1_windowM C π hπ g) le_rfl
    · exact divisorWindow_pulledEquations_eq C R' π
        (windowM_choice π hπ g + windowS_choice π hπ g) hπ
        G.certified hO hχ (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)

/-- **G-2 localization corollary at a basic open** (the DDR-9/G-5 consumer shape,
`informal/w4-g5-worksheet.md` §2 step (e)): ε-naturality along `R → S` for the pinned
`IsLocalization.Away` instance pack of `DivFamZar`.  A restatement of
`divFamEps_mapAlg` — the general theorem carries no hypotheses on the target ring, so
the localization instance is not consumed; it is recorded to pin the consumer
spelling. -/
theorem divFamEps_mapAlg_awayMap (f : R) (S : Type u) [CommRing S] [Algebra k S]
    [Algebra R S] [IsScalarTower k R S] [IsLocalization.Away f S]
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (F : DivFam C R π g) :
    divFamEps hπ g (DivFam.mapAlg S g F)
      = (windowBaseChange S (divFamEps hπ g F).1,
         windowBaseChange S (divFamEps hπ g F).2) :=
  divFamEps_mapAlg C S π hπ g hO hχ F

end Keystone

end AlgebraicGeometry
