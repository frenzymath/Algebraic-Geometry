/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RelThetaTransport

/-!
# DD-4 base-field-transport sub-brick — the section collapse at test ring `k`

The linear-algebra core of the M–L seam of I-0175.  At test ring `R = k` the section base
change `relSectionsBaseChange C k` degenerates to a `k`-linear equivalence
`sectionsCollapse : Γ(C.left, V) ≃ₗ[k] Γ(relCurve C k, V_k)`, computed as the section
pullback `relPullbackSection C k` (an isomorphism because the first projection
`relCurve C k ⟶ C.left` is an iso).  It is a ring isomorphism commuting with restriction,
the arrow through which the twisted section modules of `thetaTwistSheaf π n` (on `C.left`)
and `relThetaTwistSheaf C k π n` (on `relCurve C k`) are identified.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Over.sectionsAlgebra

section SectionsCollapse

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

/-- **The section collapse at test ring `k`**: the `k`-linear equivalence
`Γ(C.left, V) ≃ₗ[k] Γ(relCurve C k, V_k)`, the section base change `relSectionsBaseChange
C k` precomposed with the tensor-unit cancellation `M ≃ k ⊗[k] M`.  Concretely it is the
section pullback `relPullbackSection C k` (`sectionsCollapse_apply`). -/
noncomputable def sectionsCollapse (V : C.left.Opens)
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) :
    Γ(C.left, V) ≃ₗ[k] Γ(relCurve C k, (fst C (overSpec k k)).left ⁻¹ᵁ V) :=
  (TensorProduct.lid k Γ(C.left, V)).symm.trans (relSectionsBaseChange C k hV hV')

/-- The section collapse is the section pullback along the first projection. -/
lemma sectionsCollapse_apply (V : C.left.Opens)
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (s : Γ(C.left, V)) :
    sectionsCollapse C V hV hV' s = relPullbackSection C k V s := by
  rw [sectionsCollapse, LinearEquiv.trans_apply, TensorProduct.lid_symm_apply,
    relSectionsBaseChange_tmul]
  rw [map_one, one_mul]

/-- **Pullback of sections to the relative curve commutes with restriction** (the
`RelativeSectionsLinear`-level fact, re-derived here to avoid the `Challenge` import of
`H1BaseFieldInvariance`): restricting on the curve then pulling back agrees with pulling
back then restricting on the relative curve. -/
lemma relPullbackSection_resHom' {W V : C.left.Opens} (hWV : W ≤ V) (s : Γ(C.left, V)) :
    relPullbackSection C k W (C.left.resHom hWV s) =
      (relCurve C k).resHom
        (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left hWV)
        (relPullbackSection C k V s) := by
  have h1 : C.left.presheaf.map (homOfLE hWV).op ≫
      (fst C (overSpec k k)).left.appLE W ((fst C (overSpec k k)).left ⁻¹ᵁ W) le_rfl =
      (fst C (overSpec k k)).left.appLE V ((fst C (overSpec k k)).left ⁻¹ᵁ W)
        (le_rfl.trans (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left hWV)) :=
    Scheme.Hom.map_appLE _ le_rfl (homOfLE hWV).op
  have h2 : (fst C (overSpec k k)).left.appLE V ((fst C (overSpec k k)).left ⁻¹ᵁ V)
        le_rfl ≫
      (relCurve C k).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left hWV)).op =
      (fst C (overSpec k k)).left.appLE V ((fst C (overSpec k k)).left ⁻¹ᵁ W)
        (le_rfl.trans (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left hWV)) :=
    Scheme.Hom.appLE_map _ le_rfl
      (homOfLE (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left hWV)).op
  exact (congr($(h1).hom s)).trans (congr($(h2).hom s)).symm

/-- Restriction along an equality of opens, as a `k`-linear equivalence (the two
restrictions along `U ≤ U'` and `U' ≤ U` are mutually inverse). -/
noncomputable def presheafCongr {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {U U' : X.Opens} (h : U = U') :
    Γ(X, U) ≃ₗ[k] Γ(X, U') :=
  LinearEquiv.ofLinear
    (secRes (X.moduleKSheaf k) (le_of_eq h.symm))
    (secRes (X.moduleKSheaf k) (le_of_eq h))
    (LinearMap.ext fun s => by
      change (secRes (X.moduleKSheaf k) (le_of_eq h.symm))
          ((secRes (X.moduleKSheaf k) (le_of_eq h)) s) = s
      rw [secRes_secRes, secRes_self])
    (LinearMap.ext fun s => by
      change (secRes (X.moduleKSheaf k) (le_of_eq h))
          ((secRes (X.moduleKSheaf k) (le_of_eq h.symm)) s) = s
      rw [secRes_secRes, secRes_self])

/-- Restriction into an open equal to the source cancels the open-equality transport. -/
lemma presheafCongr_resHom {X : Scheme.{u}} [X.Over (Spec (.of k))] {U U' V : X.Opens}
    (h : U = U') (h₁ : U ≤ V) (h₂ : U' ≤ V) (s : Γ(X, V)) :
    presheafCongr (k := k) h (X.resHom h₁ s) = X.resHom h₂ s := by
  rw [presheafCongr, LinearEquiv.ofLinear_apply]
  change X.resHom (le_of_eq h.symm) (X.resHom h₁ s) = X.resHom h₂ s
  rw [Scheme.resHom_resHom]

/-- The open-equality transport is the restriction ring map, hence multiplicative. -/
lemma presheafCongr_mul {X : Scheme.{u}} [X.Over (Spec (.of k))] {U U' : X.Opens}
    (h : U = U') (a b : Γ(X, U)) :
    presheafCongr (k := k) h (a * b) =
      presheafCongr (k := k) h a * presheafCongr (k := k) h b := by
  rw [presheafCongr, LinearEquiv.ofLinear_apply, LinearEquiv.ofLinear_apply,
    LinearEquiv.ofLinear_apply]
  change X.resHom (le_of_eq h.symm) (a * b) =
    X.resHom (le_of_eq h.symm) a * X.resHom (le_of_eq h.symm) b
  rw [map_mul]

/-- The section collapse is multiplicative (it is the section pullback). -/
lemma sectionsCollapse_mul (V : C.left.Opens)
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (a b : Γ(C.left, V)) :
    sectionsCollapse C V hV hV' (a * b) =
      sectionsCollapse C V hV hV' a * sectionsCollapse C V hV hV' b := by
  rw [sectionsCollapse_apply, sectionsCollapse_apply, sectionsCollapse_apply,
    relPullbackSection_mul]

end SectionsCollapse

/-! ## The twisted section modules collapse across the pinned charts -/

section TwistCollapse

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (π : C.left ⟶ P1 k) [IsFinite π] (n : ℕ)

noncomputable local instance (priority := 50) instOverCleftCore :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

noncomputable local instance instQcohThetaField₀' :
    Scheme.QcohOn (thetaTwistSheaf π n) (fiberChart₀ π) :=
  twistSheaf.instQcohOn₀ k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)

noncomputable local instance instQcohThetaField₁' :
    Scheme.QcohOn (thetaTwistSheaf π n) (fiberChart₁ π) :=
  twistSheaf.instQcohOn₁ k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)

attribute [local instance 10000] relCurve.instOver

/-- **Chart-0 collapse of twisted sections**: the field twisted sections of `𝒪(Θⁿ)` over
`V₀` are identified with the relative twisted sections over `V₀ᵏ`, through the two chart
trivializations and the section collapse. -/
noncomputable def twistCollapse₀ :
    ↥(twistSubmodule k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)
        (fiberChart₀ π)) ≃ₗ[k]
      ↥(twistSubmodule k (relCover C k (fiberTwoCover π)).V₀
        (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n)
        (relCover C k (fiberTwoCover π)).V₀) :=
  (twistTriv₀ k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) (le_refl _)).trans
    ((sectionsCollapse C (fiberChart₀ π)
        (isAffineOpen_preimage_chartOpen π 0).isCompact
        (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated).trans
      (twistTriv₀ k (relCover C k (fiberTwoCover π)).V₀
        (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n) (le_refl _)).symm)

/-- **Chart-1 collapse of twisted sections**. -/
noncomputable def twistCollapse₁ :
    ↥(twistSubmodule k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)
        (fiberChart₁ π)) ≃ₗ[k]
      ↥(twistSubmodule k (relCover C k (fiberTwoCover π)).V₀
        (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n)
        (relCover C k (fiberTwoCover π)).V₁) :=
  (twistTriv₁ k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) (le_refl _)).trans
    ((sectionsCollapse C (fiberChart₁ π)
        (isAffineOpen_preimage_chartOpen π 1).isCompact
        (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated).trans
      (twistTriv₁ k (relCover C k (fiberTwoCover π)).V₀
        (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n) (le_refl _)).symm)

/-- **Overlap collapse of twisted sections**: the overlap-term identification, whose
cokernel is the twisted `H¹`. -/
noncomputable def twistCollapseN :
    ↥(twistSubmodule k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)
        (fiberChart₀ π ⊓ fiberChart₁ π)) ≃ₗ[k]
      ↥(twistSubmodule k (relCover C k (fiberTwoCover π)).V₀
        (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n)
        ((relCover C k (fiberTwoCover π)).V₀ ⊓ (relCover C k (fiberTwoCover π)).V₁)) :=
  (twistTriv₀ k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) inf_le_left).trans
    ((sectionsCollapse C (fiberChart₀ π ⊓ fiberChart₁ π)
        (fiberTwoCover π).isAffineOpen_inf.isCompact
        (fiberTwoCover π).isAffineOpen_inf.isQuasiSeparated).trans
      ((@presheafCongr k _ (relCurve C k) (relCurve.instOver C k) _ _
          (relCover_inf C k (fiberTwoCover π)).symm).trans
        (twistTriv₀ k (relCover C k (fiberTwoCover π)).V₀
          (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n) inf_le_left).symm))

/-! ### Triv-naturality of the collapse maps -/

/-- Applying the chart-0 trivialization on the relative side to the chart-0 collapse is the
section collapse of the chart-0 trivialization on the field side. -/
lemma twistTriv₀_twistCollapse₀ (x) :
    twistTriv₀ k (relCover C k (fiberTwoCover π)).V₀ (relCover C k (fiberTwoCover π)).V₁
        (relThetaCocycle C k π n) (le_refl _) (twistCollapse₀ C π n x) =
      sectionsCollapse C (fiberChart₀ π)
        (isAffineOpen_preimage_chartOpen π 0).isCompact
        (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated
        (twistTriv₀ k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) (le_refl _) x) := by
  rw [twistCollapse₀]
  simp only [LinearEquiv.trans_apply]
  exact LinearEquiv.apply_symm_apply _ _

/-- Chart-1 analogue of `twistTriv₀_twistCollapse₀`. -/
lemma twistTriv₁_twistCollapse₁ (y) :
    twistTriv₁ k (relCover C k (fiberTwoCover π)).V₀ (relCover C k (fiberTwoCover π)).V₁
        (relThetaCocycle C k π n) (le_refl _) (twistCollapse₁ C π n y) =
      sectionsCollapse C (fiberChart₁ π)
        (isAffineOpen_preimage_chartOpen π 1).isCompact
        (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated
        (twistTriv₁ k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) (le_refl _) y) := by
  rw [twistCollapse₁]
  simp only [LinearEquiv.trans_apply]
  exact LinearEquiv.apply_symm_apply _ _

/-- Overlap analogue: through the chart-0 trivialization on the overlap. -/
lemma twistTriv₀_twistCollapseN (q) :
    twistTriv₀ k (relCover C k (fiberTwoCover π)).V₀ (relCover C k (fiberTwoCover π)).V₁
        (relThetaCocycle C k π n) inf_le_left (twistCollapseN C π n q) =
      (@presheafCongr k _ (relCurve C k) (relCurve.instOver C k) _ _
          (relCover_inf C k (fiberTwoCover π)).symm)
        (sectionsCollapse C (fiberChart₀ π ⊓ fiberChart₁ π)
          (fiberTwoCover π).isAffineOpen_inf.isCompact
          (fiberTwoCover π).isAffineOpen_inf.isQuasiSeparated
          (twistTriv₀ k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) inf_le_left q)) := by
  rw [twistCollapseN]
  simp only [LinearEquiv.trans_apply]
  exact LinearEquiv.apply_symm_apply _ _

/-- The section collapse commutes with restriction. -/
lemma sectionsCollapse_resHom {W V : C.left.Opens} (hWV : W ≤ V)
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left))
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (s : Γ(C.left, V)) :
    sectionsCollapse C W hW hW' (C.left.resHom hWV s) =
      (relCurve C k).resHom (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left hWV)
        (sectionsCollapse C V hV hV' s) := by
  rw [sectionsCollapse_apply, sectionsCollapse_apply, relPullbackSection_resHom']

/-- **The relative theta cocycle is the collapse of `thetaUnit π ^ n`**: the section value
of `relThetaCocycle C k π n` is the overlap collapse of the field-level cocycle. -/
lemma relThetaCocycle_val_eq :
    ((relThetaCocycle C k π n :
        Γ(relCurve C k, (relCover C k (fiberTwoCover π)).V₀ ⊓
          (relCover C k (fiberTwoCover π)).V₁)ˣ) :
        Γ(relCurve C k, (relCover C k (fiberTwoCover π)).V₀ ⊓
          (relCover C k (fiberTwoCover π)).V₁)) =
      (@presheafCongr k _ (relCurve C k) (relCurve.instOver C k) _ _
          (relCover_inf C k (fiberTwoCover π)).symm)
        (sectionsCollapse C (fiberChart₀ π ⊓ fiberChart₁ π)
          (fiberTwoCover π).isAffineOpen_inf.isCompact
          (fiberTwoCover π).isAffineOpen_inf.isQuasiSeparated
          ((thetaUnit π ^ n :
            Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) :
            Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π))) := by
  rw [sectionsCollapse_apply, presheafCongr, LinearEquiv.ofLinear_apply]
  change (((fst C (overSpec k k)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
      ((relCover C k (fiberTwoCover π)).V₀ ⊓ (relCover C k (fiberTwoCover π)).V₁)
      (le_of_eq (relCover_inf C k (fiberTwoCover π)))).hom
        ((thetaUnit π ^ n : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) : Γ(C.left, _))) =
    ((relCurve C k).presheaf.map (homOfLE
        (le_of_eq (relCover_inf C k (fiberTwoCover π)))).op).hom
      (((fst C (overSpec k k)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
        ((fst C (overSpec k k)).left ⁻¹ᵁ (fiberChart₀ π ⊓ fiberChart₁ π)) le_rfl).hom
        ((thetaUnit π ^ n : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) : Γ(C.left, _)))
  exact (congr($(Scheme.Hom.appLE_map (fst C (overSpec k k)).left
    (le_rfl : (fst C (overSpec k k)).left ⁻¹ᵁ (fiberChart₀ π ⊓ fiberChart₁ π) ≤
      (fst C (overSpec k k)).left ⁻¹ᵁ (fiberChart₀ π ⊓ fiberChart₁ π))
    (homOfLE (le_of_eq (relCover_inf C k (fiberTwoCover π)))).op).hom
      ((thetaUnit π ^ n : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) : Γ(C.left, _)))).symm

/-- **Chart-0 leg of the Čech differential square**: the collapse commutes with the
restriction of the chart-0 lattice into the overlap. -/
lemma twistCollapseN_twistRes_left
    (x : ↥(twistSubmodule k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)
      (fiberChart₀ π))) :
    twistCollapseN C π n (twistRes k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)
        (inf_le_left : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₀ π) x) =
      twistRes k (relCover C k (fiberTwoCover π)).V₀ (relCover C k (fiberTwoCover π)).V₁
        (relThetaCocycle C k π n) inf_le_left (twistCollapse₀ C π n x) := by
  apply (twistTriv₀ k (relCover C k (fiberTwoCover π)).V₀
    (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n) inf_le_left).injective
  rw [twistTriv₀_twistCollapseN, twistTriv₀_res, twistTriv₀_res, twistTriv₀_twistCollapse₀,
    sectionsCollapse_resHom C
      (inf_le_left : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₀ π)
      (fiberTwoCover π).isAffineOpen_inf.isCompact
      (fiberTwoCover π).isAffineOpen_inf.isQuasiSeparated
      (isAffineOpen_preimage_chartOpen π 0).isCompact
      (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated]
  · exact presheafCongr_resHom _ _ _ _
  all_goals exact le_refl _

/-- **Chart-1 leg of the Čech differential square**: the collapse commutes with the
restriction of the chart-1 lattice into the overlap (the cocycle-twisted leg). -/
lemma twistCollapseN_twistRes_right
    (y : ↥(twistSubmodule k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)
      (fiberChart₁ π))) :
    twistCollapseN C π n (twistRes k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)
        (inf_le_right : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₁ π) y) =
      twistRes k (relCover C k (fiberTwoCover π)).V₀ (relCover C k (fiberTwoCover π)).V₁
        (relThetaCocycle C k π n) inf_le_right (twistCollapse₁ C π n y) := by
  apply (twistTriv₀ k (relCover C k (fiberTwoCover π)).V₀
    (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n) inf_le_left).injective
  rw [twistTriv₀_twistCollapseN, twistTriv₀_inf_eq, twistTriv₀_inf_eq, twistTriv₁_res,
    twistTriv₁_res, twistTriv₁_twistCollapse₁, sectionsCollapse_mul, presheafCongr_mul,
    ← relThetaCocycle_val_eq,
    sectionsCollapse_resHom C
      (inf_le_right : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₁ π)
      (fiberTwoCover π).isAffineOpen_inf.isCompact
      (fiberTwoCover π).isAffineOpen_inf.isQuasiSeparated
      (isAffineOpen_preimage_chartOpen π 1).isCompact
      (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated]
  · congr 1
    exact presheafCongr_resHom _ _ _ _
  all_goals exact le_refl _

/-! ### The Čech differential square and the `H⁰`/`H¹` identifications -/

/-- **The Čech differential square**: the overlap collapse intertwines the two-cover Čech
differential of the field pair with that of the relative pair, through the two chart
collapses. -/
lemma twistCollapseN_diff
    (z : (thetaTwistSheaf π n).obj.obj (op (fiberChart₀ π)) ×
      (thetaTwistSheaf π n).obj.obj (op (fiberChart₁ π))) :
    twistCollapseN C π n ((thetaFieldPair C π n).diff z) =
      (relTwistPair C k π (relThetaCocycle C k π n)).diff
        (twistCollapse₀ C π n z.1, twistCollapse₁ C π n z.2) := by
  rw [TwoLatticePair.diff_apply, TwoLatticePair.diff_apply, map_sub]
  congr 1
  · exact twistCollapseN_twistRes_left C π n z.1
  · exact twistCollapseN_twistRes_right C π n z.2

/-- The product of the two chart collapses, as a `k`-linear map of the domains of the two
Čech differentials. -/
noncomputable def twistCollapseDom :
    (↥(twistSubmodule k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)
          (fiberChart₀ π)) ×
        ↥(twistSubmodule k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)
          (fiberChart₁ π))) →ₗ[k]
      (↥(twistSubmodule k (relCover C k (fiberTwoCover π)).V₀
            (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n)
            (relCover C k (fiberTwoCover π)).V₀) ×
        ↥(twistSubmodule k (relCover C k (fiberTwoCover π)).V₀
            (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n)
            (relCover C k (fiberTwoCover π)).V₁)) :=
  (twistCollapse₀ C π n).toLinearMap.prodMap (twistCollapse₁ C π n).toLinearMap

lemma twistCollapseDom_range : LinearMap.range (twistCollapseDom C π n) = ⊤ := by
  rw [twistCollapseDom, LinearMap.range_prodMap, LinearEquiv.range, LinearEquiv.range,
    Submodule.prod_top]

/-- The Čech differential square in range form: the overlap collapse carries the range of
the field differential onto the range of the relative differential. -/
lemma twistCollapseN_range_diff :
    Submodule.map (twistCollapseN C π n).toLinearMap
        (LinearMap.range (thetaFieldPair C π n).diff) =
      LinearMap.range (relTwistPair C k π (relThetaCocycle C k π n)).diff := by
  have hcomp : (twistCollapseN C π n).toLinearMap.comp (thetaFieldPair C π n).diff =
      (relTwistPair C k π (relThetaCocycle C k π n)).diff.comp (twistCollapseDom C π n) :=
    LinearMap.ext fun z => twistCollapseN_diff C π n z
  rw [← LinearMap.range_comp, hcomp,
    LinearMap.range_comp_of_range_eq_top _ (twistCollapseDom_range C π n)]

/-- **`H¹` collapse**: the two-lattice-pair `H¹` of `𝒪(Θⁿ)` on `C.left` is `k`-linearly the
`H¹` of the relative pair of `relThetaTwistSheaf C k π n` on `relCurve C k`. -/
noncomputable def fieldToRelH1 :
    (thetaFieldPair C π n).H1 ≃ₗ[k]
      (relTwistPair C k π (relThetaCocycle C k π n)).H1 :=
  (Submodule.quotEquivOfEq _ _ (thetaFieldPair C π n).range_diff_eq.symm).trans
    ((Submodule.Quotient.equiv _ _ (twistCollapseN C π n)
        (twistCollapseN_range_diff C π n)).trans
      (Submodule.quotEquivOfEq _ _
        (relTwistPair C k π (relThetaCocycle C k π n)).range_diff_eq))

/-- **(c) The `H¹` subsingleton transport**: if `H¹(𝒪(Θⁿ)) = H¹(thetaTwistSheaf π n)`
vanishes (as DAT-0a's `UniformVanishing` + `ThetaSectionsIso` supply through the ledger),
then the `hH1` hypothesis of the landed keystone `relThetaTwistH0BaseChange` is discharged:
`Subsingleton (relTwistPair C k π (relThetaCocycle C k π n)).H1`. -/
theorem subsingleton_relThetaPairH1
    (h : Subsingleton (Sheaf.HModule (thetaTwistSheaf π n) 1)) :
    Subsingleton (relTwistPair C k π (relThetaCocycle C k π n)).H1 :=
  haveI : Subsingleton (thetaFieldPair C π n).H1 :=
    (thetaFieldH1PairEquiv C π n).toEquiv.subsingleton_congr.mp h
  (fieldToRelH1 C π n).toEquiv.subsingleton_congr.mp inferInstance

/-- The product of the two chart collapses, as a `k`-linear equivalence. -/
noncomputable def twistCollapseDomEquiv :
    (↥(twistSubmodule k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)
          (fiberChart₀ π)) ×
        ↥(twistSubmodule k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)
          (fiberChart₁ π))) ≃ₗ[k]
      (↥(twistSubmodule k (relCover C k (fiberTwoCover π)).V₀
            (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n)
            (relCover C k (fiberTwoCover π)).V₀) ×
        ↥(twistSubmodule k (relCover C k (fiberTwoCover π)).V₀
            (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n)
            (relCover C k (fiberTwoCover π)).V₁)) :=
  LinearEquiv.ofLinear (twistCollapseDom C π n)
    ((twistCollapse₀ C π n).symm.toLinearMap.prodMap
      (twistCollapse₁ C π n).symm.toLinearMap)
    (by ext p <;>
      simp only [twistCollapseDom, LinearMap.comp_apply, LinearMap.prodMap_apply,
        LinearMap.id_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])
    (by ext p <;>
      simp only [twistCollapseDom, LinearMap.comp_apply, LinearMap.prodMap_apply,
        LinearMap.id_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply])

/-- **(b) The `H⁰` identification**: the degree-zero cohomology of the relative theta twist
on `relCurve C k` is `k`-linearly the degree-zero cohomology of `thetaTwistSheaf π n` on
`C.left`. -/
noncomputable def relThetaH0FieldEquiv :
    Sheaf.HModule (relThetaTwistSheaf C k π n) 0 ≃ₗ[k]
      Sheaf.HModule (thetaTwistSheaf π n) 0 :=
  (relThetaH0PairEquiv C π n).trans
    ((AlgebraicJacobian.RigidEngine.kerCongr (thetaFieldPair C π n).diff
        (relTwistPair C k π (relThetaCocycle C k π n)).diff
        (twistCollapseDomEquiv C π n) (twistCollapseN C π n)
        (twistCollapseN_diff C π n)).symm.trans
      (thetaFieldH0PairEquiv C π n).symm)

end TwistCollapse

/-! ## The composed export for DD-4's ε construction -/

section Export

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (π : C.left ⟶ P1 k) [IsFinite π] (n : ℕ)
variable (R : Type u) [CommRing R] [Algebra k R]

noncomputable local instance instOverCleftExport : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]

/-- **(d) The composed export DD-4 consumes**: on the `H¹`-vanishing locus, the degree-zero
cohomology of the relative theta twist over the affine test ring `R` is, `R`-linearly, the
free base change of the field-level divisor sections `H_A = divisorSections k (n·F) ⊤`:

`H⁰(relThetaTwistSheaf C R π n) ≃ₗ[R] R ⊗[k] divisorSections k (n • fiberWeilDivisor π) ⊤`.

This is the landed on-the-nose base change `relThetaTwistH0BaseChange` composed with the
base-field-transported `H⁰` identification (b) and Task 1's `thetaTwistH0Equiv`, tensored up
to `R`.  The `ε` lane of DD-4 consumes this spelling verbatim (`K = k` here). -/
noncomputable def relThetaTwistH0BaseChangeDivisor
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π n)).H1) :
    Sheaf.HModule (relThetaTwistSheaf C R π n) 0 ≃ₗ[R]
      R ⊗[k] ↥(Scheme.divisorSections k (n • fiberWeilDivisor π) ⊤) :=
  (relThetaTwistH0BaseChange C R π n hH1).symm.trans
    (LinearEquiv.baseChange k R _ _
      ((relThetaH0FieldEquiv C π n).trans (thetaTwistH0Equiv k π n)))

end Export

end AlgebraicGeometry
