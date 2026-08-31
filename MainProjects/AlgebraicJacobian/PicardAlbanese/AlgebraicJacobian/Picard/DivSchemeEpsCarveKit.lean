/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyWindowTriangle
import AlgebraicJacobian.RiemannRoch.CarveDegree

/-!
# DDR-9.0 kit — the theta presentation of a divisor section and its multiplicativity

Support layer for the carve discharge `divFamEps_carve` (`Picard/DivSchemeEpsCarve.lean`,
`informal/w4-ddr9-worksheet.md` §2.0), split out for the 500-line cap.  Bottom up:

* `AlgebraicGeometry.thetaSectionPair` — the global twisted-pair presentation of a
  divisor section `h ∈ H_n = H⁰(𝒪(n·F))` on `C.left`, with germ-at-η reading
  `(uⁿ·h, h)`; its multiplicativity across the ledger exponents is the cocycle law
  `u^{M+s} = u^M·u^s` (`pow_add`) at the generic germ.
* `AlgebraicGeometry.relThetaFieldSection` — the `k`-level relative theta section of a
  divisor section on `relCurve C k` (no `H¹` input), identified with the section
  collapse of `thetaSectionPair` through `TwoCoverPairData.h0Equiv_val` and the kernel
  transport of the base-field collapse; hence the `k`-level multiplicativity
  (`resHom_relThetaFieldSection_windowShiftMul_fst/_snd`).
* `AlgebraicGeometry.resHom_relThetaWindowEquiv_one_tmul_fst/_snd` — **the pure-tensor
  value of the window identification** over any test ring `S`: on `1 ⊗ h` it reads as
  the `k → S` sections comparison of `relThetaFieldSection` (the
  `DivisorFamilyWindowTriangle` computation re-derived in consumable form).
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance (priority := 50) instOverCleftEpsCarveKit :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]

noncomputable local instance instQcohThetaECK₀ (n : ℕ) :
    Scheme.QcohOn (thetaTwistSheaf π n) (fiberChart₀ π) :=
  twistSheaf.instQcohOn₀ k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)

noncomputable local instance instQcohThetaECK₁ (n : ℕ) :
    Scheme.QcohOn (thetaTwistSheaf π n) (fiberChart₁ π) :=
  twistSheaf.instQcohOn₁ k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n)

attribute [local instance 10000] relCurve.instOver

/-! ## The field-level pair presentation of a divisor section and its germ reading -/

section FieldPair

variable (n : ℕ)

/-- **The global twisted-pair presentation of a divisor section** at exponent `n`: the
image of `h ∈ H_n = H⁰(𝒪(n·F))` under the inverse of the field bridge
`H⁰(Θⁿ) ≃ H⁰(𝒪(n·F))`, read as a global section pair of the twisted sheaf.  Its germ at
the generic point is `(uⁿ·h, h)` (`germ_thetaSectionPair_fst/_snd`) — the multiplicative
carrier of the DDR-9.0 compat. -/
noncomputable def thetaSectionPair
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    ↥(twistSubmodule k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) ⊤) :=
  Sheaf.HModule.linearEquiv₀
    (Opens.grothendieckTopology ((C.left : Scheme.{u}) : TopCat)) isTerminalTop
    (thetaTwistSheaf π n) ((thetaTwistH0Equiv k π n).symm h)

omit [IsFinite π] in
/-- (Implementation) The inverse field bridge, unfolded to the sheaf-isomorphism
functorial transport of the `H⁰` class of `h`. -/
private lemma thetaTwistH0Equiv_symm_eq
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    (thetaTwistH0Equiv k π n).symm h
      = Sheaf.HModule.map (thetaTwistDivisorSheafIso k π n).inv 0
          ((divisorSectionsEquivH0 k (n • fiberWeilDivisor π)).symm h) := by
  apply (thetaTwistH0Equiv k π n).injective
  rw [LinearEquiv.apply_symm_apply, thetaTwistH0Equiv, LinearEquiv.trans_apply,
    Sheaf.HModule.mapEquiv_apply, ← Sheaf.HModule.map_comp_apply, Iso.inv_hom_id,
    Sheaf.HModule.map_id_apply, LinearEquiv.apply_symm_apply]

set_option maxHeartbeats 800000 in
-- The degree-zero naturality square unfolds the sheaf-iso transport (heavy defeq).
omit [IsFinite π] in
/-- (Implementation) The pair presentation is inverse to the section-wise bridge map:
applying `Θⁿ(⊤) → 𝒪(n·F)(⊤)` to `thetaSectionPair h` recovers `h`. -/
private lemma thetaToDivisorPresheafApp_thetaSectionPair
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    thetaToDivisorPresheafApp k π n ⊤ (thetaSectionPair C π n h) = h := by
  have hnat := Sheaf.HModule.linearEquiv₀_naturality
    (hT := (isTerminalTop : IsTerminal (⊤ : C.left.Opens)))
    (f := (thetaTwistDivisorSheafIso k π n).hom)
    (Sheaf.HModule.map (thetaTwistDivisorSheafIso k π n).inv 0
      ((divisorSectionsEquivH0 k (n • fiberWeilDivisor π)).symm h))
  rw [← Sheaf.HModule.map_comp_apply, Iso.inv_hom_id, Sheaf.HModule.map_id_apply] at hnat
  have hx : Sheaf.HModule.linearEquiv₀
      (Opens.grothendieckTopology ((C.left : Scheme.{u}) : TopCat)) isTerminalTop
      (C.left.divisorSheaf k (n • fiberWeilDivisor π))
      ((divisorSectionsEquivH0 k (n • fiberWeilDivisor π)).symm h) = h :=
    LinearEquiv.apply_symm_apply (divisorSectionsEquivH0 k (n • fiberWeilDivisor π)) h
  rw [hx] at hnat
  have hpair : thetaSectionPair C π n h
      = Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology ((C.left : Scheme.{u}) : TopCat)) isTerminalTop
          (thetaTwistSheaf π n)
          (Sheaf.HModule.map (thetaTwistDivisorSheafIso k π n).inv 0
            ((divisorSectionsEquivH0 k (n • fiberWeilDivisor π)).symm h)) := by
    rw [thetaSectionPair, thetaTwistH0Equiv_symm_eq]
  rw [hpair]
  exact hnat

omit [IsFinite π] in
/-- **The value of the pair presentation is `h`**: `thetaVal (thetaSectionPair h) = h`. -/
private lemma thetaVal_thetaSectionPair
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    thetaVal k π n (Opens.mem_top (genericPoint C.left)) (thetaSectionPair C π n h)
      = (h : C.left.functionField) := by
  have key := congrArg (fun t : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤) =>
    (t : C.left.functionField)) (thetaToDivisorPresheafApp_thetaSectionPair C π n h)
  have hne : ((⊤ : C.left.Opens) : Set C.left).Nonempty := ⟨genericPoint C.left, trivial⟩
  rw [thetaToDivisorPresheafApp_of_nonempty k π n hne] at key
  exact key

omit [IsFinite π] in
/-- **The chart-0 germ of the pair presentation**: `germ_η (pair₀) = uⁿ · h`. -/
lemma germ_thetaSectionPair_fst
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    (C.left.presheaf.germ (⊤ ⊓ fiberChart₀ π) (genericPoint C.left)
        ⟨trivial, (genericPoint_mem_preimage_inf π).1⟩).hom
        (thetaSectionPair C π n h).val.1
      = ((fiberCoordUnit π ^ n : C.left.functionFieldˣ) : C.left.functionField)
          * (h : C.left.functionField) := by
  have hval : (((fiberCoordUnit π ^ n)⁻¹ : C.left.functionFieldˣ) : C.left.functionField)
      * (C.left.presheaf.germ (⊤ ⊓ fiberChart₀ π) (genericPoint C.left)
          ⟨trivial, (genericPoint_mem_preimage_inf π).1⟩).hom
          (thetaSectionPair C π n h).val.1
      = (h : C.left.functionField) := thetaVal_thetaSectionPair C π n h
  rw [← hval, ← mul_assoc, Units.mul_inv, one_mul]

omit [IsFinite π] in
/-- **The chart-1 germ of the pair presentation**: `germ_η (pair₁) = h`. -/
lemma germ_thetaSectionPair_snd
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    (C.left.presheaf.germ (⊤ ⊓ fiberChart₁ π) (genericPoint C.left)
        ⟨trivial, (genericPoint_mem_preimage_inf π).2⟩).hom
        (thetaSectionPair C π n h).val.2
      = (h : C.left.functionField) :=
  ((thetaVal_eq_germ_snd k π n (Opens.mem_top (genericPoint C.left))
    (thetaSectionPair C π n h)).symm).trans (thetaVal_thetaSectionPair C π n h)

end FieldPair

/-! ## The field-level multiplicativity at the ledger exponents -/

section FieldMul

variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)

/-- The window-shift multiplier is the function-field product. -/
private lemma windowShiftMul_coe
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤))
    (m : ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    ((windowShiftMul hπ g a m : ↥(divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) :
      C.left.functionField)
      = (a : C.left.functionField) * (m : C.left.functionField) := by
  rw [windowShiftMul, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_ofEq_apply, sectionMulBilin_apply_coe]

/-- **Field-level multiplicativity, chart 0**: the pair presentation of the shifted
product is the componentwise product of the presentations — the cocycle law
`u^{M+s} = u^M·u^s` as `pow_add` at the generic germ. -/
private lemma thetaSectionPair_windowShiftMul_fst
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤))
    (m : ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    (thetaSectionPair C π (windowM_choice π hπ g + windowS_choice π hπ g)
        (windowShiftMul hπ g a m)).val.1
      = (thetaSectionPair C π (windowS_choice π hπ g) a).val.1
          * (thetaSectionPair C π (windowM_choice π hπ g) m).val.1 := by
  apply germ_injective_of_isIntegral C.left (genericPoint C.left)
    (⟨trivial, (genericPoint_mem_preimage_inf π).1⟩ :
      genericPoint C.left ∈ ⊤ ⊓ fiberChart₀ π)
  rw [map_mul, germ_thetaSectionPair_fst, germ_thetaSectionPair_fst,
    germ_thetaSectionPair_fst, windowShiftMul_coe, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_add]
  ring

/-- **Field-level multiplicativity, chart 1** (mirror). -/
private lemma thetaSectionPair_windowShiftMul_snd
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤))
    (m : ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    (thetaSectionPair C π (windowM_choice π hπ g + windowS_choice π hπ g)
        (windowShiftMul hπ g a m)).val.2
      = (thetaSectionPair C π (windowS_choice π hπ g) a).val.2
          * (thetaSectionPair C π (windowM_choice π hπ g) m).val.2 := by
  apply germ_injective_of_isIntegral C.left (genericPoint C.left)
    (⟨trivial, (genericPoint_mem_preimage_inf π).2⟩ :
      genericPoint C.left ∈ ⊤ ⊓ fiberChart₁ π)
  rw [map_mul, germ_thetaSectionPair_snd, germ_thetaSectionPair_snd,
    germ_thetaSectionPair_snd, windowShiftMul_coe]

end FieldMul

/-! ## The `k`-level relative theta section of a divisor section -/

section KLevel

variable (n : ℕ)

/-- **The `k`-level relative theta section of a divisor section**: the global twisted
pair on `relCurve C k` presenting `h ∈ H_n` through the base-field collapse — the exact
`k`-side term of the landed pure-tensor computation of `relThetaWindowEquiv`
(`Picard/DivisorFamilyWindowTriangle.lean`).  Needs no `H¹` input. -/
noncomputable def relThetaFieldSection
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) : relThetaSections C k π n :=
  relTwistSectionsEquiv₀ C k (fiberTwoCover π) (relThetaCocycle C k π n)
    (((relThetaH0FieldEquiv C π n).trans (thetaTwistH0Equiv k π n)).symm h)

/-- (Implementation) The chart-0 trivialization of a top-restricted global pair is the
restriction of its first component. -/
private lemma twistTriv₀_twistRes_top {K : Type u} [CommRing K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] (V₀ V₁ : X.Opens) (γ : Γ(X, V₀ ⊓ V₁)ˣ)
    (p : ↥(twistSubmodule K V₀ V₁ γ ⊤)) :
    twistTriv₀ K V₀ V₁ γ (le_refl V₀) (twistRes K V₀ V₁ γ le_top p)
      = X.resHom (le_inf le_top le_rfl) p.val.1 := by
  rw [twistTriv₀_apply, twistRes_coe_fst, Scheme.resHom_resHom]

/-- (Implementation) Chart-1 mirror of `twistTriv₀_twistRes_top`. -/
private lemma twistTriv₁_twistRes_top {K : Type u} [CommRing K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] (V₀ V₁ : X.Opens) (γ : Γ(X, V₀ ⊓ V₁)ˣ)
    (p : ↥(twistSubmodule K V₀ V₁ γ ⊤)) :
    twistTriv₁ K V₀ V₁ γ (le_refl V₁) (twistRes K V₀ V₁ γ le_top p)
      = X.resHom (le_inf le_top le_rfl) p.val.2 := by
  rw [twistTriv₁_apply, twistRes_coe_snd, Scheme.resHom_resHom]

set_option maxHeartbeats 1600000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
/-- (Implementation) The top-restricted `k`-level section is the chart-0 collapse of the
top-restricted field pair — the `H⁰`-carrier val computation through
`TwoCoverPairData.h0Equiv_val` and the kernel transport of the base-field collapse. -/
private lemma twistRes_relThetaFieldSection
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    twistRes k (relCover C k (fiberTwoCover π)).V₀ (relCover C k (fiberTwoCover π)).V₁
        (relThetaCocycle C k π n) le_top (relThetaFieldSection C π n h)
      = twistCollapse₀ C π n
          (twistRes k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) le_top
            (thetaSectionPair C π n h)) := by
  obtain ⟨y, hy⟩ : ∃ y,
      ((relThetaH0FieldEquiv C π n).trans (thetaTwistH0Equiv k π n)).symm h = y :=
    ⟨_, rfl⟩
  have h0 : thetaTwistH0Equiv k π n (relThetaH0FieldEquiv C π n y) = h := by
    rw [← hy]
    exact ((relThetaH0FieldEquiv C π n).trans
      (thetaTwistH0Equiv k π n)).apply_symm_apply h
  have h1 : relThetaH0FieldEquiv C π n y = (thetaTwistH0Equiv k π n).symm h :=
    (LinearEquiv.eq_symm_apply (thetaTwistH0Equiv k π n)).mpr h0
  rw [relThetaH0FieldEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply] at h1
  have h2 := (LinearEquiv.symm_apply_eq (thetaFieldH0PairEquiv C π n)).mp h1
  have h3 := (LinearEquiv.symm_apply_eq
    (AlgebraicJacobian.RigidEngine.kerCongr (thetaFieldPair C π n).diff
      (relTwistPair C k π (relThetaCocycle C k π n)).diff
      (twistCollapseDomEquiv C π n) (twistCollapseN C π n)
      (twistCollapseN_diff C π n))).mp h2
  have hL := congrArg Prod.fst (Scheme.TwoCoverPairData.h0Equiv_val
    (relTwistPairData C k π (relThetaCocycle C k π n))
    (relCover_isAffineOpen₀ C k (fiberTwoCover π))
    (relCover_isAffineOpen₁ C k (fiberTwoCover π))
    (relCover_sup C k (fiberTwoCover π)) y)
  have hR := congrArg Prod.fst (Scheme.TwoCoverPairData.h0Equiv_val
    (thetaFieldPairData C π n) (isAffineOpen_preimage_chartOpen π 0)
    (isAffineOpen_preimage_chartOpen π 1) (preimage_chartOpen_sup π)
    ((thetaTwistH0Equiv k π n).symm h))
  have hW : relThetaFieldSection C π n h
      = relTwistSectionsEquiv₀ C k (fiberTwoCover π) (relThetaCocycle C k π n) y := by
    rw [relThetaFieldSection, hy]
  rw [hW]
  refine (hL.symm.trans ?_).trans (congrArg (twistCollapse₀ C π n) hR)
  exact congrArg
    (fun q : ↥(relTwistPair C k π (relThetaCocycle C k π n)).H0 => q.val.1) h3

set_option maxHeartbeats 1600000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
/-- (Implementation) Chart-1 mirror of `twistRes_relThetaFieldSection`. -/
private lemma twistRes_relThetaFieldSection_snd
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    twistRes k (relCover C k (fiberTwoCover π)).V₀ (relCover C k (fiberTwoCover π)).V₁
        (relThetaCocycle C k π n) le_top (relThetaFieldSection C π n h)
      = twistCollapse₁ C π n
          (twistRes k (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) le_top
            (thetaSectionPair C π n h)) := by
  obtain ⟨y, hy⟩ : ∃ y,
      ((relThetaH0FieldEquiv C π n).trans (thetaTwistH0Equiv k π n)).symm h = y :=
    ⟨_, rfl⟩
  have h0 : thetaTwistH0Equiv k π n (relThetaH0FieldEquiv C π n y) = h := by
    rw [← hy]
    exact ((relThetaH0FieldEquiv C π n).trans
      (thetaTwistH0Equiv k π n)).apply_symm_apply h
  have h1 : relThetaH0FieldEquiv C π n y = (thetaTwistH0Equiv k π n).symm h :=
    (LinearEquiv.eq_symm_apply (thetaTwistH0Equiv k π n)).mpr h0
  rw [relThetaH0FieldEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply] at h1
  have h2 := (LinearEquiv.symm_apply_eq (thetaFieldH0PairEquiv C π n)).mp h1
  have h3 := (LinearEquiv.symm_apply_eq
    (AlgebraicJacobian.RigidEngine.kerCongr (thetaFieldPair C π n).diff
      (relTwistPair C k π (relThetaCocycle C k π n)).diff
      (twistCollapseDomEquiv C π n) (twistCollapseN C π n)
      (twistCollapseN_diff C π n))).mp h2
  have hL := congrArg Prod.snd (Scheme.TwoCoverPairData.h0Equiv_val
    (relTwistPairData C k π (relThetaCocycle C k π n))
    (relCover_isAffineOpen₀ C k (fiberTwoCover π))
    (relCover_isAffineOpen₁ C k (fiberTwoCover π))
    (relCover_sup C k (fiberTwoCover π)) y)
  have hR := congrArg Prod.snd (Scheme.TwoCoverPairData.h0Equiv_val
    (thetaFieldPairData C π n) (isAffineOpen_preimage_chartOpen π 0)
    (isAffineOpen_preimage_chartOpen π 1) (preimage_chartOpen_sup π)
    ((thetaTwistH0Equiv k π n).symm h))
  have hW : relThetaFieldSection C π n h
      = relTwistSectionsEquiv₀ C k (fiberTwoCover π) (relThetaCocycle C k π n) y := by
    rw [relThetaFieldSection, hy]
  rw [hW]
  refine (hL.symm.trans ?_).trans (congrArg (twistCollapse₁ C π n) hR)
  exact congrArg
    (fun q : ↥(relTwistPair C k π (relThetaCocycle C k π n)).H0 => q.val.2) h3

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
/-- **The `k`-level section reads as the collapsed field pair, chart 0**: the restricted
first component of `relThetaFieldSection` is the section collapse of the restricted
first component of `thetaSectionPair`. -/
lemma resHom_relThetaFieldSection_fst
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    (relCurve C k).resHom (le_inf le_top le_rfl) ((relThetaFieldSection C π n h).val.1)
      = sectionsCollapse C (fiberChart₀ π)
          (isAffineOpen_preimage_chartOpen π 0).isCompact
          (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated
          (C.left.resHom (le_inf le_top le_rfl) ((thetaSectionPair C π n h).val.1)) := by
  have key := congrArg (twistTriv₀ k (relCover C k (fiberTwoCover π)).V₀
    (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n)
    (le_refl (relCover C k (fiberTwoCover π)).V₀))
    (twistRes_relThetaFieldSection C π n h)
  rw [twistTriv₀_twistCollapse₀, twistTriv₀_twistRes_top, twistTriv₀_twistRes_top] at key
  exact key

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
/-- **The `k`-level section reads as the collapsed field pair, chart 1** (mirror). -/
lemma resHom_relThetaFieldSection_snd
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    (relCurve C k).resHom (le_inf le_top le_rfl) ((relThetaFieldSection C π n h).val.2)
      = sectionsCollapse C (fiberChart₁ π)
          (isAffineOpen_preimage_chartOpen π 1).isCompact
          (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated
          (C.left.resHom (le_inf le_top le_rfl) ((thetaSectionPair C π n h).val.2)) := by
  have key := congrArg (twistTriv₁ k (relCover C k (fiberTwoCover π)).V₀
    (relCover C k (fiberTwoCover π)).V₁ (relThetaCocycle C k π n)
    (le_refl (relCover C k (fiberTwoCover π)).V₁))
    (twistRes_relThetaFieldSection_snd C π n h)
  rw [twistTriv₁_twistCollapse₁, twistTriv₁_twistRes_top, twistTriv₁_twistRes_top] at key
  exact key

end KLevel

/-! ## The `k`-level multiplicativity -/

section KMul

variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)

/-- **The `k`-level multiplicativity, chart 0**: the `k`-level section of the shifted
product is the componentwise product of the sections — the field multiplicativity pushed
through the multiplicative section collapse. -/
lemma resHom_relThetaFieldSection_windowShiftMul_fst
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤))
    (m : ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    (relCurve C k).resHom (le_inf le_top le_rfl)
        ((relThetaFieldSection C π (windowM_choice π hπ g + windowS_choice π hπ g)
          (windowShiftMul hπ g a m)).val.1)
      = (relCurve C k).resHom (le_inf le_top le_rfl)
          ((relThetaFieldSection C π (windowS_choice π hπ g) a).val.1)
        * (relCurve C k).resHom (le_inf le_top le_rfl)
            ((relThetaFieldSection C π (windowM_choice π hπ g) m).val.1) := by
  rw [resHom_relThetaFieldSection_fst, resHom_relThetaFieldSection_fst,
    resHom_relThetaFieldSection_fst, thetaSectionPair_windowShiftMul_fst, map_mul,
    sectionsCollapse_mul]

/-- **The `k`-level multiplicativity, chart 1** (mirror). -/
lemma resHom_relThetaFieldSection_windowShiftMul_snd
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤))
    (m : ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    (relCurve C k).resHom (le_inf le_top le_rfl)
        ((relThetaFieldSection C π (windowM_choice π hπ g + windowS_choice π hπ g)
          (windowShiftMul hπ g a m)).val.2)
      = (relCurve C k).resHom (le_inf le_top le_rfl)
          ((relThetaFieldSection C π (windowS_choice π hπ g) a).val.2)
        * (relCurve C k).resHom (le_inf le_top le_rfl)
            ((relThetaFieldSection C π (windowM_choice π hπ g) m).val.2) := by
  rw [resHom_relThetaFieldSection_snd, resHom_relThetaFieldSection_snd,
    resHom_relThetaFieldSection_snd, thetaSectionPair_windowShiftMul_snd, map_mul,
    sectionsCollapse_mul]

end KMul

/-! ## The pure-tensor value of the window identification over a test ring -/

section PureTensor

variable (S : Type u) [CommRing S] [Algebra k S]
variable (n : ℕ)
variable (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π n)).H1)

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 4000 in
/-- (Implementation) The window identification at `1 ⊗ h`, unfolded to the generic
global-sections reading of the base-changed twisted sheaf (the landed
`DivisorFamilyWindowTriangle` computation, re-derived for consumption here). -/
private lemma relThetaWindowEquiv_one_tmul_eq
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    (relThetaWindowEquiv C S π n hH1 (1 ⊗ₜ h)).val
      = (relTwistSectionsEquiv₀ C S (fiberTwoCover π) (relThetaCocycle C S π n)
          (Sheaf.HModule.mapEquiv
            (eqToIso (congrArg (relTwistSheaf C S (fiberTwoCover π))
              (relThetaCocycle_baseChange C S π n))) 0
            (relTwistH0BaseChange C k S π (relThetaCocycle C k π n) hH1
              (1 ⊗ₜ (((relThetaH0FieldEquiv C π n).trans
                (thetaTwistH0Equiv k π n)).symm h))))).val := by
  congr 1

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 4000 in
/-- **The pure-tensor value of the window identification, chart 0**: on `1 ⊗ h` the
window identification over `S` reads as the `k → S` sections comparison of the `k`-level
relative theta section of `h`. -/
lemma resHom_relThetaWindowEquiv_one_tmul_fst
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    (relCurve C S).resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C S π n hH1 (1 ⊗ₜ h)).val.1)
      = relSectionsMap C k S (fiberTwoCover π).V₀
          ((relCurve C k).resHom (le_inf le_top le_rfl)
            ((relThetaFieldSection C π n h).val.1)) := by
  rw [congrArg ((relCurve C S).resHom (le_inf le_top le_rfl))
      (congrArg Prod.fst (relThetaWindowEquiv_one_tmul_eq C π S n hH1 h)),
    congrArg ((relCurve C S).resHom (le_inf le_top le_rfl))
      (congrArg Prod.fst (val_relTwistSectionsEquiv₀_mapEquiv C S (fiberTwoCover π)
        (relThetaCocycle_baseChange C S π n) _))]
  exact resHom_relTwistH0BaseChange_one_tmul_fst C S π (relThetaCocycle C k π n) hH1 _

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 4000 in
/-- **The pure-tensor value of the window identification, chart 1** (mirror). -/
lemma resHom_relThetaWindowEquiv_one_tmul_snd
    (h : ↥(divisorSections k (n • fiberWeilDivisor π) ⊤)) :
    (relCurve C S).resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C S π n hH1 (1 ⊗ₜ h)).val.2)
      = relSectionsMap C k S (fiberTwoCover π).V₁
          ((relCurve C k).resHom (le_inf le_top le_rfl)
            ((relThetaFieldSection C π n h).val.2)) := by
  rw [congrArg ((relCurve C S).resHom (le_inf le_top le_rfl))
      (congrArg Prod.snd (relThetaWindowEquiv_one_tmul_eq C π S n hH1 h)),
    congrArg ((relCurve C S).resHom (le_inf le_top le_rfl))
      (congrArg Prod.snd (val_relTwistSectionsEquiv₀_mapEquiv C S (fiberTwoCover π)
        (relThetaCocycle_baseChange C S π n) _))]
  exact resHom_relTwistH0BaseChange_one_tmul_snd C S π (relThetaCocycle C k π n) hH1 _

end PureTensor

end AlgebraicGeometry
