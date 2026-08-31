/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyFieldDictionaryCore
import AlgebraicJacobian.Picard.DivisorFamilyField

/-!
# G-3 — Φ, the field window→functionField dictionary (`informal/spec-w4-gates.md` §G-3)

The sections dictionary at a field point, submodule form — the `Φ, hΦinj, hΦwin` seam of
`Picard/DivisorFamilyEpsMono.lean` (DD-4 Task 5's field content, I-0214's open
boundary), discharged.  Over a field extension `K/k` and a twist exponent `a`:

* `AlgebraicGeometry.divFamPhi` — **the dictionary** `Φ : K ⊗[k] H_a →ₗ[K] K(C_K)`: the
  window identification `relThetaWindowEquiv` followed by the function-field reading
  `thetaFieldRead` of the theta trivialization, shifted by the class-comparison unit
  `thetaFieldShiftUnit` so the image lands at the **transported window divisor**
  `windowTransportDivisor C K π a` — the abstract `N` of the DDR-2 `N`-pack
  (`RiemannRoch/WindowFieldTransport.lean`, I-0204's spelling).
* `AlgebraicGeometry.divFamPhi_injective` — **`hΦinj`**: `Φ` is injective (equivs
  composed with the injective reading and a nonzero multiplication).
* `AlgebraicGeometry.map_divFamPhi_divisorWindow` — the image dictionary at an
  **arbitrary** local-equation system `d`:
  `Φ(K_a(d)) = H⁰(𝒪(N(a) − div d)) = divisorSections K (windowTransportDivisor − div d)`.
  The heart is `mem_vanishingSubmodule_iff_thetaFieldRead_mem`: a global theta section
  vanishes along `d` germwise exactly when its reading has poles bounded by
  `N₀(a) − div d` — pointwise on closed points through the stalk-ideal ↔ order
  dictionary, with the theta cocycle transporting the condition across the charts.
* `AlgebraicGeometry.map_divFamPhi_eps_fst` — **`hΦwin`**, the keystone in the threaded
  shape of `Picard/DivisorFamilyEpsMono.lean:229-234`: at the ledger exponent
  `M = windowM_choice`, `Φ` carries the `ε`-window of a certified divisor family onto
  `divisorSections K (windowN − divFamDivisor F) ⊤`.

Together with the landed `N`-pack (`windowN`, `subsingleton_h1_windowN`,
`two_mul_genus_le_deg_windowN`, `subsingleton_h1_windowN_sub`, `h0_windowN`) this
discharges the six `Φ/hΦinj/hΦwin` threadings of `DivisorFamilyEpsMono` (and DDR-2's
`hdict` through `h0_eq_finrank_of_map_eq`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

/-! ## The pointwise dictionary: vanishing along `d` ↔ pole bound at `N₀(a) − div d` -/

section Pointwise

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]
variable (a : ℕ)
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **The theta cocycle transports the stalk-ideal condition across the charts**: at a
point of the chart overlap, the chart-0 germ of a global theta section lies in the stalk
ideal of `d` exactly when the chart-1 germ does — the matching relation differs by the
germ of the *unit* cocycle. -/
lemma germ_fst_mem_stalkIdeal_iff (d : (relCurve C K).LocalEquations)
    (s : relThetaSections C K π a) {z : relCurve C K}
    (hz₀ : z ∈ ⊤ ⊓ (relCover C K (fiberTwoCover π)).V₀)
    (hz₁ : z ∈ ⊤ ⊓ (relCover C K (fiberTwoCover π)).V₁) :
    ((relCurve C K).presheaf.germ (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₀) z hz₀).hom
        s.val.1 ∈ d.stalkIdeal z ↔
      ((relCurve C K).presheaf.germ (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₁) z hz₁).hom
          s.val.2 ∈ d.stalkIdeal z := by
  have hzI : z ∈ (relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁ :=
    ⟨hz₀.2, hz₁.2⟩
  have hmatch := relThetaSections_matching a s
    (le_rfl : (relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁
      ≤ (relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁)
  have hg := congrArg
    ((relCurve C K).presheaf.germ
      ((relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁) z hzI).hom
    hmatch
  rw [map_mul] at hg
  -- germs of the three restrictions
  have h1 : ((relCurve C K).presheaf.germ
      ((relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁) z hzI).hom
        ((relCurve C K).resHom (le_inf le_top (le_rfl.trans inf_le_left)) s.val.1)
      = ((relCurve C K).presheaf.germ
          (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₀) z hz₀).hom s.val.1 :=
    (relCurve C K).presheaf.germ_res_apply
      (homOfLE (le_inf le_top (le_rfl.trans inf_le_left))) z hzI s.val.1
  have h2 : ((relCurve C K).presheaf.germ
      ((relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁) z hzI).hom
        ((relCurve C K).resHom (le_inf le_top (le_rfl.trans inf_le_right)) s.val.2)
      = ((relCurve C K).presheaf.germ
          (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₁) z hz₁).hom s.val.2 :=
    (relCurve C K).presheaf.germ_res_apply
      (homOfLE (le_inf le_top (le_rfl.trans inf_le_right))) z hzI s.val.2
  have h3 : ((relCurve C K).presheaf.germ
      ((relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁) z hzI).hom
        ((relCurve C K).resHom le_rfl
          ((relThetaCocycle C K π a : Γ(relCurve C K,
            (relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁)ˣ) :
            Γ(relCurve C K,
              (relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁)))
      = ((relCurve C K).presheaf.germ
          ((relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁)
          z hzI).hom
          ((relThetaCocycle C K π a : Γ(relCurve C K,
            (relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁)ˣ) :
            Γ(relCurve C K,
              (relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁)) :=
    (relCurve C K).presheaf.germ_res_apply (homOfLE le_rfl) z hzI _
  rw [h1, h2, h3] at hg
  have hu : IsUnit (((relCurve C K).presheaf.germ
      ((relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁)
      z hzI).hom
        ((relThetaCocycle C K π a : Γ(relCurve C K,
          (relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁)ˣ) :
          Γ(relCurve C K,
            (relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁))) :=
    (relThetaCocycle C K π a).isUnit.map ((relCurve C K).presheaf.germ
      ((relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁)
      z hzI).hom
  rw [hg]
  exact Ideal.unit_mul_mem_iff_mem _ hu

/-- **The pointwise dictionary at a closed point**: the reading of a global theta
section has its order bounded by `N₀(a) − div d` at a closed point `z` exactly when the
germ at `z` of its glued component lies in the stalk ideal of `d` — the stalk-ideal ↔
order dictionary against the theta trivialization. -/
lemma ord_thetaFieldRead_le_iff (d : (relCurve C K).LocalEquations)
    (s : relThetaSections C K π a) {z : relCurve C K}
    (hzg : z ≠ genericPoint (relCurve C K)) :
    Scheme.ord (relCurve C K ↘ Spec (CommRingCat.of K)) hzg (thetaFieldRead C K π a s)
        ≤ Scheme.divisorBound
            (thetaFieldDivisor C K π a - Scheme.presentationDivisor K d.presentation) hzg
      ↔ ((relCurve C K).presheaf.germ (⊤ ⊓ (thetaFieldPointedCover C K π).opens z) z
            ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩).hom
          ((thetaFieldGluedEquiv C K π a s).val z) ∈ d.stalkIdeal z := by
  have hsplit : Scheme.divisorBound
      (thetaFieldDivisor C K π a - Scheme.presentationDivisor K d.presentation) hzg
      = Scheme.divisorBound
          (Scheme.presentationDivisor K (thetaFieldPresentation C K π a)) hzg
        * Scheme.divisorBound (-Scheme.presentationDivisor K d.presentation) hzg := by
    rw [sub_eq_add_neg]
    exact Scheme.divisorBound_add _ _ hzg
  have hpos : (0 : WithZero (Multiplicative ℤ))
      < Scheme.divisorBound
          (Scheme.presentationDivisor K (thetaFieldPresentation C K π a)) hzg := by
    rw [show Scheme.divisorBound
        (Scheme.presentationDivisor K (thetaFieldPresentation C K π a)) hzg
        = ((Multiplicative.ofAdd (coeffAt hzg
            (Scheme.presentationDivisor K (thetaFieldPresentation C K π a))) :
          Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl]
    exact zero_lt_iff.mpr WithZero.coe_ne_zero
  rw [thetaFieldRead_apply,
    Scheme.MeromorphicPresentation.gluedVal_eq_elem_inv_mul K
      (thetaFieldPresentation C K π a) z (W := ⊤) trivial
      (thetaFieldGluedEquiv C K π a s),
    map_mul, hsplit,
    Scheme.MeromorphicPresentation.ord_elem_inv K (thetaFieldPresentation C K π a) z hzg,
    mul_le_mul_iff_right₀ hpos,
    ← Scheme.LocalEquations.ord_presentation_elem K d hzg]
  exact (Scheme.LocalEquations.germ_mem_stalkIdeal_iff_ord_le K d
    (⟨trivial, (thetaFieldPointedCover C K π).genericPoint_mem_opens z⟩ :
      genericPoint (relCurve C K) ∈ ⊤ ⊓ (thetaFieldPointedCover C K π).opens z)
    (⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩ :
      z ∈ ⊤ ⊓ (thetaFieldPointedCover C K π).opens z)
    hzg ((thetaFieldGluedEquiv C K π a s).val z)).symm

/-- **The dictionary, membership form**: a global theta section vanishes along `d`
germwise (i.e. lies in `H⁰(𝒪(Θᵃ − d))`) exactly when its function-field reading has
poles bounded by `N₀(a) − div d` (i.e. lies in `H⁰(𝒪(N₀(a) − div d))`). -/
theorem mem_vanishingSubmodule_iff_thetaFieldRead_mem (d : (relCurve C K).LocalEquations)
    (s : relThetaSections C K π a) :
    s ∈ d.vanishingSubmodule K (relCover C K (fiberTwoCover π)).V₀
        (relCover C K (fiberTwoCover π)).V₁ (relThetaCocycle C K π a) ↔
      thetaFieldRead C K π a s ∈ Scheme.divisorSections K
        (thetaFieldDivisor C K π a - Scheme.presentationDivisor K d.presentation) ⊤ := by
  rw [Scheme.LocalEquations.mem_vanishingSubmodule_iff K,
    Scheme.mem_divisorSections_of_nonempty K (top_opens_nonempty (X := relCurve C K))]
  constructor
  · rintro ⟨h₀, h₁⟩ z hzg _
    rw [ord_thetaFieldRead_le_iff C K π a d s hzg]
    by_cases hz₀ : z ∈ (relCover C K (fiberTwoCover π)).V₀
    · rw [germ_thetaFieldGluedEquiv_fst C K π a s hz₀
        ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩ ⟨trivial, hz₀⟩]
      exact h₀ z ⟨trivial, hz₀⟩
    · rw [germ_thetaFieldGluedEquiv_snd C K π a s hz₀
        ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩
        ⟨trivial, mem_V₁_of_notMem_V₀ C K π hz₀⟩]
      exact h₁ z ⟨trivial, mem_V₁_of_notMem_V₀ C K π hz₀⟩
  · intro h
    constructor
    · intro z hz
      rcases eq_or_ne z (genericPoint (relCurve C K)) with rfl | hzg
      · rw [Scheme.LocalEquations.stalkIdeal_genericPoint]
        trivial
      · have hb := h z hzg trivial
        rw [ord_thetaFieldRead_le_iff C K π a d s hzg,
          germ_thetaFieldGluedEquiv_fst C K π a s hz.2
            ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩ hz] at hb
        exact hb
    · intro z hz
      rcases eq_or_ne z (genericPoint (relCurve C K)) with rfl | hzg
      · rw [Scheme.LocalEquations.stalkIdeal_genericPoint]
        trivial
      · have hb := h z hzg trivial
        rw [ord_thetaFieldRead_le_iff C K π a d s hzg] at hb
        by_cases hz₀ : z ∈ (relCover C K (fiberTwoCover π)).V₀
        · rw [germ_thetaFieldGluedEquiv_fst C K π a s hz₀
            ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩ ⟨trivial, hz₀⟩] at hb
          exact (germ_fst_mem_stalkIdeal_iff C K π a d s ⟨trivial, hz₀⟩ hz).mp hb
        · rw [germ_thetaFieldGluedEquiv_snd C K π a s hz₀
            ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩
            ⟨trivial, mem_V₁_of_notMem_V₀ C K π hz₀⟩] at hb
          exact hb

/-- **The image identification at the theta divisor**: the reading carries
`H⁰(𝒪(Θᵃ − d))` (the vanishing submodule of `d`) exactly onto
`H⁰(𝒪(N₀(a) − div d))`.  The `⊇` direction lifts along the surjectivity of the reading
onto `H⁰(𝒪(N₀(a)))` (`exists_thetaFieldRead_eq`), using effectivity of `div d`. -/
theorem map_thetaFieldRead_vanishingSubmodule (d : (relCurve C K).LocalEquations) :
    Submodule.map (thetaFieldRead C K π a)
        (d.vanishingSubmodule K (relCover C K (fiberTwoCover π)).V₀
          (relCover C K (fiberTwoCover π)).V₁ (relThetaCocycle C K π a))
      = Scheme.divisorSections K
          (thetaFieldDivisor C K π a - Scheme.presentationDivisor K d.presentation) ⊤ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact (mem_vanishingSubmodule_iff_thetaFieldRead_mem C K π a d s).mp hs
  · intro f hf
    have hle : thetaFieldDivisor C K π a - Scheme.presentationDivisor K d.presentation
        ≤ thetaFieldDivisor C K π a := by
      refine Scheme.CurveDivisor.le_iff_coeffAt.mpr fun x hx => ?_
      rw [Scheme.CurveDivisor.coeffAt_sub]
      have h0 := Scheme.zero_le_coeffAt_presentationDivisor K d hx
      omega
    have hmono : Scheme.divisorSections K
        (thetaFieldDivisor C K π a - Scheme.presentationDivisor K d.presentation) ⊤
        ≤ Scheme.divisorSections K (thetaFieldDivisor C K π a) ⊤ := by
      rw [Scheme.divisorSections_of_nonempty K (top_opens_nonempty (X := relCurve C K)),
        Scheme.divisorSections_of_nonempty K (top_opens_nonempty (X := relCurve C K))]
      exact Scheme.boundedSections_mono K hle ⊤
    obtain ⟨s, hs⟩ := exists_thetaFieldRead_eq C K π a (hmono hf)
    exact ⟨s, (mem_vanishingSubmodule_iff_thetaFieldRead_mem C K π a d s).mpr
      (hs.symm ▸ hf), hs⟩

end Pointwise

/-! ## Φ — the dictionary at the free window, and the §G-3 keystones -/

section Phi

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance instOverCleftDict : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable (a : ℕ)
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **Φ, the field window→functionField dictionary** (`informal/spec-w4-gates.md` §G-3
keystone): the injective `K`-linear reading of the free window `K ⊗[k] H_a` into the
function field of the fibre curve — the window identification `relThetaWindowEquiv`,
the theta-trivialization reading `thetaFieldRead`, and the class-comparison shift
`thetaFieldShiftUnit` aligning the image with the transported window divisor
`windowTransportDivisor C K π a` (the abstract `N` of the `N`-pack). -/
noncomputable def divFamPhi
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    (K ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) →ₗ[K]
      (relCurve C K).functionField :=
  (Scheme.mulLinear K
      ((thetaFieldShiftUnit C K π a : (relCurve C K).functionFieldˣ) :
        (relCurve C K).functionField)).comp
    ((thetaFieldRead C K π a).comp (relThetaWindowEquiv C K π a hH1).toLinearMap)

omit [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **`hΦinj`** (§G-3 keystone): the dictionary `Φ` is injective. -/
theorem divFamPhi_injective
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    Function.Injective (divFamPhi C K π a hH1) := by
  refine Function.Injective.comp (g := Scheme.mulLinear K _) ?_
    (Function.Injective.comp (g := thetaFieldRead C K π a)
      (thetaFieldRead_injective C K π a) (relThetaWindowEquiv C K π a hH1).injective)
  intro u v huv
  exact mul_left_cancel₀ (Units.ne_zero (thetaFieldShiftUnit C K π a)) huv

/-- **The image dictionary at an arbitrary divisor family** (the general form of
`hΦwin`): `Φ` carries the window submodule `K_a(d)` exactly onto the section space of
`windowTransportDivisor C K π a − div d` — the sections dictionary at the field point,
submodule form. -/
theorem map_divFamPhi_divisorWindow
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (d : (relCurve C K).LocalEquations) :
    Submodule.map (divFamPhi C K π a hH1) (divisorWindow d hH1)
      = Scheme.divisorSections K
          (windowTransportDivisor C K π a
            - Scheme.presentationDivisor K d.presentation) ⊤ := by
  have h1 : Submodule.map (relThetaWindowEquiv C K π a hH1).toLinearMap
      (divisorWindow d hH1)
      = d.vanishingSubmodule K (relCover C K (fiberTwoCover π)).V₀
          (relCover C K (fiberTwoCover π)).V₁ (relThetaCocycle C K π a) := by
    rw [divisorWindow]
    exact Submodule.map_comap_eq_of_surjective
      (relThetaWindowEquiv C K π a hH1).surjective _
  have hmk : Units.mk0
      ((thetaFieldShiftUnit C K π a : (relCurve C K).functionFieldˣ) :
        (relCurve C K).functionField)
      (Units.ne_zero (thetaFieldShiftUnit C K π a)) = thetaFieldShiftUnit C K π a :=
    Units.ext rfl
  simp only [divFamPhi]
  rw [Submodule.map_comp, Submodule.map_comp, h1,
    map_thetaFieldRead_vanishingSubmodule C K π a d,
    map_mulLinear_divisorSections_top K
      (Units.ne_zero (thetaFieldShiftUnit C K π a)) _]
  congr 1
  rw [hmk, ← divOf_thetaFieldShiftUnit C K π a]
  abel

end Phi

/-! ## The keystone at the ledger window: the `ε`-threading discharged -/

section Keystone

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable (K : Type u) [Field K] [Algebra k K]
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftDictKey : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **`hΦwin`, the §G-3 keystone** in the threaded shape of
`Picard/DivisorFamilyEpsMono.lean:229-234`: at the ledger embedding exponent
`M = windowM_choice π hπ g`, the dictionary `Φ = divFamPhi` carries the first component
of the `ε`-window of a certified divisor family exactly onto
`H⁰(𝒪(N − divFamDivisor F))` at the `N`-pack divisor `N = windowN C K hπ g`.  With
`divFamPhi_injective` this discharges the `Φ, hΦinj, hΦwin` threading (the `N`-pack
facts are `RiemannRoch/WindowFieldTransport.lean`). -/
theorem map_divFamPhi_eps_fst (g : ℕ) (G : CertifiedDivisorFamily C K π g) :
    Submodule.map
        (divFamPhi C K π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g))
        ((divFamEps hπ g (DivFam.mk G)).1)
      = Scheme.divisorSections K
          (windowN C K hπ g - divFamDivisor (DivFam.mk G)) ⊤ := by
  have h1 : (divFamEps hπ g (DivFam.mk G)).1
      = divisorWindow G.eqns (relThetaPairH1_windowM C π hπ g) := rfl
  rw [h1, map_divFamPhi_divisorWindow C K π (windowM_choice π hπ g)
    (relThetaPairH1_windowM C π hπ g) G.eqns]
  rfl

end Keystone

end AlgebraicGeometry
