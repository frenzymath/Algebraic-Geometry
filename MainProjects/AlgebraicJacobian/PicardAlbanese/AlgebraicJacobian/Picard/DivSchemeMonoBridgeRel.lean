/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeMonoBridgeRelKit
import AlgebraicJacobian.Picard.DivSchemeMonoBridgeRelWindow
import AlgebraicJacobian.Picard.DivSchemeMonoBridgeField

/-!
# DDR-8 — the `hwin` seam over a general test ring: the relative mono, seam-free

This file closes the ONE named seam `hwin` of `Picard/DivSchemeMonoBridge.lean` over an
ARBITRARY commutative test ring `R` (no Noetherian hypothesis), completing the relative
mono: **`divFam_divEq_of_eps_eq_total`** — two certified divisor families with equal
`ε`-pairs are equal in `DivFam`, with no residual hypothesis beyond the standing curve
normalizations `hO`/`hχ` over the base field.

## The fibre-stalk transfer (the I-0231 recipe, section-level)

At a point `z` with base prime `s := (algebraMap R 𝒪_z)⁻¹(m_z)` and residue field
`κ(s)`, the window generation transports from the fibre — with NO new scheme theory:

* the field-level generation (`stalkIdeal_le_span_windowGerm_of_field`) holds on
  `relCurve C κ(s)` for the base-changed family `G.mapAlg κ(s)`;
* per piece of the certified adaptation, the fibre stalk ideal is read on SECTIONS:
  the germ chain `span_twistGermSet_le_map_germ_fst/snd` (any germ of the window germ
  set is, up to the cocycle unit, the germ of a piece-restricted window section) plus
  the affine local-global principle (`IsAffineOpen.mem_of_germ_mem_map`, Kit) give
  `pulledEqn ∈ (piece-restricted κ(s)-window)` in the fibre piece ring;
* the κ(s)-window is the pushed R-window (`divFamEps_mapAlg`, G-2), and its piece
  restrictions are the compared R-window restrictions
  (`piecesMap_windowRes_cancelBaseChange`, the crux triangle at the pieces), so the
  membership descends through the piece-level term identification
  (`pieceTermBaseChange`) and the fibre-descent kit
  (`exists_smul_mem_sup_map_of_one_tmul_mem_map`): `t • eqn ∈ (window) ⊔ s·B` with
  `t ∉ s`;
* the germ of `t` is a unit of `𝒪_z` (`t ∉ s`!), so the stalk ideal lands in
  `⟨window germs⟩ ⊔ s·𝒪_z` — exactly the threaded `hwin` shape.

No Nakayama: the landed unit trick of `DivSchemeMonoBridge` consumes the mod-`s`
generation directly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.stalkOverAlgebra
attribute [local instance 10000] relCurve.instOver

/-! ## §3 The `hwin` discharge over a general test ring -/

section RelWindow

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

attribute [local instance] instOverCleftWFT

variable [hsmC : SmoothOfRelativeDimension 1 C.hom] [hprC : IsProper C.hom]
  [hgiC : GeometricallyIrreducible C.hom]
variable [hsmL : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [hintL : IsIntegral C.left]
  [hlftL : LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [hqcL : QuasiCompact (C.left ↘ Spec (.of k))]
  [hdom : IsDominant π]
variable [hfin0 : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [hfin1 : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

-- The fibre-curve geometric package at every field extension, re-keyed on the
-- `relCurve` spelling (the `DivisorThetaFibreData` local-instance pack).
noncomputable local instance instIsIntegralRelCurveRel (K : Type u) [Field K]
    [Algebra k K] : IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveRel (K : Type u) [Field K]
    [Algebra k K] :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveRel (K : Type u) [Field K] [Algebra k K] :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveRel (K : Type u) [Field K] [Algebra k K] :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveRel (K : Type u) [Field K]
    [Algebra k K] : Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveRel (K : Type u) [Field K]
    [Algebra k K] : Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

omit hsmL hintL hlftL hqcL hfin0 hfin1 in
/-- `h⁰(𝒪) = 1` at every field extension (`h0_moduleKSheaf` at the base-changed
bundle). -/
private lemma h0_relCurve (K : Type u) [Field K] [Algebra k K] :
    Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1 := by
  haveI : IsProper (baseChangeBundle C K).hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C K).hom :=
    instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible (baseChangeBundle C K).hom :=
    instGeometricallyIrreducibleSndLeft C K
  exact h0_moduleKSheaf (baseChangeBundle C K)

omit hsmL hintL hlftL hqcL hfin0 hfin1 in
/-- `χ(𝒪) = 1 − g` at every field extension, from the base normalization (file-local
re-derivation of the `DivisorThetaFibreData` private `chi_relCurve_of_chi`). -/
private lemma chi_relCurve (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (K : Type u) [Field K] [Algebra k K] :
    Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ) := by
  haveI : IsProper (baseChangeBundle C K).hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C K).hom :=
    instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible (baseChangeBundle C K).hom :=
    instGeometricallyIrreducibleSndLeft C K
  have h1 : Sheaf.chi ((relCurve C K).moduleKSheaf K)
      = 1 - (genus (baseChangeBundle C K) : ℤ) := chi_moduleKSheaf (baseChangeBundle C K)
  have h2 : genus (baseChangeBundle C K) = genus C := genus_baseField C K
  have h3 : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (genus C : ℤ) := chi_moduleKSheaf C
  have h4 : (genus C : ℤ) = (g : ℤ) := by rw [h3] at hχ; linarith
  rw [h1, h2, h4]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
-- The two-ring instance towers (R and κ(s)) and the window-submodule defeqs exceed the
-- default limits; the I-0198 escape hatch, as in `Picard/DivSchemeMonoBridgeField.lean`.
set_option synthInstance.maxHeartbeats 800000 in
/-- **The fibre-window clearance at a piece** (the I-0231 fibre-stalk transfer,
section-level): for a certified family over `R`, a prime `s` of `R` and a piece `j` of
the adaptation, some multiple `t • f_j` with `t ∉ s` of the piece equation lies in the
ideal generated by the piece-restricted `ε₁`-window sections together with `s`.  The
window generation at the residue field `κ(s)` (`stalkIdeal_le_span_windowGerm_of_field`
for `G.mapAlg κ(s)`, read through `divFamEps_mapAlg` and the germ chain) gives the
membership on the fibre piece by the affine local-global principle; it descends through
the piece-level term identification and the fibre-descent kit. -/
theorem CertifiedDivisorFamily.exists_smul_eqn_mem_window_sup (g : ℕ)
    (G : CertifiedDivisorFamily C R π g)
    (hOk : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχk : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (s : Ideal R) [s.IsPrime] (j : G.adaptation.index) :
    ∃ t : R, t ∉ s ∧
      t • G.adaptation.eqn j
        ∈ Ideal.span ((fun x => G.adaptation.toFinCoverData.windowRes
              (windowM_choice π hπ g) j
              (relThetaWindowEquiv C R π (windowM_choice π hπ g)
                (relThetaPairH1_windowM C π hπ g) x)) ''
            ↑((divFamEps hπ g (DivFam.mk G)).1))
          ⊔ Ideal.map (algebraMap R Γ(relCurve C R, G.adaptation.pieces j)) s := by
  -- the fibre normalizations at `κ(s)`
  have hOK : Sheaf.h0 ((relCurve C s.ResidueField).moduleKSheaf s.ResidueField) = 1 :=
    h0_relCurve s.ResidueField
  have hχK : Sheaf.chi ((relCurve C s.ResidueField).moduleKSheaf s.ResidueField)
      = 1 - (g : ℤ) := chi_relCurve g hχk s.ResidueField
  -- the κ(s)-window is the pushed R-window (G-2 ε-naturality)
  have hepsEq : (divFamEps hπ g (DivFam.mk (G.mapAlg s.ResidueField g))).1
      = windowBaseChange s.ResidueField (divFamEps hπ g (DivFam.mk G)).1 := by
    rw [← DivFam.mapAlg_mk,
      divFamEps_mapAlg C s.ResidueField π hπ g hOk hχk (DivFam.mk G)]
  -- the pulled piece equation lies in the piece-restricted κ(s)-window span
  have hJ : G.adaptation.pulledEqn s.ResidueField j
      ∈ Ideal.span (G.adaptation.toFinCoverData.piecesMap s.ResidueField j ''
          ((fun x => G.adaptation.toFinCoverData.windowRes
              (windowM_choice π hπ g) j
              (relThetaWindowEquiv C R π (windowM_choice π hπ g)
                (relThetaPairH1_windowM C π hπ g) x)) ''
            ↑((divFamEps hπ g (DivFam.mk G)).1))) := by
    refine ((G.adaptation.toFinCoverData.baseChange
      s.ResidueField).isAffineOpen_pieces j).mem_of_germ_mem_map ?_
    intro z hz
    -- the germ of the pulled equation generates the fibre stalk ideal
    have hgen : ((relCurve C s.ResidueField).presheaf.germ
        ((G.adaptation.toFinCoverData.baseChange s.ResidueField).pieces j) z hz).hom
        (G.adaptation.pulledEqn s.ResidueField j)
        ∈ (G.mapAlg s.ResidueField g).eqns.stalkIdeal z := by
      rw [(G.mapAlg s.ResidueField g).adaptation.stalkIdeal_eq_span_germ_eqn j hz]
      exact Ideal.subset_span rfl
    -- the field-level window generation, read through the pushed window
    have hle1 := CertifiedDivisorFamily.stalkIdeal_le_span_windowGerm_of_field
      (K := s.ResidueField) hπ g (G.mapAlg s.ResidueField g) hOk hχk hOK hχK z
    have hset : divFamEpsWindowGermSet hπ g (DivFam.mk (G.mapAlg s.ResidueField g)) z
        = Scheme.twistGermSet
            (A := s.ResidueField)
            (V₀ := (relCover C s.ResidueField (fiberTwoCover π)).V₀)
            (V₁ := (relCover C s.ResidueField (fiberTwoCover π)).V₁)
            (gc := relThetaCocycle C s.ResidueField π (windowM_choice π hπ g))
            (↑(Submodule.map (relThetaWindowEquiv C s.ResidueField π
                (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)).toLinearMap
              (windowBaseChange s.ResidueField (divFamEps hπ g (DivFam.mk G)).1))) z := by
      unfold divFamEpsWindowGermSet
      rw [hepsEq]
    rw [hset] at hle1
    -- the germ chain, per chart
    cases j with
    | inl ℓ =>
      have hchain := span_twistGermSet_le_map_germ_fst
        (A := s.ResidueField)
        (V₀ := (relCover C s.ResidueField (fiberTwoCover π)).V₀)
        (V₁ := (relCover C s.ResidueField (fiberTwoCover π)).V₁)
        (gc := relThetaCocycle C s.ResidueField π (windowM_choice π hπ g))
        (T := ↑(Submodule.map (relThetaWindowEquiv C s.ResidueField π
            (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)).toLinearMap
          (windowBaseChange s.ResidueField (divFamEps hπ g (DivFam.mk G)).1)))
        (le_inf le_top ((G.adaptation.toFinCoverData.baseChange
          s.ResidueField).pieces_inl_le ℓ)) z hz
      have hpush := span_resFst_windowBaseChange_le (R' := s.ResidueField)
        (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)
        G.adaptation.toFinCoverData ℓ ((divFamEps hπ g (DivFam.mk G)).1)
      exact Ideal.map_mono hpush (hchain (hle1 hgen))
    | inr ℓ =>
      have hchain := span_twistGermSet_le_map_germ_snd
        (A := s.ResidueField)
        (V₀ := (relCover C s.ResidueField (fiberTwoCover π)).V₀)
        (V₁ := (relCover C s.ResidueField (fiberTwoCover π)).V₁)
        (gc := relThetaCocycle C s.ResidueField π (windowM_choice π hπ g))
        (T := ↑(Submodule.map (relThetaWindowEquiv C s.ResidueField π
            (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)).toLinearMap
          (windowBaseChange s.ResidueField (divFamEps hπ g (DivFam.mk G)).1)))
        (le_inf le_top ((G.adaptation.toFinCoverData.baseChange
          s.ResidueField).pieces_inr_le ℓ)) z hz
      have hpush := span_resSnd_windowBaseChange_le (R' := s.ResidueField)
        (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)
        G.adaptation.toFinCoverData ℓ ((divFamEps hπ g (DivFam.mk G)).1)
      exact Ideal.map_mono hpush (hchain (hle1 hgen))
  -- descend through the piece-level term identification
  have h1 : G.adaptation.toFinCoverData.pieceTermBaseChange s.ResidueField j
      ((1 : s.ResidueField) ⊗ₜ[R] G.adaptation.eqn j)
      = G.adaptation.pulledEqn s.ResidueField j :=
    G.adaptation.toFinCoverData.pieceTermBaseChange_one_tmul s.ResidueField j
      (G.adaptation.eqn j)
  have hspan_le : Ideal.span (G.adaptation.toFinCoverData.piecesMap s.ResidueField j ''
        ((fun x => G.adaptation.toFinCoverData.windowRes
            (windowM_choice π hπ g) j
            (relThetaWindowEquiv C R π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g) x)) ''
          ↑((divFamEps hπ g (DivFam.mk G)).1)))
      ≤ Ideal.map ((G.adaptation.toFinCoverData.pieceTermBaseChange
            s.ResidueField j).toRingEquiv : _ →+* _)
          (Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := s.ResidueField))
            (Ideal.span ((fun x => G.adaptation.toFinCoverData.windowRes
                (windowM_choice π hπ g) j
                (relThetaWindowEquiv C R π (windowM_choice π hπ g)
                  (relThetaPairH1_windowM C π hπ g) x)) ''
              ↑((divFamEps hπ g (DivFam.mk G)).1)))) := by
    rw [Ideal.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw1 : G.adaptation.toFinCoverData.piecesMap s.ResidueField j w
        = G.adaptation.toFinCoverData.pieceTermBaseChange s.ResidueField j
            ((1 : s.ResidueField) ⊗ₜ[R] w) :=
      (G.adaptation.toFinCoverData.pieceTermBaseChange_one_tmul s.ResidueField j w).symm
    rw [hw1]
    exact Ideal.mem_map_of_mem _
      (Ideal.mem_map_of_mem _ (Ideal.subset_span hw))
  -- pull back along the equivalence and clear denominators (the fibre-descent kit)
  have hmem : (1 : s.ResidueField) ⊗ₜ[R] G.adaptation.eqn j
      ∈ Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := s.ResidueField))
          (Ideal.span ((fun x => G.adaptation.toFinCoverData.windowRes
              (windowM_choice π hπ g) j
              (relThetaWindowEquiv C R π (windowM_choice π hπ g)
                (relThetaPairH1_windowM C π hπ g) x)) ''
            ↑((divFamEps hπ g (DivFam.mk G)).1))) := by
    refine (Ideal.apply_mem_of_equiv_iff
      (f := (G.adaptation.toFinCoverData.pieceTermBaseChange
        s.ResidueField j).toRingEquiv)).mp ?_
    have h2 : (G.adaptation.toFinCoverData.pieceTermBaseChange
        s.ResidueField j).toRingEquiv
        ((1 : s.ResidueField) ⊗ₜ[R] G.adaptation.eqn j)
        = G.adaptation.pulledEqn s.ResidueField j := h1
    rw [h2]
    exact hspan_le hJ
  exact exists_smul_mem_sup_map_of_one_tmul_mem_map s hmem

omit hsmC hprC hgiC in
set_option maxRecDepth 8000 in
/-- The germ at a point of a piece of a window piece restriction lies in the window
germ set (the two chart cases of the `divFamEpsWindowGermSet` union). -/
private lemma germ_windowRes_mem (g : ℕ) (G : CertifiedDivisorFamily C R π g)
    (j : G.adaptation.index) {z : relCurve C R} (hz : z ∈ G.adaptation.pieces j)
    {x : R ⊗[k] ↥(Scheme.divisorSections k
      (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)}
    (hx : x ∈ (divFamEps hπ g (DivFam.mk G)).1) :
    ((relCurve C R).presheaf.germ (G.adaptation.pieces j) z hz).hom
      (G.adaptation.toFinCoverData.windowRes (windowM_choice π hπ g) j
        (relThetaWindowEquiv C R π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g) x))
      ∈ divFamEpsWindowGermSet hπ g (DivFam.mk G) z := by
  cases j with
  | inl ℓ =>
    refine Set.mem_union_left _
      ⟨relThetaWindowEquiv C R π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g) x,
        Submodule.mem_map_of_mem hx,
        le_inf le_top (G.adaptation.toFinCoverData.pieces_inl_le ℓ) hz, ?_⟩
    exact germ_resHom
      (le_inf le_top (G.adaptation.toFinCoverData.pieces_inl_le ℓ)) z hz _
  | inr ℓ =>
    refine Set.mem_union_right _
      ⟨relThetaWindowEquiv C R π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g) x,
        Submodule.mem_map_of_mem hx,
        le_inf le_top (G.adaptation.toFinCoverData.pieces_inr_le ℓ) hz, ?_⟩
    exact germ_resHom
      (le_inf le_top (G.adaptation.toFinCoverData.pieces_inr_le ℓ)) z hz _

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
-- The two-ring instance towers and the window-submodule defeqs exceed the default
-- limits; the I-0198 escape hatch, as in `Picard/DivSchemeMonoBridgeField.lean`.
set_option synthInstance.maxHeartbeats 800000 in
/-- **The window generation input over a general test ring** (the `hwin` seam of
`Picard/DivSchemeMonoBridge.lean`, DISCHARGED): for every certified family over ANY
commutative test ring and every point `z`, the stalk ideal is generated by the
`ε₁`-window germs modulo the base prime `s = (algebraMap R 𝒪_z)⁻¹(m_z)` — in exactly
the shape threaded through `divFam_divEq_of_eps_eq'`.  The witness prime is the base
point of `z`; the generation is the fibre-window clearance pushed through the germ,
with `t ∉ s` becoming a unit of the local ring `𝒪_z`. -/
theorem CertifiedDivisorFamily.windowGen (g : ℕ) (G : CertifiedDivisorFamily C R π g)
    (hOk : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχk : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    ∀ z : relCurve C R, ∃ s : Ideal R,
      (∀ r ∈ s, algebraMap R ((relCurve C R).presheaf.stalk z) r
        ∈ IsLocalRing.maximalIdeal ((relCurve C R).presheaf.stalk z)) ∧
      G.eqns.stalkIdeal z
        ≤ Ideal.span (divFamEpsWindowGermSet hπ g (DivFam.mk G) z)
          ⊔ Ideal.map (algebraMap R ((relCurve C R).presheaf.stalk z)) s := by
  intro z
  obtain ⟨j, hz⟩ := G.adaptation.toFinCoverData.exists_mem_pieces z
  refine ⟨(IsLocalRing.maximalIdeal ((relCurve C R).presheaf.stalk z)).comap
    (algebraMap R ((relCurve C R).presheaf.stalk z)), fun r hr => hr, ?_⟩
  obtain ⟨t, ht, hmem⟩ := G.exists_smul_eqn_mem_window_sup hπ g hOk hχk
    ((IsLocalRing.maximalIdeal ((relCurve C R).presheaf.stalk z)).comap
      (algebraMap R ((relCurve C R).presheaf.stalk z))) j
  letI : Algebra Γ(relCurve C R, G.adaptation.pieces j)
      ((relCurve C R).presheaf.stalk z) :=
    (relCurve C R).presheaf.algebra_section_stalk ⟨z, hz⟩
  haveI htower : IsScalarTower R Γ(relCurve C R, G.adaptation.pieces j)
      ((relCurve C R).presheaf.stalk z) :=
    Scheme.stalkOverAlgebra_isScalarTower R hz
  rw [G.adaptation.stalkIdeal_eq_span_germ_eqn j hz, Ideal.span_le,
    Set.singleton_subset_iff]
  -- push the clearance through the germ
  have hpush : ((relCurve C R).presheaf.germ (G.adaptation.pieces j) z hz).hom
      (t • G.adaptation.eqn j)
      ∈ Ideal.span (divFamEpsWindowGermSet hπ g (DivFam.mk G) z)
        ⊔ Ideal.map (algebraMap R ((relCurve C R).presheaf.stalk z))
            ((IsLocalRing.maximalIdeal ((relCurve C R).presheaf.stalk z)).comap
              (algebraMap R ((relCurve C R).presheaf.stalk z))) := by
    have h0 := Ideal.mem_map_of_mem
      ((relCurve C R).presheaf.germ (G.adaptation.pieces j) z hz).hom hmem
    rw [Ideal.map_sup] at h0
    have hleft : Ideal.map
        ((relCurve C R).presheaf.germ (G.adaptation.pieces j) z hz).hom
        (Ideal.span ((fun x => G.adaptation.toFinCoverData.windowRes
            (windowM_choice π hπ g) j
            (relThetaWindowEquiv C R π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g) x)) ''
          ↑((divFamEps hπ g (DivFam.mk G)).1)))
        ≤ Ideal.span (divFamEpsWindowGermSet hπ g (DivFam.mk G) z) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact Ideal.subset_span (germ_windowRes_mem hπ g G j hz hx)
    have hright : Ideal.map
        ((relCurve C R).presheaf.germ (G.adaptation.pieces j) z hz).hom
        (Ideal.map (algebraMap R Γ(relCurve C R, G.adaptation.pieces j))
          ((IsLocalRing.maximalIdeal ((relCurve C R).presheaf.stalk z)).comap
            (algebraMap R ((relCurve C R).presheaf.stalk z))))
        ≤ Ideal.map (algebraMap R ((relCurve C R).presheaf.stalk z))
            ((IsLocalRing.maximalIdeal ((relCurve C R).presheaf.stalk z)).comap
              (algebraMap R ((relCurve C R).presheaf.stalk z))) := by
      rw [Ideal.map_map]
      refine le_of_eq (congrArg (Ideal.map · _) ?_)
      exact RingHom.ext fun r => Scheme.germ_algebraMap_overSections R hz r
    exact sup_le_sup hleft hright h0
  -- the unit trick: `t ∉ s` makes the germ of `t` a unit
  have hgermsmul : ((relCurve C R).presheaf.germ (G.adaptation.pieces j) z hz).hom
      (t • G.adaptation.eqn j)
      = algebraMap R ((relCurve C R).presheaf.stalk z) t
        * ((relCurve C R).presheaf.germ (G.adaptation.pieces j) z hz).hom
            (G.adaptation.eqn j) := by
    rw [Algebra.smul_def, map_mul, Scheme.germ_algebraMap_overSections]
  have hunit : IsUnit (algebraMap R ((relCurve C R).presheaf.stalk z) t) := by
    by_contra hnu
    exact ht (Ideal.mem_comap.mpr
      ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)))
  obtain ⟨u, hu⟩ := hunit
  have hval : ((relCurve C R).presheaf.germ (G.adaptation.pieces j) z hz).hom
      (G.adaptation.eqn j)
      = ↑u⁻¹ * ((relCurve C R).presheaf.germ (G.adaptation.pieces j) z hz).hom
          (t • G.adaptation.eqn j) := by
    rw [hgermsmul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hval]
  exact Ideal.mul_mem_left _ _ hpush

/-- **The relative mono / Law-1 core, seam-free** (DDR-8 COMPLETE): two certified
divisor families of degree `g` over ANY commutative test ring `R` — no Noetherian
hypothesis — with equal `ε`-pairs are equal in `DivFam`.  The only inputs beyond the
standing geometric package are the base-field curve normalizations `hO`/`hχ`.  This
composes the pinned `divFam_divEq_of_eps_eq'` of `Picard/DivSchemeMonoBridge.lean` with
the discharged window generation `CertifiedDivisorFamily.windowGen`. -/
theorem divFam_divEq_of_eps_eq_total (g : ℕ) (G G' : CertifiedDivisorFamily C R π g)
    (heps : divFamEps hπ g (DivFam.mk G) = divFamEps hπ g (DivFam.mk G'))
    (hOk : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχk : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    DivFam.mk G = DivFam.mk G' :=
  divFam_divEq_of_eps_eq' hπ g G G' heps
    (G.windowGen hπ g hOk hχk) (G'.windowGen hπ g hOk hχk)

end RelWindow

end AlgebraicGeometry
