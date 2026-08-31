/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeUnivFibreHdiv

/-!
# DD-4 — the chart-level carve pin: base-change transport and the reading bridge

The carve rank-`g` fibre non-collapse `hinj` must, to sidestep the piece-level definitional
cycle (I-0293), be stated at the **chart level**: over the whole pinned chart
`V = relPinnedChart C R π b` (`le_rfl`, `h z`-free), with base ideal
`J = ⟨relThetaResSide a b le_rfl ψ : ψ ∈ K⟩` and chart colength `Γ(V) ⧸ J`.  The universal
carve `divUniversal_carve_residueField` is itself `h z`-free, so it supplies the chart-level
pin; the piece-level `hsub` then follows by localizing to `D(h z) ⊆ V` *after* `h z` is
chosen (a later lane).

This file assembles the `h z`-free ingredients of that pin:

* `relPinnedTermBaseChangeAlg` / `relPinnedQuotBaseChangeAlg` — **the chart-level colength
  base-change transport** `R' ⊗[R] (Γ(V) ⧸ (E)) ≃ₐ[R'] Γ(V') ⧸ (relPinnedSectionsMap '' E)`,
  the whole-chart (`le_rfl`) analogue of `pinnedPieceQuotBaseChangeAlg`, built on the
  chart-ring iso `relTermBaseChangeAlg` (no basic-open localization);
* `mk_tmul_one_eq_zero_iff_relPinnedSectionsMap_mem` — the transported fibre-vanishing
  clause, `[s] ⊗ₜ 1 = 0 ↔ relPinnedSectionsMap s ∈ span (image)`.

These are the chart-level plumbing the carve pin (`hinj_chart`) consumes to identify
`κ(p) ⊗ (Γ(V) ⧸ J)` with the fibre chart colength.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable (π : C.left ⟶ P1 k) [IsFinite π] {a : ℕ}

namespace ThetaGeneratorSeed

/-! ## The chart-level base-change transport (whole chart `V`, `le_rfl`) -/

/-- **The side-uniform chart-ring base change**: the whole-chart (`le_rfl`) analogue of
`pinnedPieceSectionsMap`, cased over the side `b` to `relTermBaseChangeAlg` at the fibre
chart.  Its target chart ring is that of the base-changed pinned chart. -/
noncomputable def relPinnedTermBaseChangeAlg (b : Bool) :
    R' ⊗[R] Γ(relCurve C R, relPinnedChart C R π b) ≃ₐ[R']
      Γ(relCurve C R', relPinnedChart C R' π b) :=
  match b with
  | false =>
      relTermBaseChangeAlg R' (fiberChart₀ π)
        (fiberTwoCover π).isAffineOpen₀.isCompact
        (fiberTwoCover π).isAffineOpen₀.isQuasiSeparated
  | true =>
      relTermBaseChangeAlg R' (fiberChart₁ π)
        (fiberTwoCover π).isAffineOpen₁.isCompact
        (fiberTwoCover π).isAffineOpen₁.isQuasiSeparated

/-- The chart-ring base change on `1 ⊗ s` is the side-uniform chart comparison
`relPinnedSectionsMap`. -/
lemma relPinnedTermBaseChangeAlg_one_tmul (b : Bool)
    (s : Γ(relCurve C R, relPinnedChart C R π b)) :
    relPinnedTermBaseChangeAlg C R R' π b ((1 : R') ⊗ₜ[R] s)
      = relPinnedSectionsMap C R R' π b s := by
  cases b with
  | false =>
      have h := relTermBaseChangeAlg_tmul (C := C) (R := R) R' (fiberChart₀ π)
        (fiberTwoCover π).isAffineOpen₀.isCompact
        (fiberTwoCover π).isAffineOpen₀.isQuasiSeparated (1 : R') s
      rw [one_smul] at h
      exact h
  | true =>
      have h := relTermBaseChangeAlg_tmul (C := C) (R := R) R' (fiberChart₁ π)
        (fiberTwoCover π).isAffineOpen₁.isCompact
        (fiberTwoCover π).isAffineOpen₁.isQuasiSeparated (1 : R') s
      rw [one_smul] at h
      exact h

/-- The chart-ring base change carries the extended span of a set of equations to the span
of the compared equations (`Ideal.map_span` + `relPinnedTermBaseChangeAlg_one_tmul`). -/
lemma relPinnedSpan_map_eq (b : Bool)
    (E : Set Γ(relCurve C R, relPinnedChart C R π b)) :
    Ideal.span (relPinnedSectionsMap C R R' π b '' E) =
      ((Ideal.span E).map (Algebra.TensorProduct.includeRight (R := R) (A := R')
        (B := Γ(relCurve C R, relPinnedChart C R π b)))).map
        (relPinnedTermBaseChangeAlg C R R' π b : _ →+* _) := by
  rw [Ideal.map_span, Ideal.map_span, ← Set.image_comp]
  exact congrArg Ideal.span (Set.image_congr fun s _ =>
    (relPinnedTermBaseChangeAlg_one_tmul C R R' π b s).symm)

/-- **The chart-level colength base-change transport**: for a set `E` of equations on the
whole pinned chart `V`, `R' ⊗[R] (Γ(V) ⧸ (E)) ≃ₐ[R'] Γ(V') ⧸ (relPinnedSectionsMap '' E)`.
The whole-chart (`le_rfl`) analogue of `pinnedPieceQuotBaseChangeAlg`, with no basic-open
localization: quotient right-exactness followed by transport along the chart-ring iso
`relPinnedTermBaseChangeAlg`. -/
noncomputable def relPinnedQuotBaseChangeAlg (b : Bool)
    (E : Set Γ(relCurve C R, relPinnedChart C R π b)) :
    R' ⊗[R] (Γ(relCurve C R, relPinnedChart C R π b) ⧸ Ideal.span E) ≃ₐ[R']
      Γ(relCurve C R', relPinnedChart C R' π b) ⧸
        Ideal.span (relPinnedSectionsMap C R R' π b '' E) :=
  (Algebra.TensorProduct.tensorQuotientEquiv R'
    Γ(relCurve C R, relPinnedChart C R π b) R' (Ideal.span E)).trans
    (Ideal.quotientEquivAlg _ _ (relPinnedTermBaseChangeAlg C R R' π b)
      (relPinnedSpan_map_eq C R R' π b E))

/-- The chart-level colength transport on a pure tensor of a residue class:
`1 ⊗ [s] ↦ [relPinnedSectionsMap s]`. -/
lemma relPinnedQuotBaseChangeAlg_one_tmul_mk (b : Bool)
    (E : Set Γ(relCurve C R, relPinnedChart C R π b))
    (s : Γ(relCurve C R, relPinnedChart C R π b)) :
    relPinnedQuotBaseChangeAlg C R R' π b E
        ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span E) s) =
      Ideal.Quotient.mk (Ideal.span (relPinnedSectionsMap C R R' π b '' E))
        (relPinnedSectionsMap C R R' π b s) := by
  have h1 : relPinnedQuotBaseChangeAlg C R R' π b E
      ((1 : R') ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span E) s) =
      Ideal.Quotient.mk (Ideal.span (relPinnedSectionsMap C R R' π b '' E))
        (relPinnedTermBaseChangeAlg C R R' π b ((1 : R') ⊗ₜ[R] s)) := rfl
  rw [h1, relPinnedTermBaseChangeAlg_one_tmul]

/-- **The transported fibre-vanishing clause** (chart level): the residue class `[s]` of a
chart section dies in the fibre `κ(p)` (`[s] ⊗ₜ 1 = 0`) iff its image
`relPinnedSectionsMap s` in the base-changed chart lies in the ideal generated by the
transported equations `relPinnedSectionsMap '' E`. -/
lemma mk_tmul_one_eq_zero_iff_relPinnedSectionsMap_mem (b : Bool)
    (E : Set Γ(relCurve C R, relPinnedChart C R π b))
    (s : Γ(relCurve C R, relPinnedChart C R π b)) :
    (Ideal.Quotient.mk (Ideal.span E) s ⊗ₜ[R] (1 : R')
        : (Γ(relCurve C R, relPinnedChart C R π b) ⧸ Ideal.span E) ⊗[R] R') = 0
      ↔ relPinnedSectionsMap C R R' π b s
          ∈ Ideal.span (relPinnedSectionsMap C R R' π b '' E) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    ← relPinnedQuotBaseChangeAlg_one_tmul_mk C R R' π b E s,
    map_eq_zero_iff _ (relPinnedQuotBaseChangeAlg C R R' π b E).injective,
    ← LinearEquiv.map_eq_zero_iff (TensorProduct.comm R _ R'), TensorProduct.comm_tmul]

/-! ## The generic fibre-injectivity equivalence (`hsub ⟺ hinj`, chart level) -/

section GenericFibre

variable {R₀ : Type u} [CommRing R₀] {M N : Type u} [AddCommGroup M] [Module R₀ M]
  [AddCommGroup N] [Module R₀ N]

/-- **The generic fibre-injectivity equivalence** (the pure linear algebra behind
`hsub ⟺ hinj`, at any base prime): for an `R₀`-linear map `f : M → N`, the residue fibre of
the range inclusion `range f ↪ N` is injective iff the residue fibre of the injectivization
`f̄ = (ker f).liftQ f : M ⧸ ker f → N` is injective.  The two differ only by the (always
bijective) corestriction equivalence `ē : M ⧸ ker f ≃ range f`, so `f̄ ⊗ κ` and
`(range f).subtype ⊗ κ` are interchangeable through `ē ⊗ κ`.

This is the level-agnostic form of the landed piece-level equivalence
(`ThetaGeneratorSeed.hsub_of_forall_liftQ_rTensor_injective` /
`hinj_of_forall_sideColengthSubmodule_subtype_rTensor_injective`); the carve pin may target
whichever of the two is cleanest and still discharge the other. -/
theorem liftQ_rTensor_injective_iff_range_subtype_rTensor_injective
    (f : M →ₗ[R₀] N) (p : PrimeSpectrum R₀) :
    Function.Injective
        (((LinearMap.ker f).liftQ f le_rfl).rTensor p.asIdeal.ResidueField)
      ↔ Function.Injective
        ((LinearMap.range f).subtype.rTensor p.asIdeal.ResidueField) := by
  set fbar := (LinearMap.ker f).liftQ f le_rfl with hfbar
  have hfbar_inj : Function.Injective fbar := by
    rw [← LinearMap.ker_eq_bot, hfbar]
    exact Submodule.ker_liftQ_eq_bot' _ f rfl
  have hrange : LinearMap.range fbar = LinearMap.range f := by
    rw [hfbar, Submodule.range_liftQ]
  set g := fbar.codRestrict (LinearMap.range f)
    (fun x => hrange ▸ LinearMap.mem_range_self fbar x) with hg
  have hgcomp : (LinearMap.range f).subtype ∘ₗ g = fbar :=
    LinearMap.subtype_comp_codRestrict _ _ _
  have hg_inj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, hg, LinearMap.ker_codRestrict, LinearMap.ker_eq_bot]
    exact hfbar_inj
  have hg_surj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, hg, LinearMap.range_codRestrict, hrange,
      Submodule.comap_subtype_eq_top]
  set ebar := LinearEquiv.ofBijective g ⟨hg_inj, hg_surj⟩ with hebar
  have hfactor : fbar.rTensor p.asIdeal.ResidueField
      = (LinearMap.range f).subtype.rTensor p.asIdeal.ResidueField ∘ₗ
          g.rTensor p.asIdeal.ResidueField := by
    rw [← LinearMap.rTensor_comp, hgcomp]
  have hg_rTensor_bij : Function.Bijective (g.rTensor p.asIdeal.ResidueField) := by
    change Function.Bijective (ebar.toLinearMap.rTensor p.asIdeal.ResidueField)
    rw [← LinearEquiv.coe_rTensor]
    exact (LinearEquiv.rTensor p.asIdeal.ResidueField ebar).bijective
  rw [hfactor, LinearMap.coe_comp]
  exact Function.Injective.of_comp_iff' _ hg_rTensor_bij

end GenericFibre

/-! ## The chart-level `hsub ⟺ hinj` at the reading map -/

/-- **The chart-level reading map** `f_V^b = relThetaResSide b (le_rfl) ∘ K.subtype`: reads a
`K`-element into the whole pinned chart `Γ(V)` of the side `b` (`le_rfl`, `h z`-free).  Its
range is the chart base ideal image `N_V = ⟨read ψ : ψ ∈ K⟩`. -/
noncomputable def chartReadMap {C : Over (Spec (.of k))} {R : Type u} [CommRing R] [Algebra k R]
    {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}
    (K : Submodule R (relThetaSections C R π a)) (b : Bool) :
    ↥K →ₗ[R] Γ(relCurve C R, relPinnedChart C R π b) :=
  (relThetaResSide a b (le_rfl : relPinnedChart C R π b ≤ relPinnedChart C R π b)).comp
    K.subtype

/-- **The chart-level `hsub ⟺ hinj`** (`h z`-free): the carve fibre non-collapse
`hsub_chart` — injectivity, at every base prime `p`, of the residue fibre of the chart base
ideal inclusion `N_V = range (chartReadMap K b) ↪ Γ(V)` — is equivalent to the induced-map
fibre injectivity `hinj_chart`, the residue-fibre injectivity of the injectivization
`K ⧸ ker f_V^b → Γ(V)`.  The universal carve `divUniversal_carve_residueField` (itself
`h z`-free) supplies `hinj_chart`, which this equivalence turns into `hsub_chart`; the
piece-level `hsub` then follows by localizing to `D(h z) ⊆ V`. -/
theorem forall_chartRead_range_subtype_rTensor_injective_iff
    {C : Over (Spec (.of k))} {R : Type u} [CommRing R] [Algebra k R]
    {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}
    (K : Submodule R (relThetaSections C R π a)) (b : Bool) :
    (∀ p : PrimeSpectrum R, Function.Injective
        ((LinearMap.range (chartReadMap K b)).subtype.rTensor p.asIdeal.ResidueField))
      ↔ (∀ p : PrimeSpectrum R, Function.Injective
        (((LinearMap.ker (chartReadMap K b)).liftQ (chartReadMap K b) le_rfl).rTensor
          p.asIdeal.ResidueField)) :=
  ⟨fun h p => (liftQ_rTensor_injective_iff_range_subtype_rTensor_injective
      (chartReadMap K b) p).mpr (h p),
    fun h p => (liftQ_rTensor_injective_iff_range_subtype_rTensor_injective
      (chartReadMap K b) p).mp (h p)⟩

end ThetaGeneratorSeed

end AlgebraicGeometry
