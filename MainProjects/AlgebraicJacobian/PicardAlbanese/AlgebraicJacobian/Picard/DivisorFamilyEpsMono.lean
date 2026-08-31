/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.CarveDegree
import AlgebraicJacobian.Picard.DivisorFamilyFieldEquiv
import AlgebraicJacobian.Picard.DivisorThetaPairing

/-!
# DD-4 (Task 6) — mono-ness of the embedding `ε` at the field level

A certified divisor family over a field is recovered from its window `K_M(d)`
(`informal/dat-d-worksheet.md` §2.3.4; `informal/spec-dd-r.md` §3 item 7's fibrewise
input): the **base divisor of the window is the family divisor**, so two families with
equal `ε`-windows cut equal divisors, hence are `DivEq`
(`divFamDivisor_injective`, the landed DD-1c converse dictionary) — `divFamEps` is
injective on field points.  Equality of the FIRST components `K_M(d)` alone suffices.

## The mechanism

Fibrewise this is exactly the route DDR-8 consumes (spec-dd-r §3 items 7–8): the window
is read through the **sections dictionary** as `H⁰(𝒪(N − D_F)) ⊆ K(Y)` at the
transported embedding level `N`; the certified-degree pinch (`deg_divFamDivisor_of_carve`,
DDR-2) gives `deg D_F = g`; then the abstract-`N` recovery
(`baseDivisorAt_window_normalization`, DDR-2's stated DDR-8 hook) presents `D_F` as the
base divisor of that section space.  The base divisor is a function of the section space
alone, so equal windows force equal divisors.

## Layout

* **§1 The generic recovery** (abstract curve `Y` over a field `K`, the CarveDegreePinch
  pack): `baseDivisor_window_normalization` — the assembled-`baseDivisor` form of the
  DDR-8 hook (`bd(H⁰(𝒪(N − D))) = D`); `eq_of_divisorSections_window_eq` — **uniqueness
  of an effective degree-`g` divisor from its window section space**;
  `h0_eq_finrank_of_map_eq` — the `h⁰` shadow of a submodule-level sections dictionary
  (derives DDR-2's threaded `hdict` from the dictionary map).
* **§2 The family level** (`relCurve C K`): `baseDivisorAt_map_divFamEps` /
  `baseDivisor_map_divFamEps` — **the window-recovery keystone**
  `bd(Φ(K_M(d))) = divFamDivisor F`, in the pointwise shape DDR-8's fibrewise step
  consumes and in assembled form; `eq_of_divFamEps_fst_eq` / `eq_of_divFamEps_eq` —
  **mono-ness of `ε` on field points**.

## Threaded hypotheses (each a named seam; spellings pinned to the sibling lanes)

* `hsurj` — right exactness of the section sequence at the embedding window
  (`thetaGluedEval_surjective`, `Picard/DivisorThetaSurjectivity.lean`, gated on the
  fibrewise `hfib`); the Θ-pairing input is NOT threaded — it fires from the certificate
  (`IsCertified.isThetaPaired`, `Picard/DivisorThetaPairing.lean`).
* `hcarve` — the ε-pair carve `(♦)` (pins the statement to the certified carve locus,
  exactly as in DDR-2; the mechanism does not consume it).
* `N, hNwin, hNnorm, hNdeg, hNrank` — the base-field transport of the DD-0 embedding
  window `M·F` to `relCurve C K` (the I-0175 seam, I-0204 spellings; at `K = k` these
  are the ledger names `window_embedding` / `window_normalization` /
  `two_mul_genus_le_M_mul_windowδ`).  Discharged by the window-transport lane.
* `Φ, hΦinj, hΦwin` — **the sections dictionary at the field point, submodule form**
  (DD-4 Task 5's field content, the strengthening of DDR-2's `hdict` that mono-ness
  genuinely needs): a `K`-linear embedding of the free window `K ⊗[k] H_M` into the
  function field of `relCurve C K` carrying the family window `ε₁ = K_M(d)` onto
  `H⁰(𝒪(N − divFamDivisor F))`.  Its `h⁰` shadow `hdict` is DERIVED
  (`h0_eq_finrank_of_map_eq`), so `hdict` is not separately threaded.  This is the
  `mem_divisorWindow_iff` germ-vanishing ↔ `ordZ` pole-bound dictionary
  (`Picard/DivisorStalkIdeal.lean` + `coeffAt_eq_toAdd_ordZ_eqn`) composed with the
  `Θᵃ ↔ 𝒪(a·F_K)` bridge at `K` — the one genuinely open DD-4 field-content boundary.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

attribute [local instance] AlgebraicGeometry.Scheme.functionFieldOverModule
  AlgebraicGeometry.Scheme.overModule AlgebraicGeometry.Scheme.overSectionsAlgebra

namespace AlgebraicGeometry

open Scheme

/-! ## §1 The generic recovery on an abstract curve over a field -/

section WindowRecovery

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]

omit [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)] in
/-- **The `h⁰` shadow of a submodule-level sections dictionary**: an injective `K`-linear
reading `Φ` of an ambient module into the function field that carries a submodule `E`
onto the section space `H⁰(𝒪(A))` identifies dimensions — `h⁰(𝒪(A)) = dim_K E`.  This
derives DDR-2's threaded `hdict` from the submodule-form dictionary `hE`, so consumers
of the dictionary map need not thread the `h⁰` form separately. -/
theorem h0_eq_finrank_of_map_eq {V : Type u} [AddCommGroup V] [Module K V]
    {Φ : V →ₗ[K] Y.functionField} (hΦinj : Function.Injective Φ)
    {E : Submodule K V} {A : Y.CurveDivisor}
    (hE : Submodule.map Φ E = divisorSections K A ⊤) :
    Sheaf.h0 (Y.divisorSheaf K A) = Module.finrank K ↥E := by
  rw [← finrank_divisorSections_top K A, ← hE]
  exact ((Submodule.equivMapOfInjective Φ hΦinj E).finrank_eq).symm

/-- **Recovery of the divisor from its window, assembled form** (the `baseDivisor`
packaging of DDR-2's `baseDivisorAt_window_normalization`, the DDR-8 hook): for an
effective `D` of degree `g` under an embedding level `N` with exact normalization
windows and budget `2g ≤ deg N`, any submodule `T` equal to the window section space
`H⁰(𝒪(N − D))` has base divisor exactly `D` relative to `N`. -/
theorem baseDivisor_window_normalization (g : ℕ)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (N : Y.CurveDivisor)
    (hNnorm : ∀ D' : Y.CurveDivisor, CurveDivisor.deg K D' ≤ 2 * (g : ℤ) →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K N)
    (D : Y.CurveDivisor) (hD0 : 0 ≤ D) (hdeg : CurveDivisor.deg K D = (g : ℤ))
    {T : Submodule K Y.functionField} (hT : T = divisorSections K (N - D) ⊤)
    (hne : ∃ f ∈ T, f ≠ 0) :
    Scheme.baseDivisor K T N hne = D := by
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  rw [Scheme.coeffAt_baseDivisor K hne hx, hT]
  exact baseDivisorAt_window_normalization g hO hχ N hNnorm hNdeg D hD0 hdeg hx

omit [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] in
/-- **The window section space is nonzero** (discharges the `hne` slot of
`baseDivisor_window_normalization` from the pack itself): under the pinch pack, the
window `H⁰(𝒪(N − D))` of an effective degree-`g` divisor has
`h⁰ = deg N − 2g + 1 ≥ 1`, so any submodule equal to it has a nonzero element. -/
theorem exists_mem_ne_zero_of_window_normalization (g : ℕ)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (N : Y.CurveDivisor)
    (hNnorm : ∀ D' : Y.CurveDivisor, CurveDivisor.deg K D' ≤ 2 * (g : ℤ) →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K N)
    (D : Y.CurveDivisor) (hdeg : CurveDivisor.deg K D = (g : ℤ))
    {T : Submodule K Y.functionField} (hT : T = divisorSections K (N - D) ⊤) :
    ∃ f ∈ T, f ≠ 0 := by
  have hgnn : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg g
  have hg2 : CurveDivisor.deg K D ≤ 2 * (g : ℤ) := by omega
  have hrank : (Sheaf.h0 (Y.divisorSheaf K (N - D)) : ℤ)
      = CurveDivisor.deg K N - CurveDivisor.deg K D
        + Sheaf.chi (Y.moduleKSheaf K) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (hNnorm D hg2),
      Scheme.CurveDivisor.deg_sub' K]
  rw [hχ, hdeg] at hrank
  have hfr : Module.finrank K ↥T = Sheaf.h0 (Y.divisorSheaf K (N - D)) := by
    rw [hT]
    exact finrank_divisorSections_top K _
  refine Submodule.exists_mem_ne_zero_of_ne_bot (fun hbot => ?_)
  rw [hbot, finrank_bot] at hfr
  omega

/-- **Decoupled recovery of the divisor from its window.**  The divisor and
normalization budget have degree `n`, while the Euler characteristic is normalized by
an independent curve parameter `gamma ≤ n`. -/
theorem baseDivisor_window_normalization_at (n : ℕ) {gamma : ℕ}
    (hgamma : gamma ≤ n)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (gamma : ℤ))
    (N : Y.CurveDivisor)
    (hNnorm : ∀ D' : Y.CurveDivisor, CurveDivisor.deg K D' ≤ 2 * (n : ℤ) →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (n : ℤ) ≤ CurveDivisor.deg K N)
    (D : Y.CurveDivisor) (hD0 : 0 ≤ D) (hdeg : CurveDivisor.deg K D = (n : ℤ))
    {T : Submodule K Y.functionField} (hT : T = divisorSections K (N - D) ⊤)
    (hne : ∃ f ∈ T, f ≠ 0) :
    Scheme.baseDivisor K T N hne = D := by
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  rw [Scheme.coeffAt_baseDivisor K hne hx, hT]
  exact baseDivisorAt_window_normalization
    n hO hχ N hNnorm hNdeg D hD0 hdeg hx hgamma

omit [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] in
/-- **The decoupled window section space is nonzero.**  Its exact rank is
`deg N - n + 1 - gamma`, which is positive under `deg N ≥ 2n` and `gamma ≤ n`. -/
theorem exists_mem_ne_zero_of_window_normalization_at (n : ℕ) {gamma : ℕ}
    (hgamma : gamma ≤ n)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (gamma : ℤ))
    (N : Y.CurveDivisor)
    (hNnorm : ∀ D' : Y.CurveDivisor, CurveDivisor.deg K D' ≤ 2 * (n : ℤ) →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (n : ℤ) ≤ CurveDivisor.deg K N)
    (D : Y.CurveDivisor) (hdeg : CurveDivisor.deg K D = (n : ℤ))
    {T : Submodule K Y.functionField} (hT : T = divisorSections K (N - D) ⊤) :
    ∃ f ∈ T, f ≠ 0 := by
  have hn2 : CurveDivisor.deg K D ≤ 2 * (n : ℤ) := by omega
  have hrank : (Sheaf.h0 (Y.divisorSheaf K (N - D)) : ℤ)
      = CurveDivisor.deg K N - CurveDivisor.deg K D
        + Sheaf.chi (Y.moduleKSheaf K) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (hNnorm D hn2),
      Scheme.CurveDivisor.deg_sub' K]
  rw [hχ, hdeg] at hrank
  have hfr : Module.finrank K ↥T = Sheaf.h0 (Y.divisorSheaf K (N - D)) := by
    rw [hT]
    exact finrank_divisorSections_top K _
  refine Submodule.exists_mem_ne_zero_of_ne_bot (fun hbot => ?_)
  rw [hbot, finrank_bot] at hfr
  have hcast : (gamma : ℤ) ≤ (n : ℤ) := by exact_mod_cast hgamma
  omega

/-- **Uniqueness of an effective degree-`g` divisor from its window section space** (the
field-level heart of Task 6, family-free): under the pinch pack, two effective
degree-`g` divisors with the same window section space `H⁰(𝒪(N − ·))` coincide — both
are presented as the base divisor of the common section space
(`baseDivisorAt_window_normalization`), which is a function of that space alone. -/
theorem eq_of_divisorSections_window_eq (g : ℕ)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (N : Y.CurveDivisor)
    (hNnorm : ∀ D' : Y.CurveDivisor, CurveDivisor.deg K D' ≤ 2 * (g : ℤ) →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K N)
    (D D' : Y.CurveDivisor)
    (hD0 : 0 ≤ D) (hdeg : CurveDivisor.deg K D = (g : ℤ))
    (hD'0 : 0 ≤ D') (hdeg' : CurveDivisor.deg K D' = (g : ℤ))
    (h : divisorSections K (N - D) ⊤ = divisorSections K (N - D') ⊤) :
    D = D' := by
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  rw [← baseDivisorAt_window_normalization g hO hχ N hNnorm hNdeg D hD0 hdeg hx,
    ← baseDivisorAt_window_normalization g hO hχ N hNnorm hNdeg D' hD'0 hdeg' hx, h]

end WindowRecovery

/-! ## §2 The family level: window recovery and mono-ness of `ε` -/

section EpsMono

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {K : Type u} [Field K] [Algebra k K]
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftEpsMono : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]

/-- **Window recovery, pointwise form** (the family instance of the DDR-8 hook): under
the pinch pack and the sections dictionary `Φ`, the base multiplicity of the
`ε`-window's function-field image `Φ(K_M(d))` relative to `N` at every closed point is
the family divisor's coefficient — `bd(Φ(K_M(d)))ₓ = (divFamDivisor F)ₓ`.  The pairing
input fires from the certificate (`IsCertified.isThetaPaired`); the degree is DDR-2's
pinch. -/
theorem baseDivisorAt_map_divFamEps (g : ℕ) (G : CertifiedDivisorFamily C K π g)
    (hsurj : Function.Surjective
      (G.adaptation.thetaGluedEval (windowM_choice π hπ g)))
    (hcarve : ∀ a : ↥(divisorSections k
        (windowS_choice π hπ g • fiberWeilDivisor π) ⊤),
      Grassmannian.carvePairArrow (windowShiftMul hπ g a)
        (divFamEps hπ g (DivFam.mk G)).1 (divFamEps hπ g (DivFam.mk G)).2 = 0)
    (hO : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (hχ : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ))
    (N : (relCurve C K).CurveDivisor)
    (hNwin : Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K N) 1))
    (hNnorm : ∀ D' : (relCurve C K).CurveDivisor,
      CurveDivisor.deg K D' ≤ 2 * (g : ℤ) →
      Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K N)
    (hNrank : Sheaf.h0 ((relCurve C K).divisorSheaf K N)
      = Sheaf.h0 (C.left.divisorSheaf k
          (windowM_choice π hπ g • fiberWeilDivisor π)))
    (Φ : (K ⊗[k] ↥(divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) →ₗ[K]
        (relCurve C K).functionField)
    (hΦinj : Function.Injective Φ)
    (hΦwin : Submodule.map Φ ((divFamEps hπ g (DivFam.mk G)).1)
      = divisorSections K (N - divFamDivisor (DivFam.mk G)) ⊤)
    {x : relCurve C K} (hx : x ≠ genericPoint (relCurve C K)) :
    (Scheme.baseDivisorAt K
        (Submodule.map Φ ((divFamEps hπ g (DivFam.mk G)).1)) N ⟨x, hx⟩ : ℤ)
      = coeffAt hx (divFamDivisor (DivFam.mk G)) := by
  have hdict := h0_eq_finrank_of_map_eq hΦinj hΦwin
  have hdeg := deg_divFamDivisor_of_carve hπ g G hsurj
    (G.certified.isThetaPaired _) hcarve hO hχ N hNwin hNnorm hNdeg hNrank hdict
  rw [hΦwin]
  exact baseDivisorAt_window_normalization g hO hχ N hNnorm hNdeg _
    (zero_le_divFamDivisor _) hdeg hx

/-- **Window recovery, assembled form — `bd(K_M(d)) = divFamDivisor F`** (DD-4 Task 6's
recovery keystone, the shape DDR-8's fibrewise step consumes): under the pinch pack and
the sections dictionary, the base divisor of the `ε`-window's function-field image
relative to the embedding level `N` is exactly the family divisor. -/
theorem baseDivisor_map_divFamEps (g : ℕ) (G : CertifiedDivisorFamily C K π g)
    (hsurj : Function.Surjective
      (G.adaptation.thetaGluedEval (windowM_choice π hπ g)))
    (hcarve : ∀ a : ↥(divisorSections k
        (windowS_choice π hπ g • fiberWeilDivisor π) ⊤),
      Grassmannian.carvePairArrow (windowShiftMul hπ g a)
        (divFamEps hπ g (DivFam.mk G)).1 (divFamEps hπ g (DivFam.mk G)).2 = 0)
    (hO : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (hχ : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ))
    (N : (relCurve C K).CurveDivisor)
    (hNwin : Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K N) 1))
    (hNnorm : ∀ D' : (relCurve C K).CurveDivisor,
      CurveDivisor.deg K D' ≤ 2 * (g : ℤ) →
      Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K N)
    (hNrank : Sheaf.h0 ((relCurve C K).divisorSheaf K N)
      = Sheaf.h0 (C.left.divisorSheaf k
          (windowM_choice π hπ g • fiberWeilDivisor π)))
    (Φ : (K ⊗[k] ↥(divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) →ₗ[K]
        (relCurve C K).functionField)
    (hΦinj : Function.Injective Φ)
    (hΦwin : Submodule.map Φ ((divFamEps hπ g (DivFam.mk G)).1)
      = divisorSections K (N - divFamDivisor (DivFam.mk G)) ⊤)
    (hne : ∃ f ∈ Submodule.map Φ ((divFamEps hπ g (DivFam.mk G)).1), f ≠ 0) :
    Scheme.baseDivisor K
        (Submodule.map Φ ((divFamEps hπ g (DivFam.mk G)).1)) N hne
      = divFamDivisor (DivFam.mk G) := by
  have hdict := h0_eq_finrank_of_map_eq hΦinj hΦwin
  have hdeg := deg_divFamDivisor_of_carve hπ g G hsurj
    (G.certified.isThetaPaired _) hcarve hO hχ N hNwin hNnorm hNdeg hNrank hdict
  exact baseDivisor_window_normalization g hO hχ N hNnorm hNdeg _
    (zero_le_divFamDivisor _) hdeg hΦwin hne

omit [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **The `ε`-window's image is nonzero** (the family form of
`exists_mem_ne_zero_of_window_normalization`; discharges the `hne` slot of
`baseDivisor_map_divFamEps` from the pack itself). -/
theorem exists_map_divFamEps_ne_zero (g : ℕ) (G : CertifiedDivisorFamily C K π g)
    (hsurj : Function.Surjective
      (G.adaptation.thetaGluedEval (windowM_choice π hπ g)))
    (hcarve : ∀ a : ↥(divisorSections k
        (windowS_choice π hπ g • fiberWeilDivisor π) ⊤),
      Grassmannian.carvePairArrow (windowShiftMul hπ g a)
        (divFamEps hπ g (DivFam.mk G)).1 (divFamEps hπ g (DivFam.mk G)).2 = 0)
    (hO : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (hχ : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ))
    (N : (relCurve C K).CurveDivisor)
    (hNwin : Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K N) 1))
    (hNnorm : ∀ D' : (relCurve C K).CurveDivisor,
      CurveDivisor.deg K D' ≤ 2 * (g : ℤ) →
      Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K N)
    (hNrank : Sheaf.h0 ((relCurve C K).divisorSheaf K N)
      = Sheaf.h0 (C.left.divisorSheaf k
          (windowM_choice π hπ g • fiberWeilDivisor π)))
    (Φ : (K ⊗[k] ↥(divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) →ₗ[K]
        (relCurve C K).functionField)
    (hΦinj : Function.Injective Φ)
    (hΦwin : Submodule.map Φ ((divFamEps hπ g (DivFam.mk G)).1)
      = divisorSections K (N - divFamDivisor (DivFam.mk G)) ⊤) :
    ∃ f ∈ Submodule.map Φ ((divFamEps hπ g (DivFam.mk G)).1), f ≠ 0 := by
  have hdict := h0_eq_finrank_of_map_eq hΦinj hΦwin
  have hdeg := deg_divFamDivisor_of_carve hπ g G hsurj
    (G.certified.isThetaPaired _) hcarve hO hχ N hNwin hNnorm hNdeg hNrank hdict
  exact exists_mem_ne_zero_of_window_normalization g hχ N hNnorm hNdeg _ hdeg hΦwin

/-- **The divisor-level core of Task-6 mono-ness** (the shape DDR-8's fibrewise step
consumes at a residue field): two certified families whose `ε`-windows `K_M(d)` agree —
FIRST components alone — cut the SAME divisor.  Both family divisors are effective of
degree `g` (DDR-2's pinch) and are presented as the base divisor of the common window
section space through the dictionary (`eq_of_divisorSections_window_eq`), a function of
that space alone.

The dictionary `Φ` and the window pack `N, …` are SHARED between the two families (one
embedding level, one reading); `hsurj`/`hcarve`/`hΦwin` are per-family.  The Θ-pairing
input is not threaded — it fires from each family's certificate. -/
theorem divFamDivisor_eq_of_divFamEps_fst_eq (g : ℕ)
    (G G' : CertifiedDivisorFamily C K π g)
    (hsurj : Function.Surjective
      (G.adaptation.thetaGluedEval (windowM_choice π hπ g)))
    (hsurj' : Function.Surjective
      (G'.adaptation.thetaGluedEval (windowM_choice π hπ g)))
    (hcarve : ∀ a : ↥(divisorSections k
        (windowS_choice π hπ g • fiberWeilDivisor π) ⊤),
      Grassmannian.carvePairArrow (windowShiftMul hπ g a)
        (divFamEps hπ g (DivFam.mk G)).1 (divFamEps hπ g (DivFam.mk G)).2 = 0)
    (hcarve' : ∀ a : ↥(divisorSections k
        (windowS_choice π hπ g • fiberWeilDivisor π) ⊤),
      Grassmannian.carvePairArrow (windowShiftMul hπ g a)
        (divFamEps hπ g (DivFam.mk G')).1 (divFamEps hπ g (DivFam.mk G')).2 = 0)
    (hO : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (hχ : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ))
    (N : (relCurve C K).CurveDivisor)
    (hNwin : Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K N) 1))
    (hNnorm : ∀ D' : (relCurve C K).CurveDivisor,
      CurveDivisor.deg K D' ≤ 2 * (g : ℤ) →
      Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K N)
    (hNrank : Sheaf.h0 ((relCurve C K).divisorSheaf K N)
      = Sheaf.h0 (C.left.divisorSheaf k
          (windowM_choice π hπ g • fiberWeilDivisor π)))
    (Φ : (K ⊗[k] ↥(divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) →ₗ[K]
        (relCurve C K).functionField)
    (hΦinj : Function.Injective Φ)
    (hΦwin : Submodule.map Φ ((divFamEps hπ g (DivFam.mk G)).1)
      = divisorSections K (N - divFamDivisor (DivFam.mk G)) ⊤)
    (hΦwin' : Submodule.map Φ ((divFamEps hπ g (DivFam.mk G')).1)
      = divisorSections K (N - divFamDivisor (DivFam.mk G')) ⊤)
    (h : (divFamEps hπ g (DivFam.mk G)).1 = (divFamEps hπ g (DivFam.mk G')).1) :
    divFamDivisor (DivFam.mk G) = divFamDivisor (DivFam.mk G') := by
  have hdict := h0_eq_finrank_of_map_eq hΦinj hΦwin
  have hdict' := h0_eq_finrank_of_map_eq hΦinj hΦwin'
  have hdeg := deg_divFamDivisor_of_carve hπ g G hsurj
    (G.certified.isThetaPaired _) hcarve hO hχ N hNwin hNnorm hNdeg hNrank hdict
  have hdeg' := deg_divFamDivisor_of_carve hπ g G' hsurj'
    (G'.certified.isThetaPaired _) hcarve' hO hχ N hNwin hNnorm hNdeg hNrank hdict'
  refine eq_of_divisorSections_window_eq g hO hχ N hNnorm hNdeg _ _
    (zero_le_divFamDivisor _) hdeg (zero_le_divFamDivisor _) hdeg' ?_
  rw [← hΦwin, ← hΦwin', h]

/-- **Mono-ness of `ε` at the field level** (DD-4 Task 6, worksheet §2.3.4): two
certified divisor families of degree `g` over the field `K` whose `ε`-windows `K_M(d)`
agree — equality of the FIRST components alone — are equal in `DivFam`.  The divisors
coincide (`divFamDivisor_eq_of_divFamEps_fst_eq`); `divFamDivisor_injective` (the
landed DD-1c converse dictionary) closes the setoid equality. -/
theorem eq_of_divFamEps_fst_eq (g : ℕ) (G G' : CertifiedDivisorFamily C K π g)
    (hsurj : Function.Surjective
      (G.adaptation.thetaGluedEval (windowM_choice π hπ g)))
    (hsurj' : Function.Surjective
      (G'.adaptation.thetaGluedEval (windowM_choice π hπ g)))
    (hcarve : ∀ a : ↥(divisorSections k
        (windowS_choice π hπ g • fiberWeilDivisor π) ⊤),
      Grassmannian.carvePairArrow (windowShiftMul hπ g a)
        (divFamEps hπ g (DivFam.mk G)).1 (divFamEps hπ g (DivFam.mk G)).2 = 0)
    (hcarve' : ∀ a : ↥(divisorSections k
        (windowS_choice π hπ g • fiberWeilDivisor π) ⊤),
      Grassmannian.carvePairArrow (windowShiftMul hπ g a)
        (divFamEps hπ g (DivFam.mk G')).1 (divFamEps hπ g (DivFam.mk G')).2 = 0)
    (hO : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (hχ : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ))
    (N : (relCurve C K).CurveDivisor)
    (hNwin : Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K N) 1))
    (hNnorm : ∀ D' : (relCurve C K).CurveDivisor,
      CurveDivisor.deg K D' ≤ 2 * (g : ℤ) →
      Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K N)
    (hNrank : Sheaf.h0 ((relCurve C K).divisorSheaf K N)
      = Sheaf.h0 (C.left.divisorSheaf k
          (windowM_choice π hπ g • fiberWeilDivisor π)))
    (Φ : (K ⊗[k] ↥(divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) →ₗ[K]
        (relCurve C K).functionField)
    (hΦinj : Function.Injective Φ)
    (hΦwin : Submodule.map Φ ((divFamEps hπ g (DivFam.mk G)).1)
      = divisorSections K (N - divFamDivisor (DivFam.mk G)) ⊤)
    (hΦwin' : Submodule.map Φ ((divFamEps hπ g (DivFam.mk G')).1)
      = divisorSections K (N - divFamDivisor (DivFam.mk G')) ⊤)
    (h : (divFamEps hπ g (DivFam.mk G)).1 = (divFamEps hπ g (DivFam.mk G')).1) :
    DivFam.mk G = DivFam.mk G' :=
  divFamDivisor_injective
    (divFamDivisor_eq_of_divFamEps_fst_eq hπ g G G' hsurj hsurj' hcarve hcarve'
      hO hχ N hNwin hNnorm hNdeg hNrank Φ hΦinj hΦwin hΦwin' h)

/-- **Mono-ness of `ε` at the field level, full-pair form**: two certified families with
equal `ε`-pairs are equal in `DivFam` — the first components already suffice
(`eq_of_divFamEps_fst_eq`). -/
theorem eq_of_divFamEps_eq (g : ℕ) (G G' : CertifiedDivisorFamily C K π g)
    (hsurj : Function.Surjective
      (G.adaptation.thetaGluedEval (windowM_choice π hπ g)))
    (hsurj' : Function.Surjective
      (G'.adaptation.thetaGluedEval (windowM_choice π hπ g)))
    (hcarve : ∀ a : ↥(divisorSections k
        (windowS_choice π hπ g • fiberWeilDivisor π) ⊤),
      Grassmannian.carvePairArrow (windowShiftMul hπ g a)
        (divFamEps hπ g (DivFam.mk G)).1 (divFamEps hπ g (DivFam.mk G)).2 = 0)
    (hcarve' : ∀ a : ↥(divisorSections k
        (windowS_choice π hπ g • fiberWeilDivisor π) ⊤),
      Grassmannian.carvePairArrow (windowShiftMul hπ g a)
        (divFamEps hπ g (DivFam.mk G')).1 (divFamEps hπ g (DivFam.mk G')).2 = 0)
    (hO : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (hχ : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ))
    (N : (relCurve C K).CurveDivisor)
    (hNwin : Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K N) 1))
    (hNnorm : ∀ D' : (relCurve C K).CurveDivisor,
      CurveDivisor.deg K D' ≤ 2 * (g : ℤ) →
      Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K (N - D')) 1))
    (hNdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K N)
    (hNrank : Sheaf.h0 ((relCurve C K).divisorSheaf K N)
      = Sheaf.h0 (C.left.divisorSheaf k
          (windowM_choice π hπ g • fiberWeilDivisor π)))
    (Φ : (K ⊗[k] ↥(divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) →ₗ[K]
        (relCurve C K).functionField)
    (hΦinj : Function.Injective Φ)
    (hΦwin : Submodule.map Φ ((divFamEps hπ g (DivFam.mk G)).1)
      = divisorSections K (N - divFamDivisor (DivFam.mk G)) ⊤)
    (hΦwin' : Submodule.map Φ ((divFamEps hπ g (DivFam.mk G')).1)
      = divisorSections K (N - divFamDivisor (DivFam.mk G')) ⊤)
    (h : divFamEps hπ g (DivFam.mk G) = divFamEps hπ g (DivFam.mk G')) :
    DivFam.mk G = DivFam.mk G' :=
  eq_of_divFamEps_fst_eq hπ g G G' hsurj hsurj' hcarve hcarve' hO hχ N hNwin hNnorm
    hNdeg hNrank Φ hΦinj hΦwin hΦwin' (congrArg Prod.fst h)

end EpsMono

end AlgebraicGeometry
