/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.CarveDegreePinch
import AlgebraicJacobian.RiemannRoch.SectionMul
import AlgebraicJacobian.Picard.DivCarveKit
import AlgebraicJacobian.Picard.DivisorFamilyWindow
import AlgebraicJacobian.Picard.DivisorFamilyThetaRank
import AlgebraicJacobian.Picard.DivisorFamilyField

/-!
# DDR-2 — the certified-degree pinch (`informal/spec-dd-r.md` §3 item 2, §1(ii))

The fibrewise degree identity of the DD-R route, **for carve-certified families only**,
closed without Mayer–Vietoris: a certified divisor family whose window has corank `g`
inside the embedding window cuts a divisor of degree exactly `g`.  The pure
Riemann–Roch mechanism (the abstract window pinch) is
`RiemannRoch/CarveDegreePinch.lean`; this file supplies the field-level corank of the
certified window and assembles the pinned deliverables on the relative curve.

## The mechanism (spec §1(ii))

At a field point, `K_M = H⁰(𝒪(MF − D_F))` (the sections dictionary, DD-4 Task 5's field
content) with corank `g` in `H_M`; the DD-0 section bound
(`h0_divisorSheaf_le_max_of_h0_one`) forces `deg D_F ≤ 2g` (the F1 move, exactly as
P-fib's normalization step); then the exact normalization window (`window_normalization`
+ the rank anchor, licensed at `deg ≤ 2g` by `two_mul_genus_le_M_mul_windowδ`) gives
`r_M − g = h⁰(𝒪(MF − D_F)) = M·δ − deg D_F + 1 − g`, i.e. `deg D_F = g`.

## Layout

* **§3 The certified corank** (field-level DD-4 content): over a field `K` the window
  submodule `K_a(d)` of a certified adaptation has corank exactly `n` in `K ⊗[k] H_a` —
  `IsCertified.finrank_divisorWindow_add`, from `windowQuotEquiv` (THREADED `hsurj`, the
  sibling keystone `thetaGluedEval_surjective`) and the (c2)-transport
  `rankAtStalk_thetaGlued` (THREADED `hpair : IsThetaPaired`, I-0199's residual), plus
  the free-rank collapse over the field.  `finrank_tensor_divisorSections` reads the
  ambient rank as the base-field window size `h⁰(𝒪(a·F))`.
* **§4 The pinned deliverables**: `deg_divFamDivisor_of_carve` and
  `baseDivisor_eq_divFamDivisor_of_carve` on `relCurve C K`, threading the two open
  seams by name:
  - `hdict` — **the sections dictionary at the field point**: `h⁰(𝒪(N − D_F))` equals
    the `K`-dimension of the family's window `ε₁ = K_M(d)` (DD-4 Task 5's field content:
    `mem_divisorWindow_iff`'s germ-vanishing read as pole bounds along the divisor);
  - `hNrank` — **the window-size transport**: `h⁰_K(𝒪(N)) = h⁰_k(𝒪(M·F))` (flat base
    change of the embedding window across `k → K`, the I-0175 base-field seam);
  together with the transported window pack (`N`, `hNwin`, `hNnorm`, `hNdeg` — the
  base-field transport of the DD-0 embedding window, ledger names at `K = k`) and the
  sibling spellings `hsurj`/`hpair`.  The carve hypothesis (`hcarve`, the ε-pair form of
  `(♦)` through `carvePairArrow` at the multiplier `windowShiftMul`) pins the statement
  to the certified carve locus; the pinch itself does not consume it — corank `g` plus
  the window ledger already force the degree.

The certificate (`G.certified : IsCertified g`) supplies the rank input; effectivity is
`zero_le_divFamDivisor`.  Everything else is landed SectionBound/WindowLedger/
BaseDivisor material — no numeric window bound appears (DAT-D discipline rule 1).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

attribute [local instance] AlgebraicGeometry.Scheme.functionFieldOverModule
  AlgebraicGeometry.Scheme.overModule AlgebraicGeometry.Scheme.overSectionsAlgebra

namespace AlgebraicGeometry

open Scheme

/-! ## §3 The certified corank of the window at a field -/

section CertifiedWindow

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {K : Type u} [Field K] [Algebra k K]
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftCarve : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

omit [IsFinite π] in
/-- **The ambient window rank is the base-field window size**: over a field extension
`K/k` the free window `K ⊗[k] H_a` has `K`-dimension `h⁰(𝒪(a·F))`, the base ledger
number. -/
theorem finrank_tensor_divisorSections (a : ℕ) :
    Module.finrank K
        (K ⊗[k] ↥(divisorSections k (a • fiberWeilDivisor π) ⊤))
      = Sheaf.h0 (C.left.divisorSheaf k (a • fiberWeilDivisor π)) := by
  rw [Module.finrank_baseChange, finrank_divisorSections_top]

/-- **The certified corank of the window at a field** (the corank-`g` half of the
pinch, DD-4 Task 5's field content): over a field `K`, the window submodule `K_a(d)` of
a certified adaptation has corank exactly `n` inside the free window `K ⊗[k] H_a`.
From the corank identification `windowQuotEquiv` (THREADED `hsurj`: the sibling
keystone `thetaGluedEval_surjective`, `Picard/DivisorThetaSurjectivity.lean`) and the
(c2)-transport `rankAtStalk_thetaGlued` (THREADED `hpair : IsThetaPaired`, the I-0199
residual), collapsed to a dimension over the field by freeness. -/
theorem DivisorAdaptation.IsCertified.finrank_divisorWindow_add
    {d : (relCurve C K).LocalEquations} {A : DivisorAdaptation C K π d} {n : ℕ}
    (hc : A.IsCertified n) (a : ℕ)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (hsurj : Function.Surjective (A.thetaGluedEval a))
    (hpair : A.IsThetaPaired a) :
    Module.finrank K ↥(divisorWindow d hH1) + n
      = Module.finrank K
          (K ⊗[k] ↥(divisorSections k (a • fiberWeilDivisor π) ⊤)) := by
  have hq := Submodule.finrank_quotient_add_finrank (divisorWindow d hH1)
  have he : Module.finrank K
        ((K ⊗[k] ↥(divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d hH1)
      = Module.finrank K (A.ThetaGlued a) :=
    (windowQuotEquiv A hH1 hsurj).finrank_eq
  have hg : Module.finrank K (A.ThetaGlued a) = n := by
    haveI : Module.Free K (A.ThetaGlued a) := Module.Free.of_divisionRing K _
    have h := congrFun
      (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := A.ThetaGlued a))
      (⊥ : PrimeSpectrum K)
    rw [A.rankAtStalk_thetaGlued a hpair hc ⊥] at h
    simpa using h.symm
  omega

/-! ## §4 The pinned deliverables on the relative curve -/

variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

/-- **The window-shift multiplier** `a · (−) : H_M → H_{M+s}` of the carve `(♦)` at the
DD-0 ledger exponents: multiplication by a section `a ∈ H⁰(𝒪(s·F))` on the embedding
window, landing in the shifted window through the divisor identity
`s·F + M·F = (M+s)·F`.  The ε-pair form of the carve is
`carvePairArrow (windowShiftMul hπ g a) ε₁ ε₂ = 0` for all `a`. -/
noncomputable def windowShiftMul (g : ℕ)
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤) →ₗ[k]
      ↥(divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤) :=
  (LinearEquiv.ofEq _ _ (congrArg (fun D => divisorSections k D ⊤)
      (by rw [add_nsmul]; exact add_comm _ _))).toLinearMap
    ∘ₗ sectionMulBilin k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) a

variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]

omit [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))] in
set_option linter.unusedVariables false in
/-- **DDR-2, the certified-degree pinch** (`informal/spec-dd-r.md` §3 item 2, §1(ii)):
a certified divisor family of degree `g` over a field `K` whose ε-pair satisfies the
carve `(♦)` cuts a divisor of degree exactly `g` — `deg K (divFamDivisor F) = g` — with
no Mayer–Vietoris, no adaptation independence, no `hdeg`.

THREADED HYPOTHESES (each a named seam, spellings pinned to the sibling lanes):
* `hsurj` — right exactness of the section sequence at the embedding window; discharged
  by `thetaGluedEval_surjective` (`Picard/DivisorThetaSurjectivity.lean`, conditional on
  the fibrewise `hfib`, sibling lane in flight);
* `hpair` — the Θ-pairing input `IsThetaPaired` (I-0199's residual);
* `N, hNwin, hNnorm, hNdeg` — the base-field transport of the DD-0 embedding window
  `M·F` to `relCurve C K` (the I-0175 seam): an avatar divisor with `H¹(𝒪(N)) = 0`,
  exact normalization windows below `2g`, and budget `2g ≤ deg N`; at `K = k` these are
  the ledger names `window_embedding`/`window_normalization`/
  `two_mul_genus_le_M_mul_windowδ` themselves;
* `hNrank` — the window-size transport `h⁰_K(𝒪(N)) = h⁰_k(𝒪(M·F))` (flat base change);
* `hdict` — **the sections dictionary at the field point** (DD-4 Task 5's field
  content): `h⁰(𝒪(N − D_F))` is the `K`-dimension of the family window
  `ε₁ = K_M(d)` (`mem_divisorWindow_iff`'s germ-vanishing read as pole bounds).

The carve `hcarve` pins the statement to the certified carve locus (spec §3 item 2);
the pinch mechanism itself does not consume it. -/
theorem deg_divFamDivisor_of_carve (g : ℕ) (G : CertifiedDivisorFamily C K π g)
    (hsurj : Function.Surjective
      (G.adaptation.thetaGluedEval (windowM_choice π hπ g)))
    (hpair : G.adaptation.IsThetaPaired (windowM_choice π hπ g))
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
    (hdict : Sheaf.h0 ((relCurve C K).divisorSheaf K
        (N - divFamDivisor (DivFam.mk G)))
      = Module.finrank K ↥((divFamEps hπ g (DivFam.mk G)).1)) :
    CurveDivisor.deg K (divFamDivisor (DivFam.mk G)) = (g : ℤ) := by
  have hEps : (divFamEps hπ g (DivFam.mk G)).1
      = divisorWindow G.eqns (relThetaPairH1_windowM C π hπ g) := by
    rw [divFamEps_mk]
  rw [hEps] at hdict
  have hB1 := G.certified.finrank_divisorWindow_add (windowM_choice π hπ g)
    (relThetaPairH1_windowM C π hπ g) hsurj hpair
  have hB2 := finrank_tensor_divisorSections (K := K) (π := π) (windowM_choice π hπ g)
  refine deg_eq_genus_of_window_corank g hO hχ N hNwin hNnorm hNdeg _ ?_
  have hfr : Module.finrank K
        ↥(divisorSections K (N - divFamDivisor (DivFam.mk G)) ⊤)
      = Sheaf.h0 ((relCurve C K).divisorSheaf K
          (N - divFamDivisor (DivFam.mk G))) :=
    finrank_divisorSections_top K _
  omega

/-- **DDR-2 corollary — recovery of the family divisor as the base divisor of its
window** (feeds DDR-8 through the abstract-`N` `baseDivisorAt_window_normalization`):
under the pinch hypotheses, the base divisor of `H⁰(𝒪(N − D_F))` relative to the
embedding level `N` is exactly `D_F = divFamDivisor F`.  Effectivity is
`zero_le_divFamDivisor`; the degree is the pinch. -/
theorem baseDivisor_eq_divFamDivisor_of_carve (g : ℕ)
    (G : CertifiedDivisorFamily C K π g)
    (hsurj : Function.Surjective
      (G.adaptation.thetaGluedEval (windowM_choice π hπ g)))
    (hpair : G.adaptation.IsThetaPaired (windowM_choice π hπ g))
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
    (hdict : Sheaf.h0 ((relCurve C K).divisorSheaf K
        (N - divFamDivisor (DivFam.mk G)))
      = Module.finrank K ↥((divFamEps hπ g (DivFam.mk G)).1))
    (hne : ∃ f ∈ divisorSections K (N - divFamDivisor (DivFam.mk G)) ⊤, f ≠ 0) :
    Scheme.baseDivisor K
        (divisorSections K (N - divFamDivisor (DivFam.mk G)) ⊤) N hne
      = divFamDivisor (DivFam.mk G) := by
  have hdeg : CurveDivisor.deg K (divFamDivisor (DivFam.mk G)) = (g : ℤ) :=
    deg_divFamDivisor_of_carve hπ g G hsurj hpair hcarve hO hχ N hNwin hNnorm hNdeg
      hNrank hdict
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  rw [Scheme.coeffAt_baseDivisor K hne hx]
  exact baseDivisorAt_window_normalization g hO hχ N hNnorm hNdeg _
    (zero_le_divFamDivisor _) hdeg hx

end CertifiedWindow

end AlgebraicGeometry
