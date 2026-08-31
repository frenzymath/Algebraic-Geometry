/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyTheta
import AlgebraicJacobian.Cohomology.RelThetaTransportCore
import AlgebraicJacobian.Picard.GrassmannianFunctor
import AlgebraicJacobian.RiemannRoch.WindowLedger

/-!
# DD-4 (Task 5) — the window submodules `K_A(d)` and the embedding `ε` of `DivFam`

The embedding of the divisor functor into the Grassmannian pair
(`informal/dat-d-worksheet.md` §2.3 step 3), submodule layer.  The base-field seam is
the landed transport `relThetaTwistH0BaseChangeDivisor`
(`Cohomology/RelThetaTransportCore.lean`), which identifies
`H⁰(C_R, 𝒪(Θᵃ)) ≃ₗ[R] R ⊗[k] H_a` with `H_a = divisorSections k (a • F) ⊤` — the
`grFunctorAff` orientation (algebra factor LEFT), so no `TensorProduct.comm` is needed.

* `AlgebraicGeometry.relThetaWindowEquiv` — `R ⊗[k] H_a ≃ₗ[R] H⁰(𝒪(Θᵃ))` in global
  twisted-pair form (`relThetaSections`), the composite of the transport (symmetrized)
  with the degree-zero collapse `Sheaf.HModule.linearEquiv₀`.
* `AlgebraicGeometry.divisorWindow` — **the window submodule `K_a(d) ⊆ R ⊗[k] H_a`**:
  the preimage of the vanishing submodule `d.vanishingSubmodule` under the window
  identification, i.e. `H⁰(𝒪(Θᵃ − d))` inside `R ⊗[k] H_a`.  Cover- and
  adaptation-independent; invariant under divisor equality
  (`divisorWindow_eq_of_divEq`).
* `AlgebraicGeometry.DivFam.window` — the descent of `divisorWindow` to the divisor
  functor value `DivFam C R π n` (the setoid quotient) — **the underlying-submodule form
  of `ε`'s components**.
* `AlgebraicGeometry.windowCarve`, `ker_windowCarve`, `windowQuotEquiv` — the Task-4
  section-sequence bookkeeping over a chart adaptation: the composite
  `R ⊗[k] H_a → W(d)^{Θᵃ}` has kernel exactly `K_a(d)`, so once the evaluation is
  surjective (the open right-exactness heart), `(R ⊗[k] H_a)/K_a(d) ≃ W(d)^{Θᵃ}`.
* `AlgebraicGeometry.divisorWindowGr` — the conditional Grassmannian point: given the
  surjectivity and a finite-projective rank-`n` certificate for `W(d)^{Θᵃ}`, the window
  submodule is a point of `grFunctorAff k H_a n R`.
* `AlgebraicGeometry.relThetaPairH1_windowM`/`_windowMS` and
  `AlgebraicGeometry.divFamEps` — the ledger instantiation: at the DD-0 windows
  `a = M, M + s` the `H¹` input is discharged through `window_embedding`(`_shift`) and
  DAT-0a, and `ε` sends a divisor family of degree `g` to its pair of window submodules
  `(K_M(d), K_{M+s}(d))`.

Mono-ness of `ε` (Task 6) and naturality in `R` (Task 7) are OTHER lanes; they consume
`DivFam.window`/`divFamEps` and the kernel spelling `mem_divisorWindow_iff` here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance instOverCleftWindow : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]

variable (a : ℕ)

/-! ## The window identification `R ⊗[k] H_a ≃ H⁰(𝒪(Θᵃ))` -/

/-- The degree-zero collapse of the relative theta twist: `H⁰` is the module of global
twisted sections (`Sheaf.HModule.linearEquiv₀` at the terminal open). -/
noncomputable def relThetaSectionsEquiv :
    Sheaf.HModule (relThetaTwistSheaf C R π a) 0 ≃ₗ[R] relThetaSections C R π a :=
  Sheaf.HModule.linearEquiv₀
    (Opens.grothendieckTopology ((relCurve C R : Scheme.{u}) : TopCat))
    (isTerminalTop) (relThetaTwistSheaf C R π a)

/-- **The window identification** (the DD-4 base-field seam, consumed): the free base
change of the field window `H_a = divisorSections k (a • F) ⊤` is the module of global
sections of the relative theta twist, `R`-linearly — `relThetaTwistH0BaseChangeDivisor`
composed with the degree-zero collapse.  The `H¹` input is discharged by the DD-0
window ledger at the pinned exponents (`relThetaPairH1_windowM` below). -/
noncomputable def relThetaWindowEquiv
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤) ≃ₗ[R]
      relThetaSections C R π a :=
  (relThetaTwistH0BaseChangeDivisor C π a R hH1).symm.trans
    (relThetaSectionsEquiv C R π a)

/-! ## The window submodule `K_a(d)` -/

variable {C R π a} in
/-- **The window submodule `K_a(d) ⊆ R ⊗[k] H_a`** (worksheet §2.3 step 3): the sections
of `𝒪(Θᵃ)` vanishing along the divisor family `d`, read inside the free window through
the window identification — the DD-4 spelling of `H⁰(𝒪(Θᵃ − d)) ⊆ H_a ⊗ R`.  Depends
only on `d`, not on any chart adaptation. -/
noncomputable def divisorWindow (d : (relCurve C R).LocalEquations)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    Submodule R (R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) :=
  Submodule.comap (relThetaWindowEquiv C R π a hH1).toLinearMap
    (d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
      (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a))

variable {C R π a} in
lemma mem_divisorWindow_iff {d : (relCurve C R).LocalEquations}
    {hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1}
    {x : R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)} :
    x ∈ divisorWindow d hH1 ↔
      relThetaWindowEquiv C R π a hH1 x ∈
        (d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
          (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)) :=
  Iff.rfl

variable {C R π a} in
/-- **Setoid invariance of the window submodule** (worksheet §2.3.4): divisor equality
does not move `K_a(d)` — the embedding `ε` is well defined on the quotient. -/
theorem divisorWindow_eq_of_divEq {d₁ d₂ : (relCurve C R).LocalEquations}
    (h : d₁.DivEq d₂)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    divisorWindow d₁ hH1 = divisorWindow d₂ hH1 := by
  rw [divisorWindow, divisorWindow,
    Scheme.LocalEquations.vanishingSubmodule_eq_of_divEq R h]

variable {C R π a} in
/-- **The window submodule of a divisor family** (`ε`'s component at exponent `a`): the
descent of `divisorWindow` to the divisor functor value `DivFam C R π n`. -/
noncomputable def DivFam.window {n : ℕ} (F : DivFam C R π n)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    Submodule R (R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) :=
  Quotient.lift
    (fun G : CertifiedDivisorFamily C R π n => divisorWindow G.eqns hH1)
    (fun _ _ h => divisorWindow_eq_of_divEq h hH1) F

variable {C R π a} in
@[simp]
lemma DivFam.window_mk {n : ℕ} (G : CertifiedDivisorFamily C R π n)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    (DivFam.mk G).window hH1 = divisorWindow G.eqns hH1 :=
  rfl

/-! ## The Task-4 bookkeeping over a chart adaptation -/

section Carve

variable {C R π a}
variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d)
variable (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)

/-- **The window carve arrow** `R ⊗[k] H_a → W(d)^{Θᵃ}`: the Θ-twisted colength
evaluation through the window identification.  Its kernel is `K_a(d)`
(`ker_windowCarve`); its surjectivity is the open right-exactness heart of Task 4. -/
noncomputable def windowCarve :
    R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤) →ₗ[R]
      A.ThetaGlued a :=
  A.thetaGluedEval a ∘ₗ (relThetaWindowEquiv C R π a hH1).toLinearMap

/-- **Left exactness of the section sequence** (Task 4): the kernel of the window carve
arrow is exactly the window submodule `K_a(d)` — the sequence
`0 → K_a(d) → R ⊗[k] H_a → W(d)^{Θᵃ}` is exact. -/
theorem ker_windowCarve :
    LinearMap.ker (windowCarve A hH1) = divisorWindow d hH1 := by
  rw [windowCarve, LinearMap.ker_comp, A.ker_thetaGluedEval, divisorWindow]

/-- Surjectivity of the carve arrow follows from surjectivity of the evaluation. -/
lemma windowCarve_surjective (hsurj : Function.Surjective (A.thetaGluedEval a)) :
    Function.Surjective (windowCarve A hH1) := by
  rw [windowCarve, LinearMap.coe_comp]
  exact hsurj.comp (relThetaWindowEquiv C R π a hH1).surjective

/-- **The corank identification** (Task 4, conditional on the right-exactness heart):
once the evaluation is surjective, the quotient of the free window by `K_a(d)` is the
Θ-twisted colength module `W(d)^{Θᵃ}`. -/
noncomputable def windowQuotEquiv (hsurj : Function.Surjective (A.thetaGluedEval a)) :
    ((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d hH1) ≃ₗ[R] A.ThetaGlued a :=
  (Submodule.quotEquivOfEq _ _ (ker_windowCarve A hH1).symm).trans
    ((windowCarve A hH1).quotKerEquivOfSurjective (windowCarve_surjective A hH1 hsurj))

variable (n : ℕ)

/-- **The conditional Grassmannian point** (worksheet §2.3 step 3, corank certificate):
given the right-exactness heart (surjectivity of the evaluation) and a
finite-projective rank-`n` certificate for the Θ-twisted colength module `W(d)^{Θᵃ}`,
the window submodule `K_a(d)` is a point of the affine Grassmannian functor
`grFunctorAff k H_a n R`.  The rank-`n` input at the DD-0 windows is the certificate
clause (c2) transported across the twist — the remaining Task-4 obligation together
with surjectivity. -/
noncomputable def divisorWindowGr (hsurj : Function.Surjective (A.thetaGluedEval a))
    (hfin : Module.Finite R (A.ThetaGlued a))
    (hproj : Module.Projective R (A.ThetaGlued a))
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk (A.ThetaGlued a) p = n) :
    Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) n R where
  toSubmodule := divisorWindow d hH1
  finite_quotient :=
    letI := hfin
    Module.Finite.equiv (windowQuotEquiv A hH1 hsurj).symm
  projective_quotient :=
    letI := hproj
    Module.Projective.of_equiv (windowQuotEquiv A hH1 hsurj).symm
  rankAtStalk_eq := fun p => by
    rw [congrFun (Module.rankAtStalk_eq_of_equiv (windowQuotEquiv A hH1 hsurj)) p]
    exact hrank p

@[simp]
lemma divisorWindowGr_coe (hsurj : Function.Surjective (A.thetaGluedEval a))
    (hfin : Module.Finite R (A.ThetaGlued a))
    (hproj : Module.Projective R (A.ThetaGlued a))
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk (A.ThetaGlued a) p = n) :
    ((divisorWindowGr A hH1 n hsurj hfin hproj hrank :
        Grassmannian.grFunctorAff k
          (↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) n R) :
      Submodule R (R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)))
      = divisorWindow d hH1 :=
  rfl

end Carve

/-! ## The ledger instantiation: the `H¹` inputs and the embedding `ε` -/

section Ledger

variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

/-- **The `H¹` input at the embedding window `M`**, discharged through the DD-0 ledger:
`H¹(𝒪(M·F)) = 0` (`window_embedding`, DAT-0a) transports across the field bridge
`Θᴹ ≅ 𝒪(M·F)` and the base-field collapse onto the relative theta pair. -/
theorem relThetaPairH1_windowM (g : ℕ) :
    Subsingleton
      (relTwistPair C k π (relThetaCocycle C k π (windowM_choice π hπ g))).H1 :=
  subsingleton_relThetaPairH1 C π _
    ((subsingleton_hModule_thetaTwistSheaf_one_iff k π _).mpr (window_embedding π hπ g))

/-- **The `H¹` input at the shifted embedding window `M + s`** (`window_embedding_shift`,
DAT-0a). -/
theorem relThetaPairH1_windowMS (g : ℕ) :
    Subsingleton (relTwistPair C k π (relThetaCocycle C k π
      (windowM_choice π hπ g + windowS_choice π hπ g))).H1 :=
  subsingleton_relThetaPairH1 C π _
    ((subsingleton_hModule_thetaTwistSheaf_one_iff k π _).mpr
      (window_embedding_shift π hπ g))

variable {C R π}

/-- **The embedding `ε` of the divisor functor, submodule form** (worksheet §2.3 step 3,
Task 5): a certified divisor family of degree `g` over `R` is sent to its pair of window
submodules `(K_M(d), K_{M+s}(d))` inside the free windows `R ⊗[k] H_M`, `R ⊗[k] H_{M+s}`
at the DD-0 ledger exponents.  Well defined on the setoid quotient by
`divisorWindow_eq_of_divEq`.  The Grassmannian-pair membership of the components — the
corank-`g` certificates — is Task 4's remaining heart (`divisorWindowGr`); mono-ness and
naturality are Tasks 6/7. -/
noncomputable def divFamEps (g : ℕ) (F : DivFam C R π g) :
    Submodule R (R ⊗[k]
        ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
      × Submodule R (R ⊗[k] ↥(Scheme.divisorSections k
          ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) :=
  (F.window (relThetaPairH1_windowM C π hπ g),
   F.window (relThetaPairH1_windowMS C π hπ g))

@[simp]
lemma divFamEps_mk (g : ℕ) (G : CertifiedDivisorFamily C R π g) :
    divFamEps hπ g (DivFam.mk G)
      = (divisorWindow G.eqns (relThetaPairH1_windowM C π hπ g),
         divisorWindow G.eqns (relThetaPairH1_windowMS C π hπ g)) :=
  rfl

end Ledger

end AlgebraicGeometry
