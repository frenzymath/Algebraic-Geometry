/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeFamily
import AlgebraicJacobian.Picard.DivSchemeCertificateEngine
import AlgebraicJacobian.Picard.DivisorThetaPairing

/-!
# DDR-5 — the ε-projection identity (`informal/spec-dd-r.md` §3 item 5)

The projection identity for families constructed from a theta generator seed: the
window submodule `K_a(d)` of the DDR-3 family *is* the Grassmannian point the seed was
drawn from — `ε` of the constructed family returns the tautological pair.

* `LinearMap.injective_of_surjective_of_rankAtStalk_eq` /
  `Submodule.eq_of_le_of_rankAtStalk_quotient_eq` — **the rank-`g`-quotient surjection
  engine** (spec §3 item 5, the equality half): a surjection of finite projective
  modules of equal rank at every stalk is an isomorphism (its kernel is finite
  projective of rank zero, hence trivial), so nested submodules with same-rank finite
  projective quotients coincide.
* `AlgebraicGeometry.divisorWindow_eq_of_le`(`_of_isCertified`) — **the window form**:
  a Grassmannian point `x` contained in the window submodule `K_a(d)` equals it, once
  the Θ-twisted colength module carries its finite/projective/rank-`g` certificate
  (`IsCertified.finite/projective/rankAtStalk_thetaGlued`, I-0211) and the evaluation
  is surjective (`windowQuotEquiv`).
* `AlgebraicGeometry.ThetaGeneratorSeed.divisorWindow_eq` — **the ε-projection
  identity at the seed's window**: for a seed drawn from the point `x` (its submodule
  `K = relThetaWindowEquiv '' x`, the W1 spelling), the containment half is DDR-3's
  `le_vanishingSubmodule` and the equality half is the rank engine — no fibrewise
  input beyond the `IsGenerator` boundary.
* `AlgebraicGeometry.ThetaGeneratorSeed.certifiedFamily` and the ε-forms
  `divFamEps_mk_eq_of_le` / `ThetaGeneratorSeed.divFamEps_certifiedFamily` — **the
  pair identity**: `ε` of a certified family whose windows contain the pair
  `(x₁, x₂)` is exactly `(x₁, x₂)` at the pinned ledger exponents `M`, `M + s`.  For
  the seed-built family the first containment is automatic; the second-window
  containment is the named DDR-5 boundary (fibrewise second-window exactness →
  relative, the W2/DDR-4 fan-in; spec §3 item 5 with risk 5's nonreduced guard).

The universal instantiation is the G-4 chain (`informal/w4-g4-worksheet.md`), in
progress: the tautological pair transported to the pinned window ambients — the seed
submodules `K_univ`/`K'_univ` — is LANDED in
`AlgebraicJacobian.Picard.DivSchemeSeedUniv` (with the fibre P-fib-N keystone in
`AlgebraicJacobian.Picard.DivSchemeSeedUnivFibre`); the certificate discharge and the
final `DivSchemeEpsUniv` consumer of this file's keystone are the remaining bricks.

All statements are conditional on the DDR-3 `IsGenerator` boundary and the DDR-4
certificate exactly as `Picard/DivSchemeCertificate*` are — nothing here assumes the
unbuilt seed instantiation (I-0210's W2).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 8

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

/-! ## The rank-`g`-quotient surjection engine (pure module algebra) -/

section RankEngine

variable {R : Type u} [CommRing R]

/-- **A surjection of finite projective modules of equal rank at every stalk is
injective** (`informal/spec-dd-r.md` §3 item 5, the equality mechanism): the projective
lifting splits the surjection, so the kernel is a finite projective direct summand
whose rank at every stalk is zero — a subsingleton, by
`Module.rankAtStalk_eq_zero_iff_subsingleton`. -/
theorem LinearMap.injective_of_surjective_of_rankAtStalk_eq
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.Projective R M] [Module.Projective R N]
    (φ : M →ₗ[R] N) (hsurj : Function.Surjective φ)
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk M p = Module.rankAtStalk N p) :
    Function.Injective φ := by
  -- a right inverse of `φ` (the projective lifting), and the induced splitting
  obtain ⟨l, hl⟩ := φ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  obtain ⟨e, he₁, -⟩ := (LinearMap.exact_subtype_ker_map φ).splitSurjectiveEquiv
    (Submodule.injective_subtype (LinearMap.ker φ)) ⟨l, hl⟩
  -- the kernel is a finite projective direct summand
  haveI : Module.Finite R N := Module.Finite.of_surjective φ hsurj
  haveI : Module.Finite R ↥(LinearMap.ker φ) :=
    Module.Finite.of_surjective
      (LinearMap.fst R ↥(LinearMap.ker φ) N ∘ₗ e.toLinearMap)
      (Prod.fst_surjective.comp e.surjective)
  haveI : Module.Projective R ↥(LinearMap.ker φ) :=
    Module.Projective.of_split (LinearMap.ker φ).subtype
      (LinearMap.fst R ↥(LinearMap.ker φ) N ∘ₗ e.toLinearMap)
      (LinearMap.ext fun x => by
        have hx := LinearMap.congr_fun he₁ x
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at hx ⊢
        rw [hx, e.apply_symm_apply]
        rfl)
  -- the kernel has rank zero at every stalk
  have hker : Module.rankAtStalk (R := R) ↥(LinearMap.ker φ) = 0 := by
    funext p
    have h1 := congrFun (Module.rankAtStalk_eq_of_equiv e) p
    have h2 := congrFun (Module.rankAtStalk_prod (R := R) ↥(LinearMap.ker φ) N) p
    rw [Pi.add_apply] at h2
    have h3 := hrank p
    rw [Pi.zero_apply]
    omega
  haveI : Subsingleton ↥(LinearMap.ker φ) :=
    Module.rankAtStalk_eq_zero_iff_subsingleton.mp hker
  exact LinearMap.ker_eq_bot.mp (Submodule.eq_bot_of_subsingleton)

/-- **Nested submodules with same-rank finite projective quotients are equal**: the
canonical surjection `M ⧸ K₁ → M ⧸ K₂` is injective by the rank engine, so the larger
submodule collapses onto the smaller. -/
theorem Submodule.eq_of_le_of_rankAtStalk_quotient_eq
    {M : Type u} [AddCommGroup M] [Module R M] {K₁ K₂ : Submodule R M} (hle : K₁ ≤ K₂)
    [Module.Finite R (M ⧸ K₁)] [Module.Projective R (M ⧸ K₁)]
    [Module.Projective R (M ⧸ K₂)]
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (M ⧸ K₁) p = Module.rankAtStalk (M ⧸ K₂) p) :
    K₁ = K₂ := by
  have hcomap : K₁ ≤ K₂.comap LinearMap.id := hle
  have hsurj : Function.Surjective (Submodule.mapQ K₁ K₂ LinearMap.id hcomap) := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective K₂ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hinj := LinearMap.injective_of_surjective_of_rankAtStalk_eq _ hsurj hrank
  refine le_antisymm hle fun x hx => ?_
  have h0 : Submodule.mapQ K₁ K₂ LinearMap.id hcomap (Submodule.Quotient.mk x) = 0 := by
    rw [Submodule.mapQ_apply, LinearMap.id_apply]
    exact (Submodule.Quotient.mk_eq_zero K₂).mpr hx
  have hx0 : (Submodule.Quotient.mk x : M ⧸ K₁) = 0 := hinj (by rw [h0, map_zero])
  exact (Submodule.Quotient.mk_eq_zero K₁).mp hx0

end RankEngine

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftEps : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]

/-! ## The window form of the projection identity -/

section WindowEq

variable {a g : ℕ} {d : (relCurve C R).LocalEquations}

set_option linter.unusedVariables false in
/-- **The window form of the ε-projection identity** (`informal/spec-dd-r.md` §3
item 5, the equality half): a Grassmannian point `x` whose submodule is contained in
the window submodule `K_a(d)` *equals* it, given the Θ-twisted colength certificate
slots (surjective evaluation + finite projective of constant rank `g`, exactly the
`divisorWindowGr` inputs).  Both quotients are then finite projective of rank `g`, and
nested submodules with same-rank quotients coincide by the rank engine.

`hfin` and `hproj` are consumed by typeclass synthesis as local instances (they carry
the `Module.Finite`/`Module.Projective` slots into `Module.Finite.equiv` /
`Module.Projective.of_equiv`); the `unusedVariables` linter does not see the `hfin`
synthesis and is disabled here for that false positive. -/
theorem divisorWindow_eq_of_le (A : DivisorAdaptation C R π d)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (x : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) g R)
    (hsurj : Function.Surjective (A.thetaGluedEval a))
    (hfin : Module.Finite R (A.ThetaGlued a))
    (hproj : Module.Projective R (A.ThetaGlued a))
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk (A.ThetaGlued a) p = g)
    (hle : x.toSubmodule ≤ divisorWindow d hH1) :
    divisorWindow d hH1 = x.toSubmodule := by
  haveI hfinW : Module.Finite R
      ((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d hH1) :=
    Module.Finite.equiv (windowQuotEquiv A hH1 hsurj).symm
  haveI hprojW : Module.Projective R
      ((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d hH1) :=
    Module.Projective.of_equiv (windowQuotEquiv A hH1 hsurj).symm
  refine (Submodule.eq_of_le_of_rankAtStalk_quotient_eq hle fun p => ?_).symm
  rw [x.rankAtStalk_eq p,
    congrFun (Module.rankAtStalk_eq_of_equiv (windowQuotEquiv A hH1 hsurj)) p,
    hrank p]

/-- The window form of the ε-projection identity, with the colength certificate slots
discharged from the DD-1 certificate (`IsCertified.finite/projective/rankAtStalk_thetaGlued`,
the I-0211 keystones): only the surjectivity of the evaluation remains threaded. -/
theorem divisorWindow_eq_of_le_of_isCertified (A : DivisorAdaptation C R π d)
    (hc : A.IsCertified g)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (x : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) g R)
    (hsurj : Function.Surjective (A.thetaGluedEval a))
    (hle : x.toSubmodule ≤ divisorWindow d hH1) :
    divisorWindow d hH1 = x.toSubmodule :=
  divisorWindow_eq_of_le A hH1 x hsurj (hc.finite_thetaGlued a)
    (hc.projective_thetaGlued a) (fun p => hc.rankAtStalk_thetaGlued a p) hle

end WindowEq

/-! ## The seed form: the ε-projection identity at the seed's window -/

section SeedEq

variable {a g : ℕ} [IsNoetherianRing R]

/-- **The ε-projection identity at the seed's window** (`informal/spec-dd-r.md` §3
item 5): for a theta generator seed drawn from the Grassmannian point `x` — its
submodule `K` is the image of `x` under the window identification, the W1 spelling —
the window submodule of the constructed family is exactly `x`.  Containment is DDR-3's
`le_vanishingSubmodule` (the landed half); equality is the rank engine on the
certificate slots. -/
theorem ThetaGeneratorSeed.divisorWindow_eq
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (x : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) g R)
    (D : ThetaGeneratorSeed C R π a
      (Submodule.map (relThetaWindowEquiv C R π a hH1).toLinearMap x.toSubmodule))
    (hD : D.IsGenerator) (hc : (D.divisorAdaptation hD).IsCertified g)
    (hsurj : Function.Surjective ((D.divisorAdaptation hD).thetaGluedEval a)) :
    divisorWindow (D.localEquations hD) hH1 = x.toSubmodule :=
  divisorWindow_eq_of_le_of_isCertified (D.divisorAdaptation hD) hc hH1 x hsurj
    (Submodule.map_le_iff_le_comap.mp (D.le_vanishingSubmodule hD))

variable (g) in
/-- **The certified divisor family of a theta generator seed**: the DDR-3
local-equation system with its adaptation, bundled with a degree-`g` certificate (the
DDR-4 output) into the DD-1 carrier. -/
noncomputable def ThetaGeneratorSeed.certifiedFamily
    {K : Submodule R (relThetaSections C R π a)} (D : ThetaGeneratorSeed C R π a K)
    (hD : D.IsGenerator) (hc : (D.divisorAdaptation hD).IsCertified g) :
    CertifiedDivisorFamily C R π g where
  eqns := D.localEquations hD
  adaptation := D.divisorAdaptation hD
  certified := hc

omit [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))] [IsDominant π] in
@[simp]
lemma ThetaGeneratorSeed.certifiedFamily_eqns
    {K : Submodule R (relThetaSections C R π a)} (D : ThetaGeneratorSeed C R π a K)
    (hD : D.IsGenerator) (hc : (D.divisorAdaptation hD).IsCertified g) :
    (D.certifiedFamily g hD hc).eqns = D.localEquations hD :=
  rfl

omit [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))] [IsDominant π] in
@[simp]
lemma ThetaGeneratorSeed.certifiedFamily_adaptation
    {K : Submodule R (relThetaSections C R π a)} (D : ThetaGeneratorSeed C R π a K)
    (hD : D.IsGenerator) (hc : (D.divisorAdaptation hD).IsCertified g) :
    (D.certifiedFamily g hD hc).adaptation = D.divisorAdaptation hD :=
  rfl

end SeedEq

/-! ## The pair form: `ε` returns the tautological pair -/

section Eps

variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable {g : ℕ}

/-- **The ε-pair identity for a certified family** (`informal/spec-dd-r.md` §3
item 5): if the two window submodules of a certified family contain the Grassmannian
pair `(x₁, x₂)` at the pinned ledger exponents `M`, `M + s`, then `ε` of the family
*is* the pair.  The certificate slots fire from the family's own certificate
(I-0211); only the two evaluation surjectivities are threaded (the DD-4 Task-4
boundary, discharged by `thetaGluedEval_surjective` under `hfib`). -/
theorem divFamEps_mk_eq_of_le (G : CertifiedDivisorFamily C R π g)
    (x₁ : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) g R)
    (x₂ : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) g R)
    (hsurj₁ : Function.Surjective
      (G.adaptation.thetaGluedEval (windowM_choice π hπ g)))
    (hsurj₂ : Function.Surjective
      (G.adaptation.thetaGluedEval (windowM_choice π hπ g + windowS_choice π hπ g)))
    (hle₁ : x₁.toSubmodule ≤ divisorWindow G.eqns (relThetaPairH1_windowM C π hπ g))
    (hle₂ : x₂.toSubmodule ≤ divisorWindow G.eqns (relThetaPairH1_windowMS C π hπ g)) :
    divFamEps hπ g (DivFam.mk G) = (x₁.toSubmodule, x₂.toSubmodule) := by
  rw [divFamEps_mk]
  exact Prod.ext
    (divisorWindow_eq_of_le_of_isCertified G.adaptation G.certified
      (relThetaPairH1_windowM C π hπ g) x₁ hsurj₁ hle₁)
    (divisorWindow_eq_of_le_of_isCertified G.adaptation G.certified
      (relThetaPairH1_windowMS C π hπ g) x₂ hsurj₂ hle₂)

variable [IsNoetherianRing R]

/-- **THE ε-PROJECTION IDENTITY** (`informal/spec-dd-r.md` §3 item 5): `ε` of the
family constructed from a theta generator seed drawn from the Grassmannian point `x₁`
at the embedding window `M` is the tautological pair `(x₁, x₂)`.  The first-window
containment is DDR-3's `le_vanishingSubmodule`; the second-window containment `hle₂`
is the named DDR-5 boundary (fibrewise second-window exactness upgraded to relative
divisibility — the W2/DDR-4 fan-in; a fibrewise statement does NOT suffice over
nonreduced chart rings, spec risk 5).  The universal carve-pair instantiation is the
in-progress G-4 chain rooted at `AlgebraicJacobian.Picard.DivSchemeSeedUniv`. -/
theorem ThetaGeneratorSeed.divFamEps_certifiedFamily
    (x₁ : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) g R)
    (x₂ : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) g R)
    (D : ThetaGeneratorSeed C R π (windowM_choice π hπ g)
      (Submodule.map
        (relThetaWindowEquiv C R π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g)).toLinearMap x₁.toSubmodule))
    (hD : D.IsGenerator) (hc : (D.divisorAdaptation hD).IsCertified g)
    (hsurj₁ : Function.Surjective
      ((D.divisorAdaptation hD).thetaGluedEval (windowM_choice π hπ g)))
    (hsurj₂ : Function.Surjective
      ((D.divisorAdaptation hD).thetaGluedEval
        (windowM_choice π hπ g + windowS_choice π hπ g)))
    (hle₂ : x₂.toSubmodule ≤
      divisorWindow (D.localEquations hD) (relThetaPairH1_windowMS C π hπ g)) :
    divFamEps hπ g (DivFam.mk (D.certifiedFamily g hD hc))
      = (x₁.toSubmodule, x₂.toSubmodule) :=
  divFamEps_mk_eq_of_le hπ (D.certifiedFamily g hD hc) x₁ x₂ hsurj₁ hsurj₂
    (Submodule.map_le_iff_le_comap.mp (D.le_vanishingSubmodule hD)) hle₂

end Eps

end AlgebraicGeometry
