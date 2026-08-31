/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyEpsNaturality
import AlgebraicJacobian.Picard.DivSchemeFrameKit
import AlgebraicJacobian.Picard.GrassmannianChartCompare
import AlgebraicJacobian.Picard.DivCarveLocus

/-!
# G-5 §1/§2 — the ε frame-locus cover and its chart maps (DDR-9 backward assembly)

The keystone `divFamEps_exists_frameCover` (`informal/w4-g5-worksheet.md` §1.2 + §2,
stated directly in `divClassifyAff`'s hypothesis shapes): a divisor family `F` of
degree `g` over an affine test `S` admits a finite span-⊤ family `f : Fin m → S` such
that over each piece `Localization.Away (f t)` a pair-chart map
`w : R_{I,J} →ₐ[k] Localization.Away (f t)` pulls the tautological pair back to the
coordinate images of the RESTRICTED ε pair through the DD-4 boundary bases.  This
manufactures `divClassifyAff`'s honest inputs `hw₁`/`hw₂` over a cover; the per-piece
classification and the morphism stitch (worksheet §3/§4, files 5–6) consume it
verbatim.

Route, per prime `p` of `S` (quotient frame convention, worksheet §0.1): the ε
quotients are finite projective of rank `g` over `S`
(`DivFam.finite/projective/rankAtStalk_window_quotient` — the G-1 keystone
`IsCertified.thetaGluedEval_surjective` + the (c2) clauses through `windowQuotEquiv`);
K3 (`exists_away_free_pair`) picks `h ∉ p` with both localized quotients FREE; the
restricted window pair over `Localization.Away h` is the `windowBaseChange` pushforward
(G-2: `DivFam.window_mapAlg` = `divisorWindow_pulledEquations_eq`), so the coordinate
points `congrAmbient b.equivFun (divFamWindowGr …)` have free quotients and K2
(`exists_matrixPoint_eq_of_free`) presents them by matrices `X₁, X₂`; K5
(`exists_det_submatrix_notMem_of_mul_eq_one`) selects frame minors `(I, J)` avoiding
the prime over `p`; K6 (`exists_away_isUnit_of_notMem`) produces the numerator-stage
element `u ∉ p` making both minor determinants units after the further localization
`awayLiftAlgHom : Localization.Away h →ₐ[k] Localization.Away u`; the presentations
transport along the tower (`map_matrixPoint`, K4 `map_congrAmbient`,
`map_divFamWindowGr` — G-2 again + `DivFam.mapAlg_comp`), the unit minors fire
`matrixPoint_eq_map_chartTautologicalPoint_of_isUnit`, and
`Algebra.TensorProduct.productMap` assembles the pair-chart map.  Finitely many `u_p`
span `⊤` (`Submodule.mem_span_finite_of_mem_span`).  The genus normalization
`hO : h⁰(𝒪) = 1`, `hχ : χ(𝒪) = 1 − g` is the standing G-1 input, threaded exactly as
in `divFamEps_mapAlg`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

open Grassmannian

section Curve

open Scheme

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftFrameCover :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g : ℕ)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
variable (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

/-! ## The window layer: quotient certificates and G-2 naturality at a ledger window -/

section WindowLayer

variable (a : ℕ) (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
variable (hMa : windowM_choice π hπ g ≤ a)
variable {R : Type u} [CommRing R] [Algebra k R]

include hπ hO hχ hMa in
/-- The ε window quotient is a finite module: the certificate's (c2) clause through
`windowQuotEquiv`, with surjectivity from the G-1 keystone. -/
theorem DivFam.finite_window_quotient (F : DivFam C R π g) :
    Module.Finite R ((TensorProduct k R
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ F.window ha1) := by
  induction F using Quotient.inductionOn with
  | h G =>
    haveI := G.certified.finite_thetaGlued a
    exact Module.Finite.equiv (windowQuotEquiv G.adaptation ha1
      (G.certified.thetaGluedEval_surjective (C := C) (π := π) hπ hO hχ ha1 hMa)).symm

include hπ hO hχ hMa in
/-- The ε window quotient is projective. -/
theorem DivFam.projective_window_quotient (F : DivFam C R π g) :
    Module.Projective R ((TensorProduct k R
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ F.window ha1) := by
  induction F using Quotient.inductionOn with
  | h G =>
    haveI := G.certified.projective_thetaGlued a
    exact Module.Projective.of_equiv (windowQuotEquiv G.adaptation ha1
      (G.certified.thetaGluedEval_surjective (C := C) (π := π) hπ hO hχ ha1 hMa)).symm

include hπ hO hχ hMa in
/-- The ε window quotient has constant fibre rank `g`. -/
theorem DivFam.rankAtStalk_window_quotient (F : DivFam C R π g) :
    ∀ p : PrimeSpectrum R, Module.rankAtStalk
      ((TensorProduct k R
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ F.window ha1) p = g := by
  induction F using Quotient.inductionOn with
  | h G =>
    intro p
    exact (congrFun (Module.rankAtStalk_eq_of_equiv (windowQuotEquiv G.adaptation ha1
      (G.certified.thetaGluedEval_surjective (C := C) (π := π) hπ hO hχ ha1 hMa))) p).trans
      (G.certified.rankAtStalk_thetaGlued a p)

include hπ hO hχ hMa in
/-- **G-2 at one ledger window, class level** (`divisorWindow_pulledEquations_eq` in
`DivFam` form): the window of the restricted family is the pinned `windowBaseChange`
pushforward.  Generic in the base ring; no Noetherian hypotheses (I-0232). -/
theorem DivFam.window_mapAlg (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R']
    [IsScalarTower k R R'] (F : DivFam C R π g) :
    (DivFam.mapAlg R' g F).window ha1 = windowBaseChange R' (F.window ha1) := by
  induction F using Quotient.inductionOn with
  | h G =>
    exact divisorWindow_pulledEquations_eq C R' π a hπ G.certified hO hχ ha1 hMa

include hπ hO hχ hMa in
/-- **The ε window component of the restricted family, as a Grassmannian point** over
any test change `R → R'`: the `windowBaseChangeGr` package of the `R`-level window —
by G-2 (`DivFam.window_mapAlg`) the window of `DivFam.mapAlg R' g F`. -/
noncomputable def divFamWindowGr (F : DivFam C R π g) (R' : Type u) [CommRing R']
    [Algebra k R'] [Algebra R R'] [IsScalarTower k R R'] :
    Grassmannian.grFunctorAff k
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤) g R' :=
  haveI := DivFam.finite_window_quotient hπ g hO hχ a ha1 hMa F
  haveI := DivFam.projective_window_quotient hπ g hO hχ a ha1 hMa F
  windowBaseChangeGr R' (F.window ha1) g
    (DivFam.rankAtStalk_window_quotient hπ g hO hχ a ha1 hMa F)

@[simp]
lemma divFamWindowGr_toSubmodule (F : DivFam C R π g) (R' : Type u) [CommRing R']
    [Algebra k R'] [Algebra R R'] [IsScalarTower k R R'] :
    (divFamWindowGr hπ g hO hχ a ha1 hMa F R').toSubmodule
      = windowBaseChange R' (F.window ha1) :=
  rfl

/-- The quotient of the packaged point is the base change of the `R`-level quotient
(re-exported for the freeness transfer). -/
noncomputable def divFamWindowGrQuotEquiv (F : DivFam C R π g) (R' : Type u) [CommRing R']
    [Algebra k R'] [Algebra R R'] [IsScalarTower k R R'] :
    ((TensorProduct k R' ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        (divFamWindowGr hπ g hO hχ a ha1 hMa F R').toSubmodule) ≃ₗ[R']
      TensorProduct R R' ((TensorProduct k R
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ F.window ha1) :=
  haveI := DivFam.projective_window_quotient hπ g hO hχ a ha1 hMa F
  (Submodule.quotEquivOfEq _ _
      (windowBaseChange_eq_ker_baseChangeMkQ R' (F.window ha1))).trans
    (Module.Grassmannian.baseChangeMkQEquiv (F.window ha1))

end WindowLayer

/-! ## The transport of the packaged point along the numerator stage -/

section Transport

variable (a : ℕ) (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
variable (hMa : windowM_choice π hπ g ≤ a)
variable {S : Type u} [CommRing S] [Algebra k S]

set_option maxHeartbeats 800000 in
-- Instantiates the G-2 window naturality at two localizations; elaboration cost.
/-- **The tower transport of the packaged ε point** (worksheet §1.1 K4 + §2 step (e)):
mapping the packaged point along a structure-compatible `β` between away-localizations
yields the packaged point over the target — `ker_baseChangeMkQ_eq_map_baseChange`
inside the `β.toAlgebra` tower, then G-2 on both legs and `DivFam.mapAlg_comp`. -/
theorem map_divFamWindowGr (F : DivFam C S π g) (h u : S)
    (β : Localization.Away h →ₐ[k] Localization.Away u)
    (hβ : β.toRingHom.comp (algebraMap S (Localization.Away h))
      = algebraMap S (Localization.Away u)) :
    Module.Grassmannian.map β
        (divFamWindowGr hπ g hO hχ a ha1 hMa F (Localization.Away h))
      = divFamWindowGr hπ g hO hχ a ha1 hMa F (Localization.Away u) := by
  letI : Algebra (Localization.Away h) (Localization.Away u) := β.toAlgebra
  letI : IsScalarTower k (Localization.Away h) (Localization.Away u) :=
    IsScalarTower.of_algebraMap_eq' (IsScalarTower.algebraMap_eq k _ _)
  haveI htowerS : IsScalarTower S (Localization.Away h) (Localization.Away u) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [RingHom.algebraMap_toAlgebra]
    exact hβ.symm
  refine Module.Grassmannian.ext ?_
  have h0 := Module.Grassmannian.map_toSubmodule β
    (divFamWindowGr hπ g hO hχ a ha1 hMa F (Localization.Away h))
  rw [h0, divFamWindowGr_toSubmodule, divFamWindowGr_toSubmodule,
    ← DivFam.window_mapAlg hπ g hO hχ a ha1 hMa (Localization.Away h) F,
    ← DivFam.window_mapAlg hπ g hO hχ a ha1 hMa (Localization.Away u) F]
  haveI : Module.Projective (Localization.Away h)
      ((TensorProduct k (Localization.Away h)
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        (DivFam.mapAlg (Localization.Away h) g F).window ha1) :=
    DivFam.projective_window_quotient hπ g hO hχ a ha1 hMa _
  rw [Grassmannian.ker_baseChangeMkQ_eq_map_baseChange (Localization.Away u)
    ((DivFam.mapAlg (Localization.Away h) g F).window ha1)]
  have hcomp : DivFam.mapAlg (Localization.Away u) g
      (DivFam.mapAlg (Localization.Away h) g F) = DivFam.mapAlg (Localization.Away u) g F :=
    DivFam.mapAlg_comp (Localization.Away h) g (Localization.Away u) F
  exact ((DivFam.window_mapAlg hπ g hO hχ a ha1 hMa (R := Localization.Away h)
      (Localization.Away u) (DivFam.mapAlg (Localization.Away h) g F)).symm).trans
    (congrArg (fun F' => DivFam.window F' ha1) hcomp)

end Transport

/-! ## The per-prime frame data -/

section PerPrime

variable (a : ℕ) (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
variable (hMa : windowM_choice π hπ g ≤ a)
variable {S : Type u} [CommRing S] [Algebra k S]

set_option maxHeartbeats 800000 in
-- Instantiates the free-quotient/matrix kit at the ε types; elaboration cost.
/-- **One window component, presented over the free locus** (worksheet §1.2, single
window): given freeness of the localized ε quotient at `Localization.Away h` and a
prime of the piece, the coordinate point of the restricted window is a matrix point
whose frame minor at some `I` avoids the prime. -/
private theorem exists_component_matrix {r : ℕ}
    (b : Module.Basis (Fin r) k
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))
    (F : DivFam C S π g) (h : S) (pl : PrimeSpectrum (Localization.Away h))
    (hfree : Module.Free (Localization.Away h) (TensorProduct S (Localization.Away h)
      ((TensorProduct k S
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ F.window ha1))) :
    ∃ (X : Matrix (Fin g) (Fin r) (Localization.Away h))
      (hX : Function.Surjective (matrixProj k g r (Localization.Away h) X))
      (I : Finset (Fin r)) (hI : I.card = g),
      (frameMinor k g r (Localization.Away h) X I hI).det ∉ pl.asIdeal ∧
      matrixPoint k g r (Localization.Away h) X hX
        = congrAmbient b.equivFun
            (divFamWindowGr hπ g hO hχ a ha1 hMa F (Localization.Away h)) := by
  haveI : Nontrivial (Localization.Away h) := by
    rcases subsingleton_or_nontrivial (Localization.Away h) with hs | hn
    · exact absurd (pl.asIdeal.eq_top_iff_one.mpr
        (by rw [Subsingleton.elim (1 : Localization.Away h) 0]; exact zero_mem _))
        pl.isPrime.ne_top
    · exact hn
  -- the packaged point has free quotient, hence so does its coordinate image
  have hfreeP : Module.Free (Localization.Away h)
      ((TensorProduct k (Localization.Away h)
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        (divFamWindowGr hπ g hO hχ a ha1 hMa F (Localization.Away h)).toSubmodule) :=
    haveI := hfree
    Module.Free.of_equiv
      (divFamWindowGrQuotEquiv hπ g hO hχ a ha1 hMa F (Localization.Away h)).symm
  obtain ⟨X, hX, hXeq⟩ := exists_matrixPoint_eq_of_free
    (congrAmbient b.equivFun (divFamWindowGr hπ g hO hχ a ha1 hMa F (Localization.Away h)))
    (free_quotient_congrAmbient b.equivFun _ hfreeP)
  obtain ⟨Y, hY⟩ := exists_mul_eq_one_of_matrixProj_surjective k g r _ X hX
  obtain ⟨I, hI, hdet⟩ := exists_det_submatrix_notMem_of_mul_eq_one pl.asIdeal X Y hY
  exact ⟨X, hX, I, hI, hdet, hXeq⟩

set_option maxHeartbeats 800000 in
-- Transports a matrix presentation along the numerator stage; elaboration cost.
/-- **One window component, chart-framed over the numerator stage** (worksheet §2
(a)–(e), single window): pushing the presentation along `β` and firing the frame
factorisation at the unit minor exhibits the coordinate point of the restricted
window over `Localization.Away u` as a chart pullback. -/
private theorem map_component_chart {r : ℕ}
    (b : Module.Basis (Fin r) k
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))
    (F : DivFam C S π g) (h u : S)
    (β : Localization.Away h →ₐ[k] Localization.Away u)
    (hβ : β.toRingHom.comp (algebraMap S (Localization.Away h))
      = algebraMap S (Localization.Away u))
    (X : Matrix (Fin g) (Fin r) (Localization.Away h))
    (hX : Function.Surjective (matrixProj k g r (Localization.Away h) X))
    (I : Finset (Fin r)) (hI : I.card = g)
    (hu : IsUnit (β (frameMinor k g r (Localization.Away h) X I hI).det))
    (heq : matrixPoint k g r (Localization.Away h) X hX
      = congrAmbient b.equivFun
          (divFamWindowGr hπ g hO hχ a ha1 hMa F (Localization.Away h))) :
    Module.Grassmannian.map
        (chartFrameMap k g r (Localization.Away u) (X.map β) I hI)
        (chartTautologicalPoint k g r I hI)
      = congrAmbient b.equivFun
          (divFamWindowGr hπ g hO hχ a ha1 hMa F (Localization.Away u)) := by
  have hX' : Function.Surjective (matrixProj k g r (Localization.Away u) (X.map β)) :=
    matrixProj_surjective_map k g r β X hX
  have hminor : IsUnit (frameMinor k g r (Localization.Away u) (X.map β) I hI).det := by
    have hdet : (frameMinor k g r (Localization.Away u) (X.map β) I hI).det
        = β (frameMinor k g r (Localization.Away h) X I hI).det := by
      rw [frameMinor, Matrix.submatrix_map]
      exact (RingHom.map_det β.toRingHom _).symm
    rw [hdet]
    exact hu
  rw [← matrixPoint_eq_map_chartTautologicalPoint_of_isUnit k g r (Localization.Away u)
      (X.map β) hX' I hI hminor,
    ← map_matrixPoint k g r β X hX hX', heq,
    map_congrAmbient β b.equivFun
      (divFamWindowGr hπ g hO hχ a ha1 hMa F (Localization.Away h)),
    map_divFamWindowGr hπ g hO hχ a ha1 hMa F h u β hβ]

end PerPrime

/-! ## §1.2: the frame-locus cover keystone -/

section Keystone

variable (r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(divisorSections k
    ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤))
variable {S : Type u} [CommRing S] [Algebra k S]

set_option maxHeartbeats 1600000 in
-- The full per-prime assembly instantiates the kit at both ε windows; elaboration cost.
include hO hχ in
/-- **The per-prime frame data** (worksheet §1.2 assembly at one prime): an element
`u ∉ p` and a pair-chart map over `Localization.Away u` framing the restricted ε pair
in exactly `divClassifyAff`'s hypothesis shapes. -/
private theorem exists_frame_chart_at_prime (F : DivFam C S π g) (p : PrimeSpectrum S) :
    ∃ u : S, u ∉ p.asIdeal ∧
      ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
        (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away u),
        (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
          = Submodule.map
              (LinearMap.baseChange (Localization.Away u) b₁.equivFun.toLinearMap)
              (divFamEps hπ g (DivFam.mapAlg (Localization.Away u) g F)).1 ∧
        (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
          = Submodule.map
              (LinearMap.baseChange (Localization.Away u) b₂.equivFun.toLinearMap)
              (divFamEps hπ g (DivFam.mapAlg (Localization.Away u) g F)).2 := by
  -- the two ε quotients over `S` are finite projective
  haveI hfin₁ := DivFam.finite_window_quotient hπ g hO hχ (windowM_choice π hπ g)
    (relThetaPairH1_windowM C π hπ g) le_rfl F
  haveI hproj₁ := DivFam.projective_window_quotient hπ g hO hχ (windowM_choice π hπ g)
    (relThetaPairH1_windowM C π hπ g) le_rfl F
  haveI hfin₂ := DivFam.finite_window_quotient hπ g hO hχ
    (windowM_choice π hπ g + windowS_choice π hπ g)
    (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) F
  haveI hproj₂ := DivFam.projective_window_quotient hπ g hO hχ
    (windowM_choice π hπ g + windowS_choice π hπ g)
    (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) F
  -- K3: a basic open around `p` on which both localized quotients are free
  obtain ⟨h, hh, hfree₁, hfree₂⟩ := exists_away_free_pair p
    ((TensorProduct k S
      ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) ⧸
      F.window (relThetaPairH1_windowM C π hπ g))
    ((TensorProduct k S
      ↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) ⧸
      F.window (relThetaPairH1_windowMS C π hπ g))
  -- a prime of the piece over `p`
  obtain ⟨pl, hpl⟩ : p ∈ Set.range
      (PrimeSpectrum.comap (algebraMap S (Localization.Away h))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away h) h]
    exact hh
  have hq : Ideal.comap (algebraMap S (Localization.Away h)) pl.asIdeal = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hpl
  -- matrix presentations of the two coordinate points, minors avoiding the prime
  obtain ⟨X₁, hX₁, I, hI, hdet₁, heq₁⟩ := exists_component_matrix hπ g hO hχ
    (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) le_rfl b₁ F h pl hfree₁
  obtain ⟨X₂, hX₂, J, hJ, hdet₂, heq₂⟩ := exists_component_matrix hπ g hO hχ
    (windowM_choice π hπ g + windowS_choice π hπ g)
    (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) b₂ F h pl hfree₂
  -- K6: the numerator stage
  have hc : (frameMinor k g r₁ (Localization.Away h) X₁ I hI).det
      * (frameMinor k g r₂ (Localization.Away h) X₂ J hJ).det ∉ pl.asIdeal := fun hmem =>
    (pl.isPrime.mem_or_mem hmem).elim hdet₁ hdet₂
  obtain ⟨u, hup, hdvd, hβu⟩ := exists_away_isUnit_of_notMem h hh hq _ hc
  -- the tower map `β` and the unit minors over `Localization.Away u`
  have hxu : IsUnit (algebraMap S (Localization.Away u) h) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap S (Localization.Away u)) hdvd)
      (IsLocalization.Away.algebraMap_isUnit u)
  set β : Localization.Away h →ₐ[k] Localization.Away u :=
    awayLiftAlgHom h (IsScalarTower.toAlgHom k S (Localization.Away u)) hxu with hβdef
  have hβcomp : β.toRingHom.comp (algebraMap S (Localization.Away h))
      = algebraMap S (Localization.Away u) :=
    congrArg AlgHom.toRingHom
      (awayLiftAlgHom_comp_algHom h (IsScalarTower.toAlgHom k S (Localization.Away u)) hxu)
  have hβc : IsUnit (β ((frameMinor k g r₁ (Localization.Away h) X₁ I hI).det
      * (frameMinor k g r₂ (Localization.Away h) X₂ J hJ).det)) :=
    hβu (Localization.Away u) β.toRingHom hβcomp
  rw [map_mul] at hβc
  have hu₁ : IsUnit (β (frameMinor k g r₁ (Localization.Away h) X₁ I hI).det) :=
    isUnit_of_mul_isUnit_left hβc
  have hu₂ : IsUnit (β (frameMinor k g r₂ (Localization.Away h) X₂ J hJ).det) :=
    isUnit_of_mul_isUnit_right hβc
  -- the chart-framed points over `Localization.Away u`
  have hcomp₁ := map_component_chart hπ g hO hχ (windowM_choice π hπ g)
    (relThetaPairH1_windowM C π hπ g) le_rfl b₁ F h u β hβcomp X₁ hX₁ I hI hu₁ heq₁
  have hcomp₂ := map_component_chart hπ g hO hχ
    (windowM_choice π hπ g + windowS_choice π hπ g)
    (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) b₂ F h u β hβcomp
    X₂ hX₂ J hJ hu₂ heq₂
  -- assemble the pair-chart map
  refine ⟨u, hup, ULift.up ⟨I, hI⟩, ULift.up ⟨J, hJ⟩,
    Algebra.TensorProduct.productMap
      (chartFrameMap k g r₁ (Localization.Away u) (X₁.map β) I hI)
      (chartFrameMap k g r₂ (Localization.Away u) (X₂.map β) J hJ), ?_, ?_⟩
  · have hpt : Module.Grassmannian.map
        (Algebra.TensorProduct.productMap
          (chartFrameMap k g r₁ (Localization.Away u) (X₁.map β) I hI)
          (chartFrameMap k g r₂ (Localization.Away u) (X₂.map β) J hJ))
        (pairTautFst k g r₁ r₂ (ULift.up ⟨I, hI⟩) (ULift.up ⟨J, hJ⟩))
        = congrAmbient b₁.equivFun
            (divFamWindowGr hπ g hO hχ (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g) le_rfl F (Localization.Away u)) := by
      rw [pairTautFst, ← Module.Grassmannian.map_comp,
        Algebra.TensorProduct.productMap_left]
      exact hcomp₁
    rw [hpt, congrAmbient_toSubmodule, divFamWindowGr_toSubmodule,
      ← DivFam.window_mapAlg hπ g hO hχ (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g) le_rfl (Localization.Away u) F]
    rfl
  · have hpt : Module.Grassmannian.map
        (Algebra.TensorProduct.productMap
          (chartFrameMap k g r₁ (Localization.Away u) (X₁.map β) I hI)
          (chartFrameMap k g r₂ (Localization.Away u) (X₂.map β) J hJ))
        (pairTautSnd k g r₁ r₂ (ULift.up ⟨I, hI⟩) (ULift.up ⟨J, hJ⟩))
        = congrAmbient b₂.equivFun
            (divFamWindowGr hπ g hO hχ
              (windowM_choice π hπ g + windowS_choice π hπ g)
              (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) F
              (Localization.Away u)) := by
      rw [pairTautSnd, ← Module.Grassmannian.map_comp,
        Algebra.TensorProduct.productMap_right]
      exact hcomp₂
    rw [hpt, congrAmbient_toSubmodule, divFamWindowGr_toSubmodule,
      ← DivFam.window_mapAlg hπ g hO hχ
        (windowM_choice π hπ g + windowS_choice π hπ g)
        (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)
        (Localization.Away u) F]
    rfl

include hO hχ in
/-- **G-5 §1.2 keystone — the ε frame-locus cover** (`informal/w4-g5-worksheet.md` §1.2
+ §2, in `divClassifyAff`'s hypothesis shapes): a finite span-⊤ family `f : Fin m → S`
such that over each piece some pair-chart map `w` frames the ε pair of the restricted
family — the `hw₁`/`hw₂` inputs of `divClassifyAff` at the piece.  The stitch
(worksheet §3–§4, `divClassify`) glues the resulting unique morphisms over this
cover. -/
theorem divFamEps_exists_frameCover (F : DivFam C S π g) :
    ∃ (m : ℕ) (f : Fin m → S), Ideal.span (Set.range f) = ⊤ ∧
      ∀ t : Fin m,
        ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
          (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away (f t)),
          (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
            = Submodule.map
                (LinearMap.baseChange (Localization.Away (f t)) b₁.equivFun.toLinearMap)
                (divFamEps hπ g (DivFam.mapAlg (Localization.Away (f t)) g F)).1 ∧
          (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
            = Submodule.map
                (LinearMap.baseChange (Localization.Away (f t)) b₂.equivFun.toLinearMap)
                (divFamEps hπ g (DivFam.mapAlg (Localization.Away (f t)) g F)).2 := by
  choose U hU hdata using exists_frame_chart_at_prime hπ g hO hχ r₁ r₂ b₁ b₂ F
  -- the chosen elements span the unit ideal: they avoid every maximal ideal
  have hspan : Ideal.span (Set.range U) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    refine hU ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ?_))
    exact Set.mem_range_self _
  have h1 : (1 : S) ∈ Ideal.span (Set.range U) := by
    rw [hspan]
    exact Submodule.mem_top
  -- restrict to a finite subfamily
  obtain ⟨t, hts, h1t⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨t.card, fun i => (t.equivFin.symm i : S), ?_, ?_⟩
  · have hrange : Set.range (fun i : Fin t.card => (t.equivFin.symm i : S)) = ↑t := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (t.equivFin.symm i).2
      · intro hx
        exact ⟨t.equivFin ⟨x, hx⟩, by simp⟩
    rw [hrange, Ideal.eq_top_iff_one]
    exact h1t
  · intro tt
    obtain ⟨p, hp⟩ : ((t.equivFin.symm tt : S)) ∈ Set.range U := hts (t.equivFin.symm tt).2
    have hgoal := hdata p
    rw [hp] at hgoal
    exact hgoal

end Keystone

end Curve

end AlgebraicGeometry
