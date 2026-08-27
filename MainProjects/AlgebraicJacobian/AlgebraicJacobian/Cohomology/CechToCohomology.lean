/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.AbsoluteCohomology

/-!
# Čech-to-cohomology comparison on a basis (Stacks 01EO) — L1/L2 chain

Project-local: builds the section-Čech short-exact-sequence (L1) and the
quotient-vanishing step (L2) of the 01EO dimension-shift argument.
-/

universe u

open CategoryTheory Limits CategoryTheory.Abelian

namespace AlgebraicGeometry

-- Re-activate the (file-local) `HasExt` instance from `AbsoluteCohomology.lean` so that the
-- `Ext`-based absolute cohomology resolves here without the slow `HasSmallLocalizedHom` search.
attribute [local instance] hasExtModules

variable {X : Scheme.{u}}

/-! ## Project-local Mathlib supplement — functoriality of the section Čech complex -/

/-- The cosimplicial morphism of section Čech objects induced by a morphism `φ` of
presheaves of modules, acting coordinatewise by the underlying presheaf morphism on each
basic-open section group. Project-local: `sectionCechCosimplicial` has no functoriality in
Mathlib. -/
noncomputable def sectionCechCosimplicialMap {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    {F G : X.PresheafOfModules} (φ : F ⟶ G) :
    sectionCechCosimplicial U F ⟶ sectionCechCosimplicial U G where
  app n := Limits.Pi.map (fun σ : Fin (n.len + 1) → ι =>
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ).app (Opposite.op (⨅ k, U (σ k))))
  naturality {m n} f := by
    apply Limits.Pi.hom_ext
    intro σ
    simp only [sectionCechCosimplicial, Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_π,
      Limits.Pi.map_π_assoc, Limits.Pi.lift_π_assoc]
    congr 1
    exact ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ).naturality _

/-- The section Čech cosimplicial object as a functor in the coefficient presheaf of modules.
Project-local: packages `sectionCechCosimplicialMap` with functoriality so the induced
short-complex maps compose and respect zero. -/
noncomputable def sectionCechCosimplicialFunctor {ι : Type u}
    (U : ι → TopologicalSpace.Opens X) : X.PresheafOfModules ⥤ CosimplicialObject Ab.{u} where
  obj F := sectionCechCosimplicial U F
  map φ := sectionCechCosimplicialMap U φ
  map_id F := by
    apply NatTrans.ext
    funext n
    change (Limits.Pi.map fun σ : Fin (n.len + 1) → ι =>
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (𝟙 F)).app
        (Opposite.op (⨅ k, U (σ k)))) = 𝟙 _
    rw [show (fun σ : Fin (n.len + 1) → ι =>
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (𝟙 F)).app
          (Opposite.op (⨅ k, U (σ k))))
      = (fun σ : Fin (n.len + 1) → ι =>
        𝟙 ((PresheafOfModules.presheaf F).obj (Opposite.op (⨅ k, U (σ k))))) from by
        funext σ; rw [CategoryTheory.Functor.map_id]; rfl]
    exact Limits.Pi.map_id
  map_comp φ ψ := by
    apply NatTrans.ext
    funext n
    change (Limits.Pi.map fun σ : Fin (n.len + 1) → ι =>
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (φ ≫ ψ)).app
        (Opposite.op (⨅ k, U (σ k)))) = _
    rw [show (fun σ : Fin (n.len + 1) → ι =>
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (φ ≫ ψ)).app
          (Opposite.op (⨅ k, U (σ k))))
      = (fun σ : Fin (n.len + 1) → ι =>
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ).app
              (Opposite.op (⨅ k, U (σ k))) ≫
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map ψ).app
              (Opposite.op (⨅ k, U (σ k)))) from by
        funext σ
        rw [CategoryTheory.Functor.map_comp]
        rfl]
    exact (Limits.Pi.map_comp_map _ _).symm

/-- The section Čech cochain complex as a functor in the coefficient presheaf of modules.
Project-local: functoriality of `sectionCechComplex`, used to form the short exact sequence of
Čech complexes. -/
noncomputable def sectionCechComplexFunctor {ι : Type u}
    (U : ι → TopologicalSpace.Opens X) : X.PresheafOfModules ⥤ CochainComplex Ab.{u} ℕ :=
  sectionCechCosimplicialFunctor U ⋙ AlgebraicTopology.alternatingCofaceMapComplex Ab.{u}

/-- The chain map of section Čech complexes induced by a morphism `φ` of presheaves of
modules. Project-local: functoriality of `sectionCechComplex` in the coefficient presheaf. -/
noncomputable def sectionCechComplexMap {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    {F G : X.PresheafOfModules} (φ : F ⟶ G) :
    sectionCechComplex U F ⟶ sectionCechComplex U G :=
  (AlgebraicTopology.alternatingCofaceMapComplex Ab.{u}).map (sectionCechCosimplicialMap U φ)

/-- **{\v C}ech cohomology accessor** `Ȟ^p(𝒰, F)`: the degree-`p` homology of the section
Čech complex, packaged as a named `Ab`-object. Project-local thin wrapper so the 01EO chain
can refer to `Ȟ^p` uniformly. -/
noncomputable def cechCohomology {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    (F : X.PresheafOfModules) (p : ℕ) : Ab.{u} :=
  (sectionCechComplex U F).homology p

/-! ## Project-local Mathlib supplement — product of short exact sequences in `Ab` -/

private lemma pi_π_map_apply {J : Type u} {f g : J → Ab.{u}} (φ : ∀ j, f j ⟶ g j)
    (x : ToType (∏ᶜ f)) (σ : J) :
    Limits.Pi.π g σ (Limits.Pi.map φ x) = φ σ (Limits.Pi.π f σ x) := by
  rw [← ConcreteCategory.comp_apply, Limits.Pi.map_π, ConcreteCategory.comp_apply]

/-- **A product of short exact sequences of abelian groups is short exact.** This is the AB4*
content used in the section Čech short-exact-sequence: each Čech term is a product of section
groups over basic opens, so degreewise short-exactness of the Čech complexes reduces to this.
Project-local: Mathlib has no off-the-shelf "product of short exact sequences" lemma. -/
theorem shortExact_piMap {J : Type u} (S : J → ShortComplex Ab.{u}) (h : ∀ j, (S j).ShortExact) :
    (ShortComplex.mk (Limits.Pi.map (fun j => (S j).f)) (Limits.Pi.map (fun j => (S j).g))
      (by rw [Limits.Pi.map_comp_map]
          have hz : (fun j => (S j).f ≫ (S j).g) = (fun j => (0 : (S j).X₁ ⟶ (S j).X₃)) := by
            funext j; exact (S j).zero
          rw [hz]; ext x; simp)).ShortExact := by
  haveI : ∀ j, Mono (S j).f := fun j => (h j).mono_f
  -- Epi of the product map: surjectivity, chosen componentwise
  have hepi : Epi (Limits.Pi.map (fun j => (S j).g)) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    refine ⟨(Concrete.productEquiv (fun j => (S j).X₂)).symm
      (fun σ => ((h σ).ab_surjective_g (Limits.Pi.π (fun j => (S j).X₃) σ y)).choose), ?_⟩
    refine (Concrete.productEquiv (fun j => (S j).X₃)).injective (funext fun σ => ?_)
    rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply,
      pi_π_map_apply, Concrete.productEquiv_symm_apply_π]
    exact ((h σ).ab_surjective_g (Limits.Pi.π (fun j => (S j).X₃) σ y)).choose_spec
  haveI := hepi
  haveI hmono : Mono (Limits.Pi.map (fun j => (S j).f)) := inferInstance
  refine ShortComplex.ShortExact.mk ?_
  rw [ShortComplex.ab_exact_iff_function_exact]
  change Function.Exact (Limits.Pi.map (fun j => (S j).f)) (Limits.Pi.map (fun j => (S j).g))
  intro x
  constructor
  · intro hx
    have hcomp : ∀ σ, (S σ).g (Limits.Pi.π (fun j => (S j).X₂) σ x) = 0 := by
      intro σ
      have := congrArg (Limits.Pi.π (fun j => (S j).X₃) σ) hx
      rwa [pi_π_map_apply, map_zero] at this
    choose w hw using fun σ => (((ShortComplex.ab_exact_iff_function_exact (S σ)).mp
      (h σ).exact (Limits.Pi.π (fun j => (S j).X₂) σ x)).mp
      (hcomp σ) : Limits.Pi.π (fun j => (S j).X₂) σ x ∈ Set.range (S σ).f)
    refine ⟨(Concrete.productEquiv (fun j => (S j).X₁)).symm w, ?_⟩
    refine (Concrete.productEquiv (fun j => (S j).X₂)).injective (funext fun σ => ?_)
    rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply,
      pi_π_map_apply, Concrete.productEquiv_symm_apply_π]
    exact hw σ
  · rintro ⟨w, rfl⟩
    rw [← ConcreteCategory.comp_apply, Limits.Pi.map_comp_map]
    have hz : (fun j => (S j).f ≫ (S j).g) = (fun j => (0 : (S j).X₁ ⟶ (S j).X₃)) := by
      funext j; exact (S j).zero
    rw [hz, show (Limits.Pi.map fun j => (0 : (S j).X₁ ⟶ (S j).X₃)) = 0 from by ext z; simp]
    rfl

/-! ## Project-local Mathlib supplement — L1 short exact sequence of section Čech complexes -/

/-- The degree-`p`, index-`σ` term short complex of section groups over the basic open
`⨅ₖ U(σ k)` induced by a short complex `P` of presheaves of modules. Project-local: the
building block of the section Čech short exact sequence. -/
noncomputable def faceShortComplex {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    (P : ShortComplex X.PresheafOfModules) {p : ℕ} (σ : Fin (p + 1) → ι) : ShortComplex Ab.{u} :=
  ShortComplex.mk
    (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map P.f).app (Opposite.op (⨅ k, U (σ k))))
    (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map P.g).app (Opposite.op (⨅ k, U (σ k))))
    (by rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, P.zero,
          CategoryTheory.Functor.map_zero]; rfl)

/-- The short complex of section Čech cochain complexes `0 → Č(F) → Č(I) → Č(Q) → 0` induced by
a short complex `P : 0 → F → I → Q → 0` of presheaves of modules. Project-local: Mathlib has no
section Čech complex, hence no short complex of them. -/
noncomputable def sectionCechComplexShortComplex {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    (P : ShortComplex X.PresheafOfModules) : ShortComplex (CochainComplex Ab.{u} ℕ) :=
  ShortComplex.mk (sectionCechComplexMap U P.f) (sectionCechComplexMap U P.g) (by
    apply HomologicalComplex.hom_ext
    intro i
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
    change (Limits.Pi.map fun σ : Fin (i + 1) → ι =>
        (faceShortComplex U P σ).f) ≫ (Limits.Pi.map fun σ : Fin (i + 1) → ι =>
        (faceShortComplex U P σ).g) = 0
    rw [Limits.Pi.map_comp_map,
      show (fun σ : Fin (i + 1) → ι => (faceShortComplex U P σ).f ≫ (faceShortComplex U P σ).g)
        = (fun σ : Fin (i + 1) → ι => (0 : (faceShortComplex U P σ).X₁ ⟶
            (faceShortComplex U P σ).X₃)) from by funext σ; exact (faceShortComplex U P σ).zero,
      show (Limits.Pi.map fun σ : Fin (i + 1) → ι => (0 : (faceShortComplex U P σ).X₁ ⟶
          (faceShortComplex U P σ).X₃)) = 0 from by ext z; simp])

/-- **Short exact sequence of section Čech complexes from a basis (Stacks 01EO L1).** Given a
short complex `P` of presheaves of modules whose section sequences over every basic open
`⨅ₖ U(σ k)` are short exact (left-exactness from the sheaf sequence plus the basis surjectivity
of `ses_cech_h1`), the induced section Čech complexes form a short exact sequence. Project-local:
this is the term-wise-product step of the 01EO proof; degreewise it is a product of the
basic-open section short exact sequences. -/
theorem cechComplex_shortExact_of_basis {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    (P : ShortComplex X.PresheafOfModules)
    (hface : ∀ (p : ℕ) (σ : Fin (p + 1) → ι), (faceShortComplex U P σ).ShortExact) :
    (sectionCechComplexShortComplex U P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact shortExact_piMap (fun σ : Fin (i + 1) → ι => faceShortComplex U P σ) (hface i)

/-! ## Project-local Mathlib supplement — L2 homological core (quotient vanishing) -/

/-- **Quotient preserves vanishing higher cohomology (homological core, Stacks 01EO L2).**
Given a short exact sequence of cochain complexes `0 → X₁ → X₂ → X₃ → 0` in which the middle
term `X₂` has vanishing positive homology (the injective/acyclic term) and the left term `X₁`
has vanishing positive homology (condition (3)), the right term `X₃` (the quotient) again has
vanishing positive homology. Proved by the homology long exact sequence: the connecting map
gives `Hᵖ(X₃) ≅ Hᵖ⁺¹(X₁) = 0`. Project-local: the 01EO dimension-shift needs this abstract
shape; it is then instantiated at the section Čech complexes. -/
theorem cechHomology_quotient_vanishing (T : ShortComplex (CochainComplex Ab.{u} ℕ))
    (hT : T.ShortExact) (hI : ∀ p, 0 < p → IsZero (T.X₂.homology p))
    (hF : ∀ p, 0 < p → IsZero (T.X₁.homology p)) :
    ∀ p, 0 < p → IsZero (T.X₃.homology p) := by
  intro p hp
  have hrel : (ComplexShape.up ℕ).Rel p (p + 1) := rfl
  have hiso : T.X₃.homology p ≅ T.X₁.homology (p + 1) :=
    hT.δIso p (p + 1) hrel (hI p hp) (hI (p + 1) (Nat.succ_pos p))
  exact (hF (p + 1) (Nat.succ_pos p)).of_iso hiso

/-- **Quotient preserves vanishing higher Čech cohomology (Stacks 01EO L2).** Concrete form in
terms of `cechCohomology`: with the section Čech short exact sequence of `P` (from L1), if the
middle term `I` (injective/acyclic, condition from `injective_cech_acyclic`) and the left term
`F` (condition (3)) both have vanishing positive Čech cohomology, then so does the quotient `Q`.
Project-local: instantiates `cechHomology_quotient_vanishing` at the section Čech complexes. -/
theorem quotient_cech_vanishing_of_basis {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    (P : ShortComplex X.PresheafOfModules)
    (hSES : (sectionCechComplexShortComplex U P).ShortExact)
    (hI : ∀ p, 0 < p → IsZero (cechCohomology U P.X₂ p))
    (hF : ∀ p, 0 < p → IsZero (cechCohomology U P.X₁ p)) :
    ∀ p, 0 < p → IsZero (cechCohomology U P.X₃ p) :=
  cechHomology_quotient_vanishing (sectionCechComplexShortComplex U P) hSES hI hF

/-! ## Project-local Mathlib supplement — per-face short exact sequence (01EO) -/

/-- The sections functor `Γ(V, -) : X.Modules ⥤ Ab` over a fixed open `V`, as the composite of
the inclusion of sheaves of modules into presheaves of modules, the forgetful to presheaves of
abelian groups, and evaluation at `V`. Project-local: used only to package the left-exactness of
sections (each factor preserves finite limits) for the per-face short exact sequence. -/
noncomputable def sectionsFunctor (V : TopologicalSpace.Opens X) : X.Modules ⥤ Ab.{u} :=
  Scheme.Modules.toPresheafOfModules X ⋙ PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation _ _).obj (Opposite.op V)

/-- **Per-face short exact sequence from a sheaf short exact sequence (Stacks 01EO).** Given a
short exact sequence `S : 0 → F → I → Q → 0` of sheaves of `O_X`-modules and the assumption that
on every face `V_σ = ⨅ₖ U(σ k)` the section map `I(V_σ) → Q(V_σ)` is surjective, the per-face
short complex `faceShortComplex U (S.map toPresheafOfModules) σ` is short exact. Mono and middle
exactness come from left-exactness of the sections functor (`sectionsFunctor` preserves finite
limits); the epi is the surjectivity hypothesis (supplied downstream by `ses_cech_h1`).
Project-local: produces the per-face hypothesis consumed by `cechComplex_shortExact_of_basis`. -/
theorem faceShortComplex_shortExact_of_sheaf_ses {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hsurj : ∀ (p : ℕ) (σ : Fin (p + 1) → ι), Function.Surjective (ConcreteCategory.hom
      (faceShortComplex U (S.map (Scheme.Modules.toPresheafOfModules X)) σ).g))
    (p : ℕ) (σ : Fin (p + 1) → ι) :
    (faceShortComplex U (S.map (Scheme.Modules.toPresheafOfModules X)) σ).ShortExact := by
  haveI hpzm : (sectionsFunctor (⨅ k, U (σ k))).PreservesZeroMorphisms := by
    unfold sectionsFunctor; infer_instance
  haveI hpfl : PreservesFiniteLimits (sectionsFunctor (⨅ k, U (σ k))) := by
    unfold sectionsFunctor; infer_instance
  haveI : Mono S.f := hS.mono_f
  change (S.map (sectionsFunctor (⨅ k, U (σ k)))).ShortExact
  have hex : (S.map (sectionsFunctor (⨅ k, U (σ k)))).Exact :=
    ShortComplex.Exact.map_of_mono_of_preservesKernel hS.exact
      (sectionsFunctor (⨅ k, U (σ k))) hS.mono_f inferInstance
  haveI : Mono (S.map (sectionsFunctor (⨅ k, U (σ k)))).f :=
    inferInstanceAs (Mono ((sectionsFunctor (⨅ k, U (σ k))).map S.f))
  haveI : Epi (S.map (sectionsFunctor (⨅ k, U (σ k)))).g := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact hsurj p σ
  exact ShortComplex.ShortExact.mk hex

/-! ## Project-local Mathlib supplement — L3 base case `H¹(U, F) = 0` -/

/-- **Sheaf-cohomology base case `H¹(U, F) = 0` (Stacks 01EO L3).** Given a short exact
sequence `S : 0 → F → I → Q → 0` in `X.Modules` with `I = S.X₂` injective, and assuming the
section map `I(U) → Q(U)` is surjective, the first absolute cohomology `H¹(U, F) = Ext¹(jShriekOU
U, F)` vanishes. The proof runs the covariant Ext long exact sequence: `H¹(U, I) = 0` by injective
vanishing, and surjectivity of the section map transfers (via the natural `H⁰ ≅ Γ`) to
surjectivity of `H⁰(U, I) → H⁰(U, Q)`, killing the connecting map. Project-local: assembles the
`AbsoluteCohomology` Ext wrappers into the 01EO base case. -/
theorem absoluteCohomology_one_eq_zero_of_basis (U : TopologicalSpace.Opens X)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) [Injective S.X₂]
    (hsurj : Function.Surjective
      (ConcreteCategory.hom (((Scheme.Modules.toPresheafOfModules X).map S.g).app (Opposite.op U))))
    (e : Ext (jShriekOU U) S.X₁ 1) : e = 0 := by
  have hef : e.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    absoluteCohomology_eq_zero_of_injective 0 U S.X₂ _
  obtain ⟨x₃, hx₃⟩ := absoluteCohomology_covariant_exact₁ U hS e hef (rfl : 0 + 1 = 1)
  have hgsurj : Function.Surjective
      (fun y : Ext (jShriekOU U) S.X₂ 0 => y.comp (Ext.mk₀ S.g) (add_zero 0)) := by
    intro z
    obtain ⟨i, hi⟩ := hsurj (absoluteCohomologyZeroAddEquiv U S.X₃ z)
    refine ⟨(absoluteCohomologyZeroAddEquiv U S.X₂).symm i, ?_⟩
    apply (absoluteCohomologyZeroAddEquiv U S.X₃).injective
    rw [absoluteCohomologyZeroAddEquiv_naturality, AddEquiv.apply_symm_apply, hi]
  obtain ⟨x₂, hx₂⟩ := hgsurj x₃
  rw [← hx₃, ← hx₂,
    Ext.comp_assoc x₂ (Ext.mk₀ S.g) hS.extClass (add_zero 0) (rfl : 0 + 1 = 1) rfl,
    hS.comp_extClass, Ext.comp_zero]

/-! ## Project-local Mathlib supplement — cover system on a basis (01EO conditions 1–2) -/

/-- A **covering datum** on `X`: an index family of opens (the covered open is `⨆ i, c.2 i`).
Project-local: the lightweight cover representation matching the cover-local Čech lemmas
(`cechCohomology`, `faceShortComplex`), which are indexed by a family `ι → Opens X`. -/
abbrev CovDatum (X : Scheme.{u}) : Type (u + 1) :=
  Σ ι : Type u, ι → TopologicalSpace.Opens X

/-- **Cover system on a basis** (Stacks 01EO conditions (1)–(2)). Records a basis `B`, a set of
admissible coverings `Cov`, the faces-in-basis datum (every finite intersection of a covering's
opens lies in `B`, condition (1)), and the cofinality datum in the form it is consumed —
condition (2) packaged as the section-surjectivity it produces through `ses_cech_h1`: for every
short exact sequence `S` of `O_X`-modules whose left term has vanishing higher Čech cohomology,
the section map of `S.g` is surjective over every basic open. The auxiliary `injective_acyclic`
field records the standard-cover injective Čech-acyclicity (Stacks
`lemma-injective-trivial-cech`, i.e. `injective_cech_acyclic`) for the system's coverings.
Project-local: bespoke encoding; the two sheaf-theoretic fields are discharged at the affine
(02KG) instantiation by `ses_cech_h1` + standard-cover cofinality and by `injective_cech_acyclic`
respectively. -/
structure BasisCovSystem (X : Scheme.{u}) where
  /-- The basis of opens. -/
  B : Set (TopologicalSpace.Opens X)
  /-- The set of admissible coverings. -/
  Cov : Set (CovDatum X)
  /-- Condition (1): every finite intersection of a covering's opens lies in the basis. -/
  faces_mem : ∀ c ∈ Cov, ∀ (p : ℕ) (σ : Fin (p + 1) → c.1), (⨅ k, c.2 (σ k)) ∈ B
  /-- Condition (2), in the section-surjectivity shape produced by `ses_cech_h1` + cofinality. -/
  surj_of_vanishing : ∀ (S : ShortComplex X.Modules), S.ShortExact →
    (∀ c ∈ Cov, ∀ q, 0 < q →
      IsZero (cechCohomology c.2 ((Scheme.Modules.toPresheafOfModules X).obj S.X₁) q)) →
    ∀ V ∈ B, Function.Surjective (ConcreteCategory.hom
      (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((Scheme.Modules.toPresheafOfModules X).map S.g)).app (Opposite.op V)))
  /-- Injective Čech-acyclicity for the system's coverings (`injective_cech_acyclic`). -/
  injective_acyclic : ∀ (I : X.Modules), Injective I → ∀ c ∈ Cov, ∀ q, 0 < q →
    IsZero (cechCohomology c.2 ((Scheme.Modules.toPresheafOfModules X).obj I) q)

/-- **Vanishing higher Čech cohomology for a cover system** (Stacks 01EO condition (3)). An
`O_X`-module `F` satisfies this when `Ȟᵖ(𝒰, F) = 0` for every covering `𝒰 ∈ s.Cov` and every
`p > 0`. Stated for an arbitrary module (not necessarily quasi-coherent): the dimension-shift
induction feeds the quotient `Q = I/F` back as coefficient, and `Q` need not be quasi-coherent.
Project-local: the inductive predicate of the 01EO argument. -/
@[reducible] def HasVanishingHigherCech (s : BasisCovSystem X) (F : X.Modules) : Prop :=
  ∀ c ∈ s.Cov, ∀ p, 0 < p →
    IsZero (cechCohomology c.2 ((Scheme.Modules.toPresheafOfModules X).obj F) p)

/-! ## Project-local Mathlib supplement — L4 dimension-shift induction -/

-- The dimension-shift induction embeds modules into injectives, which needs
-- `EnoughInjectives X.Modules`. That instance is NOT available in Mathlib for sheaves of modules
-- (it would follow from `IsGrothendieckAbelian (SheafOfModules R)`, which is absent — see
-- `analogies/p5a.md`), so — following the project convention for the P5a derived-functor lane —
-- it is carried as an explicit hypothesis on `injSES`/L4 rather than synthesized.

/-- The injective-embedding short exact sequence `0 → F → I → I/F → 0` of an `O_X`-module `F`,
with `I = Injective.under F` the chosen injective and `I/F` its cokernel. Project-local helper for
the 01EO dimension-shift induction; carries `[EnoughInjectives X.Modules]` as a hypothesis. -/
@[reducible] private noncomputable def injSES [EnoughInjectives X.Modules] (F : X.Modules) :
    ShortComplex X.Modules :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

private lemma injSES_shortExact [EnoughInjectives X.Modules] (F : X.Modules) :
    (injSES F).ShortExact :=
  ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel _)

/-- **Dimension-shift induction `Hᵖ(U, F) = 0` for `p > 0` (Stacks 01EO L4).** For a cover system
`s` on a basis and any `O_X`-module `F` with vanishing higher Čech cohomology for `s`, the
absolute cohomology `Hᵖ(U, F) = Extᵖ(jShriekOU U, F)` vanishes for every basic open `U ∈ s.B` and
`p > 0`. Induction on `p`, quantified over all `F` in the inductive class: the quotient
`Q = I/F` re-enters the class (via the section Čech SES of L1 from the per-face SES, plus L2
quotient-vanishing and the cover system's injective acyclicity), the base case is L3, and the
inductive step is the covariant Ext long exact sequence. Project-local: the 01EO inductive core. -/
theorem absoluteCohomology_eq_zero_of_basis [EnoughInjectives X.Modules] (s : BasisCovSystem X)
    {F : X.Modules} (hF : HasVanishingHigherCech s F)
    {U : TopologicalSpace.Opens X} (hU : U ∈ s.B) {p : ℕ} (hp : 0 < p)
    (e : Ext (jShriekOU U) F p) : e = 0 := by
  have key : ∀ (n : ℕ) (F : X.Modules), HasVanishingHigherCech s F →
      ∀ (U : TopologicalSpace.Opens X), U ∈ s.B →
        ∀ e : Ext (jShriekOU U) F (n + 1), e = 0 := by
    intro n
    induction n with
    | zero =>
      intro F hF U hU e
      have hS := injSES_shortExact F
      haveI : Injective (injSES F).X₂ := inferInstance
      exact absoluteCohomology_one_eq_zero_of_basis U hS
        (s.surj_of_vanishing (injSES F) hS hF U hU) e
    | succ m ih =>
      intro F hF U hU e
      have hS := injSES_shortExact F
      haveI : Injective (injSES F).X₂ := inferInstance
      -- The quotient `Q = (injSES F).X₃` again has vanishing higher Čech cohomology.
      have hQ : HasVanishingHigherCech s (injSES F).X₃ := by
        intro c hc q hq
        set P := (injSES F).map (Scheme.Modules.toPresheafOfModules X) with hP
        have hface : ∀ (pp : ℕ) (σ : Fin (pp + 1) → c.1),
            (faceShortComplex c.2 P σ).ShortExact := by
          intro pp σ
          refine faceShortComplex_shortExact_of_sheaf_ses c.2 (injSES F) hS ?_ pp σ
          intro pp' σ'
          exact s.surj_of_vanishing (injSES F) hS hF _ (s.faces_mem c hc pp' σ')
        have hSES := cechComplex_shortExact_of_basis c.2 P hface
        exact quotient_cech_vanishing_of_basis c.2 P hSES
          (s.injective_acyclic (injSES F).X₂ inferInstance c hc) (hF c hc) q hq
      -- Ext long exact sequence step: `H^{m+2}(F)` is squeezed by `H^{m+1}(Q) = 0` (IH) and
      -- `H^{m+2}(I) = 0` (injective vanishing).
      have hef : e.comp (Ext.mk₀ (injSES F).f) (add_zero (m + 1 + 1)) = 0 :=
        absoluteCohomology_eq_zero_of_injective (m + 1) U (injSES F).X₂ _
      obtain ⟨x₃, hx₃⟩ :=
        absoluteCohomology_covariant_exact₁ U hS e hef (rfl : (m + 1) + 1 = m + 1 + 1)
      have hx₃zero : x₃ = 0 := ih (injSES F).X₃ hQ U hU x₃
      rw [← hx₃, hx₃zero, Ext.zero_comp]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  exact key n F hF U hU e

/-! ## Project-local Mathlib supplement — Čech-to-cohomology comparison on a basis (01EO top) -/

/-- **Čech-to-cohomology comparison on a basis (Stacks 01EO).** Let `s` be a cover system on a
basis for `X` and `F` an `O_X`-module with vanishing higher Čech cohomology for `s` (conditions
(1)–(3) of 01EO, packaged in `s` and `hF`). Then the absolute cohomology `Hᵖ(U, F) =
Extᵖ(jShriekOU U, F)` vanishes for every basic open `U ∈ s.B` and every `p > 0`. The thin assembly
of the dimension-shift induction `absoluteCohomology_eq_zero_of_basis` (L4), which itself chains
the section-Čech short exact sequence (L1), quotient vanishing (L2), and the base case (L3).
Project-local: the named 01EO target, carrying `[EnoughInjectives X.Modules]` as a hypothesis (the
instance is absent in Mathlib for sheaves of modules; see `injSES`). -/
theorem cech_eq_cohomology_of_basis [EnoughInjectives X.Modules] (s : BasisCovSystem X)
    {F : X.Modules} (hF : HasVanishingHigherCech s F) :
    ∀ U ∈ s.B, ∀ p, 0 < p → ∀ e : Ext (jShriekOU U) F p, e = 0 :=
  fun _ hU _ hp e => absoluteCohomology_eq_zero_of_basis s hF hU hp e

end AlgebraicGeometry
