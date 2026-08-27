/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Topology.Sheaves.LocallySurjective
import AlgebraicJacobian.Cohomology.CechBridge
import AlgebraicJacobian.Cohomology.CechToCohomology
import AlgebraicJacobian.Cohomology.QcohTildeSections

/-!
# Serre vanishing on affines (Stacks 02KG) — affine cover-system infrastructure

Project-local: builds the *affine cover system* feeding the basis-comparison criterion
`cech_eq_cohomology_of_basis` (01EO). The basis `B` is the distinguished opens `D(f)`
of an affine scheme, and the admissible coverings `Cov` are the standard open covers.

This file builds the cover-system infrastructure (Lane 1 of the 02KG decomposition) as far
as possible; the quasi-coherent seed `affine_cech_vanishing_qcoh` and the top
`affine_serre_vanishing` are handed off to the assembly iteration (they consume Lane 2's
`qcoh_iso_tilde_sections`).
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

-- Re-activate the (file-local) `HasExt` instance from `AbsoluteCohomology.lean` so that the
-- `Ext`-based absolute cohomology resolves here without the slow `HasSmallLocalizedHom` search.
attribute [local instance] hasExtModules

variable {X : Scheme.{u}}

/-! ## Project-local Mathlib supplement — distinguished opens closed under finite intersection -/

/-- **Distinguished opens are closed under finite intersection** (Stacks 02KG, condition (1)).
For a family `s : ι → R` of ring elements and a Čech multi-index `σ : Fin (p + 1) → ι`, the
`(p + 1)`-fold intersection of distinguished opens `⨅ₖ D(s_{σ k})` is again a distinguished
open, namely `D(∏ₖ s_{σ k})`; hence it lies in the basis of distinguished opens. This discharges
the `faces_mem` field of the affine cover system. Project-local: re-export of `basicOpen_sprod`
in the membership shape the `BasisCovSystem.faces_mem` field consumes. -/
theorem affine_faces_mem {R : CommRingCat.{u}} {ι : Type u} (s : ι → R)
    {p : ℕ} (σ : Fin (p + 1) → ι) :
    (⨅ k, PrimeSpectrum.basicOpen (s (σ k)) : (Spec R).Opens)
      ∈ Set.range (fun f : R => (PrimeSpectrum.basicOpen f : (Spec R).Opens)) :=
  ⟨∏ k, s (σ k), (basicOpen_sprod (p + 1) s σ).symm⟩

/-! ## Project-local Mathlib supplement — covering-datum bridge to the open-cover Čech form -/

/-- **The standard affine open cover realizes the distinguished-open family.** For a spanning
family `s : ι → R`, the `i`-th member of the standard affine open cover
`affineOpenCoverOfSpanRangeEqTop s hs` of `Spec R` has open range exactly the distinguished open
`D(s_i)`, i.e. `coverOpen 𝒰 i = PrimeSpectrum.basicOpen (s i)`. This is the open-level half of the
covering-datum bridge (`lem:cover_datum_bridge`): funext-rewriting the raw family `c.2 = fun i ↦
D(s_i)` to `coverOpen 𝒰` identifies the two section Čech complexes, so the Čech cohomology computed
over the raw `CovDatum` and over the `X.OpenCover` agree. Project-local: needed to feed the
`X.OpenCover`-shaped `injective_cech_acyclic` into the raw-family `BasisCovSystem` fields. -/
theorem coverOpen_affineOpenCoverOfSpan {R : CommRingCat.{u}} {ι : Type u} [Finite ι]
    (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤) (i : ι) :
    coverOpen (Scheme.AffineOpenCover.openCover (Scheme.affineOpenCoverOfSpanRangeEqTop s hs)) i
      = PrimeSpectrum.basicOpen (s i) := by
  unfold coverOpen
  change (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (s i))))).opensRange = _
  apply TopologicalSpace.Opens.ext
  change Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (s i))))).base = _
  rw [Spec.map_base]
  exact PrimeSpectrum.localization_away_comap_range (Localization.Away (s i)) (s i)

/-! ## Project-local Mathlib supplement — injective acyclicity for the standard affine cover -/

/-- **Injective Čech-acyclicity for the standard affine cover** (Stacks 02KG, `injective_acyclic`
field; Stacks `lemma-injective-trivial-cech`). For a spanning family `s : ι → R` (so the
distinguished opens `D(s_i)` cover `Spec R`) and an injective `O_X`-module `I`, the positive-degree
section Čech cohomology over the standard cover vanishes:
`Ȟ^q(𝒰, I) = 0` for all `q > 0`. Reduces the raw-family `cechCohomology` to the `X.OpenCover` form
via `coverOpen_affineOpenCoverOfSpan` and applies `injective_cech_acyclic`. Project-local: this is
the affine instantiation of `injective_cech_acyclic` discharging the
`BasisCovSystem.injective_acyclic` field for standard covers of the whole affine. -/
theorem affine_injective_acyclic {R : CommRingCat.{u}} {ι : Type u} [Finite ι]
    (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    (I : (Spec R).Modules) [Injective I] (q : ℕ) (hq : 0 < q) :
    IsZero (cechCohomology (fun i => PrimeSpectrum.basicOpen (s i))
      ((Scheme.Modules.toPresheafOfModules (Spec R)).obj I) q) := by
  have hbridge : (fun i => PrimeSpectrum.basicOpen (s i))
      = coverOpen (Scheme.affineOpenCoverOfSpanRangeEqTop s hs).openCover := by
    funext i; exact (coverOpen_affineOpenCoverOfSpan s hs i).symm
  haveI : Finite (Scheme.affineOpenCoverOfSpanRangeEqTop s hs).openCover.I₀ :=
    inferInstanceAs (Finite ι)
  rw [cechCohomology, hbridge]
  exact injective_cech_acyclic (Scheme.affineOpenCoverOfSpanRangeEqTop s hs).openCover I q hq

/-! ## Project-local Mathlib supplement — the underlying-abelian-sheaf functor preserves colimits

The gap-fill `toSheaf_preservesFiniteColimits` / `toSheaf_preservesEpimorphisms` (blueprint
`lem:toSheaf_preservesFiniteColimits`, `lem:to_sheaf_preserves_epi`) — the statement that
`SheafOfModules.toSheaf R` (the forgetful functor to abelian sheaves) preserves finite colimits,
hence epimorphisms — is the foundational ingredient for `affine_surj_of_vanishing` (and hence for
the `surj_of_vanishing` field of `affineCoverSystem`).  Mathlib provides only the limit-side dual
`PreservesFiniteLimits (toSheaf R)` (`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`); the
colimit side is genuinely absent because epis of sheaves of modules are only *locally* surjective
and no factorisation through the right adjoint `forget` can capture it.

The build below mirrors Mathlib's `…/ModuleCat/Sheaf/Colimits.lean` construction but routes through
the **sheafification square** `PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)` (not through
`forget`).  Write `L := PresheafOfModules.sheafification (𝟙 R.obj)`, a left adjoint (counit iso).
Step 1: `L ⋙ toSheaf R ≅ toPresheaf R.obj ⋙ presheafToSheaf J Ab` (the square), and the right-hand
composite preserves finite colimits (`toPresheaf` does objectwise; `presheafToSheaf` is a left
adjoint).  Step 2 (descent): for a finite diagram `F`, `F ≅ (F ⋙ forget R) ⋙ L`; applying the
colimit-preserving `L` and then `L ⋙ toSheaf R` to a colimit cocone of `F ⋙ forget R` exhibits
`toSheaf R` as preserving the colimit of `F`.  Epi-preservation follows from `WalkingSpan` being
finite. -/

/-- **The underlying-abelian-sheaf functor preserves finite colimits** (blueprint
`lem:toSheaf_preservesFiniteColimits`).  The forgetful functor `SheafOfModules.toSheaf R` from
sheaves of `R`-modules to the underlying sheaves of abelian groups preserves finite colimits — the
right-exact dual of the Mathlib-supplied `PreservesFiniteLimits (toSheaf R)`.  Project-local: the
missing colimit side, built through the sheafification square (never through the right adjoint
`forget`). -/
theorem toSheaf_preservesFiniteColimits.{v', u', w'} {C : Type u'} [Category.{w'} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{v'})
    [HasWeakSheafify J AddCommGrpCat.{v'}] [J.WEqualsLocallyBijective AddCommGrpCat.{v'}] :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{v'} R) := by
  have step1 : PreservesFiniteColimits
      (PresheafOfModules.sheafification (𝟙 R.obj) ⋙ SheafOfModules.toSheaf.{v'} R) :=
    preservesFiniteColimits_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  haveI : PreservesColimitsOfSize (PresheafOfModules.sheafification.{v'} (𝟙 R.obj)) :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).leftAdjoint_preservesColimits
  constructor
  intro K _ _
  constructor
  intro F
  set D := F ⋙ SheafOfModules.forget R with hD
  have e : F ≅ D ⋙ PresheafOfModules.sheafification (𝟙 R.obj) :=
    Functor.isoWhiskerLeft F
      (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
  have hc : IsColimit (colimit.cocone D) := colimit.isColimit D
  have hLc := isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 R.obj)) hc
  have hF := isColimitOfPreserves
    (PresheafOfModules.sheafification (𝟙 R.obj) ⋙ SheafOfModules.toSheaf R) hc
  haveI hpres : PreservesColimit (D ⋙ PresheafOfModules.sheafification (𝟙 R.obj))
      (SheafOfModules.toSheaf R) :=
    preservesColimit_of_preserves_colimit_cocone hLc hF
  exact preservesColimit_of_iso_diagram (SheafOfModules.toSheaf R) e.symm

/-- **The underlying-abelian-sheaf functor preserves epimorphisms** (blueprint
`lem:to_sheaf_preserves_epi`).  A one-line corollary of `toSheaf_preservesFiniteColimits`:
finite-colimit preservation implies preservation of pushouts (`WalkingSpan`), hence of
epimorphisms.  This is the instance unlocking the passage from a module epimorphism to local
surjectivity in `affine_surj_of_vanishing`. -/
theorem toSheaf_preservesEpimorphisms.{v', u', w'} {C : Type u'} [Category.{w'} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{v'})
    [HasWeakSheafify J AddCommGrpCat.{v'}] [J.WEqualsLocallyBijective AddCommGrpCat.{v'}] :
    (SheafOfModules.toSheaf.{v'} R).PreservesEpimorphisms := by
  haveI : PreservesColimitsOfShape WalkingSpan (SheafOfModules.toSheaf.{v'} R) :=
    (toSheaf_preservesFiniteColimits R).preservesFiniteColimits WalkingSpan
  exact preservesEpimorphisms_of_preservesColimitsOfShape _

/-! ## Project-local Mathlib supplement — standard covers are cofinal -/

/-- **Standard covers are cofinal among open covers of a distinguished open** (Stacks 02KG, Tag
009L; blueprint `lem:standard_cover_cofinal`).  Given a distinguished open `D(f)` of `Spec R` and an
arbitrary open cover `W : α → (Spec R).Opens` of it, there is a finite standard subcover refining
it: finitely many `g : Fin n → R` with `D(f) = ⨆ᵢ D(gᵢ)` and each `D(gᵢ) ≤ W (φ i)`.  This is the
refinement step invoked in `affine_surj_of_vanishing`.  Project-local: combines quasi-compactness of
`D(f)` with the basic-open basis. -/
theorem standard_cover_cofinal {R : CommRingCat.{u}} (f : R) {α : Type u}
    (W : α → (Spec R).Opens)
    (hcov : (PrimeSpectrum.basicOpen f : (Spec R).Opens) ≤ ⨆ a, W a) :
    ∃ (n : ℕ) (g : Fin n → R) (φ : Fin n → α),
      (PrimeSpectrum.basicOpen f : (Spec R).Opens) = ⨆ i, PrimeSpectrum.basicOpen (g i) ∧
      ∀ i, (PrimeSpectrum.basicOpen (g i) : (Spec R).Opens) ≤ W (φ i) := by
  classical
  set Uf : (Spec R).Opens := PrimeSpectrum.basicOpen f with hUf
  have hK : IsCompact (Uf : Set ↥(Spec R)) := PrimeSpectrum.isCompact_basicOpen f
  have hbasis := PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)
  -- `B r` is the distinguished open `D(r)` typed as an open of `Spec R`.
  let B : R → (Spec R).Opens := fun r => PrimeSpectrum.basicOpen r
  -- Index type: basic opens contained in `Uf ⊓ W a`, carrying the witness `a`.
  let I := {p : R × α // B p.1 ≤ Uf ⊓ W p.2}
  let cover : I → Set ↥(Spec R) := fun p => (B p.1.1 : Set ↥(Spec R))
  have hopen : ∀ i, IsOpen (cover i) := fun i => (B i.1.1).isOpen
  -- The chosen basic opens cover `Uf`.
  have hsub : (Uf : Set ↥(Spec R)) ⊆ ⋃ i, cover i := by
    intro x hx
    have hxUf : x ∈ Uf := hx
    obtain ⟨a, hxa⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hxUf)
    have hxinf : x ∈ ((Uf ⊓ W a : (Spec R).Opens) : Set ↥(Spec R)) := by
      rw [TopologicalSpace.Opens.coe_inf]
      exact ⟨hxUf, hxa⟩
    obtain ⟨v, hvrange, hxv, hvsub⟩ :=
      hbasis.exists_subset_of_mem_open hxinf (Uf ⊓ W a).isOpen
    obtain ⟨r, hr⟩ := hvrange
    have hr' : (B r : Set ↥(Spec R)) = v := hr
    have hle : B r ≤ Uf ⊓ W a := by
      rw [← SetLike.coe_subset_coe, hr']; exact hvsub
    refine Set.mem_iUnion.mpr ⟨⟨(r, a), hle⟩, ?_⟩
    change x ∈ (B r : Set ↥(Spec R))
    rw [hr']; exact hxv
  -- Quasi-compactness: extract a finite subcover.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover cover hopen hsub
  -- Repackage the finite index set `t : Finset I` as `Fin n`.
  let e := t.equivFin
  refine ⟨t.card, fun i => (e.symm i).1.1.1, fun i => (e.symm i).1.1.2, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
      rw [TopologicalSpace.Opens.mem_iSup]
      refine ⟨e ⟨i, hit⟩, ?_⟩
      change x ∈ B (e.symm (e ⟨i, hit⟩)).1.1.1
      rw [Equiv.symm_apply_apply]; exact hxi
    · rw [iSup_le_iff]
      intro i
      exact le_trans (e.symm i).1.2 inf_le_left
  · intro i
    exact le_trans (e.symm i).1.2 inf_le_right

/-! ## Project-local Mathlib supplement — section surjectivity for the affine cover system -/

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The local-lift assembly unfolds the sheaf-to-presheaf map and finite-cover restrictions;
-- this exceeds the default kernel reduction budget.
/-- **Section surjectivity for the affine cover system** (Stacks 02KG, `surj_of_vanishing` field;
Stacks `lemma-ses-cech-h1`). Let `S : 0 → S₁ → S₂ → S₃ → 0` be a short exact sequence of
`O_X`-modules on `Spec R` whose left term `S₁` has vanishing positive Čech cohomology over every
standard cover `i ↦ D(gᵢ)` (`hvanish`). Then the section map `S₂(D f) → S₃(D f)` is surjective over
every distinguished open `D f`. This discharges the `surj_of_vanishing` field of
`affineCoverSystem`.

Proof: `S.g` is an epi of `O_X`-modules, so (via `toSheaf_preservesEpimorphisms` + the sheaf
local-surjectivity criterion) the underlying map of abelian presheaves is locally surjective. A
section `t ∈ S₃(D f)` therefore lifts locally on an open cover of `D f`; refine it to a standard
cover `D(gᵢ)` (`standard_cover_cofinal`) carrying local lifts, feed the cover, the lifts and the
vanishing `Ȟ¹(𝒰, S₁) = 0` to the Čech `Ȟ¹`-surjectivity criterion `ses_cech_h1`, and glue to a
global lift. Project-local: the affine instantiation of the `ses_cech_h1` criterion. -/
theorem affine_surj_of_vanishing {R : CommRingCat.{u}}
    (S : ShortComplex (Spec R).Modules) (hS : S.ShortExact)
    (hvanish : ∀ (n : ℕ) (g : Fin n → R) (f' : R),
      (PrimeSpectrum.basicOpen f' : (Spec R).Opens)
        = ⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down) →
      ∀ (q : ℕ), 0 < q →
        IsZero (cechCohomology (fun i : ULift.{u} (Fin n) => PrimeSpectrum.basicOpen (g i.down))
          ((Scheme.Modules.toPresheafOfModules (Spec R)).obj S.X₁) q))
    (f : R) :
    Function.Surjective (ConcreteCategory.hom
      (((PresheafOfModules.toPresheaf (Spec R).ringCatSheaf.obj).map
        ((Scheme.Modules.toPresheafOfModules (Spec R)).map S.g)).app
          (Opposite.op (PrimeSpectrum.basicOpen f)))) := by
  classical
  set V₀ : (Spec R).Opens := PrimeSpectrum.basicOpen f with hV₀
  set FX := (Scheme.Modules.toPresheafOfModules (Spec R)).obj S.X₁ with hFX
  set GX := (Scheme.Modules.toPresheafOfModules (Spec R)).obj S.X₂ with hGX
  set HX := (Scheme.Modules.toPresheafOfModules (Spec R)).obj S.X₃ with hHX
  set fι := (PresheafOfModules.toPresheaf (Spec R).ringCatSheaf.obj).map
    ((Scheme.Modules.toPresheafOfModules (Spec R)).map S.f) with hfι
  set gπ := (PresheafOfModules.toPresheaf (Spec R).ringCatSheaf.obj).map
    ((Scheme.Modules.toPresheafOfModules (Spec R)).map S.g) with hgπ
  -- Step 1: a module epi becomes a locally surjective map of abelian presheaves.
  haveI hgepi : Epi S.g := hS.epi_g
  have hepiTS : Epi ((SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf).map S.g) :=
    @Functor.map_epi _ _ _ _ (SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf)
      (toSheaf_preservesEpimorphisms.{u} (Spec R).ringCatSheaf) _ _ S.g hgepi
  have hls : TopCat.Presheaf.IsLocallySurjective gπ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
      ((SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf).map S.g)).mpr hepiTS
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hls
  intro t
  -- Step 2: per-point local lifts of `t`.
  have hch : ∀ p : ↥V₀, ∃ (W : (Spec R).Opens) (hWle : W ≤ V₀)
      (sl : ToType (GX.presheaf.obj (Opposite.op W))),
      ConcreteCategory.hom (gπ.app (Opposite.op W)) sl
        = ConcreteCategory.hom (HX.presheaf.map (homOfLE hWle).op) t ∧ (p : Spec R) ∈ W := by
    intro p
    obtain ⟨W, hWle, ⟨sl, hsl⟩, hmem⟩ := hls V₀ t p.1 p.2
    exact ⟨W, hWle, sl, hsl, hmem⟩
  choose W hWle sLift hsLift hmem using hch
  have hVcov : V₀ ≤ ⨆ p : ↥V₀, W p := by
    intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  -- Step 3: refine to a standard cover `D(gᵢ)`.
  obtain ⟨n, g, φ, hVeq, hgle⟩ := standard_cover_cofinal f W hVcov
  set U : ULift.{u} (Fin n) → (Spec R).Opens := fun i => PrimeSpectrum.basicOpen (g i.down) with hU
  have hUsup : ⨆ i, U i = V₀ := by
    rw [hU, hV₀, hVeq]
    exact Equiv.ulift.{u}.iSup_comp (g := fun i => PrimeSpectrum.basicOpen (g i))
  -- the restricted local lifts on the standard cover
  set sLoc : ∀ i : ULift.{u} (Fin n), ToType (GX.presheaf.obj (Opposite.op (U i))) :=
    fun i => ConcreteCategory.hom (GX.presheaf.map (homOfLE (hgle i.down)).op)
      (sLift (φ i.down)) with hsLoc
  -- the section `t` transported to `⨆ U` (`= V₀`)
  have hopV : (Opposite.op (⨆ i, U i) : (TopologicalSpace.Opens (Spec R))ᵒᵖ) = Opposite.op V₀ :=
    congrArg Opposite.op hUsup
  set s : ToType (HX.presheaf.obj (Opposite.op (⨆ i, U i))) :=
    ConcreteCategory.hom (HX.presheaf.map (eqToHom hopV.symm)) t with hs
  -- assemble the hypotheses of `ses_cech_h1`
  have hπι : ∀ (V : (TopologicalSpace.Opens ↥(Spec R))ᵒᵖ) (x : ToType (FX.presheaf.obj V)),
      ConcreteCategory.hom (gπ.app V) (ConcreteCategory.hom (fι.app V) x) = 0 := by
    intro V x
    have hz : fι ≫ gπ = 0 := by
      rw [hfι, hgπ, ← Functor.map_comp, ← Functor.map_comp, S.zero,
        Functor.map_zero, Functor.map_zero]
    have h := congrArg (fun (ψ : FX.presheaf ⟶ HX.presheaf) => ConcreteCategory.hom (ψ.app V) x) hz
    simp only [PresheafOfModules.toPresheaf_obj_coe] at h ⊢
    exact h
  have hmono : ∀ (V : (TopologicalSpace.Opens ↥(Spec R))ᵒᵖ),
      Function.Injective (ConcreteCategory.hom (fι.app V)) := by
    intro V
    haveI hpzm : (sectionsFunctor (Opposite.unop V)).PreservesZeroMorphisms := by
      unfold sectionsFunctor; infer_instance
    haveI hpfl : PreservesFiniteLimits (sectionsFunctor (Opposite.unop V)) := by
      unfold sectionsFunctor; infer_instance
    haveI : Mono S.f := hS.mono_f
    have hmonoAb : Mono (fι.app V) :=
      inferInstanceAs (Mono ((sectionsFunctor (Opposite.unop V)).map S.f))
    rwa [AddCommGrpCat.mono_iff_injective] at hmonoAb
  have hker : ∀ (V : (TopologicalSpace.Opens ↥(Spec R))ᵒᵖ) (x : ToType (GX.presheaf.obj V)),
      ConcreteCategory.hom (gπ.app V) x = 0 → ∃ y, ConcreteCategory.hom (fι.app V) y = x := by
    intro V x hx
    haveI hpzm : (sectionsFunctor (Opposite.unop V)).PreservesZeroMorphisms := by
      unfold sectionsFunctor; infer_instance
    haveI hpfl : PreservesFiniteLimits (sectionsFunctor (Opposite.unop V)) := by
      unfold sectionsFunctor; infer_instance
    have hex : (S.map (sectionsFunctor (Opposite.unop V))).Exact :=
      ShortComplex.Exact.map_of_mono_of_preservesKernel hS.exact
        (sectionsFunctor (Opposite.unop V)) hS.mono_f inferInstance
    rw [ShortComplex.ab_exact_iff_function_exact] at hex
    exact (hex x).mp hx
  -- the vanishing input, packaged as homology of the section Čech complex
  have hcovf : (PrimeSpectrum.basicOpen f : (Spec R).Opens)
      = ⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down) := by
    rw [hVeq]
    exact (Equiv.ulift.{u}.iSup_comp (g := fun i => PrimeSpectrum.basicOpen (g i))).symm
  have hH1 : IsZero ((sectionCechComplex U FX).homology 1) := hvanish n g f hcovf 1 one_pos
  -- the local-lift compatibility `gπ(sLocᵢ) = s |_ Uᵢ`
  have hlift : ∀ i, ConcreteCategory.hom (gπ.app (Opposite.op (U i))) (sLoc i)
      = ConcreteCategory.hom (HX.presheaf.map (TopologicalSpace.Opens.leSupr U i).op) s := by
    intro i
    simp only [hsLoc, hs]
    erw [gπ.naturality_apply (homOfLE (hgle i.down)).op (sLift (φ i.down)), hsLift (φ i.down)]
    change ConcreteCategory.hom (HX.presheaf.map (homOfLE (hgle i.down)).op)
        (ConcreteCategory.hom (HX.presheaf.map (homOfLE (hWle (φ i.down))).op) t)
      = ConcreteCategory.hom (HX.presheaf.map (TopologicalSpace.Opens.leSupr U i).op)
        (ConcreteCategory.hom (HX.presheaf.map (eqToHom hopV.symm)) t)
    have hmaps : HX.presheaf.map (homOfLE (hWle (φ i.down))).op
          ≫ HX.presheaf.map (homOfLE (hgle i.down)).op
        = HX.presheaf.map (eqToHom hopV.symm)
          ≫ HX.presheaf.map (TopologicalSpace.Opens.leSupr U i).op := by
      rw [← HX.presheaf.map_comp, ← HX.presheaf.map_comp]
      congr 1
    simp only [← ConcreteCategory.comp_apply]
    rw [← hmaps]
  -- apply the Čech surjectivity criterion
  obtain ⟨glob, hglob⟩ := ses_cech_h1 U FX GX HX fι gπ S.X₂.isSheaf S.X₃.isSheaf
    hπι hmono hker s hH1 sLoc hlift
  -- transport the global lift back to `V₀`
  refine ⟨ConcreteCategory.hom (GX.presheaf.map (eqToHom hopV)) glob, ?_⟩
  erw [gπ.naturality_apply (eqToHom hopV) glob, hglob]
  change ConcreteCategory.hom (HX.presheaf.map (eqToHom hopV))
      (ConcreteCategory.hom (HX.presheaf.map (eqToHom hopV.symm)) t) = t
  rw [← ConcreteCategory.comp_apply, ← HX.presheaf.map_comp]
  simp only [eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

/-! ## Project-local Mathlib supplement — the affine cover system (Stacks 02KG) -/

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- The cover-system structure literal elaborates three large fields at once; the default
-- kernel reduction budget is insufficient for their presheaf and finite-cover transports.
/-- **The affine cover system** (Stacks 02KG, `def:affine_cover_system`). For `X = Spec R`, the
basis `B` is the distinguished opens `D f` (`f : R`) and the admissible coverings `Cov` are the
standard finite covers `i ↦ D(gᵢ)` (indexed by `ULift (Fin n)`, so as to land in `Type u`).
The three nontrivial fields are discharged by:
- `faces_mem` ← `affine_faces_mem` (finite intersections of distinguished opens are distinguished);
- `surj_of_vanishing` ← `affine_surj_of_vanishing` (the `ses_cech_h1` section-surjectivity
  criterion);
- `injective_acyclic` ← `injective_cech_acyclicFam` (cover-agnostic injective Čech-acyclicity,
  applied directly to the distinguished opens of each standard cover — no `Spec R_f` restriction
  detour).
Project-local: the affine instantiation of `BasisCovSystem` consumed by
`cech_eq_cohomology_of_basis`. -/
noncomputable def affineCoverSystem (R : CommRingCat.{u}) : BasisCovSystem (Spec R) where
  B := Set.range (fun f : R => (PrimeSpectrum.basicOpen f : (Spec R).Opens))
  Cov := { c : CovDatum (Spec R) | ∃ (n : ℕ) (g : Fin n → R) (f : R),
    c = ⟨ULift.{u} (Fin n), fun i => PrimeSpectrum.basicOpen (g i.down)⟩ ∧
    (PrimeSpectrum.basicOpen f : (Spec R).Opens)
      = ⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down) }
  faces_mem := by
    rintro c ⟨n, g, f, rfl, hcov⟩ p σ
    exact affine_faces_mem (fun j : ULift.{u} (Fin n) => g j.down) σ
  surj_of_vanishing := by
    rintro S hSE hvanish V ⟨f, rfl⟩
    refine affine_surj_of_vanishing S hSE (fun n g f' hcov q hq => ?_) f
    exact hvanish ⟨ULift.{u} (Fin n), fun i => PrimeSpectrum.basicOpen (g i.down)⟩
      ⟨n, g, f', rfl, hcov⟩ q hq
  injective_acyclic := by
    rintro I hI c ⟨n, g, f, rfl, hcov⟩ q hq
    haveI : Injective I := hI
    have hfam := injective_cech_acyclicFam
      (U := fun i : ULift.{u} (Fin n) => PrimeSpectrum.basicOpen (g i.down)) I q hq
    exact hfam

/-! ## Project-local Mathlib supplement — base change of the cover spanning condition -/

/-- **A standard cover of `D(f)` spans the unit ideal of `R_f`.** If the distinguished opens
`D(gᵢ)` cover `D(f)` in `Spec R`, then the images `gᵢ ↦ R_f` of the cover family span the whole
ring `R_f = Localization.Away f`: pulled back along `Spec R_f ≅ D(f) ↪ Spec R` the union of the
`D(gᵢ)` becomes `D(f)` itself, which is all of `Spec R_f` since `f` is a unit there. Project-local:
the spanning hypothesis required to apply the standard-cover tilde {\v C}ech vanishing
`sectionCech_affine_vanishing` over `R_f` in the quasi-coherent seed's change-of-base leaf. -/
theorem affine_cover_span_localizationAway {R : CommRingCat.{u}} {ι : Type u} [Finite ι]
    (g : ι → R) (f : R)
    (hcov : (PrimeSpectrum.basicOpen f : (Spec R).Opens)
      = ⨆ i, PrimeSpectrum.basicOpen (g i)) :
    Ideal.span (Set.range (fun i => algebraMap R (Localization.Away f) (g i))) = ⊤ := by
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
  simp only [← PrimeSpectrum.comap_basicOpen]
  rw [← map_iSup, ← hcov, PrimeSpectrum.comap_basicOpen, eq_top_iff]
  rintro p -
  rw [PrimeSpectrum.mem_basicOpen]
  exact fun hmem => p.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hmem (IsLocalization.Away.algebraMap_isUnit f))

/-! ## Project-local Mathlib supplement — Čech cohomology transports along isomorphisms -/

/-- **{\v C}ech cohomology transports along an isomorphism of coefficient presheaves.** An
isomorphism `e : F ≅ G` of presheaves of `𝒪_X`-modules induces an isomorphism of section {\v C}ech
complexes (`sectionCechComplexFunctor`), hence of their degree-`p` homologies; so vanishing of
`Ȟᵖ(𝒰, F)` transfers to `Ȟᵖ(𝒰, G)`. Project-local: the naturality used to reduce the
quasi-coherent {\v C}ech-vanishing seed to the tilde case via `F ≅ ~(ΓF)`. -/
theorem cechCohomology_isZero_of_iso {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    {F G : X.PresheafOfModules} (e : F ≅ G) (p : ℕ)
    (h : IsZero (cechCohomology U F p)) : IsZero (cechCohomology U G p) :=
  h.of_iso ((HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℕ) p).mapIso
    ((sectionCechComplexFunctor U).mapIso e)).symm

/-! ## Project-local Mathlib supplement — quasi-coherent {\v C}ech-vanishing seed (reduction) -/

/-- **Reduction of the quasi-coherent {\v C}ech-vanishing seed to the tilde case.**  For a
quasi-coherent `𝒪_{Spec R}`-module `F`, the affine structure theorem `qcoh_iso_tilde_sections`
gives `F ≅ ~M` with `M = Γ(Spec R, F)`; transporting along this isomorphism
(`cechCohomology_isZero_of_iso`) reduces the seed `HasVanishingHigherCech (affineCoverSystem R) F`
to the tilde-case standard-cover {\v C}ech vanishing supplied in `htilde`.  Project-local: isolates
the single remaining geometric obligation (positive-degree {\v C}ech vanishing of `~M` over a
standard cover of a distinguished open `D(f)`), which is the change-of-base-to-`R_f` leaf. -/
theorem affine_cech_vanishing_qcoh_of_tildeVanishing {R : CommRingCat.{u}}
    (F : (Spec R).Modules) [F.IsQuasicoherent]
    (htilde : ∀ (n : ℕ) (g : Fin n → R) (f : R),
        (PrimeSpectrum.basicOpen f : (Spec R).Opens)
          = ⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down) →
        ∀ p, 0 < p →
          IsZero (cechCohomology
            (fun i : ULift.{u} (Fin n) => PrimeSpectrum.basicOpen (g i.down))
            ((Scheme.Modules.toPresheafOfModules (Spec R)).obj
              (tilde (moduleSpecΓFunctor.obj F))) p)) :
    HasVanishingHigherCech (affineCoverSystem R) F := by
  intro c hc p hp
  obtain ⟨n, g, f, rfl, hcov⟩ := hc
  refine cechCohomology_isZero_of_iso _
    ((Scheme.Modules.toPresheafOfModules (Spec R)).mapIso
      (qcoh_iso_tilde_sections F).symm) p ?_
  exact htilde n g f hcov p hp

/-! ## Project-local Mathlib supplement — Serre vanishing on affines (assembly reduction) -/

/-- **Serre vanishing on affines, reduced to the tilde {\v C}ech-vanishing leaf** (Stacks 02KG).
Instantiates the basis-comparison criterion `cech_eq_cohomology_of_basis` (01EO) at the affine
cover system `affineCoverSystem R`, taking the whole affine `⊤ = D(1)` for the basic open: the
absolute cohomology `Hᵖ(Spec R, F) = Extᵖ(jShriekOU ⊤, F)` of a quasi-coherent `F` vanishes for
`p > 0`, modulo the standard-cover tilde {\v C}ech vanishing `htilde`.  Carries
`[EnoughInjectives (Spec R).Modules]` exactly as `cech_eq_cohomology_of_basis` does.
Project-local: verifies the full Lane-1 assembly end-to-end, so that the blueprint targets
`affine_cech_vanishing_qcoh`
and `affine_serre_vanishing` both reduce to the single residual `htilde` (the change-of-base to
`R_f` leaf). -/
theorem affine_serre_vanishing_of_tildeVanishing {R : CommRingCat.{u}}
    [EnoughInjectives (Spec R).Modules] (F : (Spec R).Modules) [F.IsQuasicoherent]
    (htilde : ∀ (n : ℕ) (g : Fin n → R) (f : R),
        (PrimeSpectrum.basicOpen f : (Spec R).Opens)
          = ⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down) →
        ∀ p, 0 < p →
          IsZero (cechCohomology
            (fun i : ULift.{u} (Fin n) => PrimeSpectrum.basicOpen (g i.down))
            ((Scheme.Modules.toPresheafOfModules (Spec R)).obj
              (tilde (moduleSpecΓFunctor.obj F))) p))
    (p : ℕ) (hp : 0 < p)
    (e : CategoryTheory.Abelian.Ext (jShriekOU (⊤ : (Spec R).Opens)) F p) : e = 0 :=
  cech_eq_cohomology_of_basis (affineCoverSystem R)
    (affine_cech_vanishing_qcoh_of_tildeVanishing F htilde)
    ⊤ ⟨1, PrimeSpectrum.basicOpen_one⟩ p hp e

/-! ## Project-local Mathlib supplement — the unconditional 02KG tops -/

/-- **The standard-cover {\v C}ech vanishing residual `htilde`, discharged unconditionally.**  For a
quasi-coherent `𝒪_{Spec R}`-module `F` with global module `M = Γ(Spec R, F)`, the positive-degree
section {\v C}ech cohomology of the tilde sheaf `~M` over any standard cover `i ↦ D(gᵢ)` of a
distinguished open `D(f)` vanishes. This is exactly the hypothesis fed to the `_of_tildeVanishing`
forms, now proved by the change-of-base-to-`R_f` theorem
`sectionCech_homology_exact_of_localizationAway` (with `ι := ULift (Fin n)`, `s := g ∘ down`).
Project-local: bundles the residual leaf in the precise shape both 02KG tops consume. -/
private theorem affine_tildeVanishing {R : CommRingCat.{u}} (F : (Spec R).Modules)
    (n : ℕ) (g : Fin n → R) (f : R)
    (hcov : (PrimeSpectrum.basicOpen f : (Spec R).Opens)
      = ⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down))
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology
      (fun i : ULift.{u} (Fin n) => PrimeSpectrum.basicOpen (g i.down))
      ((Scheme.Modules.toPresheafOfModules (Spec R)).obj
        (tilde (moduleSpecΓFunctor.obj F))) p) :=
  sectionCech_homology_exact_of_localizationAway (moduleSpecΓFunctor.obj F)
    (fun i : ULift.{u} (Fin n) => g i.down) f hcov p hp

/-- **Standard-cover {\v C}ech vanishing for quasi-coherent coefficients, unconditional**
(Stacks 02KG, condition (3)). For a quasi-coherent `𝒪_{Spec R}`-module `F`, the positive-degree
{\v C}ech cohomology over every standard cover of a distinguished open vanishes:
`HasVanishingHigherCech (affineCoverSystem R) F`. Obtained by discharging the `htilde` hypothesis of
`affine_cech_vanishing_qcoh_of_tildeVanishing` with the now-proved residual
`sectionCech_homology_exact_of_localizationAway`. Project-local: the unconditional Lane-1 seed
feeding the basis-comparison criterion. -/
theorem affine_cech_vanishing_qcoh {R : CommRingCat.{u}}
    (F : (Spec R).Modules) [F.IsQuasicoherent] :
    HasVanishingHigherCech (affineCoverSystem R) F :=
  affine_cech_vanishing_qcoh_of_tildeVanishing F (affine_tildeVanishing F)

/-- **Serre vanishing on affines, unconditional** (Stacks 02KG,
`lemma-quasi-coherent-affine-cohomology-zero`). For a quasi-coherent `𝒪_{Spec R}`-module `F`, the
absolute cohomology `Hᵖ(Spec R, F) = Extᵖ(jShriekOU ⊤, F)` vanishes for all `p > 0`. Obtained by
discharging the `htilde` hypothesis of `affine_serre_vanishing_of_tildeVanishing` with the
now-proved residual `sectionCech_homology_exact_of_localizationAway`. Project-local: the Serre
vanishing top, instantiating `cech_eq_cohomology_of_basis` at `affineCoverSystem R`. -/
theorem affine_serre_vanishing {R : CommRingCat.{u}}
    [EnoughInjectives (Spec R).Modules] (F : (Spec R).Modules) [F.IsQuasicoherent]
    (p : ℕ) (hp : 0 < p)
    (e : CategoryTheory.Abelian.Ext (jShriekOU (⊤ : (Spec R).Opens)) F p) : e = 0 :=
  affine_serre_vanishing_of_tildeVanishing F (affine_tildeVanishing F) p hp e

/-! ## Project-local Mathlib supplement — general-affine-open Serre vanishing (Need #2)

The declarations below **enlarge** the affine cover system from the distinguished-open basis
`{D f}` to the basis of *all* affine opens of `Spec R`, so that the basis-comparison criterion
`cech_eq_cohomology_of_basis` yields `Ext^q(jShriekOU V, H) = 0` for any affine open `V` (not just a
distinguished `D f`), entirely inside `(Spec R).Modules` (no restriction functor). The route is the
ambient `enlarge-B` of `analogies/change-of-scheme-cohomology.md`: the only structurally new pieces
are the generalisations of `standard_cover_cofinal` and `affine_surj_of_vanishing` from `D f` to a
general affine open (swapping `PrimeSpectrum.isCompact_basicOpen` for `IsAffineOpen.isCompact`); the
`faces_mem`/`injective_acyclic` fields are unchanged (faces are distinguished ⊆ affine; injective
acyclicity is cover-agnostic). The positive-degree quasi-coherent Čech-vanishing *seed* over covers
of a general affine open is the single remaining geometric residual; it is carried as an explicit
hypothesis `hseed` (the general analogue of `affine_tildeVanishing`, needing a change-of-base to
`Γ(V)` rather than to a single `R_f`). -/

/-- **Distinguished opens of `Spec R` are affine opens.**  `D(r) ⊆ Spec R` is affine, being
isomorphic to `Spec R[1/r]` via `basicOpenIsoSpecAway`.  Project-local: places each distinguished
open into the enlarged affine-open basis, discharging `faces_mem` for `affineCoverSystemGeneral`. -/
theorem isAffineOpen_specBasicOpen {R : CommRingCat.{u}} (r : R) :
    IsAffineOpen (X := Spec R) (PrimeSpectrum.basicOpen r) :=
  IsAffine.of_isIso (basicOpenIsoSpecAway r).hom

/-- **Standard covers are cofinal among open covers of a general affine open** (Stacks 02KG,
Tag 009L), generalising `standard_cover_cofinal` from a distinguished `D(f)` to an *arbitrary affine
open* `V` of `Spec R`.  Given an arbitrary open cover `W : α → (Spec R).Opens` of `V`, there is a
finite standard subcover refining it: finitely many `g : Fin n → R` with `V = ⨆ᵢ D(gᵢ)` and each
`D(gᵢ) ≤ W (φ i)`.  The only change from `standard_cover_cofinal` is the source of
quasi-compactness: `IsAffineOpen.isCompact` in place of `PrimeSpectrum.isCompact_basicOpen`.  The
refinement step for `affine_surj_of_vanishing_affine` over a general affine open. -/
theorem standard_cover_cofinal_affine {R : CommRingCat.{u}} (V : (Spec R).Opens)
    (hV : IsAffineOpen V) {α : Type u} (W : α → (Spec R).Opens) (hcov : V ≤ ⨆ a, W a) :
    ∃ (n : ℕ) (g : Fin n → R) (φ : Fin n → α),
      V = ⨆ i, PrimeSpectrum.basicOpen (g i) ∧
      ∀ i, (PrimeSpectrum.basicOpen (g i) : (Spec R).Opens) ≤ W (φ i) := by
  classical
  have hK : IsCompact (V : Set ↥(Spec R)) := hV.isCompact
  have hbasis := PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)
  -- `B r` is the distinguished open `D(r)` typed as an open of `Spec R`.
  let B : R → (Spec R).Opens := fun r => PrimeSpectrum.basicOpen r
  -- Index type: basic opens contained in `V ⊓ W a`, carrying the witness `a`.
  let I := {p : R × α // B p.1 ≤ V ⊓ W p.2}
  let cover : I → Set ↥(Spec R) := fun p => (B p.1.1 : Set ↥(Spec R))
  have hopen : ∀ i, IsOpen (cover i) := fun i => (B i.1.1).isOpen
  -- The chosen basic opens cover `V`.
  have hsub : (V : Set ↥(Spec R)) ⊆ ⋃ i, cover i := by
    intro x hx
    have hxV : x ∈ V := hx
    obtain ⟨a, hxa⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hxV)
    have hxinf : x ∈ ((V ⊓ W a : (Spec R).Opens) : Set ↥(Spec R)) := by
      rw [TopologicalSpace.Opens.coe_inf]
      exact ⟨hxV, hxa⟩
    obtain ⟨v, hvrange, hxv, hvsub⟩ :=
      hbasis.exists_subset_of_mem_open hxinf (V ⊓ W a).isOpen
    obtain ⟨r, hr⟩ := hvrange
    have hr' : (B r : Set ↥(Spec R)) = v := hr
    have hle : B r ≤ V ⊓ W a := by
      rw [← SetLike.coe_subset_coe, hr']; exact hvsub
    refine Set.mem_iUnion.mpr ⟨⟨(r, a), hle⟩, ?_⟩
    change x ∈ (B r : Set ↥(Spec R))
    rw [hr']; exact hxv
  -- Quasi-compactness: extract a finite subcover.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover cover hopen hsub
  -- Repackage the finite index set `t : Finset I` as `Fin n`.
  let e := t.equivFin
  refine ⟨t.card, fun i => (e.symm i).1.1.1, fun i => (e.symm i).1.1.2, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨e ⟨i, hit⟩, ?_⟩
      change x ∈ B (e.symm (e ⟨i, hit⟩)).1.1.1
      rw [Equiv.symm_apply_apply]; exact hxi
    · exact iSup_le fun i => le_trans (e.symm i).1.2 inf_le_left
  · intro i
    exact le_trans (e.symm i).1.2 inf_le_right

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The `ses_cech_h1` assembly over a general affine open is heartbeat-heavy (large product
-- presheaf-section equalities); the bound matches `affine_surj_of_vanishing`.
/-- **Section surjectivity for the enlarged affine cover system** (Stacks 02KG, `surj_of_vanishing`
field, general-affine-open form), generalising `affine_surj_of_vanishing` from a distinguished `D f`
to an *arbitrary affine open* `V₀`.  Let `S : 0 → S₁ → S₂ → S₃ → 0` be short exact with `S₁` having
vanishing positive Čech cohomology over every standard cover `i ↦ D(gᵢ)` *whose union is affine*
(`hvanish`). Then the section map `S₂(V₀) → S₃(V₀)` is surjective over every affine open `V₀`.

Same proof as `affine_surj_of_vanishing`, with the quasi-compact refinement supplied by
`standard_cover_cofinal_affine` (using `IsAffineOpen.isCompact`) and the cover's affineness
(`V₀ = ⨆ D(gᵢ)`) fed to `hvanish`. Project-local: discharges the `surj_of_vanishing` field of
`affineCoverSystemGeneral`. -/
theorem affine_surj_of_vanishing_affine {R : CommRingCat.{u}}
    (S : ShortComplex (Spec R).Modules) (hS : S.ShortExact)
    (hvanish : ∀ (n : ℕ) (g : Fin n → R),
      IsAffineOpen (X := Spec R)
          (⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down)) →
      ∀ (q : ℕ), 0 < q →
        IsZero (cechCohomology (fun i : ULift.{u} (Fin n) => PrimeSpectrum.basicOpen (g i.down))
          ((Scheme.Modules.toPresheafOfModules (Spec R)).obj S.X₁) q))
    (V₀ : (Spec R).Opens) (hV₀ : IsAffineOpen V₀) :
    Function.Surjective (ConcreteCategory.hom
      (((PresheafOfModules.toPresheaf (Spec R).ringCatSheaf.obj).map
        ((Scheme.Modules.toPresheafOfModules (Spec R)).map S.g)).app
          (Opposite.op V₀))) := by
  classical
  set FX := (Scheme.Modules.toPresheafOfModules (Spec R)).obj S.X₁ with hFX
  set GX := (Scheme.Modules.toPresheafOfModules (Spec R)).obj S.X₂ with hGX
  set HX := (Scheme.Modules.toPresheafOfModules (Spec R)).obj S.X₃ with hHX
  set fι := (PresheafOfModules.toPresheaf (Spec R).ringCatSheaf.obj).map
    ((Scheme.Modules.toPresheafOfModules (Spec R)).map S.f) with hfι
  set gπ := (PresheafOfModules.toPresheaf (Spec R).ringCatSheaf.obj).map
    ((Scheme.Modules.toPresheafOfModules (Spec R)).map S.g) with hgπ
  -- Step 1: a module epi becomes a locally surjective map of abelian presheaves.
  haveI hgepi : Epi S.g := hS.epi_g
  have hepiTS : Epi ((SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf).map S.g) :=
    @Functor.map_epi _ _ _ _ (SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf)
      (toSheaf_preservesEpimorphisms.{u} (Spec R).ringCatSheaf) _ _ S.g hgepi
  have hls : TopCat.Presheaf.IsLocallySurjective gπ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
      ((SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf).map S.g)).mpr hepiTS
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hls
  intro t
  -- Step 2: per-point local lifts of `t`.
  have hch : ∀ p : ↥V₀, ∃ (W : (Spec R).Opens) (hWle : W ≤ V₀)
      (sl : ToType (GX.presheaf.obj (Opposite.op W))),
      ConcreteCategory.hom (gπ.app (Opposite.op W)) sl
        = ConcreteCategory.hom (HX.presheaf.map (homOfLE hWle).op) t ∧ (p : Spec R) ∈ W := by
    intro p
    obtain ⟨W, hWle, ⟨sl, hsl⟩, hmem⟩ := hls V₀ t p.1 p.2
    exact ⟨W, hWle, sl, hsl, hmem⟩
  choose W hWle sLift hsLift hmem using hch
  have hVcov : V₀ ≤ ⨆ p : ↥V₀, W p := by
    intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  -- Step 3: refine to a standard cover `D(gᵢ)` of the affine open `V₀`.
  obtain ⟨n, g, φ, hVeq, hgle⟩ := standard_cover_cofinal_affine V₀ hV₀ W hVcov
  set U : ULift.{u} (Fin n) → (Spec R).Opens := fun i => PrimeSpectrum.basicOpen (g i.down) with hU
  have hUsup : ⨆ i, U i = V₀ := by
    rw [hU, hVeq]
    exact Equiv.ulift.{u}.iSup_comp (g := fun i => PrimeSpectrum.basicOpen (g i))
  -- the cover's union is affine (it equals `V₀`), so it is an admissible covering.
  have haff : IsAffineOpen (X := Spec R)
      (⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down)) := hUsup ▸ hV₀
  -- the restricted local lifts on the standard cover
  set sLoc : ∀ i : ULift.{u} (Fin n), ToType (GX.presheaf.obj (Opposite.op (U i))) :=
    fun i => ConcreteCategory.hom (GX.presheaf.map (homOfLE (hgle i.down)).op)
      (sLift (φ i.down)) with hsLoc
  -- the section `t` transported to `⨆ U` (`= V₀`)
  have hopV : (Opposite.op (⨆ i, U i) : (TopologicalSpace.Opens (Spec R))ᵒᵖ) = Opposite.op V₀ :=
    congrArg Opposite.op hUsup
  set s : ToType (HX.presheaf.obj (Opposite.op (⨆ i, U i))) :=
    ConcreteCategory.hom (HX.presheaf.map (eqToHom hopV.symm)) t with hs
  -- assemble the hypotheses of `ses_cech_h1`
  have hπι : ∀ (V : (TopologicalSpace.Opens ↥(Spec R))ᵒᵖ) (x : ToType (FX.presheaf.obj V)),
      ConcreteCategory.hom (gπ.app V) (ConcreteCategory.hom (fι.app V) x) = 0 := by
    intro V x
    have hz : fι ≫ gπ = 0 := by
      rw [hfι, hgπ, ← Functor.map_comp, ← Functor.map_comp, S.zero,
        Functor.map_zero, Functor.map_zero]
    have h := congrArg (fun (ψ : FX.presheaf ⟶ HX.presheaf) => ConcreteCategory.hom (ψ.app V) x) hz
    simp only [PresheafOfModules.toPresheaf_obj_coe] at h ⊢
    exact h
  have hmono : ∀ (V : (TopologicalSpace.Opens ↥(Spec R))ᵒᵖ),
      Function.Injective (ConcreteCategory.hom (fι.app V)) := by
    intro V
    haveI hpzm : (sectionsFunctor (Opposite.unop V)).PreservesZeroMorphisms := by
      unfold sectionsFunctor; infer_instance
    haveI hpfl : PreservesFiniteLimits (sectionsFunctor (Opposite.unop V)) := by
      unfold sectionsFunctor; infer_instance
    haveI : Mono S.f := hS.mono_f
    have hmonoAb : Mono (fι.app V) :=
      inferInstanceAs (Mono ((sectionsFunctor (Opposite.unop V)).map S.f))
    rwa [AddCommGrpCat.mono_iff_injective] at hmonoAb
  have hker : ∀ (V : (TopologicalSpace.Opens ↥(Spec R))ᵒᵖ) (x : ToType (GX.presheaf.obj V)),
      ConcreteCategory.hom (gπ.app V) x = 0 → ∃ y, ConcreteCategory.hom (fι.app V) y = x := by
    intro V x hx
    haveI hpzm : (sectionsFunctor (Opposite.unop V)).PreservesZeroMorphisms := by
      unfold sectionsFunctor; infer_instance
    haveI hpfl : PreservesFiniteLimits (sectionsFunctor (Opposite.unop V)) := by
      unfold sectionsFunctor; infer_instance
    have hex : (S.map (sectionsFunctor (Opposite.unop V))).Exact :=
      ShortComplex.Exact.map_of_mono_of_preservesKernel hS.exact
        (sectionsFunctor (Opposite.unop V)) hS.mono_f inferInstance
    rw [ShortComplex.ab_exact_iff_function_exact] at hex
    exact (hex x).mp hx
  -- the vanishing input, packaged as homology of the section Čech complex
  have hH1 : IsZero ((sectionCechComplex U FX).homology 1) := hvanish n g haff 1 one_pos
  -- the local-lift compatibility `gπ(sLocᵢ) = s |_ Uᵢ`
  have hlift : ∀ i, ConcreteCategory.hom (gπ.app (Opposite.op (U i))) (sLoc i)
      = ConcreteCategory.hom (HX.presheaf.map (TopologicalSpace.Opens.leSupr U i).op) s := by
    intro i
    simp only [hsLoc, hs]
    erw [gπ.naturality_apply (homOfLE (hgle i.down)).op (sLift (φ i.down)), hsLift (φ i.down)]
    change ConcreteCategory.hom (HX.presheaf.map (homOfLE (hgle i.down)).op)
        (ConcreteCategory.hom (HX.presheaf.map (homOfLE (hWle (φ i.down))).op) t)
      = ConcreteCategory.hom (HX.presheaf.map (TopologicalSpace.Opens.leSupr U i).op)
        (ConcreteCategory.hom (HX.presheaf.map (eqToHom hopV.symm)) t)
    have hmaps : HX.presheaf.map (homOfLE (hWle (φ i.down))).op
          ≫ HX.presheaf.map (homOfLE (hgle i.down)).op
        = HX.presheaf.map (eqToHom hopV.symm)
          ≫ HX.presheaf.map (TopologicalSpace.Opens.leSupr U i).op := by
      rw [← HX.presheaf.map_comp, ← HX.presheaf.map_comp]
      congr 1
    simp only [← ConcreteCategory.comp_apply]
    rw [← hmaps]
  -- apply the Čech surjectivity criterion
  obtain ⟨glob, hglob⟩ := ses_cech_h1 U FX GX HX fι gπ S.X₂.isSheaf S.X₃.isSheaf
    hπι hmono hker s hH1 sLoc hlift
  -- transport the global lift back to `V₀`
  refine ⟨ConcreteCategory.hom (GX.presheaf.map (eqToHom hopV)) glob, ?_⟩
  erw [gπ.naturality_apply (eqToHom hopV) glob, hglob]
  change ConcreteCategory.hom (HX.presheaf.map (eqToHom hopV))
      (ConcreteCategory.hom (HX.presheaf.map (eqToHom hopV.symm)) t) = t
  rw [← ConcreteCategory.comp_apply, ← HX.presheaf.map_comp]
  simp only [eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

/-! ## Project-local Mathlib supplement — the enlarged affine cover system -/

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- The structure literal forces three nontrivial field elaborations (`faces_mem`,
-- `surj_of_vanishing`, `injective_acyclic`), each unfolding large presheaf data.
/-- **The enlarged affine cover system** (Stacks 02KG), with basis `B` the *all affine opens* of
`Spec R` (rather than only the distinguished `D f` of `affineCoverSystem`) and admissible coverings
`Cov` the standard finite covers `i ↦ D(gᵢ)` whose union `⨆ᵢ D(gᵢ)` is affine.  The three fields:
- `faces_mem` ← faces `⨅ₖ D(g_{σk}) = D(∏ g)` are distinguished, hence affine
  (`isAffineOpen_specBasicOpen`);
- `surj_of_vanishing` ← `affine_surj_of_vanishing_affine` (general-affine-open surjectivity);
- `injective_acyclic` ← `injective_cech_acyclicFam` (cover-agnostic injective Čech-acyclicity).
Project-local: the enlarged instantiation of `BasisCovSystem` consumed by
`cech_eq_cohomology_of_basis` to obtain general-affine-open Serre vanishing. -/
noncomputable def affineCoverSystemGeneral (R : CommRingCat.{u}) : BasisCovSystem (Spec R) where
  B := { U : (Spec R).Opens | IsAffineOpen U }
  Cov := { c : CovDatum (Spec R) | ∃ (n : ℕ) (g : Fin n → R),
    c = ⟨ULift.{u} (Fin n), fun i => PrimeSpectrum.basicOpen (g i.down)⟩ ∧
    IsAffineOpen (X := Spec R)
      (⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down)) }
  faces_mem := by
    rintro c ⟨n, g, rfl, hcov⟩ p σ
    have h := basicOpen_sprod (p + 1) (fun j : ULift.{u} (Fin n) => g j.down) σ
    exact h ▸ isAffineOpen_specBasicOpen
      (∏ k, (fun j : ULift.{u} (Fin n) => g j.down) (σ k))
  surj_of_vanishing := by
    rintro S hSE hvanish V hV
    refine affine_surj_of_vanishing_affine S hSE (fun n g haff q hq => ?_) V hV
    exact hvanish ⟨ULift.{u} (Fin n), fun i => PrimeSpectrum.basicOpen (g i.down)⟩
      ⟨n, g, rfl, haff⟩ q hq
  injective_acyclic := by
    rintro I hI c ⟨n, g, rfl, hcov⟩ q hq
    haveI : Injective I := hI
    have hfam := injective_cech_acyclicFam
      (U := fun i : ULift.{u} (Fin n) => PrimeSpectrum.basicOpen (g i.down)) I q hq
    exact hfam

/-! ## Project-local Mathlib supplement — general-affine-open Serre vanishing (reduced to the seed)

The **residual** of the enlarged route is the positive-degree quasi-coherent Čech-vanishing *seed*
`HasVanishingHigherCech (affineCoverSystemGeneral R) F`: vanishing of `Ȟᵖ(𝒰, F)` for `p > 0` over
every standard cover `𝒰 : i ↦ D(gᵢ)` *whose union `⨆ᵢ D(gᵢ)` is affine* (not just a distinguished
`D(f)`). Unlike the distinguished case — discharged by
`sectionCech_homology_exact_of_localizationAway` via change of base to a single
`Rf = Localization.Away f` — a general affine open `V = ⨆ᵢ D(gᵢ)` has no single `f` with `V = D(f)`,
so the seed needs a change of base to `Γ(V, 𝒪)` (equivalently, the identification of the section
Čech complex over `{D(gᵢ) ⊆ Spec R}` with the standard-cover complex of `~(Γ(V,F))` over
`Spec Γ(V)` under `V ≅ Spec Γ(V)`). That change-of-scheme identification is the lone remaining
geometric leaf; it is isolated here as the explicit hypothesis `hseed`. -/

/-- **Reduction of the general-affine-open quasi-coherent seed to the tilde case.**  For a
quasi-coherent `𝒪_{Spec R}`-module `F`, transporting along `F ≅ ~M` (`qcoh_iso_tilde_sections`,
`M = Γ(Spec R, F)`) reduces the seed `HasVanishingHigherCech (affineCoverSystemGeneral R) F` to the
tilde-case positive-degree Čech vanishing `htilde`: vanishing of `Ȟᵖ(𝒰, ~M)` over every standard
cover `i ↦ D(gᵢ)` whose union is affine.  Verbatim analogue of
`affine_cech_vanishing_qcoh_of_tildeVanishing` for the enlarged cover system; isolates the single
geometric residual (the change-of-base-to-`Γ(V)` tilde-section identification).  Project-local: the
cleanest statement of the general-affine-open seed residual. -/
theorem affine_cech_vanishing_qcoh_general_of_tildeVanishing {R : CommRingCat.{u}}
    (F : (Spec R).Modules) [F.IsQuasicoherent]
    (htilde : ∀ (n : ℕ) (g : Fin n → R),
        IsAffineOpen (X := Spec R)
            (⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down)) →
        ∀ p, 0 < p →
          IsZero (cechCohomology
            (fun i : ULift.{u} (Fin n) => PrimeSpectrum.basicOpen (g i.down))
            ((Scheme.Modules.toPresheafOfModules (Spec R)).obj
              (tilde (moduleSpecΓFunctor.obj F))) p)) :
    HasVanishingHigherCech (affineCoverSystemGeneral R) F := by
  intro c hc p hp
  obtain ⟨n, g, rfl, hcov⟩ := hc
  refine cechCohomology_isZero_of_iso _
    ((Scheme.Modules.toPresheafOfModules (Spec R)).mapIso
      (qcoh_iso_tilde_sections F).symm) p ?_
  exact htilde n g hcov p hp

/-- **Serre vanishing for a general affine open, reduced to the Čech-vanishing seed** (Stacks 02KG,
generalised from `D(f)` to an arbitrary affine open).  For a quasi-coherent `𝒪_{Spec R}`-module `F`
and **any** affine open `V` of `Spec R`, the absolute cohomology `Hᵖ(V, F) = Extᵖ(jShriekOU V, F)`
vanishes for `p > 0`, modulo the general-affine-open Čech-vanishing seed `hseed`.  Instantiates the
basis-comparison criterion `cech_eq_cohomology_of_basis` at the enlarged cover system
`affineCoverSystemGeneral R` (whose basis is all affine opens).  Project-local: the Need #2 target
of `analogies/change-of-scheme-cohomology.md`, isolating the single seed residual. -/
theorem affine_serre_vanishing_general_of_seed {R : CommRingCat.{u}}
    [EnoughInjectives (Spec R).Modules] (F : (Spec R).Modules) [F.IsQuasicoherent]
    (hseed : HasVanishingHigherCech (affineCoverSystemGeneral R) F)
    (V : (Spec R).Opens) (hV : IsAffineOpen V) (p : ℕ) (hp : 0 < p)
    (e : CategoryTheory.Abelian.Ext (jShriekOU V) F p) : e = 0 :=
  cech_eq_cohomology_of_basis (affineCoverSystemGeneral R) hseed V hV p hp e

/-- **Serre vanishing for a general affine open, reduced to the tilde Čech-vanishing leaf**
(Stacks 02KG, generalised).  Composes `affine_cech_vanishing_qcoh_general_of_tildeVanishing` (seed
from tilde vanishing) with `affine_serre_vanishing_general_of_seed`: for quasi-coherent `F` and any
affine open `V`, `Extᵖ(jShriekOU V, F) = 0` for `p > 0`, modulo the tilde-section change-of-base
leaf `htilde`.  Project-local: the fully-reduced Need #2 top, leaving exactly the change-of-scheme
tilde residual. -/
theorem affine_serre_vanishing_general_of_tildeVanishing {R : CommRingCat.{u}}
    [EnoughInjectives (Spec R).Modules] (F : (Spec R).Modules) [F.IsQuasicoherent]
    (htilde : ∀ (n : ℕ) (g : Fin n → R),
        IsAffineOpen (X := Spec R)
            (⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down)) →
        ∀ p, 0 < p →
          IsZero (cechCohomology
            (fun i : ULift.{u} (Fin n) => PrimeSpectrum.basicOpen (g i.down))
            ((Scheme.Modules.toPresheafOfModules (Spec R)).obj
              (tilde (moduleSpecΓFunctor.obj F))) p))
    (V : (Spec R).Opens) (hV : IsAffineOpen V) (p : ℕ) (hp : 0 < p)
    (e : CategoryTheory.Abelian.Ext (jShriekOU V) F p) : e = 0 :=
  affine_serre_vanishing_general_of_seed F
    (affine_cech_vanishing_qcoh_general_of_tildeVanishing F htilde) V hV p hp e

/-! ## Project-local Mathlib supplement — the unconditional general-affine 02KG tops (Need #2) -/

/-- **The general-affine standard-cover {\v C}ech vanishing residual, discharged unconditionally.**
The general-affine analogue of `affine_tildeVanishing`: for a quasi-coherent `𝒪_{Spec R}`-module `F`
with global module `M = Γ(Spec R, F)`, the positive-degree section {\v C}ech cohomology of the tilde
sheaf `~M` over any standard cover `i ↦ D(gᵢ)` *whose union is an affine open* vanishes. Proved by
the now-built change-of-base-to-`Γ(V)` theorem `sectionCech_homology_exact_of_affineOpen` (route B1,
base change to `S = Γ(V)`), with `s := g ∘ down`, replacing the single-`R_f` change of base of
`affine_tildeVanishing`. Project-local: bundles the residual leaf in the precise shape the general
`_of_tildeVanishing` forms consume. -/
private theorem affine_tildeVanishing_general {R : CommRingCat.{u}} (F : (Spec R).Modules)
    (n : ℕ) (g : Fin n → R)
    (haff : IsAffineOpen (X := Spec R)
      (⨆ i : ULift.{u} (Fin n), PrimeSpectrum.basicOpen (g i.down)))
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology
      (fun i : ULift.{u} (Fin n) => PrimeSpectrum.basicOpen (g i.down))
      ((Scheme.Modules.toPresheafOfModules (Spec R)).obj
        (tilde (moduleSpecΓFunctor.obj F))) p) :=
  sectionCech_homology_exact_of_affineOpen (moduleSpecΓFunctor.obj F)
    (fun i : ULift.{u} (Fin n) => g i.down) haff p hp

/-- **Serre vanishing for a general affine open, unconditional** (Stacks 02KG, generalised from
`D(f)` to an arbitrary affine open; closes Need #2). For a quasi-coherent `𝒪_{Spec R}`-module `F`
and **any** affine open `V` of `Spec R`, the absolute cohomology `Hᵖ(V, F) = Extᵖ(jShriekOU V, F)`
vanishes for `p > 0`. Obtained by discharging the tilde-{\v C}ech-vanishing leaf `htilde` of
`affine_serre_vanishing_general_of_tildeVanishing` with the now-proved residual
`affine_tildeVanishing_general` (in turn `sectionCech_homology_exact_of_affineOpen`). Project-local:
the general-affine 02KG top, discharging the Need #2 general-affine cone end-to-end. -/
theorem affine_serre_vanishing_general_open {R : CommRingCat.{u}}
    [EnoughInjectives (Spec R).Modules] (F : (Spec R).Modules) [F.IsQuasicoherent]
    (V : (Spec R).Opens) (hV : IsAffineOpen V) (p : ℕ) (hp : 0 < p)
    (e : CategoryTheory.Abelian.Ext (jShriekOU V) F p) : e = 0 :=
  affine_serre_vanishing_general_of_tildeVanishing F
    (affine_tildeVanishing_general F) V hV p hp e

end AlgebraicGeometry
