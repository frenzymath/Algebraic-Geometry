/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.RigidPushforward
import AlgebraicJacobian.Picard.QuotScheme
import AlgebraicJacobian.Picard.ChartSectionsFinite
import AlgebraicJacobian.Picard.GenericFlatnessGeometric
import AlgebraicJacobian.Picard.InvertibleGrBridge
import AlgebraicJacobian.Picard.PullbackFinitePresentation
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.QuasicoherentDegreeOneVanishing

/-!
# B3 transfer package — discharging the named hypotheses of the ℙ¹ reduction

`Picard/RigidPushforward.lean` reduces B3 local freeness for the constant
curve `C_A` to the ℙ¹ engine plus a *finite-pushforward transfer package*
along the finite map `π_A : C_A ⟶ ℙ¹_A` (`rigidPushforwardLocallyFree_of_p1`,
hypotheses `hfp`/`hflat`/`hH1`/`hH0`).  This file discharges the first two
transfer hypotheses:

* **`hfp` (Stacks 01XZ/087T flavour)** —
  `pushforward_finiteMapToP1BaseChange_isFinitePresentation`: the finite
  pushforward `(π_A)_* L` of an invertible module is finitely presented.
  The engine behind it is the general noetherian coherence criterion
  `Scheme.Modules.isFinitePresentation_of_finite_sections`: a quasi-coherent
  module on a locally noetherian scheme whose section modules over affine
  opens are finite is finitely presented.  The pushforward is quasi-coherent
  by Stacks 01XJ (`pushforward_isQuasicoherent`, proved in
  `Picard/QuotScheme.lean`), its sections over an affine `V` are
  `Γ(L, π_A⁻¹ V)` *definitionally*, and these are module-finite over
  `Γ(ℙ¹_A, V)` by composing the module-finiteness of the finite morphism
  `π_A` (Stacks 01WG) with the finiteness of the sections of the finitely
  presented `L` on the affine `π_A⁻¹ V` (Stacks 01PC,
  `finite_sections_preimage_of_isAffineHom`).  `A` is a finitely generated
  `k`-algebra, hence noetherian (Hilbert basis), hence `ℙ¹_A` is locally
  noetherian and finite section modules are finitely presented.

* **`hflat` (mixed-base flat stability)** —
  `pushforward_finiteMapToP1BaseChange_coherentSheafFlat`: `(π_A)_* L`
  stays `CoherentSheafFlat` over `Spec A`.  Since
  `Γ((π_A)_* L, V) = Γ(L, π_A⁻¹ V)` definitionally and
  `q = π_A ≫ p` (`finiteMapToP1BaseChange_snd`), the statement reduces to
  `CoherentSheafFlat q L` for the invertible `L` on the `A`-flat family
  `q : C_A ⟶ Spec A` (`coherentSheafFlat_pushforward_of_isAffineHom`).
  The latter is `coherentSheafFlat_of_isLocallyTrivial_of_flat`: on a
  trivialising affine chart `W` the section module `Γ(L, W)` is an
  invertible (hence flat) `Γ(C_A, W)`-module
  (`isInvertible_of_restrict_iso`), `Γ(C_A, W)` is flat over `A` because
  `q` is a flat morphism (base change of `C ⟶ Spec k`, and everything over
  the one-point integral `Spec k` is flat), and chart flatness globalises
  to all affine pairs by the affine-locality engine
  `flat_section_of_affine_cover` (`Picard/GenericFlatnessGeometric.lean`).

* **transfer item (c) — the fibre-compatibility isomorphism and `hH0`**
  (§6–§7): the general Stacks 02KG (`i = 0`) engine for **affine**
  morphisms and **arbitrary** (non-flat) base change
  (`isIso_pushforwardBaseChangeMap_of_isPullback`), its fibre specialization
  `fiberPushforwardCompatIso : (p.fiberι t)^* ((π_A)_* L) ≅ (π_t)_* (L_t)`,
  the verbatim `hH0` discharge
  (`pushforward_finiteMapToP1BaseChange_fiberH0`), and the `hH1` transfer
  reduced to Čech cover-independence of `Ȟ¹`-vanishing on the fibre curve
  (`fiberH1Vanishing_pushforward_finiteMapToP1BaseChange_of_coverIndependence`).

* **`hH1`** — the cover-independence obligation `hindep` is
  discharged by the QC-vanishing keystone
  (`Cohomology/StructureSheafModuleK/QuasicoherentDegreeOneVanishing.lean`:
  degree-1 affine vanishing for quasi-coherent modules + the Mayer–Vietoris
  `(0,1)`-slice on every 2-affine cover), giving the verbatim pinned `hH1`
  (`pushforward_finiteMapToP1BaseChange_fiberH1`).  All four transfer
  hypotheses being discharged, B3 local freeness for `C_A` follows from the
  ℙ¹ engine alone (`rigidPushforwardLocallyFree_of_p1Engine`).

No pinned statement is touched: this file only *produces* the named
hypotheses consumed by `rigidPushforwardLocallyFree_of_p1`.

Sources: Stacks 01XJ (pushforward quasi-coherence), 01XZ/087T (finite
pushforward of coherent is coherent), 01PC (finite sections on affines),
01WG (finite morphisms are module-finite on affines), 00HB/00HT (flatness
is affine-local), 02KG (cohomology and base change, `i = 0`); Nitsure §4;
Mumford AV II §5.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-! ## §1. Finite-module transport along a semilinear additive equivalence

The elementary bookkeeping lemma for moving `Module.Finite` across the
section comparisons of the fromSpec dictionary: a surjective-semilinear
additive equivalence transports finite generation. -/

/-- **`Module.Finite` descends along a surjective-semilinear additive
equivalence.**  If `e : M ≃+ N` intertwines the `R`-action on `M` with the
`S`-action on `N` through a surjective ring homomorphism `σ : R →+* S`
(`e (r • x) = σ r • e x`) and `N` is a finite `S`-module, then `M` is a
finite `R`-module: the preimages of a finite `S`-generating set generate
`M` over `R`, because every `S`-scalar lifts along `σ`. -/
theorem Module.Finite.of_addEquiv_semilinear {R S : Type u} [Semiring R] [Semiring S]
    {M N : Type u} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
    (σ : R →+* S) (hσ : Function.Surjective σ) (e : M ≃+ N)
    (he : ∀ (r : R) (x : M), e (r • x) = σ r • e x) (hN : Module.Finite S N) :
    Module.Finite R M := by
  obtain ⟨n, w, hw⟩ := hN.exists_fin (R := S) (M := N)
  refine Module.finite_def.mpr (Submodule.fg_def.mpr
    ⟨⇑e.symm '' Set.range w, ((Set.finite_range w).image _), ?_⟩)
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ Submodule.span S (Set.range w) := hw ▸ Submodule.mem_top
  have key : ∀ (y : N), y ∈ Submodule.span S (Set.range w) →
      e.symm y ∈ Submodule.span R (⇑e.symm '' Set.range w) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul s y hy' ih =>
      obtain ⟨r, rfl⟩ := hσ s
      have : e.symm (σ r • y) = r • e.symm y := by
        apply e.injective
        rw [he, e.apply_symm_apply, e.apply_symm_apply]
      rw [this]
      exact Submodule.smul_mem _ _ ih
  simpa using key (e x) hx

/-! ## §2. The noetherian coherence criterion (finite sections ⟹ finitely presented)

For a quasi-coherent module `N` on a locally noetherian scheme, finiteness
of the section modules over affine opens forces finite presentation: over
each affine `U` the module `N|_U` is the tilde of its (finite, hence — by
noetherianity — finitely presented) section module, and a finite module
over a noetherian ring admits a finite free presentation whose tilde is a
finite `SheafOfModules.Presentation`. -/

namespace Scheme.Modules

variable {Y : Scheme.{u}}

/-- **Section finiteness of the `fromSpec` pullback.**  For a module `N` on
`Y` and an affine open `U`, the module of global sections of the pullback
of `N` along `hU.fromSpec : Spec Γ(Y, U) ⟶ Y` is finite over `Γ(Y, U)`
(with the canonical `R`-module structure of sections over `Spec R`),
provided the sections of `N` over the image open `fromSpec ''ᵁ ⊤ (= U)`
are finite over its section ring.  Transport along the section comparison
`gammaPullbackImageIso` of the open immersion `fromSpec`, which is
semilinear over the (surjective) ring comparison
`Γ(Spec Γ(Y, U), ⊤) ≃+* Γ(Y, fromSpec ''ᵁ ⊤)` composed with the global
sections identification `ΓSpecIso`. -/
theorem module_finite_gamma_pullback_fromSpec (N : Y.Modules)
    {U : Y.Opens} (hU : IsAffineOpen U)
    (hfin : Module.Finite Γ(Y, hU.fromSpec ''ᵁ (⊤ : (Spec Γ(Y, U)).Opens))
      Γ(N, hU.fromSpec ''ᵁ (⊤ : (Spec Γ(Y, U)).Opens))) :
    Module.Finite Γ(Y, U) Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) := by
  set j := hU.fromSpec with hj
  -- the surjective ring comparison `Γ(Y, U) →+* Γ(Y, j ''ᵁ ⊤)`
  let σ : (Γ(Y, U) : Type u) →+* (Γ(Y, j ''ᵁ (⊤ : (Spec Γ(Y, U)).Opens)) : Type u) :=
    (Scheme.Modules.gammaImageRingEquiv j (⊤ : (Spec Γ(Y, U)).Opens)).toRingHom.comp
      ((Scheme.ΓSpecIso Γ(Y, U)).inv.hom)
  have hmid : (Spec Γ(Y, U)).presheaf.map
      (Opens.leTop (⊤ : (Spec Γ(Y, U)).Opens)).op = 𝟙 _ := by
    rw [show (Opens.leTop (⊤ : (Spec Γ(Y, U)).Opens)) =
      𝟙 (⊤ : (Spec Γ(Y, U)).Opens) from rfl]
    exact (Spec Γ(Y, U)).presheaf.map_id _
  have hσ : Function.Surjective σ := by
    intro z
    obtain ⟨y, hy⟩ :=
      (Scheme.Modules.gammaImageRingEquiv j (⊤ : (Spec Γ(Y, U)).Opens)).surjective z
    refine ⟨(Scheme.ΓSpecIso Γ(Y, U)).hom.hom y, ?_⟩
    change (Scheme.Modules.gammaImageRingEquiv j (⊤ : (Spec Γ(Y, U)).Opens))
      ((Scheme.ΓSpecIso Γ(Y, U)).inv.hom ((Scheme.ΓSpecIso Γ(Y, U)).hom.hom y)) = z
    have hcancel : (Scheme.ΓSpecIso Γ(Y, U)).inv.hom
        ((Scheme.ΓSpecIso Γ(Y, U)).hom.hom y) = y := by
      have h0 := (Scheme.ΓSpecIso Γ(Y, U)).hom_inv_id
      have h1 := congrArg
        (fun φ : Γ(Spec Γ(Y, U), ⊤) ⟶ Γ(Spec Γ(Y, U), ⊤) => φ.hom y) h0
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
        RingHom.id_apply] at h1
      exact h1
    rw [hcancel]
    exact hy
  -- the additive section comparison of the open immersion `j`
  let e : (Γ((Scheme.Modules.pullback j).obj N, ⊤) : Type u) ≃+
      (Γ(N, j ''ᵁ (⊤ : (Spec Γ(Y, U)).Opens)) : Type u) :=
    (Scheme.Modules.gammaPullbackImageIso j N (⊤ : (Spec Γ(Y, U)).Opens)).addCommGroupIsoToAddEquiv
  refine Module.Finite.of_addEquiv_semilinear σ hσ e (fun r x => ?_) hfin
  -- semilinearity: unfold the `R`-action on Spec sections and apply the
  -- semilinearity of the pullback-section comparison
  change (Scheme.Modules.gammaPullbackImageIso j N _).hom.hom (r • x) =
    σ r • (Scheme.Modules.gammaPullbackImageIso j N _).hom.hom x
  rw [Scheme.Modules.smul_Spec_def (M := (Scheme.Modules.pullback j).obj N) r x, hmid]
  exact Scheme.Modules.gammaPullbackImageIso_hom_semilinear j N _ _ x

set_option backward.isDefEq.respectTransparency false in
/-- **A finite module sheaf on `Spec R` (R noetherian) with invertible
tilde–Γ counit admits a finite presentation.**  Choose a finite generating
family of the global sections (`Module.Finite.exists_fin`); the kernel of
the induced surjection from the finite free module is finitely generated
because `R` is noetherian; `presentationTilde` packages the data into a
finite `SheafOfModules.Presentation` of the tilde, which transports to `F`
across the (invertible) counit `fromTildeΓ`. -/
theorem exists_finite_presentation_of_isIso_fromTildeΓ {R : CommRingCat.{u}}
    (F : (Spec R).Modules) [IsIso (Scheme.Modules.fromTildeΓ F)]
    [IsNoetherianRing (R : Type u)]
    (hfin : Module.Finite (R : Type u) Γ(F, ⊤)) :
    ∃ P : F.Presentation, P.IsFinite := by
  set M0 : ModuleCat.{u} (R : Type u) :=
    (modulesSpecToSheaf.obj F).presheaf.obj (op (⊤ : (Spec R).Opens)) with hM0
  haveI hfin0 : Module.Finite (R : Type u) M0 := hfin
  obtain ⟨n, w, hw⟩ := hfin0.exists_fin
  set s : Set M0 := Set.range w with hsdef
  haveI : Finite (↥s) := (Set.finite_range w).to_subtype
  haveI : Module.Finite (R : Type u) (↥s →₀ (R : Type u)) := by infer_instance
  haveI : _root_.IsNoetherian (R : Type u) (↥s →₀ (R : Type u)) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨T, hT⟩ := _root_.IsNoetherian.noetherian
    (Finsupp.linearCombination (R : Type u) (Subtype.val : ↥s → M0)).ker
  haveI : Finite (↥(T : Set (↥s →₀ (R : Type u)))) := T.finite_toSet.to_subtype
  let P0 : (tilde M0).Presentation :=
    presentationTilde M0 s hw (T : Set (↥s →₀ (R : Type u))) hT
  haveI hP0gen : P0.generators.IsFiniteType :=
    { finite := inferInstanceAs (Finite ↥s) }
  haveI hP0rel : P0.relations.IsFiniteType :=
    { finite := inferInstanceAs (Finite (↥(T : Set (↥s →₀ (R : Type u))))) }
  haveI hP0 : P0.IsFinite :=
    SheafOfModules.Presentation.IsFinite.mk.{u, u, u} (p := P0) hP0gen hP0rel
  let eT : tilde M0 ≅ F :=
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ F) ‹_›
  exact ⟨SheafOfModules.Presentation.ofIsIso.{u} eT.hom P0, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Heartbeat headroom for the slice-site presentation transports and their
-- `IsFinite` instance searches, as elsewhere in the QuotScheme transport layer.
set_option synthInstance.maxHeartbeats 800000 in
/-- **Per-affine finite slice presentation from finite sections** (noetherian
coherence, slice form).  For a quasi-coherent `N` on a locally noetherian
scheme `Y` with finite section modules over affine opens, every affine `U`
carries a *finite* presentation of the slice `N.over U`.  This is the
finite upgrade of `pushforward_isQuasicoherent_over_affine`'s transport
chain: identify `N|_U` with the tilde of its finite section module (gap1,
`isIso_fromTildeΓ_of_isQuasicoherent`), take the finite tilde presentation
(`exists_finite_presentation_of_isIso_fromTildeΓ`), and transport back to
the slice along `U.ι = isoSpec.hom ≫ fromSpec`
(`presentationPullbackOfSchemeIso`, `overRestrictPresentationInv`), all of
which preserve the (finite) generator/relation index types. -/
theorem exists_finite_presentation_over_of_finite_sections
    [IsLocallyNoetherian Y] (N : Y.Modules) [N.IsQuasicoherent]
    (hfin : ∀ V : Y.Opens, IsAffineOpen V → Module.Finite Γ(Y, V) Γ(N, V))
    {U : Y.Opens} (hU : IsAffineOpen U) :
    ∃ P : (N.over U).Presentation, P.IsFinite := by
  haveI := Scheme.Modules.isQuasicoherent_pullback_fromSpec N hU
  haveI hP1 : IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pullback hU.fromSpec).obj N)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _
  haveI : IsNoetherianRing Γ(Y, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have himg : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(Y, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact Opens.ext hU.range_fromSpec
  have hfinTop : Module.Finite Γ(Y, U)
      Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) :=
    module_finite_gamma_pullback_fromSpec N hU
      (hfin _ (himg.symm ▸ hU))
  obtain ⟨P_M', hPfin⟩ :=
    exists_finite_presentation_of_isIso_fromTildeΓ
      ((Scheme.Modules.pullback hU.fromSpec).obj N) hfinTop
  haveI := hPfin
  have hcomp : hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
    rw [← hU.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  haveI hmapfin : (Scheme.Modules.presentationPullbackOfSchemeIso hU.isoSpec.symm
      ((Scheme.Modules.pullback hU.fromSpec).obj N) P_M').IsFinite := by
    delta Scheme.Modules.presentationPullbackOfSchemeIso
    infer_instance
  let P_ι : ((Scheme.Modules.pullback U.ι).obj N).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u}
      ((Scheme.Modules.pullbackComp hU.isoSpec.hom hU.fromSpec).app N ≪≫
        (Scheme.Modules.pullbackCongr hcomp).app N).hom
      (Scheme.Modules.presentationPullbackOfSchemeIso hU.isoSpec.symm
        ((Scheme.Modules.pullback hU.fromSpec).obj N) P_M')
  haveI hPιfin : P_ι.IsFinite := by
    change (SheafOfModules.Presentation.ofIsIso.{u, u, u}
      ((Scheme.Modules.pullbackComp hU.isoSpec.hom hU.fromSpec).app N ≪≫
        (Scheme.Modules.pullbackCongr hcomp).app N).hom
      (Scheme.Modules.presentationPullbackOfSchemeIso hU.isoSpec.symm
        ((Scheme.Modules.pullback hU.fromSpec).obj N) P_M')).IsFinite
    infer_instance
  refine ⟨Scheme.Modules.overRestrictPresentationInv U N P_ι, ?_⟩
  delta Scheme.Modules.overRestrictPresentationInv
  infer_instance

set_option maxHeartbeats 800000 in
-- Heartbeat headroom for the slice-site `HasSheafify` synthesis triggered by
-- assembling the `QuasicoherentData`, as elsewhere in this transport layer.
set_option synthInstance.maxHeartbeats 400000 in
/-- **The noetherian coherence criterion** (finite sections ⟹ finitely
presented; Stacks 01XZ-grade bookkeeping).  A quasi-coherent sheaf of
modules on a locally noetherian scheme whose section modules over all
affine opens are finite over the respective section rings is finitely
presented: assemble the per-affine finite slice presentations
(`exists_finite_presentation_over_of_finite_sections`) over the affine
opens cover into a `QuasicoherentData` witnessing
`SheafOfModules.IsFinitePresentation`. -/
theorem isFinitePresentation_of_finite_sections
    [IsLocallyNoetherian Y] (N : Y.Modules) [N.IsQuasicoherent]
    (hfin : ∀ V : Y.Opens, IsAffineOpen V → Module.Finite Γ(Y, V) Γ(N, V)) :
    N.IsFinitePresentation := by
  have h := fun V : Y.affineOpens =>
    exists_finite_presentation_over_of_finite_sections N hfin V.2
  choose P hP using h
  let q : N.QuasicoherentData :=
    { I := Y.affineOpens
      X := fun V => V.1
      coversTop := by
        intro W y hy
        obtain ⟨V, hVaff, hyV, hVW⟩ :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y) hy
        refine ⟨V, homOfLE hVW, ?_, hyV⟩
        rw [CategoryTheory.Sieve.mem_ofObjects_iff]
        exact ⟨⟨V, hVaff⟩, ⟨𝟙 V⟩⟩
      presentation := P }
  have hsh : q.shrink.IsFinitePresentation := by
    apply SheafOfModules.QuasicoherentData.IsFinitePresentation.mk
    intro i
    exact hP _
  exact { exists_quasicoherentData := ⟨q.shrink, hsh⟩ }

end Scheme.Modules

/-! ## §3. `hfp` — the finite pushforward of a line bundle is finitely presented -/

namespace Adelic

open Scheme

variable {k : Type u} [Field k]
variable (A : Type u) [CommRing A] [Algebra k A]
variable (C : Over (Spec (CommRingCat.of k)))

set_option maxHeartbeats 800000 in
-- Heartbeat headroom for the pullback/pushforward instance synthesis on the
-- base-changed projective line, as elsewhere in the B3 lane.
set_option synthInstance.maxHeartbeats 400000 in
/-- **`hfp` for the B3 reduction (Stacks 01XZ/087T flavour): the finite
pushforward of an invertible module is finitely presented.**  For the
finite map `π_A : C_A ⟶ ℙ¹_A` (base change of the gate's finite
`C ⟶ ℙ¹`) and an invertible `L` on `C_A`, the pushforward `(π_A)_* L` is a
finitely presented module on `ℙ¹_A`, for every finitely generated
`k`-algebra `A`:

* `(π_A)_* L` is quasi-coherent (Stacks 01XJ, `pushforward_isQuasicoherent`;
  `π_A` is finite, hence affine, hence qcqs);
* `ℙ¹_A` is locally noetherian (`A` is noetherian by Hilbert basis, and
  `ℙ¹_A ⟶ Spec A` is locally of finite type as a base change of the proper
  `ℙ¹_k ⟶ Spec k`);
* over an affine `V ⊆ ℙ¹_A` the sections are `Γ(L, π_A⁻¹ V)`
  (definitionally), finite over `Γ(C_A, π_A⁻¹ V)` by Stacks 01PC
  (`finite_sections_preimage_of_isAffineHom`, using that `L` is finitely
  presented since locally trivial) and hence finite over `Γ(ℙ¹_A, V)` since
  `π_A` is module-finite on affines (Stacks 01WG, `IsFinite.finite_app`);

so the noetherian coherence criterion
(`isFinitePresentation_of_finite_sections`) applies.  This discharges the
`hfp` hypothesis of `rigidPushforwardLocallyFree_of_p1`. -/
theorem pushforward_finiteMapToP1BaseChange_isFinitePresentation
    [Algebra.FiniteType k A] [HasFiniteMapToP1 C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L) :
    ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L).IsFinitePresentation := by
  haveI := hL.isFinitePresentation
  haveI : IsFinite (finiteMapToP1BaseChange A C) := isFinite_finiteMapToP1BaseChange A C
  haveI := Scheme.Modules.pushforward_isQuasicoherent (finiteMapToP1BaseChange A C) L
  -- `ℙ¹_A` is locally noetherian
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of A)) := inferInstance
  haveI : LocallyOfFiniteType (p1Over k).hom :=
    inferInstanceAs (LocallyOfFiniteType
      ((ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))) ↘ Spec (CommRingCat.of k)))
  haveI : LocallyOfFiniteType
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
    MorphismProperty.pullback_snd _ _ ‹_›
  haveI : IsLocallyNoetherian
      (Limits.pullback (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
  -- finite sections on affines, then the coherence criterion
  apply Scheme.Modules.isFinitePresentation_of_finite_sections
  intro V hV
  letI : Algebra Γ(Limits.pullback (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A))), V)
      Γ(Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))),
        finiteMapToP1BaseChange A C ⁻¹ᵁ V) :=
    ((finiteMapToP1BaseChange A C).app V).hom.toAlgebra
  haveI h1 : Module.Finite
      Γ(Limits.pullback (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A))), V)
      Γ(Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))),
        finiteMapToP1BaseChange A C ⁻¹ᵁ V) :=
    (finiteMapToP1BaseChange A C).finite_app V hV
  haveI h2 : Module.Finite
      Γ(Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))),
        finiteMapToP1BaseChange A C ⁻¹ᵁ V)
      Γ(L, finiteMapToP1BaseChange A C ⁻¹ᵁ V) :=
    Scheme.Modules.finite_sections_preimage_of_isAffineHom
      (finiteMapToP1BaseChange A C) L hV
  letI : Module Γ(Limits.pullback (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A))), V)
      Γ(L, finiteMapToP1BaseChange A C ⁻¹ᵁ V) :=
    Module.compHom _ ((finiteMapToP1BaseChange A C).app V).hom
  haveI : IsScalarTower
      Γ(Limits.pullback (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A))), V)
      Γ(Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))),
        finiteMapToP1BaseChange A C ⁻¹ᵁ V)
      Γ(L, finiteMapToP1BaseChange A C ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite
      Γ(Limits.pullback (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A))), V)
      Γ(L, finiteMapToP1BaseChange A C ⁻¹ᵁ V) :=
    Module.Finite.trans
      Γ(Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))),
        finiteMapToP1BaseChange A C ⁻¹ᵁ V)
      Γ(L, finiteMapToP1BaseChange A C ⁻¹ᵁ V)
  exact this

end Adelic

/-! ## §4. `hflat` — coherent-sheaf flatness of the finite pushforward -/

namespace Scheme

/-- **Coherent-sheaf flatness of an invertible module over an affine base
along a flat family.**  For a flat morphism `q : Y ⟶ T` with affine target
and a locally trivial (invertible) `L` on `Y`, the module `L` is flat over
`T` in the sense of `CoherentSheafFlat`: on a trivialising affine chart `W`
the sections `Γ(L, W)` form an invertible, hence flat, `Γ(Y, W)`-module
(`isInvertible_of_restrict_iso`), which is flat over `Γ(T, ⊤)` since `q` is
a flat morphism (`Flat.flat_appLE` + `Module.Flat.trans`); chart flatness
globalises to every affine pair by the affine-locality engine
`flat_section_of_affine_cover`. -/
theorem coherentSheafFlat_of_isLocallyTrivial_of_flat {T Y : Scheme.{u}} [IsAffine T]
    (q : Y ⟶ T) [AlgebraicGeometry.Flat q] {L : Y.Modules}
    (hL : Scheme.LineBundle.IsLocallyTrivial L) :
    Scheme.CoherentSheafFlat q L := by
  haveI := hL.isFinitePresentation
  choose W hxW hWaff hWtriv using hL
  have heW : ∀ y : Y, W y ≤ q ⁻¹ᵁ (⊤ : T.Opens) := by
    intro y
    rw [Scheme.Hom.preimage_top]
    exact le_top
  intro U hU V hV e
  refine flat_section_of_affine_cover q L W hWaff (fun _ => (⊤ : T.Opens))
    (fun _ => isAffineOpen_top T) heW (fun y => ⟨y, hxW y⟩) ?_ hU hV e
  intro y
  letI : Module Γ(T, ⊤) Γ(L, W y) :=
    Module.compHom _ (q.appLE ⊤ (W y) (heW y)).hom
  letI : Algebra Γ(T, ⊤) Γ(Y, W y) := (q.appLE ⊤ (W y) (heW y)).hom.toAlgebra
  haveI hflat1 : Module.Flat Γ(T, ⊤) Γ(Y, W y) :=
    q.flat_appLE (isAffineOpen_top T) (hWaff y) (heW y)
  haveI : Module.Invertible Γ(Y, W y) Γ(L, W y) :=
    Scheme.LineBundle.isInvertible_of_restrict_iso (W y) (hWtriv y).some
  haveI : IsScalarTower Γ(T, ⊤) Γ(Y, W y) Γ(L, W y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Flat.trans Γ(T, ⊤) Γ(Y, W y) Γ(L, W y)

/-- **Coherent-sheaf flatness transfers along an affine pushforward.**  For
an affine `π : X ⟶ Y` over `p : Y ⟶ T`, flatness of `F` over `T` (via the
composite `π ≫ p`) gives flatness of `π_* F` over `T` (via `p`): the
sections of `π_* F` over an affine `V` are `Γ(F, π⁻¹ V)` definitionally
(with `π⁻¹ V` affine since `π` is), and the two `Γ(T, U)`-module structures
agree because `(π ≫ p).appLE = p.appLE ≫ π.appLE`
(`Scheme.Hom.appLE_comp_appLE`). -/
theorem CoherentSheafFlat.pushforward_of_isAffineHom {X Y T : Scheme.{u}}
    (π : X ⟶ Y) [IsAffineHom π] (p : Y ⟶ T) (F : X.Modules)
    (h : Scheme.CoherentSheafFlat (π ≫ p) F) :
    Scheme.CoherentSheafFlat p ((Scheme.Modules.pushforward π).obj F) := by
  intro U hU V hV e
  have hpre : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have epre : π ⁻¹ᵁ V ≤ (π ≫ p) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage]
    intro x hx
    exact e hx
  have base := h hU hpre epre
  -- identify the two ring homomorphisms `Γ(T, U) → Γ(X, π ⁻¹ᵁ V)`
  have hφ : ((π ≫ p).appLE U (π ⁻¹ᵁ V) epre).hom =
      ((π.app V).hom).comp ((p.appLE U V e).hom) := by
    have h1 := Scheme.Hom.appLE_comp_appLE π p U V (π ⁻¹ᵁ V) e le_rfl
    refine RingHom.ext fun r => ?_
    have h2 := congrArg (fun (φ : Γ(T, U) ⟶ Γ(X, π ⁻¹ᵁ V)) => φ.hom r) h1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    rw [RingHom.comp_apply, Scheme.Hom.app_eq_appLE]
    exact h2.symm
  -- both module structures are `compHom`s of the canonical one, along
  -- pointwise-equal ring homomorphisms
  rw [hφ] at base
  exact base

end Scheme

namespace Adelic

open Scheme

variable {k : Type u} [Field k]
variable (A : Type u) [CommRing A] [Algebra k A]
variable (C : Over (Spec (CommRingCat.of k)))

/-- **`hflat` for the B3 reduction (mixed-base flat stability): the finite
pushforward `(π_A)_* L` stays flat over `Spec A`.**  Since
`Γ((π_A)_* L, V) = Γ(L, π_A⁻¹ V)` definitionally and `q = π_A ≫ p`
(`finiteMapToP1BaseChange_snd`), this reduces to `CoherentSheafFlat q L`
for the invertible `L` on the family `q : C_A ⟶ Spec A`, which is a flat
morphism as the base change of `C ⟶ Spec k` (everything over the one-point
integral `Spec k` is flat).  This discharges the `hflat` hypothesis of
`rigidPushforwardLocallyFree_of_p1`; no finiteness of `A` is needed. -/
theorem pushforward_finiteMapToP1BaseChange_coherentSheafFlat
    [HasFiniteMapToP1 C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L) :
    Scheme.CoherentSheafFlat
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : AlgebraicGeometry.Flat C.hom := inferInstance
  haveI : AlgebraicGeometry.Flat
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
    inferInstance
  haveI : IsFinite (finiteMapToP1BaseChange A C) := isFinite_finiteMapToP1BaseChange A C
  have hq : Scheme.CoherentSheafFlat
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) L :=
    Scheme.coherentSheafFlat_of_isLocallyTrivial_of_flat _ hL
  have hq' : Scheme.CoherentSheafFlat
      (finiteMapToP1BaseChange A C ≫
        pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) L := by
    rw [finiteMapToP1BaseChange_snd]
    exact hq
  intro U hU V hV e
  exact Scheme.CoherentSheafFlat.pushforward_of_isAffineHom
    (finiteMapToP1BaseChange A C)
    (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    L hq' hU hV e

end Adelic

/-! ## §5. Substrate for `hH1`/`hH0` — the fibre square of the finite map
and the definitional Čech bridges

Item (c) of the transfer package identifies `(π_A)_* L` restricted to the
fibre `ℙ¹_t` with `(π_t)_* (L_t)` and transports the Čech difference map
across it.  This section lands the geometric substrate: the induced finite
map `π_t : C_t ⟶ ℙ¹_t` between the scheme-theoretic fibres, its cartesian
square over `π_A`, and the two *definitional* Čech bridges — the difference
map of a 2-affine cover for an (affine) pushforward literally *is* the
difference map of the preimage cover, and surjectivity of the difference
map transports across isomorphisms of module sheaves.  On top of this
substrate, `hH1`/`hH0` need the affine-morphism base-change isomorphism
`(p.fiberι t)^* (π_A)_* L ≅ (π_t)_* (q.fiberι t)^* L` (Stacks 02KG for the
affine `π_A`; `κ(t)` is *not* flat over `A`, so this is the
glued form of `affinePushforwardPullbackBaseChange`), plus — for `hH1` —
the Čech-to-Čech cover-independence of `Ȟ¹`-vanishing on the fibre curve
(§6–§8 below). -/

namespace Scheme

/-- **The Čech difference map of an affine pushforward is the difference map
of the preimage cover** — definitionally: sections, intersections of
preimages, and restriction maps of `f_* M` over a 2-affine cover `V` all
agree with those of `M` over `V.preimage f`. -/
lemma AffineCoverMVSquare.moduleSectionDiff_pushforward {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] (V : Y.AffineCoverMVSquare) (M : X.Modules) :
    V.moduleSectionDiff ((Scheme.Modules.pushforward f).obj M) =
      (V.preimage f).moduleSectionDiff M :=
  rfl

/-- **Naturality of the Čech difference map** in the module: a morphism of
module sheaves intertwines the difference maps of a 2-affine cover. -/
lemma AffineCoverMVSquare.moduleSectionDiff_naturality {X : Scheme.{u}}
    (V : X.AffineCoverMVSquare) {G G' : X.Modules} (φ : G ⟶ G')
    (a : Γ(G, V.U₁)) (b : Γ(G, V.U₂)) :
    V.moduleSectionDiff G' (φ.app V.U₁ a, φ.app V.U₂ b) =
      φ.app (V.U₁ ⊓ V.U₂) (V.moduleSectionDiff G (a, b)) := by
  have h₁ := congrArg (fun (ψ : Γ(G, V.U₁) ⟶ Γ(G', V.U₁ ⊓ V.U₂)) => ψ.hom a)
    (φ.mapPresheaf.naturality (homOfLE (inf_le_left : V.U₁ ⊓ V.U₂ ≤ V.U₁)).op)
  have h₂ := congrArg (fun (ψ : Γ(G, V.U₂) ⟶ Γ(G', V.U₁ ⊓ V.U₂)) => ψ.hom b)
    (φ.mapPresheaf.naturality (homOfLE (inf_le_right : V.U₁ ⊓ V.U₂ ≤ V.U₂)).op)
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at h₁ h₂
  simp only [moduleSectionDiff_apply, map_sub]
  exact congrArg₂ Sub.sub h₁.symm h₂.symm

/-- **Surjectivity of the Čech difference map transports across an
isomorphism of module sheaves.** -/
lemma AffineCoverMVSquare.surjective_moduleSectionDiff_of_iso {X : Scheme.{u}}
    (V : X.AffineCoverMVSquare) {G G' : X.Modules} (e : G ≅ G')
    (h : Function.Surjective ⇑(V.moduleSectionDiff G)) :
    Function.Surjective ⇑(V.moduleSectionDiff G') := by
  intro c
  obtain ⟨⟨a, b⟩, hab⟩ := h (e.inv.app (V.U₁ ⊓ V.U₂) c)
  refine ⟨(e.hom.app V.U₁ a, e.hom.app V.U₂ b), ?_⟩
  rw [V.moduleSectionDiff_naturality e.hom a b, hab]
  change ((e.inv ≫ e.hom).app (V.U₁ ⊓ V.U₂)).hom c = c
  rw [e.inv_hom_id]
  rfl

end Scheme

namespace Adelic

open Scheme

variable {k : Type u} [Field k]
variable (A : Type u) [CommRing A] [Algebra k A]
variable (C : Over (Spec (CommRingCat.of k)))

/-- **The induced map on scheme-theoretic fibres of the finite
`π_A : C_A ⟶ ℙ¹_A`**: for `t : Spec A`, the map `π_t : C_t ⟶ ℙ¹_t` from the
fibre of `q = pullback.snd : C_A ⟶ Spec A` to the fibre of
`p = pullback.snd : ℙ¹_A ⟶ Spec A`, induced by functoriality of the fibre
square (`q = π_A ≫ p`, `finiteMapToP1BaseChange_snd`). -/
noncomputable def finiteMapToP1FiberMap [HasFiniteMapToP1 C]
    (t : Spec (CommRingCat.of A)) :
    (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiber t ⟶
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiber t :=
  pullback.map _ _ _ _ (finiteMapToP1BaseChange A C) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]; exact (finiteMapToP1BaseChange_snd A C).symm)
    (by simp)

/-- `π_t` lies over `π_A`: the fibre square of `π_t` against the fibre
embeddings commutes. -/
@[reassoc (attr := simp)]
lemma finiteMapToP1FiberMap_fiberι [HasFiniteMapToP1 C]
    (t : Spec (CommRingCat.of A)) :
    finiteMapToP1FiberMap A C t ≫
        (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberι t =
      (pullback.snd C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberι t ≫
        finiteMapToP1BaseChange A C :=
  pullback.lift_fst _ _ _

/-- `π_t` is a map of `κ(t)`-schemes: it commutes with the structural maps
to `Spec κ(t)`. -/
@[reassoc (attr := simp)]
lemma finiteMapToP1FiberMap_toSpecResidueField [HasFiniteMapToP1 C]
    (t : Spec (CommRingCat.of A)) :
    finiteMapToP1FiberMap A C t ≫
        (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberToSpecResidueField t =
      (pullback.snd C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberToSpecResidueField t :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- **The fibre square of the finite map is cartesian**: `C_t = C_A ×_{ℙ¹_A} ℙ¹_t`
(pasting of the two fibre squares over `Spec κ(t) ⟶ Spec A`).  This exhibits
`π_t` as the base change of the finite `π_A` along `ℙ¹_t ⟶ ℙ¹_A`. -/
lemma isPullback_finiteMapToP1FiberMap [HasFiniteMapToP1 C]
    (t : Spec (CommRingCat.of A)) :
    IsPullback
      ((pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberι t)
      (finiteMapToP1FiberMap A C t)
      (finiteMapToP1BaseChange A C)
      ((pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberι t) := by
  have hs : IsPullback
      ((pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberι t)
      (finiteMapToP1FiberMap A C t ≫
        (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberToSpecResidueField t)
      (finiteMapToP1BaseChange A C ≫
        pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      ((Spec (CommRingCat.of A)).fromSpecResidueField t) := by
    rw [finiteMapToP1FiberMap_toSpecResidueField, finiteMapToP1BaseChange_snd]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_bot hs (finiteMapToP1FiberMap_fiberι A C t).symm
    (IsPullback.of_hasPullback _ _)

/-- **`π_t` is finite** — base change of the finite `π_A` along the fibre
embedding `ℙ¹_t ⟶ ℙ¹_A` (`isPullback_finiteMapToP1FiberMap`). -/
instance isFinite_finiteMapToP1FiberMap [HasFiniteMapToP1 C]
    (t : Spec (CommRingCat.of A)) :
    IsFinite (finiteMapToP1FiberMap A C t) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite)
    (isPullback_finiteMapToP1FiberMap A C t)
    (isFinite_finiteMapToP1BaseChange A C)

end Adelic

/-! ## §6. Stacks 02KG for an affine morphism — the base-change comparison is an
isomorphism

The fibre-compatibility isomorphism of transfer item (c) is the statement that
the canonical base-change comparison `pushforwardBaseChangeMap`
(`Cohomology/FlatBaseChange.lean`) of the cartesian square

```
  X' --g'--> X
  |f'        |f            (f affine, F quasi-coherent on X)
  v          v
  Y' --g---> Y
```

is an isomorphism `g^*(f_* F) ≅ f'_*((g')^* F)` — with **no flatness** on `g`
(for the fibre embedding `g = p.fiberι t`, `κ(t)` is not flat over `A`).  This
section proves it in full generality (Stacks 02KG, `i = 0`, affine case):

* `pushforwardBaseChangeMap_app_baseMap` — the **mate–unit formula**: on the
  canonical `baseMap` sections (the images of `Γ(F, f⁻¹V)` under the
  `pullback ⊣ pushforward` unit), the abstract adjoint mate acts as the
  `g'`-side `baseMap`.  Pure adjunction bookkeeping (triangle identity + unit
  naturality); this sidesteps the recorded mate ↔ `cancelBaseChange` coherence
  wall because the mate is only ever evaluated on unit images.
* `algebra_isPushout_appLE_of_isPullback` — the **section-ring pushout**: for a
  cartesian square and compatible affine opens, the `appLE` square of section
  rings is a pushout (`Γ(X', f'⁻¹O) = Γ(X, f⁻¹V) ⊗_{Γ(Y, V)} Γ(Y', O)`).
  Assembled from Mathlib's `Scheme.Hom.isPullback_resLE` (the restricted square
  of affine opens is cartesian) and `isPushout_appTop_of_isPullback`.
* `isIso_pushforwardBaseChangeMap_of_isAffineHom` — the headline: the mate is
  an isomorphism.  Checked on the basis of affine opens lying inside a chart
  `g ⁻¹ᵁ V` (`Modules.isIso_of_isIso_app_of_isBasis`), where both sides are
  identified with the two scalar-extension tensor products by the affine
  section formula (`pullback_app_isoTensor_baseMap_sectionLinearEquiv`) and the
  bridge between them is `SectionBaseChange.bijective_addHom_of_isPushout`
  (associativity of scalar extension along the section-ring pushout — an
  arbitrary pushout, no flatness required). -/

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- Composition collapse for section restrictions of a sheaf of modules along
arbitrary (`Subsingleton`) opens homs.  Public re-derivation of the transport
lemma of `Picard/QuotScheme.lean` (`modules_res_res_hom` there is
`private`). -/
lemma sections_map_map (N : X.Modules) {W₁ W₂ W₃ : X.Opens}
    (i₁ : W₁ ⟶ W₂) (i₂ : W₂ ⟶ W₃) (i₃ : W₁ ⟶ W₃) (ξ : Γ(N, W₃)) :
    (N.presheaf.map i₁.op).hom ((N.presheaf.map i₂.op).hom ξ) =
      (N.presheaf.map i₃.op).hom ξ := by
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp, ← op_comp]
  exact (congrArg (fun (i : W₁ ⟶ W₃) =>
    (AddCommGrpCat.Hom.hom (N.presheaf.map i.op)) ξ) (Subsingleton.elim _ _)).symm

end Scheme.Modules

section MateFormula

variable {Y Y' X X' : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- **`baseMap` naturality in the sheaf argument** (public re-derivation of the
QuotScheme-private `pullback_app_isoTensor_baseMap_naturality`): the canonical
base map intertwines `(pullback g).map h` with `h.app V`, via naturality of the
`pullback ⊣ pushforward` adjunction unit. -/
lemma pullback_map_app_isoTensor_baseMap
    (g : Y' ⟶ Y) {N N' : Y.Modules}
    (h : N ⟶ N') {O : Y'.Opens} {V : Y.Opens} (e : O ≤ g ⁻¹ᵁ V) (x : Γ(N, V)) :
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map h) O).hom
        (pullback_app_isoTensor_baseMap g N e x) =
      pullback_app_isoTensor_baseMap g N' e ((Scheme.Modules.Hom.app h V).hom x) := by
  have hb := congrArg
    (fun (k : N ⟶ (Scheme.Modules.pushforward g).obj
        ((Scheme.Modules.pullback g).obj N')) =>
      (Scheme.Modules.Hom.app k V).hom x)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality h)
  have ha := congrArg
    (fun (k : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ V) ⟶
        Γ((Scheme.Modules.pullback g).obj N', O)) =>
      (AddCommGrpCat.Hom.hom k)
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app V x))
    ((Scheme.Modules.Hom.mapPresheaf ((Scheme.Modules.pullback g).map h)).naturality
      (homOfLE e).op)
  exact ha.trans (congrArg
    (fun w => ((((Scheme.Modules.pullback g).obj N').presheaf.map (homOfLE e).op).hom) w)
    hb.symm)

set_option backward.isDefEq.respectTransparency false in
/-- **The counit collapses the `baseMap` of a pushforward to a plain
restriction** (triangle identity for the mate–unit formula): for a module
`K` on `Y'` and `y ∈ Γ((pushforward g).obj K, V) = Γ(K, g⁻¹V)`, applying the
`pullback ⊣ pushforward` counit to the canonical base-map section of `y`
returns the restriction of `y` to `O ⊆ g⁻¹V`. -/
lemma counit_app_isoTensor_baseMap_pushforward
    (g : Y' ⟶ Y) (K : Y'.Modules) {O : Y'.Opens} {V : Y.Opens} (e : O ≤ g ⁻¹ᵁ V)
    (y : Γ((Scheme.Modules.pushforward g).obj K, V)) :
    (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction g).counit.app K) O).hom
      (pullback_app_isoTensor_baseMap g ((Scheme.Modules.pushforward g).obj K) e y) =
    (K.presheaf.map (homOfLE (show O ≤ g ⁻¹ᵁ V from e)).op).hom y := by
  -- (a) naturality of the counit component against the restriction `O ≤ g⁻¹V`:
  have ha := congrArg
    (fun (k : Γ((Scheme.Modules.pullback g).obj
          ((Scheme.Modules.pushforward g).obj K), g ⁻¹ᵁ V) ⟶ Γ(K, O)) =>
      (AddCommGrpCat.Hom.hom k)
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pushforward g).obj K)).app V y))
    ((Scheme.Modules.Hom.mapPresheaf
      ((Scheme.Modules.pullbackPushforwardAdjunction g).counit.app K)).naturality
      (homOfLE e).op)
  -- (b) the right triangle identity at `V`-sections: unit then (pushforward of
  -- the) counit is the identity; the pushforward's `app` at `V` is
  -- definitionally the counit's `app` at `g⁻¹V`.
  have hb := congrArg
    (fun (k : (Scheme.Modules.pushforward g).obj K ⟶
        (Scheme.Modules.pushforward g).obj K) => (Scheme.Modules.Hom.app k V).hom y)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).right_triangle_components K)
  exact ha.trans (congrArg
    (fun w => ((K.presheaf.map (homOfLE e).op).hom) w) hb)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Heartbeat headroom for the adjunction-unit/counit transport chains, as
-- elsewhere in the QuotScheme baseMap substrate.
/-- **The mate–unit formula** (the pointwise Beck–Chevalley identity powering
the 02KG isomorphism): on the canonical base-map section of
`x ∈ Γ(f_* F, V) = Γ(F, f⁻¹V)`, the abstract base-change mate
`g^*(f_* F) ⟶ f'_*((g')^* F)` acts as the `g'`-side canonical base map.

This characterizes the mate on a generating family (over `Γ(Y', O)`) of the
sections of `g^*(f_* F)` over any affine `O ≤ g⁻¹V`, which is all the
isomorphism proof consumes — the recorded mate ↔ `cancelBaseChange` coherence
wall is never touched. -/
lemma pushforwardBaseChangeMap_app_baseMap
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (comm : g' ≫ f = f' ≫ g) (F : X.Modules)
    {V : Y.Opens} {O : Y'.Opens} (e : O ≤ g ⁻¹ᵁ V)
    (e' : f' ⁻¹ᵁ O ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V))
    (x : Γ((Scheme.Modules.pushforward f).obj F, V)) :
    (Scheme.Modules.Hom.app (pushforwardBaseChangeMap f g f' g' comm F) O).hom
        (pullback_app_isoTensor_baseMap g ((Scheme.Modules.pushforward f).obj F) e x) =
      pullback_app_isoTensor_baseMap g' F e' x := by
  -- the mate is `(pullback g).map χ ≫ counit` where `χ` is the adjoint
  have hmate : pushforwardBaseChangeMap f g f' g' comm F =
      (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pushforward f).map
              ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) ≫
            (Scheme.Modules.pushforwardComp g' f).hom.app _ ≫
            (Scheme.Modules.pushforwardCongr comm).hom.app _ ≫
            (Scheme.Modules.pushforwardComp f' g).inv.app _) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
          ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)) := by
    rw [pushforwardBaseChangeMap, Adjunction.homEquiv_counit]
  rw [hmate]
  -- apply the two-step composite elementwise
  rw [Scheme.Modules.Hom.comp_app]
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
  rw [pullback_map_app_isoTensor_baseMap g _ e x]
  refine (counit_app_isoTensor_baseMap_pushforward g
    ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)) e _).trans ?_
  -- it remains to compute `restr_e (χ.app V x)` as the `g'`-side base map:
  -- `χ.app V` is the `g'`-unit at `f⁻¹V` followed by an (`eqToHom`) restriction
  -- (the `pushforwardComp` legs are identities on sections), and the two
  -- restrictions collapse to the single restriction `f'⁻¹O ≤ g'⁻¹(f⁻¹V)`.
  have hχapp : (Scheme.Modules.Hom.app
        ((Scheme.Modules.pushforward f).map
            ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) ≫
          (Scheme.Modules.pushforwardComp g' f).hom.app _ ≫
          (Scheme.Modules.pushforwardCongr comm).hom.app _ ≫
          (Scheme.Modules.pushforwardComp f' g).inv.app _) V).hom x =
      (((Scheme.Modules.pullback g').obj F).presheaf.map
          (eqToHom (show ((f' ≫ g) ⁻¹ᵁ V : X'.Opens) = (g' ≫ f) ⁻¹ᵁ V from
            comm ▸ rfl)).op).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F).app
          (f ⁻¹ᵁ V)).hom x) := by
    rfl
  refine Eq.trans (congrArg (fun w =>
    ((((Scheme.Modules.pullback g').obj F).presheaf.map
      ((Opens.map f'.base).map (homOfLE e)).op).hom) w) hχapp) ?_
  exact Scheme.Modules.sections_map_map ((Scheme.Modules.pullback g').obj F)
    _ _ (homOfLE e') _

end MateFormula

section SectionRingPushout

variable {Y Y' X X' : Scheme.{u}}

/-- **The section-ring square of a cartesian square, on compatible affine opens,
is a pushout** (`Γ(X', f'⁻¹O) = Γ(X, f⁻¹V) ⊗_{Γ(Y, V)} Γ(Y', O)`, categorical
form).  Restrict the cartesian square to the four opens
(`Scheme.Hom.isPullback_resLE`), observe that the restricted square is a
pullback of *affine* schemes, apply Mathlib's
`isPushout_appTop_of_isPullback`, and transport the resulting pushout of
`appTop`s along the four `topIso`s to the `appLE` maps of the original square
(`Scheme.Hom.resLE_app_top`). -/
theorem isPushout_appLE_of_isPullback
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g)
    {V : Y.Opens} {O : Y'.Opens} (e : O ≤ g ⁻¹ᵁ V)
    (e' : f' ⁻¹ᵁ O ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V))
    (hV : IsAffineOpen V) (hO : IsAffineOpen O)
    (hfV : IsAffineOpen (f ⁻¹ᵁ V)) (_hf'O : IsAffineOpen (f' ⁻¹ᵁ O)) :
    CategoryTheory.IsPushout (f.appLE V (f ⁻¹ᵁ V) le_rfl) (g.appLE V O e)
      (g'.appLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ O) e') (f'.appLE O (f' ⁻¹ᵁ O) le_rfl) := by
  -- the restricted square of the four opens is cartesian
  have hUY : (f' ⁻¹ᵁ O : X'.Opens) = g' ⁻¹ᵁ (f ⁻¹ᵁ V) ⊓ f' ⁻¹ᵁ O :=
    (inf_eq_right.mpr e').symm
  have hpb := Scheme.Hom.isPullback_resLE h (US := V) (UT := O) (UX := f ⁻¹ᵁ V)
    e le_rfl hUY
  -- the four corners are affine schemes
  haveI : IsAffine V.toScheme := hV
  haveI : IsAffine O.toScheme := hO
  haveI : IsAffine (f ⁻¹ᵁ V).toScheme := hfV
  haveI : IsAffine (f' ⁻¹ᵁ O).toScheme := _hf'O
  -- pushout of the `appTop`s of the restricted square
  have hpush := isPushout_appTop_of_isPullback hpb
  -- transport along the `topIso`s to the `appLE` square
  have key : ∀ {A B : Scheme.{u}} (φ : A ⟶ B) (U : B.Opens) (W : A.Opens)
      (ew : W ≤ φ ⁻¹ᵁ U),
      (φ.resLE U W ew).appTop ≫ W.topIso.hom = U.topIso.hom ≫ φ.appLE U W ew := by
    intro A B φ U W ew
    rw [show (φ.resLE U W ew).appTop = (φ.resLE U W ew).app ⊤ from rfl,
      Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hpush.of_iso (Scheme.Opens.topIso V) (Scheme.Opens.topIso (f ⁻¹ᵁ V))
    (Scheme.Opens.topIso O) (Scheme.Opens.topIso (f' ⁻¹ᵁ O))
    (key f V (f ⁻¹ᵁ V) le_rfl) (key g V O e)
    (key g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ O) (hUY.le.trans inf_le_left))
    (key f' O (f' ⁻¹ᵁ O) le_rfl)

end SectionRingPushout

section AffineBaseChangeIso

variable {Y Y' X X' : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
-- Heartbeat headroom for the section-formula transports and the tensor-bridge
-- instance searches, as elsewhere in the Lane-F section-formula layer.
set_option synthInstance.maxHeartbeats 800000 in
/-- **Stacks 02KG (`i = 0`, affine case), affine-chart form**: for a cartesian
square with `f` (hence `f'`) affine, a quasi-coherent `F` on `X`, and affine
opens `V ⊆ Y`, `O ⊆ Y'` with `O ≤ g⁻¹V`, the canonical base-change comparison
`g^*(f_* F) ⟶ f'_*((g')^* F)` is an isomorphism on sections over `O`.  **No
flatness of `g` is required.**  Both sides are identified with the two scalar
extensions of `Γ(F, f⁻¹V)` by the affine section formula
(`pullback_app_isoTensor_baseMap_sectionLinearEquiv`), the identifications are
intertwined by the mate–unit formula on the `Γ(Y', O)`-generators, and the
resulting bridge `Γ(Y', O) ⊗_{Γ(Y, V)} M ⟶ Γ(X', f'⁻¹O) ⊗_{Γ(X, f⁻¹V)} M` is
bijective by associativity of scalar extension along the section-ring pushout
(`SectionBaseChange.bijective_addHom_of_isPushout` +
`isPushout_appLE_of_isPullback`). -/
theorem isIso_pushforwardBaseChangeMap_app_of_isPullback
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [IsAffineHom f] [IsAffineHom f']
    (F : X.Modules) [F.IsQuasicoherent]
    {V : Y.Opens} {O : Y'.Opens} (e : O ≤ g ⁻¹ᵁ V)
    (hV : IsAffineOpen V) (hO : IsAffineOpen O) :
    IsIso (Scheme.Modules.Hom.app (pushforwardBaseChangeMap f g f' g' h.w F) O) := by
  -- opens bookkeeping
  have e' : f' ⁻¹ᵁ O ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
    exact f'.preimage_mono e
  have hfV : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hf'O : IsAffineOpen (f' ⁻¹ᵁ O) := hO.preimage f'
  haveI : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    Scheme.Modules.pushforward_isQuasicoherent f F
  -- the algebra dictionary of the section-ring square
  letI aAB : Algebra Γ(Y, V) Γ(Y', O) := (g.appLE V O e).hom.toAlgebra
  letI aAC : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
    (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  letI aCD : Algebra Γ(X, f ⁻¹ᵁ V) Γ(X', f' ⁻¹ᵁ O) :=
    (g'.appLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ O) e').hom.toAlgebra
  letI aBD : Algebra Γ(Y', O) Γ(X', f' ⁻¹ᵁ O) :=
    (f'.appLE O (f' ⁻¹ᵁ O) le_rfl).hom.toAlgebra
  letI aAD : Algebra Γ(Y, V) Γ(X', f' ⁻¹ᵁ O) :=
    ((f.appLE V (f ⁻¹ᵁ V) le_rfl) ≫
      (g'.appLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ O) e')).hom.toAlgebra
  have hsq : (f.appLE V (f ⁻¹ᵁ V) le_rfl) ≫ (g'.appLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ O) e') =
      (g.appLE V O e) ≫ (f'.appLE O (f' ⁻¹ᵁ O) le_rfl) :=
    (isPushout_appLE_of_isPullback h e e' hV hO hfV hf'O).w
  haveI tACD : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X', f' ⁻¹ᵁ O) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tABD : IsScalarTower Γ(Y, V) Γ(Y', O) Γ(X', f' ⁻¹ᵁ O) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      have h0 := congrArg (fun (φ : Γ(Y, V) ⟶ Γ(X', f' ⁻¹ᵁ O)) => φ.hom r) hsq
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h0
      exact h0)
  haveI pushAlg : Algebra.IsPushout Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(Y', O) Γ(X', f' ⁻¹ᵁ O) :=
    (CommRingCat.isPushout_iff_isPushout).mp
      (isPushout_appLE_of_isPullback h e e' hV hO hfV hf'O)
  -- the `appLE V (f⁻¹V) le_rfl` restriction acts on sections as `app V` does
  have happ : ∀ (r : Γ(Y, V)),
      (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom r = (f.app V).hom r := by
    intro r
    rw [← Scheme.Hom.app_eq_appLE]
  have happ' : ∀ (r : Γ(Y', O)),
      (f'.appLE O (f' ⁻¹ᵁ O) le_rfl).hom r = (f'.app O).hom r := by
    intro r
    rw [← Scheme.Hom.app_eq_appLE]
  -- the module tower on the common section module `M = Γ(F, f⁻¹V) = Γ(f_* F, V)`;
  -- the `Γ(Y, V)`-structure is `compHom` along `f.app V`, which is
  -- *definitionally* the sheaf structure of the pushforward over `V`
  letI mAM : Module Γ(Y, V) Γ(F, f ⁻¹ᵁ V) :=
    Module.compHom _ (f.app V).hom
  haveI tACM : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_smul (fun r m => by
      change (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom r • m = (f.app V).hom r • m
      rw [happ r])
  -- the two affine section formulas
  obtain ⟨⟨eL, heL⟩⟩ := pullback_app_isoTensor_baseMap_sectionLinearEquiv g
    ((Scheme.Modules.pushforward f).obj F) hO hV e
  obtain ⟨⟨eR, heR⟩⟩ := pullback_app_isoTensor_baseMap_sectionLinearEquiv g' F hf'O hfV e'
  -- the scalar-extension bridge
  let s : TensorProduct Γ(Y, V) Γ(Y', O) Γ(F, f ⁻¹ᵁ V) →+
      TensorProduct Γ(X, f ⁻¹ᵁ V) Γ(X', f' ⁻¹ᵁ O) Γ(F, f ⁻¹ᵁ V) :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
        (fun m => algebraMap Γ(Y', O) Γ(X', f' ⁻¹ᵁ O) b ⊗ₜ[Γ(X, f ⁻¹ᵁ V)] m)
        (fun m₁ m₂ => TensorProduct.tmul_add _ m₁ m₂))
        (fun b₁ b₂ => by
          ext m
          simp [TensorProduct.add_tmul]))
      (fun r b m => by
        change algebraMap Γ(Y', O) Γ(X', f' ⁻¹ᵁ O) (r • b) ⊗ₜ[Γ(X, f ⁻¹ᵁ V)] m =
          algebraMap Γ(Y', O) Γ(X', f' ⁻¹ᵁ O) b ⊗ₜ[Γ(X, f ⁻¹ᵁ V)] (r • m)
        rw [Algebra.smul_def, map_mul,
          ← IsScalarTower.algebraMap_apply Γ(Y, V) Γ(Y', O) Γ(X', f' ⁻¹ᵁ O),
          IsScalarTower.algebraMap_apply Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X', f' ⁻¹ᵁ O),
          ← Algebra.smul_def, TensorProduct.smul_tmul]
        congr 1
        change (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom r • m = (f.app V).hom r • m
        rw [happ r])
  have hs : ∀ (b : Γ(Y', O)) (m : Γ(F, f ⁻¹ᵁ V)),
      s (b ⊗ₜ[Γ(Y, V)] m) = algebraMap Γ(Y', O) Γ(X', f' ⁻¹ᵁ O) b ⊗ₜ[Γ(X, f ⁻¹ᵁ V)] m :=
    fun b m => TensorProduct.liftAddHom_tmul _ _ b m
  have hs_bij : Function.Bijective s :=
    SectionBaseChange.bijective_addHom_of_isPushout s hs
  -- the mate agrees with `eR ∘ s ∘ eL⁻¹`: check on the `Γ(Y', O)`-generators
  have hcomm : ∀ w : TensorProduct Γ(Y, V) Γ(Y', O) Γ(F, f ⁻¹ᵁ V),
      (Scheme.Modules.Hom.app (pushforwardBaseChangeMap f g f' g' h.w F) O).hom
        (eL w) = eR (s w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b m =>
      -- normalize the right-hand side to `algebraMap b • baseMap_{g'} m`
      rw [hs b m]
      have hsm : (algebraMap Γ(Y', O) Γ(X', f' ⁻¹ᵁ O) b ⊗ₜ[Γ(X, f ⁻¹ᵁ V)] m :
          TensorProduct Γ(X, f ⁻¹ᵁ V) Γ(X', f' ⁻¹ᵁ O) Γ(F, f ⁻¹ᵁ V)) =
          algebraMap Γ(Y', O) Γ(X', f' ⁻¹ᵁ O) b •
            ((1 : Γ(X', f' ⁻¹ᵁ O)) ⊗ₜ[Γ(X, f ⁻¹ᵁ V)] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hsm, map_smul, heR]
      -- normalize the left-hand side to `b • mate (baseMap_g m)`
      have hb : (b ⊗ₜ[Γ(Y, V)] m :
          TensorProduct Γ(Y, V) Γ(Y', O) Γ(F, f ⁻¹ᵁ V)) =
          b • ((1 : Γ(Y', O)) ⊗ₜ[Γ(Y, V)] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hb, map_smul, heL]
      -- LHS: the module-sheaf-hom app is `Γ(Y', O)`-linear
      have hlin : (Scheme.Modules.Hom.app (pushforwardBaseChangeMap f g f' g' h.w F) O).hom
          (b • pullback_app_isoTensor_baseMap g
            ((Scheme.Modules.pushforward f).obj F) e m) =
          b • (Scheme.Modules.Hom.app (pushforwardBaseChangeMap f g f' g' h.w F) O).hom
            (pullback_app_isoTensor_baseMap g
              ((Scheme.Modules.pushforward f).obj F) e m) :=
        Scheme.Modules.Hom.app_smul _ b _
      rw [hlin, pushforwardBaseChangeMap_app_baseMap f g f' g' h.w F e e' m]
      -- match the two scalar actions across the definitional identification
      -- `Γ(f'_*(g'^* F), O) = Γ((g')^* F, f'⁻¹O)`
      change b • (show Γ((Scheme.Modules.pushforward f').obj
            ((Scheme.Modules.pullback g').obj F), O) from
          pullback_app_isoTensor_baseMap g' F e' m) =
        (f'.appLE O (f' ⁻¹ᵁ O) le_rfl).hom b • pullback_app_isoTensor_baseMap g' F e' m
      rw [happ' b]
      rfl
  -- conclude: the app is a composition of bijections
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfun : ⇑(ConcreteCategory.hom
      (Scheme.Modules.Hom.app (pushforwardBaseChangeMap f g f' g' h.w F) O)) =
      ⇑eR ∘ ⇑s ∘ ⇑eL.symm := by
    funext z
    obtain ⟨w, rfl⟩ := eL.surjective z
    have hz : eL.symm (eL w) = w := eL.symm_apply_apply w
    simp only [Function.comp_apply, hz]
    exact hcomm w
  rw [hfun]
  exact (EquivLike.bijective eR).comp (hs_bij.comp (EquivLike.bijective eL.symm))

set_option maxHeartbeats 1600000 in
-- Heartbeat headroom for the basis-locality reduction over the affine-pairs
-- index type, as elsewhere in the B3 lane.
set_option synthInstance.maxHeartbeats 400000 in
/-- **Stacks 02KG (`i = 0`), affine morphisms, arbitrary base change**: for a
cartesian square of schemes

```
  X' --g'--> X
  |f'        |f
  v          v
  Y' --g---> Y
```

with `f` and `f'` affine and `F` quasi-coherent on `X`, the canonical
base-change comparison `g^*(f_* F) ⟶ f'_*((g')^* F)` is an isomorphism — with
**no flatness hypothesis on `g`**.  Checked on the basis of affine opens of
`Y'` contained in the `g`-preimage of an affine open of `Y`
(`Modules.isIso_of_isIso_app_of_isBasis` +
`isIso_pushforwardBaseChangeMap_app_of_isPullback`). -/
theorem isIso_pushforwardBaseChangeMap_of_isPullback
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [IsAffineHom f] [IsAffineHom f']
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIso (pushforwardBaseChangeMap f g f' g' h.w F) := by
  refine Modules.isIso_of_isIso_app_of_isBasis
    (ι := {p : Y'.Opens × Y.Opens //
      IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ p.1 ≤ g ⁻¹ᵁ p.2})
    (B := fun p => p.1.1) ?_ _ ?_
  · rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro W y hy
    obtain ⟨V, hVaff, hgyV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (Scheme.isBasis_affineOpens Y)
      (show g.base y ∈ (⊤ : Y.Opens) from trivial)
    have hyWV : y ∈ W ⊓ g ⁻¹ᵁ V := ⟨hy, hgyV⟩
    obtain ⟨O, hOaff, hyO, hOsub⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (Scheme.isBasis_affineOpens Y') hyWV
    exact ⟨O, ⟨⟨(O, V), hOaff, hVaff, hOsub.trans inf_le_right⟩, rfl⟩, hyO,
      hOsub.trans inf_le_left⟩
  · intro p
    exact isIso_pushforwardBaseChangeMap_app_of_isPullback h F p.2.2.2 p.2.2.1 p.2.1

/-- **The 02KG base-change isomorphism** for an affine morphism, bundled form:
`g^*(f_* F) ≅ f'_*((g')^* F)` for a cartesian square with `f`, `f'` affine and
`F` quasi-coherent — no flatness on `g`. -/
noncomputable def pushforwardPullbackBaseChangeIso
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [IsAffineHom f] [IsAffineHom f']
    (F : X.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F) ≅
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F) :=
  haveI := isIso_pushforwardBaseChangeMap_of_isPullback h F
  asIso (pushforwardBaseChangeMap f g f' g' h.w F)

end AffineBaseChangeIso

/-! ## §7. The fibre-compatibility isomorphism and the `hH1`/`hH0` transfers

Specializing the 02KG isomorphism to the fibre square of
`π_A : C_A ⟶ ℙ¹_A` over a scheme point `t : Spec A`
(`isPullback_finiteMapToP1FiberMap`) produces the fibre-compatibility
isomorphism of transfer item (c),

`(p.fiberι t)^* ((π_A)_* L) ≅ (π_t)_* ((q.fiberι t)^* L)`,

for **every** scheme point `t` — `κ(t)` is not flat over `A`, which is exactly
why the arbitrary-pushout form of 02KG (and never the flat 02KE engine) is used.
From it:

* `hH0` is discharged **verbatim**
  (`pushforward_finiteMapToP1BaseChange_fiberH0`): the isomorphism restricts
  to a `κ(t)`-linear equivalence on global sections over the fibre, because
  `π_t` is a `κ(t)`-morphism (`finiteMapToP1FiberMap_toSpecResidueField`);
* `hH1` transfers along the isomorphism once the Čech `h¹`-vanishing witness
  is available **on the preimage cover**
  (`fiberH1Vanishing_pushforward_finiteMapToP1BaseChange_of_preimage_cover`).
  The pinned `hH1` of `rigidPushforwardLocallyFree_of_p1` supplies the witness
  on an *arbitrary* 2-affine cover of `C_t`; bridging the two is exactly the
  Čech-to-Čech cover-independence of `Ȟ¹`-vanishing on the fibre curve (Leray
  for 2-affine covers of the separated fibre), imported from
  `Cohomology/StructureSheafModuleK/QuasicoherentDegreeOneVanishing.lean`
  rather than re-proved here. -/

namespace Adelic

open Scheme

variable {k : Type u} [Field k]
variable (A : Type u) [CommRing A] [Algebra k A]
variable (C : Over (Spec (CommRingCat.of k)))

/-- **The fibre-compatibility isomorphism** (transfer item (c), Stacks 02KG for
the finite `π_A`): for every scheme point `t : Spec A` and invertible `L` on
`C_A`, restricting the finite pushforward `(π_A)_* L` to the fibre `ℙ¹_t` is
the same as pushing the restriction `L_t` forward along the induced finite
`π_t : C_t ⟶ ℙ¹_t`.  No flatness of `κ(t)` over `A` enters. -/
noncomputable def fiberPushforwardCompatIso [HasFiniteMapToP1 C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L) (t : Spec (CommRingCat.of A)) :
    (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberModule t
        ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) ≅
      (Scheme.Modules.pushforward (finiteMapToP1FiberMap A C t)).obj
        ((pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberModule t L) :=
  haveI := hL.isFinitePresentation
  haveI : IsFinite (finiteMapToP1BaseChange A C) := isFinite_finiteMapToP1BaseChange A C
  pushforwardPullbackBaseChangeIso (isPullback_finiteMapToP1FiberMap A C t) L

/-- **`hH1` transfer along the fibre-compatibility isomorphism, preimage-cover
form**: if the Čech difference map of `L_t` is surjective on the
`π_t`-preimage of a 2-affine cover `W` of `ℙ¹_t`, then the fibrewise `h¹` of
the finite pushforward `(π_A)_* L` vanishes at `t` (with witness `W`).

This is the entire *transfer* content of the pinned `hH1` hypothesis of
`rigidPushforwardLocallyFree_of_p1`; what separates it from the pinned `hH1`
(whose hypothesis provides the surjectivity witness on an *arbitrary* 2-affine
cover of `C_t`) is exactly the cover-independence of Čech-`Ȟ¹` vanishing on
the separated fibre curve. -/
theorem fiberH1Vanishing_pushforward_finiteMapToP1BaseChange_of_preimage_cover
    [HasFiniteMapToP1 C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L) (t : Spec (CommRingCat.of A))
    (W : ((pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiber t).AffineCoverMVSquare)
    (hsurj : Function.Surjective
      ⇑((W.preimage (finiteMapToP1FiberMap A C t)).moduleSectionDiff
        ((pullback.snd C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberModule t L))) :
    (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing
      ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) t := by
  refine ⟨W, ?_⟩
  have h1 : Function.Surjective ⇑(W.moduleSectionDiff
      ((Scheme.Modules.pushforward (finiteMapToP1FiberMap A C t)).obj
        ((pullback.snd C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberModule t L))) :=
    hsurj
  exact W.surjective_moduleSectionDiff_of_iso
    (fiberPushforwardCompatIso A C L hL t).symm h1

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Heartbeat headroom for the fibre-module instance transports, as elsewhere in
-- the B3 lane.
/-- **`hH0` for the B3 reduction (fibrewise `h⁰` transfer along the finite
`π_A`)**: for every scheme point `t : Spec A`, the `κ(t)`-dimension of the
glued global sections of `(π_A)_* L` on the fibre `ℙ¹_t` equals that of `L` on
the fibre curve `C_t`.  The fibre-compatibility isomorphism
(`fiberPushforwardCompatIso`) restricts on global sections to a `κ(t)`-linear
equivalence `Γ(ℙ¹_t, ((π_A)_* L)_t) ≃ₗ[κ(t)] Γ(C_t, L_t)`: the two
`κ(t)`-structures (`Scheme.Hom.fiberSectionsModule`) are intertwined because
`π_t` is a morphism of `κ(t)`-schemes
(`finiteMapToP1FiberMap_toSpecResidueField`) and the pushforward's section
action is definitionally restriction along `π_t.appTop`.  This discharges the
`hH0` hypothesis of `rigidPushforwardLocallyFree_of_p1`. -/
theorem pushforward_finiteMapToP1BaseChange_fiberH0 [HasFiniteMapToP1 C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (t : Spec (CommRingCat.of A)) (hL : LineBundle.IsLocallyTrivial L) :
    (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0
      ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) t =
    (pullback.snd C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t := by
  haveI := hL.isFinitePresentation
  haveI : IsFinite (finiteMapToP1BaseChange A C) := isFinite_finiteMapToP1BaseChange A C
  -- the fibre-compatibility isomorphism and its global-sections comparison
  let e := fiberPushforwardCompatIso A C L hL t
  -- the residue maps of the two fibres are intertwined by `π_t.appTop`
  have hres : (pullback.snd C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberResidueMap t =
      (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberResidueMap t ≫
        (finiteMapToP1FiberMap A C t).appTop := by
    simp only [Scheme.Hom.fiberResidueMap]
    rw [Category.assoc, ← Scheme.Hom.comp_appTop,
      finiteMapToP1FiberMap_toSpecResidueField]
  -- the `κ(t)`-module structures on the two glued section spaces
  letI m₁ := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberSectionsModule t
    ((pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberModule t
      ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L))
  letI m₂ := (pullback.snd C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberSectionsModule t
    ((pullback.snd C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberModule t L)
  -- the global-sections additive equivalence of the compatibility isomorphism
  let ae := (asIso (Scheme.Modules.Hom.app e.hom
    (⊤ : ((pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiber t).Opens))).addCommGroupIsoToAddEquiv
  -- upgrade to a `κ(t)`-linear equivalence
  let le : Γ((pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberModule t
        ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L), ⊤) ≃ₗ[
      (Spec (CommRingCat.of A)).residueField t]
      Γ((pullback.snd C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberModule t L, ⊤) :=
    { ae with
      map_smul' := fun r z => by
        change (Scheme.Modules.Hom.app e.hom ⊤).hom
            (((pullback.snd (p1Over k).hom
              (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberResidueMap t).hom r
              • z) =
          ((pullback.snd C.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberResidueMap t).hom r
            • (show Γ((pullback.snd C.hom
                (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberModule t L, ⊤) from
              (Scheme.Modules.Hom.app e.hom ⊤).hom z)
        rw [hres]
        exact Scheme.Modules.Hom.app_smul e.hom _ z }
  -- transport the `κ(t)`-dimension
  simp only [Scheme.Hom.fiberH0]
  exact le.finrank_eq

/-- The fibre embedding `ℙ¹_t ⟶ ℙ¹_A` is an affine morphism: it is the base
change of the affine `Spec κ(t) ⟶ Spec A` (a morphism of affine schemes). -/
instance isAffineHom_p1BaseChange_fiberι (t : Spec (CommRingCat.of A)) :
    IsAffineHom ((pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberι t) :=
  MorphismProperty.pullback_fst (P := @IsAffineHom) _ _
    (inferInstance : IsAffineHom
      ((Spec (CommRingCat.of A)).fromSpecResidueField t))

/-- **The standard 2-chart affine cover of the fibre `ℙ¹_t`**: the preimage of
the 2-chart cover of `ℙ¹_A` (`p1BaseChangeCoverSquare`) under the affine fibre
embedding `ℙ¹_t ⟶ ℙ¹_A`.  Its `π_t`-preimage is the canonical 2-affine cover
of the fibre curve `C_t` on which the pinned `hH1` needs the Čech surjectivity
witness. -/
noncomputable def p1BaseChangeFiberCoverSquare (t : Spec (CommRingCat.of A)) :
    ((pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiber t).AffineCoverMVSquare :=
  (p1BaseChangeCoverSquare A).preimage
    ((pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberι t)

/-- **The pinned `hH1`, reduced to Čech cover-independence on the fibre curve**:
given the implication `hindep` — `h¹`-vanishing of `L_t` on
*some* 2-affine cover of `C_t` gives the surjectivity witness on the canonical
`π_t`-preimage cover — the pinned `hH1` hypothesis of
`rigidPushforwardLocallyFree_of_p1` holds at `t`.  Everything else (the
fibre-compatibility isomorphism and the definitional Čech bridges) is proved
here; `hindep` is *exactly* the Leray/cover-independence content of transfer
item (c). -/
theorem fiberH1Vanishing_pushforward_finiteMapToP1BaseChange_of_coverIndependence
    [HasFiniteMapToP1 C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L) (t : Spec (CommRingCat.of A))
    (hindep : (pullback.snd C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t →
      Function.Surjective
        ⇑(((p1BaseChangeFiberCoverSquare A t).preimage
            (finiteMapToP1FiberMap A C t)).moduleSectionDiff
          ((pullback.snd C.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberModule t L)))
    (hvan : (pullback.snd C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t) :
    (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing
      ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) t :=
  fiberH1Vanishing_pushforward_finiteMapToP1BaseChange_of_preimage_cover A C L hL t
    (p1BaseChangeFiberCoverSquare A t) (hindep hvan)

/-- **`hH1` for the B3 reduction, VERBATIM against the pinned shape**
(`rigidPushforwardLocallyFree_of_p1`, `RigidPushforward.lean`): fibrewise
Čech `h¹`-vanishing of the invertible `L` on the fibre curve `C_t` transfers
to the finite pushforward `(π_A)_* L` on the fibre `ℙ¹_t`, at every scheme
point `t`.

The `hindep` obligation of
`fiberH1Vanishing_pushforward_finiteMapToP1BaseChange_of_coverIndependence`
is discharged by the QC-vanishing keystone: the fibre restriction
`L_t` is quasi-coherent (`Scheme.Hom.fiberModule_isQuasicoherent`), so
`Ȟ¹`-vanishing on *some* 2-affine cover of `C_t` (the ∃-form `hvan`) forces
the surjectivity witness on the specific `π_t`-preimage cover
(`Scheme.Hom.FiberH1Vanishing.surjective_moduleSectionDiff`, Leray both ways
through the cover-free `H¹(C_t, L_t)` over `κ(t)`;
`Cohomology/StructureSheafModuleK/QuasicoherentDegreeOneVanishing.lean`).
This discharges the cover-independence obligation recorded in
`RigidPushforward.lean`. -/
theorem pushforward_finiteMapToP1BaseChange_fiberH1 [HasFiniteMapToP1 C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (t : Spec (CommRingCat.of A)) (hL : LineBundle.IsLocallyTrivial L)
    (hvan : (pullback.snd C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t) :
    (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing
      ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) t := by
  haveI := hL.isFinitePresentation
  haveI : ((pullback.snd C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberModule t L).IsQuasicoherent :=
    Scheme.Hom.fiberModule_isQuasicoherent _ t L
  exact fiberH1Vanishing_pushforward_finiteMapToP1BaseChange_of_coverIndependence
    A C L hL t
    (fun hv => hv.surjective_moduleSectionDiff
      ((p1BaseChangeFiberCoverSquare A t).preimage (finiteMapToP1FiberMap A C t)))
    hvan

/-- **The B3 transfer package**: with `hfp`, `hflat`, `hH0` and `hH1` all
discharged above, B3 local freeness for the constant curve `C_A` follows from
the ℙ¹ engine alone:
for every finitely generated `k`-algebra `A`, `P1RigidPushforwardStatement`
implies `RigidPushforwardLocallyFree C A`.  (This is the locally-free half
only; the gate itself is assembled — both fields — in
`Picard/RigidPushforwardGammaBaseChange.lean`.) -/
theorem rigidPushforwardLocallyFree_of_p1Engine [HasFiniteMapToP1 C]
    [Algebra.FiniteType k A] (hP1 : P1RigidPushforwardStatement k A) :
    Scheme.RigidPushforwardLocallyFree C A :=
  rigidPushforwardLocallyFree_of_p1 A C hP1
    (fun L hL => pushforward_finiteMapToP1BaseChange_isFinitePresentation A C L hL)
    (fun L hL => pushforward_finiteMapToP1BaseChange_coherentSheafFlat A C L hL)
    (fun L t hL hvan => pushforward_finiteMapToP1BaseChange_fiberH1 A C L t hL hvan)
    (fun L t hL => pushforward_finiteMapToP1BaseChange_fiberH0 A C L t hL)

end Adelic

end AlgebraicGeometry
