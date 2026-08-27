/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.RigidPushforwardGate
import AlgebraicJacobian.Cohomology.QcohRestrictBasicOpen
import AlgebraicJacobian.Cohomology.QcohTildeSections
import AlgebraicJacobian.Cohomology.PullbackQuasicoherent
import AlgebraicJacobian.Picard.GlueDescent

/-!
# The sheaf half of the `ℙ¹` output bridge

`AlgebraicGeometry.Adelic.P1PushforwardLocalFreenessBridge`
(`Picard/RigidPushforwardGate.lean` §2) upgrades the module-level conclusion of
the `ℙ¹` Čech engine — the base-linear differential `d` surjective, `H⁰ = ker d`
finite projective over `Γ(Spec A, ⊤)`, and `H⁰` compatible with arbitrary base
change — to the *sheaf* statement that `p_* M` is locally free of rank
`p.fiberH0 M t` near every `t : Spec A`.

This file supplies the **sheaf** half of that upgrade, i.e. everything except
the rank identification:

* `AlgebraicGeometry.specAwayToSpec_opensRange` — the open range of the
  localisation morphism `Spec R_f ⟶ Spec R` is the basic open `D(f)`.
* `Module.free_and_finrank_of_isLocalizedModule` — freeness and rank pass
  between two models of the same localisation of a module.
* `AlgebraicGeometry.free_finite_finrank_gammaPullbackTop` — semilinear
  transport along an open immersion of affines `j : Spec S ⟶ Spec R`: freeness,
  finiteness and the rank of `Γ(N, j ''ᵁ ⊤)` over `Γ(Spec R, j ''ᵁ ⊤)` pass to
  `Γ(j^* N, ⊤)` over `S`.
* `AlgebraicGeometry.nonempty_pullbackIsoFree_of_free_sections` — a
  quasi-coherent module whose sections are free of rank `n` *is* the free sheaf
  of rank `n`.
* `AlgebraicGeometry.exists_free_restrict_of_finite_projective_sections` — the
  crux: a quasi-coherent module on `Spec R` whose global sections are finite
  projective is free on a basic open neighbourhood of any prime, with the
  free rank read off as `Module.rankAtStalk` at that prime.  The variant
  `…_sections'` states the same with `Γ`-spelled hypotheses and the rank
  packaged as `AlgebraicGeometry.sectionsRankAtStalk`.
* `AlgebraicGeometry.module_finite_top_of_gammaSpecTop` and its projective
  companion — change of scalars along `Γ(Spec R, ⊤) ≅ R`.
* `AlgebraicGeometry.Adelic.pushforwardTop_linearEquiv_ker` — the identification
  `Γ(Spec A, p_* M) ≃ₗ[Γ(Spec A, ⊤)] ker d`, together with its `Module.Finite`
  and `Module.Projective` corollaries.
* `AlgebraicGeometry.Adelic.p1PushforwardLocalFreenessBridge_of_rank` — the
  conditional assembly: the bridge `Prop` follows from the above once the
  pointwise rank of `Γ(Spec A, p_* M)` is known to be `p.fiberH0 M t`.  The rank
  hypothesis is a fibre-chart base-change comparison and is *not* proved here.

Mathematically nothing new happens: the content is Stacks 00NX ("finite
projective is locally free"), Stacks 01HV/01I8 (the affine structure theorem,
already in the tree as `qcoh_iso_tilde_sections`) and the sheaf-condition
identification `Γ(X, M) ≅ ker d` of the two-chart Čech complex.

Sources: Stacks 00NX, 00NV, 01HV, 01I8, 01XJ; Mumford, *Abelian Varieties*,
II §5; EGA III 7.9.9; Hartshorne III 12.11; Kleiman, *The Picard scheme*
(FGA Explained), §5.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ## §1. The open range of the localisation morphism -/

/-- **The range of `Spec R_f ⟶ Spec R` is the basic open `D(f)`** (Stacks 00E4).
The morphism `specAwayToSpec f` is by definition the isomorphism
`Spec R_f ≅ D(f)` (`basicOpenIsoSpecAway f`, inverted) followed by the open
immersion `D(f) ↪ Spec R`, so its set-theoretic range is the range of that
immersion, namely `D(f)` itself (`Scheme.Opens.range_ι`). -/
theorem specAwayToSpec_opensRange {R : CommRingCat.{u}} (f : R) :
    (specAwayToSpec f).opensRange = specBasicOpen f :=
  (Scheme.Hom.opensRange_comp_of_isIso (basicOpenIsoSpecAway f).inv
    (specBasicOpen f).ι).trans (specBasicOpen f).opensRange_ι

/-! ## §2. Two localisations of the same module compare semilinearly

The engine `Module.FinitePresentation.exists_free_localizedModule_powers` produces
freeness of the *canonical* localisation `LocalizedModule (powers f) M` over the
*canonical* localisation `Localization (powers f)`; the geometric side works with
`Γ(N, D(f))` over `Γ(Spec R, D(f))`, which is another model of the same
localisation.  Comparing the two is the standard `IsLocalization.algEquiv` /
`IsLocalizedModule.iso` pair, packaged as a *semilinear* equivalence over that
ring isomorphism — the pattern of `Module.mem_freeLocus_of_isLocalization`
(mathlib `RingTheory/Spectrum/Prime/FreeLocus.lean`). -/

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- **Freeness and rank pass between two models of the same localisation**
(Stacks 02C4, 00CP).  If `Rₛ` is a localisation of `R` at `S` and `g : M → Mₛ`
exhibits `Mₛ` as the localisation of `M` at `S` (compatibly, i.e. as an
`Rₛ`-module in a scalar tower over `R`), then `Mₛ` is `Rₛ`-free exactly when the
canonical model `LocalizedModule S M` is `Localization S`-free, with the same
rank.

The comparison is the `IsLocalization.algEquiv`-semilinear upgrade of
`IsLocalizedModule.iso`: `t = a/s` acts on `Mₛ` by the unique map inverting `s`,
so the `R`-linear comparison is automatically semilinear.  Freeness transports by
`Module.Free.of_equiv`, the rank by `rank_eq_of_equiv_equiv`. -/
theorem _root_.Module.free_and_finrank_of_isLocalizedModule {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] (S : Submonoid R) (Rₛ : Type u) [CommRing Rₛ] [Algebra R Rₛ]
    [IsLocalization S Rₛ] (Mₛ : Type u) [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ]
    [IsScalarTower R Rₛ Mₛ] (g : M →ₗ[R] Mₛ) [IsLocalizedModule S g]
    [Module.Free (Localization S) (LocalizedModule S M)] :
    Module.Free Rₛ Mₛ ∧
      Module.finrank Rₛ Mₛ = Module.finrank (Localization S) (LocalizedModule S M) := by
  set e := (IsLocalization.algEquiv S (Localization S) Rₛ).toRingEquiv with he
  have E : LocalizedModule S M ≃ₛₗ[(e : Localization S →+* Rₛ)] Mₛ := by
    refine { __ := IsLocalizedModule.iso S g, map_smul' := ?_ }
    intro r x
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq S r
    apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)).1
    simp only [e, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      Module.algebraMap_end_apply, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe,
      IsLocalization.algEquiv_apply, IsLocalization.map_id_mk']
    simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul]
  refine ⟨Module.Free.of_equiv E, ?_⟩
  exact (congrArg Cardinal.toNat
    (rank_eq_of_equiv_equiv (e : Localization S → Rₛ) E.toAddEquiv e.bijective
      (fun r m => map_smulₛₗ E r m))).symm

/-- **The section restriction `Γ(Spec R, N) ⟶ Γ(D(f), N)` as an `R`-linear map.**
A named spelling of the `D(f)`-component of the presheaf restriction of a module
on `Spec R`, in the `Γ(N, -)` (rather than `modulesSpecToSheaf`) presentation, so
that the localisation instance below is found by type-class search.  Stacks
01HV(4). -/
noncomputable def sectionResBasicOpen {R : CommRingCat.{u}} (N : (Spec R).Modules) (f : R) :
    ↑(moduleSpecΓFunctor.obj N) →ₗ[R] ↑Γ(N, specBasicOpen f) :=
  ((modulesSpecToSheaf.obj N).presheaf.map
    (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom

/-- **The sections over `D(f)` of a quasi-coherent module are the localisation of
the global sections at the powers of `f`** (Stacks 01HV(4)/01I8).  Instance form
of the keystone `qcoh_section_isLocalizedModule`
(`Cohomology/QcohTildeSections.lean`), stated for the named map
`sectionResBasicOpen`. -/
instance isLocalizedModule_sectionResBasicOpen {R : CommRingCat.{u}} (N : (Spec R).Modules)
    [N.IsQuasicoherent] (f : R) :
    IsLocalizedModule (Submonoid.powers f) (sectionResBasicOpen N f) :=
  qcoh_section_isLocalizedModule N f

/-! ## §3. The crux: a finite projective quasi-coherent module is free near a point -/

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- **Freeness, finiteness and rank of the sections of a pullback along an open
immersion of affines.**  For an open immersion `j : Spec S ⟶ Spec R` and a module
`N` on `Spec R`, the global sections of `j^* N` over `S` are obtained from the
sections of `N` over the image open `j(Spec S)` by transport of structure along
the section comparison `Γ(j^* N, ⊤) ≅ Γ(N, j ''ᵁ ⊤)`
(`Scheme.Modules.gammaPullbackImageIso`), which is semilinear over the ring
isomorphism `S ≃+* Γ(Spec R, j ''ᵁ ⊤)` obtained by composing `ΓSpecIso` with
`Scheme.Modules.gammaImageRingEquiv`.  Hence freeness, finiteness and the rank
transfer verbatim.

This is the bookkeeping step that turns the *algebraic* statement "`M_f` is free
over `R_f`" into the *geometric* statement "`N|_{D(f)}` has free sections", with
no mathematical content beyond the fact that an open immersion of affines
identifies section rings and section modules over its image. -/
theorem free_finite_finrank_gammaPullbackTop {R S : CommRingCat.{u}} (j : Spec S ⟶ Spec R)
    [IsOpenImmersion j] (N : (Spec R).Modules)
    (hfree : Module.Free Γ(Spec R, j ''ᵁ (⊤ : (Spec S).Opens))
      Γ(N, j ''ᵁ (⊤ : (Spec S).Opens)))
    (hfin : Module.Finite Γ(Spec R, j ''ᵁ (⊤ : (Spec S).Opens))
      Γ(N, j ''ᵁ (⊤ : (Spec S).Opens))) :
    Module.Free S Γ((Scheme.Modules.pullback j).obj N, ⊤) ∧
      Module.Finite S Γ((Scheme.Modules.pullback j).obj N, ⊤) ∧
      Module.finrank S Γ((Scheme.Modules.pullback j).obj N, ⊤)
        = Module.finrank Γ(Spec R, j ''ᵁ (⊤ : (Spec S).Opens))
            Γ(N, j ''ᵁ (⊤ : (Spec S).Opens)) := by
  let σ : S ≃+* Γ(Spec R, j ''ᵁ (⊤ : (Spec S).Opens)) :=
    (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv.symm.trans
      (Scheme.Modules.gammaImageRingEquiv j (⊤ : (Spec S).Opens))
  let E : Γ((Scheme.Modules.pullback j).obj N, ⊤) ≃+ Γ(N, j ''ᵁ (⊤ : (Spec S).Opens)) :=
    (Scheme.Modules.gammaPullbackImageIso j N (⊤ : (Spec S).Opens)).addCommGroupIsoToAddEquiv
  have hmid : (Spec S).presheaf.map ((⊤ : (Spec S).Opens).leTop).op = 𝟙 _ := by
    rw [show ((⊤ : (Spec S).Opens).leTop) = 𝟙 (⊤ : (Spec S).Opens) from rfl]
    exact (Spec S).presheaf.map_id _
  have hsemi : ∀ (r : S) (x : Γ((Scheme.Modules.pullback j).obj N, ⊤)),
      E (r • x) = σ r • E x := by
    intro r x
    change (Scheme.Modules.gammaPullbackImageIso j N (⊤ : (Spec S).Opens)).hom.hom (r • x) = _
    rw [Scheme.Modules.smul_Spec_def (M := (Scheme.Modules.pullback j).obj N) r x, hmid]
    exact Scheme.Modules.gammaPullbackImageIso_hom_semilinear j N _ _ x
  refine ⟨?_, ?_, ?_⟩
  · have Esl : Γ((Scheme.Modules.pullback j).obj N, ⊤)
        ≃ₛₗ[(σ : S →+* Γ(Spec R, j ''ᵁ (⊤ : (Spec S).Opens)))]
        Γ(N, j ''ᵁ (⊤ : (Spec S).Opens)) := { __ := E, map_smul' := hsemi }
    exact (Module.Free.iff_of_equiv Esl).mpr hfree
  · exact Module.Finite.of_addEquiv_semilinear (σ : S →+* _) σ.surjective E hsemi hfin
  · exact congrArg Cardinal.toNat
      (rank_eq_of_equiv_equiv (σ : S → Γ(Spec R, j ''ᵁ (⊤ : (Spec S).Opens))) E σ.bijective hsemi)

/-- **A quasi-coherent module whose sections are free of rank `n` is the free
sheaf of rank `n`** (Stacks 01I8 + 01HV).  For an open immersion of affines
`j : Spec S ⟶ Spec R`, if `Γ(j^* N, ⊤)` is a free `S`-module of rank `n` (and `S`
is nontrivial, so that the rank is the cardinality of a basis), then `j^* N` is
isomorphic to `𝒪_{Spec S}^{⊕ n}`.

Proof: quasi-coherence is stable under pullback
(`pullback_isQuasicoherent_hom`), so the tilde–Γ counit of `j^* N` is invertible
(`isIso_fromTildeΓ_of_quasicoherent`) and `j^* N ≅ (Γ(j^* N, ⊤))^~`
(`qcoh_iso_tilde_sections`); a rank-`n` basis identifies the module of sections
with `S^{⊕ n}`, whose tilde is the free sheaf (`tildeFinsupp`). -/
theorem nonempty_pullbackIsoFree_of_free_sections {R S : CommRingCat.{u}} (j : Spec S ⟶ Spec R)
    [IsOpenImmersion j] (N : (Spec R).Modules) (hN : N.IsQuasicoherent) (n : ℕ)
    (hnt : Nontrivial S)
    (hfree : Module.Free S Γ((Scheme.Modules.pullback j).obj N, ⊤))
    (hfin : Module.Finite S Γ((Scheme.Modules.pullback j).obj N, ⊤))
    (hrank : Module.finrank S Γ((Scheme.Modules.pullback j).obj N, ⊤) = n) :
    Nonempty ((Scheme.Modules.pullback j).obj N ≅
      _root_.SheafOfModules.free (R := (Spec S).ringCatSheaf) (ULift.{u} (Fin n))) := by
  haveI := hnt
  haveI : ((Scheme.Modules.pullback j).obj N).IsQuasicoherent :=
    AlgebraicGeometry.pullback_isQuasicoherent_hom j N hN
  haveI : IsIso (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pullback j).obj N)) :=
    AlgebraicGeometry.isIso_fromTildeΓ_of_quasicoherent ((Scheme.Modules.pullback j).obj N)
  have eK : (Scheme.Modules.pullback j).obj N
      ≅ tilde (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback j).obj N)) :=
    qcoh_iso_tilde_sections ((Scheme.Modules.pullback j).obj N)
  haveI := hfree
  haveI := hfin
  let b : Module.Basis (ULift.{u} (Fin n)) S Γ((Scheme.Modules.pullback j).obj N, ⊤) :=
    (Module.finBasisOfFinrankEq S Γ((Scheme.Modules.pullback j).obj N, ⊤) hrank).reindex
      Equiv.ulift.symm
  have eM : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback j).obj N)
      ≅ ModuleCat.of S (ULift.{u} (Fin n) →₀ S) := LinearEquiv.toModuleIso b.repr
  exact ⟨eK ≪≫ (tilde.functor S).mapIso eM ≪≫ tildeFinsupp (ULift.{u} (Fin n))⟩

/-- **A2 (the crux): a quasi-coherent module with finite projective global
sections is free on a neighbourhood of every point, of rank the stalk rank**
(Stacks 00NX, 05P1).  Let `N` be a quasi-coherent module on `Spec R` whose global
sections `M = Γ(Spec R, N)` are a finite projective `R`-module, and let
`t ∈ Spec R`.  Then there is an open `U ∋ t` with
`N|_U ≅ 𝒪_U^{⊕ rank_t M}`.

The proof is the standard "finite projective is locally free" argument, run
through the affine dictionary:

* `M` is finitely presented (`Module.finitePresentation_of_projective`) and flat,
  so `M_t` is free over the local ring `R_t`
  (`Module.free_of_flat_of_isLocalRing`);
* freeness spreads out from the stalk to a basic open
  (`Module.FinitePresentation.exists_free_localizedModule_powers`), producing
  `f ∉ t` with `M_f` free of rank `rank_t M` over `R_f`;
* `Γ(N, D(f))` *is* that localisation (`qcoh_section_isLocalizedModule`), so it is
  free of the same rank over `Γ(Spec R, D(f))`
  (`Module.free_and_finrank_of_isLocalizedModule`);
* transporting along the affine chart `D(f) ≅ Spec R_f`
  (`free_finite_finrank_gammaPullbackTop`) and applying the affine structure
  theorem (`nonempty_pullbackIsoFree_of_free_sections`) trivialises `N` on `D(f)`.

Sources: Stacks 00NX (finite projective = finite locally free), 05P1, 01I8;
Bourbaki, *Algèbre commutative* II §5.2. -/
theorem exists_free_restrict_of_finite_projective_sections {R : CommRingCat.{u}}
    (N : (Spec R).Modules) [N.IsQuasicoherent]
    [Module.Finite R (moduleSpecΓFunctor.obj N)]
    [Module.Projective R (moduleSpecΓFunctor.obj N)]
    (t : PrimeSpectrum R) :
    ∃ U : (Spec R).Opens, t ∈ U ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj N ≅
      _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf)
        (ULift.{u} (Fin (Module.rankAtStalk (moduleSpecΓFunctor.obj N) t)))) := by
  haveI : Module.FinitePresentation R (moduleSpecΓFunctor.obj N) :=
    Module.finitePresentation_of_projective R _
  haveI : Module.Free (Localization.AtPrime t.asIdeal)
      (LocalizedModule t.asIdeal.primeCompl (moduleSpecΓFunctor.obj N)) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, hrank⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    t.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap t.asIdeal.primeCompl (moduleSpecΓFunctor.obj N))
    (Localization.AtPrime t.asIdeal)
  haveI := hfree
  have hnt : Nontrivial (CommRingCat.of (Localization.Away f)) :=
    (show Localization (Submonoid.powers f) →+* Localization.AtPrime t.asIdeal from
      IsLocalization.map (M := Submonoid.powers f) (T := t.asIdeal.primeCompl) _ (RingHom.id _)
        (Submonoid.powers_le.mpr hf)).domain_nontrivial
  obtain ⟨hfrV, hrkV⟩ := Module.free_and_finrank_of_isLocalizedModule (Submonoid.powers f)
    Γ(Spec R, specBasicOpen f) Γ(N, specBasicOpen f) (sectionResBasicOpen N f)
  have hfinV : Module.Finite Γ(Spec R, specBasicOpen f) Γ(N, specBasicOpen f) :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers f) (sectionResBasicOpen N f)
  have hV : (specAwayToSpec f) ''ᵁ
      (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens) = specBasicOpen f := by
    rw [Scheme.Hom.image_top_eq_opensRange, specAwayToSpec_opensRange]
  have key : ∀ V : (Spec R).Opens, V = specBasicOpen f →
      Module.Free Γ(Spec R, V) Γ(N, V) ∧ Module.Finite Γ(Spec R, V) Γ(N, V) ∧
        Module.finrank Γ(Spec R, V) Γ(N, V)
          = Module.rankAtStalk (moduleSpecΓFunctor.obj N) t := by
    rintro V rfl
    exact ⟨hfrV, hfinV, by rw [hrkV]; exact hrank⟩
  obtain ⟨h1, h2, h3⟩ := key _ hV
  obtain ⟨hKfree, hKfin, hKrank⟩ := free_finite_finrank_gammaPullbackTop (specAwayToSpec f) N h1 h2
  obtain ⟨eFree⟩ := nonempty_pullbackIsoFree_of_free_sections (specAwayToSpec f) N
    ‹N.IsQuasicoherent› (Module.rankAtStalk (moduleSpecΓFunctor.obj N) t) hnt hKfree hKfin
    (hKrank.trans h3)
  refine ⟨specBasicOpen f, hf, ⟨?_⟩⟩
  have hcomp : (basicOpenIsoSpecAway f).hom ≫ specAwayToSpec f = (specBasicOpen f).ι := by
    change (basicOpenIsoSpecAway f).hom ≫ (basicOpenIsoSpecAway f).inv ≫ (specBasicOpen f).ι
      = (specBasicOpen f).ι
    rw [← Category.assoc, (basicOpenIsoSpecAway f).hom_inv_id, Category.id_comp]
  exact ((Scheme.Modules.pullbackCongr hcomp).symm.app N) ≪≫
    ((Scheme.Modules.pullbackComp (basicOpenIsoSpecAway f).hom (specAwayToSpec f)).app N).symm ≪≫
    (Scheme.Modules.pullback (basicOpenIsoSpecAway f).hom).mapIso eFree ≪≫
    Scheme.Modules.pullbackFreeIso (basicOpenIsoSpecAway f).hom
      (ULift.{u} (Fin (Module.rankAtStalk (moduleSpecΓFunctor.obj N) t)))

/-- **The rank of the global sections of a module on `Spec R` at a point.**
Notation for `Module.rankAtStalk Γ(N, ⊤) t`, introduced as a named definition so
that it can be *stated* over a section ring of the shape `CommRingCat.of A`
(where the `R`-module structure on `Γ(N, ⊤)`, which is restriction of scalars
along `ΓSpecIso`, is not reachable by type-class search from the reduced
carrier). -/
noncomputable def sectionsRankAtStalk {R : CommRingCat.{u}} (N : (Spec R).Modules)
    (t : PrimeSpectrum R) : ℕ :=
  Module.rankAtStalk Γ(N, (⊤ : (Spec R).Opens)) t

/-- **A2, section-ring spelling.**  `exists_free_restrict_of_finite_projective_sections`
with the finiteness and projectivity of the global sections taken as explicit
hypotheses in the `Γ(N, ⊤)` presentation and the rank written as
`sectionsRankAtStalk`.  Logically identical to the instance-argument form; this
is the shape consumed by the `ℙ¹` output bridge. -/
theorem exists_free_restrict_of_finite_projective_sections' {R : CommRingCat.{u}}
    (N : (Spec R).Modules) [N.IsQuasicoherent]
    (hfin : Module.Finite R Γ(N, (⊤ : (Spec R).Opens)))
    (hproj : Module.Projective R Γ(N, (⊤ : (Spec R).Opens)))
    (t : PrimeSpectrum R) :
    ∃ U : (Spec R).Opens, t ∈ U ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj N ≅
      _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf)
        (ULift.{u} (Fin (sectionsRankAtStalk N t)))) := by
  haveI : Module.Finite R (moduleSpecΓFunctor.obj N) := hfin
  haveI : Module.Projective R (moduleSpecΓFunctor.obj N) := hproj
  exact exists_free_restrict_of_finite_projective_sections N t

/-! ## §4. Changing scalars along `Γ(Spec R, ⊤) ≅ R`

The engine's output is a statement about `Γ(Spec A, ⊤)`-modules; §3 consumes
`A`-modules.  The two structures on `Γ(N, ⊤)` differ by restriction of scalars
along the isomorphism `ΓSpecIso : Γ(Spec A, ⊤) ≅ A`, so finiteness and
projectivity transport verbatim. -/

/-- **The `R`-action on global sections is the `Γ(Spec R, ⊤)`-action through
`ΓSpecIso`.**  Unfolding `Scheme.Modules.smul_Spec_def` at `U = ⊤`, where the
restriction map `Γ(Spec R, ⊤) ⟶ Γ(Spec R, ⊤)` is the identity. -/
theorem smul_gammaSpecTop {R : CommRingCat.{u}} (M : (Spec R).Modules) (r : R)
    (x : Γ(M, (⊤ : (Spec R).Opens))) :
    r • x = ((Scheme.ΓSpecIso R).inv.hom r) • x := by
  have hmid : (Spec R).presheaf.map ((⊤ : (Spec R).Opens).leTop).op = 𝟙 _ := by
    rw [show ((⊤ : (Spec R).Opens).leTop) = 𝟙 (⊤ : (Spec R).Opens) from rfl]
    exact (Spec R).presheaf.map_id _
  rw [Scheme.Modules.smul_Spec_def (M := M) r x, hmid]
  rfl

/-- **Finiteness of global sections descends along `ΓSpecIso`**: a module on
`Spec R` whose global sections are finite over `Γ(Spec R, ⊤)` has global sections
finite over `R`, the two actions differing by the ring isomorphism `ΓSpecIso`. -/
theorem module_finite_top_of_gammaSpecTop {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (h : Module.Finite Γ(Spec R, (⊤ : (Spec R).Opens)) Γ(M, (⊤ : (Spec R).Opens))) :
    Module.Finite R Γ(M, (⊤ : (Spec R).Opens)) :=
  Module.Finite.of_addEquiv_semilinear
    ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm : R →+* Γ(Spec R, (⊤ : (Spec R).Opens)))
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.surjective (AddEquiv.refl _)
    (fun r x => smul_gammaSpecTop M r x) h

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- **Projectivity of global sections descends along `ΓSpecIso`**, the companion
of `module_finite_top_of_gammaSpecTop`. -/
theorem module_projective_top_of_gammaSpecTop {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (h : Module.Projective Γ(Spec R, (⊤ : (Spec R).Opens)) Γ(M, (⊤ : (Spec R).Opens))) :
    Module.Projective R Γ(M, (⊤ : (Spec R).Opens)) := by
  haveI := h
  have hcancel : ∀ s : Γ(Spec R, (⊤ : (Spec R).Opens)),
      (Scheme.ΓSpecIso R).inv.hom
        ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv s) = s := by
    intro s
    have h1 := congrArg (fun φ : Γ(Spec R, (⊤ : (Spec R).Opens)) ⟶ Γ(Spec R, ⊤) => φ.hom s)
      (Scheme.ΓSpecIso R).hom_inv_id
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at h1
    exact h1
  have E : Γ(M, (⊤ : (Spec R).Opens))
      ≃ₛₗ[((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv :
        Γ(Spec R, (⊤ : (Spec R).Opens)) →+* R)] Γ(M, (⊤ : (Spec R).Opens)) := by
    refine { __ := AddEquiv.refl _, map_smul' := ?_ }
    intro s x
    exact ((congrArg (fun z : Γ(Spec R, (⊤ : (Spec R).Opens)) => z • x) (hcancel s)).symm).trans
      (smul_gammaSpecTop M ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv s) x).symm
  exact Module.Projective.of_equiv E

/-! ## §5. The pushforward sections of a module on `ℙ¹_A` -/

namespace Scheme.Modules

/-- **Global sections of a pushforward are the base-linear global sections of
the source.**  For a morphism `p : X ⟶ S` and a module `M` on `X`, the two
`Γ(S, ⊤)`-modules `Γ(S, p_* M)` and `Γ(X, M)` — the latter with the
`baseSectionsModule` structure of `Picard/RigidPushforwardP1Engine.lean` §1 —
have the same carrier (`Scheme.Modules.pushforward_obj_obj`, `rfl`) and the same
scalar action: the pushforward acts through `p.app ⊤`, the `baseSectionsModule`
through `p.appLE ⊤ ⊤ le_top`, and those two ring maps agree
(`Scheme.Hom.appLE_eq_app`, using `p ⁻¹ᵁ ⊤ = ⊤`).

This is the dictionary entry that lets a statement about the Čech complex of
`M` be read as a statement about the sheaf `p_* M`. -/
noncomputable def pushforwardTopEquivBaseSections {X S : Scheme.{u}} (p : X ⟶ S)
    (M : X.Modules) :
    letI := p.baseSectionsModule M (⊤ : X.Opens)
    Γ((Scheme.Modules.pushforward p).obj M, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(M, (⊤ : X.Opens)) :=
  letI := p.baseSectionsModule M (⊤ : X.Opens)
  { toFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun r x => by
      have h : p.appLE (⊤ : S.Opens) (⊤ : X.Opens) le_top = p.app (⊤ : S.Opens) :=
        Scheme.Hom.appLE_eq_app p
      exact congrArg (fun (φ : Γ(S, ⊤) ⟶ Γ(X, (⊤ : X.Opens))) =>
        (φ.hom r) • (show Γ(M, (⊤ : X.Opens)) from x)) h.symm
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end Scheme.Modules

namespace Adelic

open Scheme

variable {k : Type u} [Field k]

/-- **`Γ(Spec A, p_* M)` is the Čech `H⁰` of the two-chart cover of `ℙ¹_A`.**
For the projection `p : ℙ¹_A ⟶ Spec A` and a module `M` on `ℙ¹_A`, the global
sections of the pushforward are, definitionally, the global sections of `M`
(`Γ(p_* M, ⊤) = Γ(M, p ⁻¹ᵁ ⊤) = Γ(M, ⊤)`), and their `Γ(Spec A, ⊤)`-module
structure is the `baseSectionsModule` structure of the family; the sheaf
condition on the two-element affine cover `{U₁, U₂}` then identifies them with
the kernel of the base-linear Čech differential
(`AffineCoverMVSquare.globalSectionsEquivKerModuleSectionDiffBase`,
`Picard/RigidPushforwardP1Engine.lean` §2).

This is the module-to-sheaf dictionary entry consumed by the output bridge
`P1PushforwardLocalFreenessBridge`: the engine's conclusions are statements
about `ker d`, the bridge's conclusion is a statement about `p_* M`.

Sources: Stacks 01AI (the sheaf condition), 01XJ; Hartshorne III 4. -/
noncomputable def pushforwardTop_linearEquiv_ker (A : Type u) [CommRing A] [Algebra k A]
    (M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules) :
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₁
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₂
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
    Γ((Scheme.Modules.pushforward (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj M, ⊤)
      ≃ₗ[Γ(Spec (CommRingCat.of A), ⊤)]
      LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
        (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M) :=
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (⊤ : (Limits.pullback (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Opens)
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (p1BaseChangeCoverSquare A).U₁
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (p1BaseChangeCoverSquare A).U₂
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
  Scheme.Modules.pushforwardTopEquivBaseSections
      (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M ≪≫ₗ
    (p1BaseChangeCoverSquare A).globalSectionsEquivKerModuleSectionDiffBase
      (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M

/-- **Finiteness of the Čech `H⁰` transports to the pushforward sections.**
Corollary of `pushforwardTop_linearEquiv_ker`: this is the hypothesis
`Module.Finite Γ(Spec A, ⊤) (ker d)` of `P1PushforwardLocalFreenessBridge`, read
as a statement about `Γ(Spec A, p_* M)`. -/
theorem module_finite_pushforwardTop (A : Type u) [CommRing A] [Algebra k A]
    (M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hfin :
      letI := (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
          (p1BaseChangeCoverSquare A).U₁
      letI := (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
          (p1BaseChangeCoverSquare A).U₂
      letI := (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
          ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
      Module.Finite Γ(Spec (CommRingCat.of A), ⊤)
        (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M))) :
    Module.Finite Γ(Spec (CommRingCat.of A), ⊤)
      Γ((Scheme.Modules.pushforward (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj M, ⊤) := by
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (p1BaseChangeCoverSquare A).U₁
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (p1BaseChangeCoverSquare A).U₂
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
  haveI := hfin
  exact Module.Finite.equiv (pushforwardTop_linearEquiv_ker A M).symm

/-- **Projectivity of the Čech `H⁰` transports to the pushforward sections.**
Corollary of `pushforwardTop_linearEquiv_ker`, the companion of
`module_finite_pushforwardTop`.  Together they say that the engine's
module-level output is a statement about the `Γ(Spec A, ⊤)`-module
`Γ(Spec A, p_* M)`. -/
theorem module_projective_pushforwardTop (A : Type u) [CommRing A] [Algebra k A]
    (M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hproj :
      letI := (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
          (p1BaseChangeCoverSquare A).U₁
      letI := (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
          (p1BaseChangeCoverSquare A).U₂
      letI := (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
          ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
      Module.Projective Γ(Spec (CommRingCat.of A), ⊤)
        (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M))) :
    Module.Projective Γ(Spec (CommRingCat.of A), ⊤)
      Γ((Scheme.Modules.pushforward (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj M, ⊤) := by
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (p1BaseChangeCoverSquare A).U₁
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (p1BaseChangeCoverSquare A).U₂
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
  haveI := hproj
  exact Module.Projective.of_equiv (pushforwardTop_linearEquiv_ker A M).symm

/-! ## §6. The output bridge, conditional on the rank identification -/

/-- **The rank identity, stated on the engine's output.**  For a finitely
presented `M` on `ℙ¹_A` *whose Čech complex already satisfies the conclusions
of the two-term engine* — `d` surjective, `H⁰ = ker d` finite projective over
`Γ(Spec A, ⊤)`, and the formation of `H⁰` commuting with arbitrary base change
— the pointwise rank of the pushforward sections is the fibre invariant
`p.fiberH0 M t`.

**The engine hypotheses are load-bearing and must not be dropped.**  Without
them the statement is FALSE, and its consumers become vacuous.  Counterexample
(found in review): `A = k[x]`, `M = 𝒪_{ℙ¹_A}/x = coker(𝒪 --x--> 𝒪)`, which is
finitely presented.  Then `Γ(ℙ¹_A, M) = A/(x) = k`, a *torsion* `A`-module, so
`Module.rankAtStalk` at `t = (x)` takes its junk value `0`; but the fibre is
`ℙ¹_k` with `M_t = 𝒪_{ℙ¹_k}`, so `p.fiberH0 M t = 1`.  What excludes it is
exactly `Module.Projective` (`k` is not a projective `k[x]`-module): for a
finite projective module `Module.rankAtStalk_eq` identifies the stalk rank with
`finrank κ(t) (κ(t) ⊗ H⁰)`, and the base-change conclusion at `B = κ(t)`
identifies *that* with the fibre `h⁰`.

This is the remaining half of leaf 3 of the gate factorization.  It is
assembly, not new mathematics: the chart comparison
`exists_fiberChartTensorEquiv` and its restriction naturality
(`Picard/RigidPushforwardFiberChart.lean`) already identify
`ker (d ⊗ κ(t))` with the Čech `H⁰` of the fibre cover, hence with
`Γ(ℙ¹_t, M_t)`. -/
def P1RankIdentity (k : Type u) [Field k]
    (A : Type u) [CommRing A] [Algebra k A] : Prop :=
  ∀ (M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules),
    M.IsFinitePresentation →
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₁
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₂
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
    Function.Surjective ⇑((p1BaseChangeCoverSquare A).moduleSectionDiffBase
        (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M) →
    Module.Finite Γ(Spec (CommRingCat.of A), ⊤)
      (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
        (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)) →
    Module.Projective Γ(Spec (CommRingCat.of A), ⊤)
      (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
        (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)) →
    (∀ (B : Type u) [CommRing B] [Algebra Γ(Spec (CommRingCat.of A), ⊤) B],
      Function.Bijective (AlgebraicJacobian.TwoTerm.kerBaseChange
        ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M) B)) →
    ∀ t : Spec (CommRingCat.of A),
      sectionsRankAtStalk ((Scheme.Modules.pushforward (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj M) t
        = (pullback.snd (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 M t

set_option maxHeartbeats 1600000 in
-- Heartbeat headroom: the `letI`-laden bridge `Prop` forces large `isDefEq`
-- checks when the engine's kernel hypotheses are matched against the
-- pushforward-section statements (fleet recipe).
/-- **Leaf 3 (`P1PushforwardLocalFreenessBridge`) modulo the rank
identification.**  Granting that the pointwise rank of the `Γ(Spec A, ⊤)`-module
`Γ(Spec A, p_* M)` at `t` is the fibre invariant `p.fiberH0 M t`, the output
bridge of `Picard/RigidPushforwardGate.lean` §2 follows from the sheaf-theoretic
package of this file:

* `Γ(Spec A, p_* M) ≅ ker d` (`pushforwardTop_linearEquiv_ker`), so the engine's
  finiteness and projectivity of `ker d` are finiteness and projectivity of the
  pushforward sections (`module_finite_pushforwardTop`,
  `module_projective_pushforwardTop`), read over `A` rather than
  `Γ(Spec A, ⊤)` via `module_finite_top_of_gammaSpecTop` and its projective
  companion;
* `p_* M` is quasi-coherent (`Scheme.Modules.pushforward_isQuasicoherent`,
  Stacks 01XJ, `p` being quasi-compact and quasi-separated as a base change of
  the proper `ℙ¹_k ⟶ Spec k`);
* hence `p_* M` is free of rank `sectionsRankAtStalk (p_* M) t` on a
  neighbourhood of `t` (`exists_free_restrict_of_finite_projective_sections'`,
  Stacks 00NX).

The hypothesis `P1RankIdentity` is *not* proved here: it is the fibre-chart
base-change comparison `κ(t) ⊗_{Γ(Spec A,⊤)} H⁰ ≅ H⁰(ℙ¹_t, M_t)` (Stacks 02KG
in degree 0), the `B = κ(t)` case of the engine's fourth conclusion, and is the
remaining half of leaf 3.

Sources: Stacks 00NX, 01XJ, 02KG; Mumford, *Abelian Varieties*, II §5;
EGA III 7.9.9. -/
theorem p1PushforwardLocalFreenessBridge_of_rank
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hrank : P1RankIdentity k A) :
    P1PushforwardLocalFreenessBridge k A := by
  intro M hfp hsurj hfin hproj hbc t
  haveI := hfp
  haveI : ((Scheme.Modules.pushforward (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj M).IsQuasicoherent :=
    Scheme.Modules.pushforward_isQuasicoherent _ M
  have hfin' := module_finite_top_of_gammaSpecTop
    ((Scheme.Modules.pushforward (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj M)
    (module_finite_pushforwardTop A M hfin)
  have hproj' := module_projective_top_of_gammaSpecTop
    ((Scheme.Modules.pushforward (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj M)
    (module_projective_pushforwardTop A M hproj)
  obtain ⟨U, htU, hiso⟩ := exists_free_restrict_of_finite_projective_sections'
    ((Scheme.Modules.pushforward (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj M) hfin' hproj' t
  exact ⟨U, htU, (hrank M hfp hsurj hfin hproj hbc t) ▸ hiso⟩

end Adelic

end AlgebraicGeometry
