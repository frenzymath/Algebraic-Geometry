/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivPushforwardFlat
import AlgebraicJacobian.Picard.AffineOpenStalkLocalization
import AlgebraicJacobian.Picard.LineBundleCoherence
import AlgebraicJacobian.Cohomology.QcohTildeSections

/-!
# The universal locally closed rank locus

This file upgrades the matrix-defined flattening stratum from flatness to the
rank-indexed local-freeness predicate used by the Grassmannian construction.
In rank one it is therefore the universal locally closed locus on which the
module becomes an invertible sheaf.

The construction is unconditional.  It uses the existing presentation charts
and their entry-ideal strata; it does not assume Picard representability or a
rational point.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

variable {X : Scheme.{u}}

/-- An explicit rank-`e` basis of sections on an affine open trivialises the
corresponding restriction of a quasi-coherent module. -/
theorem pullback_isFreeOfRank_of_sectionsEquiv
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (e : ℕ) (E : (Fin e → Γ(X, U)) ≃ₗ[Γ(X, U)] Γ(M, U)) :
    Nonempty ((pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin e))) := by
  let N := (pullback hU.fromSpec).obj M
  haveI : N.IsQuasicoherent := pullback_isQuasicoherent_hom hU.fromSpec M inferInstance
  haveI : IsIso (fromSpecRestrictTopHom M hU) :=
    fromSpecRestrictTopHom_isIso M hU
  haveI : IsIso ((restrictFunctorIsoPullback hU.fromSpec).hom.app M) := inferInstance
  haveI : IsIso
      (moduleSpecΓFunctor.map ((restrictFunctorIsoPullback hU.fromSpec).hom.app M)) :=
    inferInstance
  let sectionHom : ModuleCat.of Γ(X, U) Γ(M, U) ⟶ moduleSpecΓFunctor.obj N :=
    fromSpecRestrictTopHom M hU ≫
      moduleSpecΓFunctor.map ((restrictFunctorIsoPullback hU.fromSpec).hom.app M)
  haveI : IsIso sectionHom := by
    dsimp only [sectionHom]
    exact IsIso.comp_isIso' (fromSpecRestrictTopHom_isIso M hU) inferInstance
  haveI : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  let eIndex : (ULift.{u} (Fin e) →₀ Γ(X, U)) ≃ₗ[Γ(X, U)] (Fin e → Γ(X, U)) :=
    (Finsupp.linearEquivFunOnFinite Γ(X, U) Γ(X, U) (ULift.{u} (Fin e))).trans
      (LinearEquiv.funCongrLeft Γ(X, U) Γ(X, U) Equiv.ulift.symm)
  let eSections : (ULift.{u} (Fin e) →₀ Γ(X, U)) ≃ₗ[Γ(X, U)]
      moduleSpecΓFunctor.obj N :=
    eIndex.trans (E.trans (asIso sectionHom).toLinearEquiv)
  let eSpec : N ≅
      SheafOfModules.free (R := (Spec Γ(X, U)).ringCatSheaf) (ULift.{u} (Fin e)) :=
    qcoh_iso_tilde_sections N ≪≫
      (tilde.functor Γ(X, U)).mapIso eSections.toModuleIso.symm ≪≫
      tildeFinsupp (ULift.{u} (Fin e))
  have hcomp : hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
    rw [← hU.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  exact ⟨
    ((pullbackCongr hcomp).symm.app M) ≪≫
      ((pullbackComp hU.isoSpec.hom hU.fromSpec).app M).symm ≪≫
      (pullback hU.isoSpec.hom).mapIso eSpec ≪≫
      pullbackFreeIso hU.isoSpec.hom (ULift.{u} (Fin e))⟩

/-- The entry-ideal stratum is locally free of its prescribed rank.  This is
the locally-free strengthening of `coherentSheafFlat_stratum`. -/
theorem stratum_isLocallyFreeOfRank
    (M : X.Modules) [M.IsQuasicoherent] {e : ℕ} (hcov : ChartsCover M e) :
    SheafOfModules.IsLocallyFreeOfRank
      ((pullback (stratumι M e hcov)).obj M) e := by
  let N := (pullback (stratumι M e hcov)).obj M
  haveI : N.IsQuasicoherent :=
    pullback_isQuasicoherent_hom (stratumι M e hcov) M inferInstance
  let I := {V : X.affineOpens // IsPresentationChart M e V}
  let W : I → (stratum M e hcov).Opens := fun j =>
    stratumι M e hcov ⁻¹ᵁ j.1.1
  refine ⟨I, W, ?_, fun j => ?_⟩
  · rw [eq_top_iff]
    intro z _
    obtain ⟨V, hzV, hchart⟩ := hcov ((stratumι M e hcov).base z)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hchart⟩, hzV⟩
  · obtain ⟨mm, ⟨P⟩⟩ := j.2
    have hW : IsAffineOpen (W j) :=
      j.1.2.preimage (stratumι M e hcov)
    obtain ⟨P', hP'⟩ := exists_matrixPresentation_pullback_sections
      (stratumι M e hcov) M j.1.2 hW le_rfl P
    have h0 : P'.relMatrix = 0 := by
      rw [hP']
      ext a b
      simp only [Matrix.map_apply, Matrix.zero_apply]
      have hmem : ((stratumι M e hcov).app j.1.1).hom (P.relMatrix a b) = 0 := by
        have hker : P.relMatrix a b ∈
            RingHom.ker (((strataData M e hcov).subschemeι.app j.1.1).hom) := by
          rw [Scheme.IdealSheafData.ker_subschemeι_app]
          change P.relMatrix a b ∈ strataIdeal M e j.1
          rw [strataIdeal_eq_entryIdeal M P]
          exact P.relMatrix_mem_entryIdeal a b
        exact RingHom.mem_ker.mp hker
      change ((stratumι M e hcov).appLE j.1.1 (W j) le_rfl).hom
          (P.relMatrix a b) = 0
      have happ : ((stratumι M e hcov).appLE j.1.1 (W j) le_rfl).hom
          (P.relMatrix a b) =
          ((stratum M e hcov).presheaf.map (homOfLE le_rfl).op).hom
            (((stratumι M e hcov).app j.1.1).hom (P.relMatrix a b)) := rfl
      rw [happ, hmem, map_zero]
    exact pullback_isFreeOfRank_of_sectionsEquiv N hW e (P'.projEquiv h0)

/-- Rank-indexed local freeness transports along an isomorphism of module
sheaves, in arbitrary universe. -/
theorem isLocallyFreeOfRank_of_iso_general {M N : X.Modules} (E : M ≅ N)
    {e : ℕ} (hN : SheafOfModules.IsLocallyFreeOfRank N e) :
    SheafOfModules.IsLocallyFreeOfRank M e := by
  obtain ⟨I, U, hU, hfree⟩ := hN
  exact ⟨I, U, hU, fun i => ⟨(pullback (U i).ι).mapIso E ≪≫ (hfree i).some⟩⟩

/-- The canonical locally closed rank stratum carries a locally free module
of exactly the indexed rank. -/
theorem rankStratum_isLocallyFreeOfRank {S : Scheme.{u}}
    (F : S.Modules) [F.IsQuasicoherent] (e : ℕ) :
    SheafOfModules.IsLocallyFreeOfRank
      ((pullback (rankStratumι F e)).obj F) e := by
  let G := (pullback (chartLocus F e).ι).obj F
  haveI : G.IsQuasicoherent :=
    pullback_isQuasicoherent_hom (chartLocus F e).ι F inferInstance
  let hcov : ChartsCover G e := chartsCover_chartLocus F e
  have hfree := stratum_isLocallyFreeOfRank G hcov
  let E : (pullback (rankStratumι F e)).obj F ≅
      (pullback (stratumι G e hcov)).obj G :=
    ((pullbackComp (stratumι G e hcov) (chartLocus F e).ι).app F).symm
  exact isLocallyFreeOfRank_of_iso_general E hfree

/-- The locally closed locus on which a module has rank one. -/
noncomputable abbrev lineBundleLocus {S : Scheme.{u}} (F : S.Modules)
    [F.IsQuasicoherent] : Scheme.{u} :=
  rankStratum F 1

/-- The immersion of the rank-one locus into its base. -/
noncomputable abbrev lineBundleLocusι {S : Scheme.{u}} (F : S.Modules)
    [F.IsQuasicoherent] : lineBundleLocus F ⟶ S :=
  rankStratumι F 1

instance {S : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent] :
    IsImmersion (lineBundleLocusι F) := inferInstance

/-- The support of the rank-one locus is exactly the point-rank-one set. -/
theorem mem_range_lineBundleLocusι_iff {S : Scheme.{u}}
    [IsLocallyNoetherian S] (F : S.Modules) [F.IsFinitePresentation] (s : S) :
    s ∈ Set.range (lineBundleLocusι F).base ↔ pointRank S F s = 1 :=
  mem_range_rankStratumι_iff F 1 s

/-- On the rank-one locus the pulled-back module is an invertible sheaf. -/
theorem lineBundleLocus_isLocallyTrivial {S : Scheme.{u}}
    (F : S.Modules) [F.IsQuasicoherent] :
    LineBundle.IsLocallyTrivial
      ((pullback (lineBundleLocusι F)).obj F) := by
  obtain ⟨I, U, hU, hfree⟩ := rankStratum_isLocallyFreeOfRank F 1
  apply LineBundle.isLocallyTrivial_of_pointwise_free_one
  intro x
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U i, hxi, hfree i⟩

/-- A locally trivial line bundle is flat over its base.  This is the
representation-facing form of the chart-local flatness recorded by
`LineBundle.IsLocallyTrivial`: on a trivialising affine chart its section
module is linearly equivalent to the coordinate ring. -/
theorem coherentSheafFlat_id_of_isLocallyTrivial {S : Scheme.{u}}
    {F : S.Modules} (hF : LineBundle.IsLocallyTrivial F) :
    Scheme.CoherentSheafFlat (𝟙 S) F := by
  haveI : F.IsFinitePresentation := hF.isFinitePresentation
  obtain ⟨I, U, hUaff, hUtop, hUiso⟩ := hF.exists_trivializing_cover
  apply coherentSheafFlat_id_of_charts F U hUaff
  · intro s
    have hs : s ∈ iSup U := by rw [hUtop]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hs
  · intro i
    let eRes : F.restrict (U i).ι ≅
        (restrictFunctor (U i).ι).obj
          (SheafOfModules.unit S.ringCatSheaf) :=
      (hUiso i).some ≪≫
        ((restrictFunctorIsoPullback (U i).ι).app
          (SheafOfModules.unit S.ringCatSheaf) ≪≫ pullbackUnitIso (U i).ι).symm
    let eΓ : Γ(F, U i) ≃ₗ[Γ(S, U i)] Γ(S, U i) :=
      sectionLinearEquivOfRestrictIso (U i) eRes
    exact Module.Flat.of_linearEquiv (M := Γ(S, U i)) eΓ

/-- Every fibre of a locally trivial line bundle has dimension one. -/
theorem pointRank_eq_one_of_isLocallyTrivial {S : Scheme.{u}}
    {F : S.Modules} [F.IsQuasicoherent]
    (hF : LineBundle.IsLocallyTrivial F) (s : S) :
    pointRank S F s = 1 := by
  obtain ⟨U, hsU, hUaff, ⟨eU⟩⟩ := hF s
  let V : S.affineOpens := ⟨U, hUaff⟩
  have hsV : s ∈ V.1 := hsU
  rw [pointRank_eq_chartFiberRank F (V := V) s hsV]
  let p : PrimeSpectrum Γ(S, U) := hUaff.primeIdealOf ⟨s, hsU⟩
  haveI : Nontrivial Γ(S, U) := PrimeSpectrum.nontrivial p
  change p.asIdeal.fiberRank Γ(F, U) = 1
  let eRes : F.restrict U.ι ≅
      (restrictFunctor U.ι).obj (SheafOfModules.unit S.ringCatSheaf) :=
    eU ≪≫ ((restrictFunctorIsoPullback U.ι).app
      (SheafOfModules.unit S.ringCatSheaf) ≪≫ pullbackUnitIso U.ι).symm
  let eΓ : Γ(F, U) ≃ₗ[Γ(S, U)] Γ(S, U) :=
    sectionLinearEquivOfRestrictIso U eRes
  rw [Ideal.fiberRank_congr _ eΓ]
  exact (Ideal.finrank_fiber_eq_rankAtStalk _).trans
    (congrFun (Module.rankAtStalk_self (R := Γ(S, U))) p)

/-- Universal factorisation through the locally closed rank-one locus.  The
antecedent is the existing flattening condition: flat pullback with constant
point rank one. -/
theorem existsUnique_factor_lineBundleLocus {S : Scheme.{u}}
    [IsLocallyNoetherian S] (F : S.Modules) [F.IsFinitePresentation]
    {T : Scheme.{u}} (φ : T ⟶ S)
    (hflat : Scheme.CoherentSheafFlat (𝟙 T) ((pullback φ).obj F))
    (hrank : ∀ t : T, pointRank S F (φ.base t) = 1) :
    ∃! l : T ⟶ lineBundleLocus F, l ≫ lineBundleLocusι F = φ :=
  existsUnique_factor_rankStratum F 1 φ hflat hrank

/-- Universal factorisation through the line-bundle locus, stated only in
terms of the predicate represented by that locus.  Local triviality of the
pullback supplies both flatness and constant fibre rank one. -/
theorem existsUnique_factor_lineBundleLocus_of_isLocallyTrivial
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : S.Modules) [F.IsFinitePresentation]
    {T : Scheme.{u}} (φ : T ⟶ S)
    (hline : LineBundle.IsLocallyTrivial ((pullback φ).obj F)) :
    ∃! l : T ⟶ lineBundleLocus F, l ≫ lineBundleLocusι F = φ := by
  haveI : ((pullback φ).obj F).IsQuasicoherent :=
    pullback_isQuasicoherent_hom φ F inferInstance
  apply existsUnique_factor_lineBundleLocus F φ
    (coherentSheafFlat_id_of_isLocallyTrivial hline)
  intro t
  rw [← pointRank_pullback φ F t]
  exact pointRank_eq_one_of_isLocallyTrivial hline t

end Modules

namespace LocallyFreeQuotient

variable {S X : Scheme.{u}} {π : X ⟶ S} {T : Over S}

/-- The evaluation on `X_T` attached to a Grassmannian quotient of `π_* L`.

The base-change map sends `T^*(π_*L)` to `pr_{T*}(pr_X^*L)`.  Precomposing
with the kernel inclusion of the Grassmannian quotient and transposing along
`pr_T^* ⊣ pr_{T*}` gives the displayed map.  Its kernel is not itself the
divisor ideal: the divisor candidate is obtained from its cokernel below. -/
noncomputable def kernelEvaluation (L : X.Modules) {d : ℕ}
    (q : LocallyFreeQuotient ((Modules.pushforward π).obj L) d T) :
    (Modules.pullback (pullback.snd π T.hom)).obj (kernel q.q) ⟶
      (Modules.pullback (pullback.fst π T.hom)).obj L :=
  ((Modules.pullbackPushforwardAdjunction
    (pullback.snd π T.hom)).homEquiv _ _).symm
    (kernel.ι q.q ≫
      pushforwardBaseChangeMap π T.hom (pullback.snd π T.hom)
        (pullback.fst π T.hom) pullback.condition L)

/-- The quotient on `X_T` reconstructed from a Grassmannian quotient: take the
cokernel of `kernelEvaluation`.  The later D3 locus is where this quotient is
a divisor quotient and its kernel is invertible. -/
noncomputable def candidateQuotient (L : X.Modules) {d : ℕ}
    (q : LocallyFreeQuotient ((Modules.pushforward π).obj L) d T) :
    (Modules.pullback (pullback.fst π T.hom)).obj L ⟶
      cokernel (kernelEvaluation L q) :=
  cokernel.π (kernelEvaluation L q)

/-- The reconstructed Grassmannian quotient is epimorphic by construction. -/
theorem candidateQuotient_epi (L : X.Modules) {d : ℕ}
    (q : LocallyFreeQuotient ((Modules.pushforward π).obj L) d T) :
    Epi (candidateQuotient L q) := by
  dsimp only [candidateQuotient]
  infer_instance

/-- The candidate twisted divisor ideal attached to a Grassmannian quotient. -/
noncomputable def candidateIdeal (L : X.Modules) {d : ℕ}
    (q : LocallyFreeQuotient ((Modules.pushforward π).obj L) d T) :
    (pullback π T.hom).Modules :=
  kernel (candidateQuotient L q)

end LocallyFreeQuotient

end Scheme

end AlgebraicGeometry
