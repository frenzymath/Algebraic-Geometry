/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSupportQuasiFinite
import AlgebraicJacobian.Picard.SupportBaseChange
import AlgebraicJacobian.Picard.DivDegree
import AlgebraicJacobian.Picard.GrassmannianQuot
import AlgebraicJacobian.RiemannRoch.Ledger.StalksDVR

/-!
# Finite support of relative effective Cartier divisors

This file closes the finite-fibre input demanded by the divisor-to-Grassmannian
route.  The only public result is specialised to a family of divisors on a
proper smooth relative curve.  Its affine and line-bundle reductions are kept
private: they are implementation details, not a second projectivity API.
-/

open CategoryTheory Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Grassmannian

private noncomputable def unitEndSection'
    {X : Scheme.{u}}
    (e : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Γ(X, ⊤) :=
  e.val.app (op ⊤) (1 : X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))

set_option backward.isDefEq.respectTransparency false in
private lemma scalarEnd_unitEndSection'
    {X : Scheme.{u}}
    (e : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    scalarEnd (unitEndSection' e) = e := by
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  rw [unitHomEquiv_scalarEnd]
  refine PresheafOfModules.sections_ext _ _ (fun Y => ?_)
  change X.ringCatSheaf.obj.map (homOfLE le_top).op
      (e.val.app (op ⊤) (1 : X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) =
    e.val.app Y (1 : X.ringCatSheaf.obj.obj Y)
  have hnat := PresheafOfModules.naturality_apply e.val
    (homOfLE (le_top : Y.unop ≤ ⊤)).op
    (1 : X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))
  refine hnat.symm.trans (congrArg (fun z => e.val.app Y z) ?_)
  exact PresheafOfModules.unit_map_one X.ringCatSheaf.obj
    (homOfLE (le_top : Y.unop ≤ ⊤)).op

set_option backward.isDefEq.respectTransparency false in
private lemma smulGlobal_naturality'
    {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (a : Γ(X, ⊤)) :
    smulGlobal M a ≫ f = f ≫ smulGlobal N a := by
  ext U x
  exact Scheme.Modules.Hom.app_smul f
    (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a) x

set_option backward.isDefEq.respectTransparency false in
private lemma smulGlobal_unit_eq_scalarEnd'
    {X : Scheme.{u}} (a : Γ(X, ⊤)) :
    smulGlobal (SheafOfModules.unit X.ringCatSheaf) a = scalarEnd a := by
  ext U x
  rw [smulGlobal_app_apply]
  change X.presheaf.map (homOfLE le_top).op a • x =
    (scalarEnd a).val.app (op U) x
  rw [scalarEnd_val_app, smul_eq_mul, mul_comm]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma unitEndSection_ne_zero_of_mono'
    {X : Scheme.{u}} [IsIntegral X]
    (j : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    [Mono j] : unitEndSection' j ≠ 0 := by
  intro ha
  have hj : j = 0 := by
    rw [← scalarEnd_unitEndSection' j, ha, scalarEnd_zero]
  have hcat : 𝟙 (SheafOfModules.unit X.ringCatSheaf) = 0 := by
    rw [← cancel_mono j, hj]
    simp
  have hring := congrArg unitEndSection' hcat
  change (1 : Γ(X, ⊤)) = 0 at hring
  exact one_ne_zero hring

set_option backward.isDefEq.respectTransparency false in
private lemma smulGlobal_eq_zero_of_unit_relation'
    {X : Scheme.{u}} {F : X.Modules}
    (j : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ F) [Epi q]
    (hjq : j ≫ q = 0) :
    smulGlobal F (unitEndSection' j) = 0 := by
  apply (cancel_epi q).1
  rw [← smulGlobal_naturality', smulGlobal_unit_eq_scalarEnd',
    scalarEnd_unitEndSection', hjq]
  exact comp_zero.symm

set_option backward.isDefEq.respectTransparency false in
private lemma unitEndSection_mem_annihilator'
    {X : Scheme.{u}} {F : X.Modules}
    (j : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ F) [Epi q]
    (hjq : j ≫ q = 0) :
    unitEndSection' j ∈ Module.annihilator Γ(X, ⊤) Γ(F, ⊤) := by
  rw [Module.mem_annihilator]
  intro x
  have hzero := congrArg (fun e : F ⟶ F => e.app ⊤ x)
    (smulGlobal_eq_zero_of_unit_relation' j q hjq)
  change X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op
    (unitEndSection' j) • x = 0 at hzero
  have hid : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op =
      𝟙 (op (⊤ : X.Opens)) := rfl
  rw [hid] at hzero
  have hres : X.presheaf.map (𝟙 (op (⊤ : X.Opens)))
      (unitEndSection' j) = unitEndSection' j := by
    simp
  rw [hres] at hzero
  exact hzero

set_option backward.isDefEq.respectTransparency false in
private theorem genericPoint_not_mem_annihilator_support_of_trivial_kernel'
    {X : Scheme.{u}} [IsIntegral X] [IsAffine X] {F : X.Modules}
    (j : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    [Mono j]
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ F) [Epi q]
    (hjq : j ≫ q = 0) [F.IsFinitePresentation] :
    genericPoint X ∉ (annihilator F).support := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have hξU : genericPoint X ∈ (U : X.Opens) := trivial
  letI : Nonempty (U : X.Opens) := ⟨⟨genericPoint X, hξU⟩⟩
  let a : Γ(X, ⊤) := unitEndSection' j
  have ha : a ∈ Module.annihilator Γ(X, ⊤) Γ(F, ⊤) :=
    unitEndSection_mem_annihilator' j q hjq
  have hane : a ≠ 0 := unitEndSection_ne_zero_of_mono' j
  intro hξ
  have hzero : genericPoint X ∈ X.zeroLocus (U := (U : X.Opens))
      (↑((annihilator F).ideal U) : Set Γ(X, (U : X.Opens))) :=
    (Scheme.IdealSheafData.mem_support_iff_of_mem hξU).mp hξ
  rw [annihilator_ideal F
    (fun V => module_finite_sections_of_isFinitePresentation F V) U] at hzero
  have hzspec : U.2.primeIdealOf ⟨genericPoint X, hξU⟩ ∈
      PrimeSpectrum.zeroLocus
        (Module.annihilator Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens))) := by
    rw [← U.2.fromSpec_preimage_zeroLocus]
    change U.2.fromSpec (U.2.primeIdealOf ⟨genericPoint X, hξU⟩) ∈
      X.zeroLocus (U := (U : X.Opens))
        (↑(Module.annihilator Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens))) :
          Set Γ(X, (U : X.Opens)))
    rw [U.2.fromSpec_primeIdealOf]
    exact hzero
  rw [PrimeSpectrum.mem_zeroLocus] at hzspec
  have habot : a ∈ (⊥ : Ideal Γ(X, ⊤)) := by
    have hap := hzspec ha
    rw [U.2.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine] at hap
    exact hap
  exact hane (Ideal.mem_bot.mp habot)

private theorem genericPoint_not_mem_annihilator_support
    {X : Scheme.{u}} [IsIntegral X]
    {L F : X.Modules}
    (j : L ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j]
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ F) [Epi q]
    (hjq : j ≫ q = 0)
    (hL : LineBundle.IsLocallyTrivial L)
    [F.IsFinitePresentation] :
    genericPoint X ∉ (annihilator F).support := by
  obtain ⟨U, hηU, hUaff, ⟨eLres⟩⟩ := hL (genericPoint X)
  letI : Nonempty U := ⟨⟨genericPoint X, hηU⟩⟩
  letI : IsAffine U := hUaff
  letI : IsIntegral U := inferInstance
  let unitX := SheafOfModules.unit X.ringCatSheaf
  let unitU := SheafOfModules.unit U.toScheme.ringCatSheaf
  let FU := (pullback U.ι).obj F
  let eL : (pullback U.ι).obj L ≅ unitU :=
    ((restrictFunctorIsoPullback U.ι).app L).symm ≪≫ eLres
  let eO : (pullback U.ι).obj unitX ≅ unitU := pullbackUnitIso U.ι
  let jU : unitU ⟶ unitU :=
    eL.inv ≫ (pullback U.ι).map j ≫ eO.hom
  let qU : unitU ⟶ FU := eO.inv ≫ (pullback U.ι).map q
  haveI hjMapMono : Mono ((pullback U.ι).map j) :=
    Functor.map_mono (pullback U.ι) j
  have heLMono : Mono eL.inv := IsIso.mono_of_iso _
  have heOMono : Mono eO.hom := IsIso.mono_of_iso _
  have htailMono : Mono ((pullback U.ι).map j ≫ eO.hom) :=
    @mono_comp _ _ _ _ _ ((pullback U.ι).map j) hjMapMono eO.hom heOMono
  haveI hjUMono : Mono jU := by
    dsimp [jU]
    exact @mono_comp _ _ _ _ _ eL.inv heLMono
      ((pullback U.ι).map j ≫ eO.hom) htailMono
  haveI hpres : PreservesColimitsOfSize.{u, u} (pullback U.ι) :=
    (pullbackPushforwardAdjunction U.ι).leftAdjoint_preservesColimits
  have hqEpi : Epi q := inferInstance
  haveI hqMapEpi : Epi ((pullback U.ι).map q) :=
    @Functor.map_epi _ _ _ _ (pullback U.ι) inferInstance _ _ q hqEpi
  haveI hqUEpi : Epi qU := by
    dsimp [qU]
    exact @epi_comp _ _ _ _ _ eO.inv (IsIso.epi_of_iso _)
      ((pullback U.ι).map q) hqMapEpi
  haveI hFUfp : FU.IsFinitePresentation := by
    dsimp [FU]
    exact pullback_isFinitePresentation U.ι F inferInstance
  have hcancel :
      (eL.inv ≫ (pullback U.ι).map j ≫ eO.hom) ≫
          (eO.inv ≫ (pullback U.ι).map q) =
        eL.inv ≫ (pullback U.ι).map j ≫ (pullback U.ι).map q := by
    simp
  have hjqU : jU ≫ qU = 0 := by
    calc
      jU ≫ qU =
          eL.inv ≫ (pullback U.ι).map j ≫ (pullback U.ι).map q := hcancel
      _ = eL.inv ≫ (pullback U.ι).map (j ≫ q) := by
        rw [Functor.map_comp]
      _ = 0 := by
        rw [hjq, Functor.map_zero, comp_zero]
  have hnot : genericPoint U.toScheme ∉ (annihilator FU).support :=
    genericPoint_not_mem_annihilator_support_of_trivial_kernel' jU qU hjqU
  intro hη
  apply hnot
  rw [show (annihilator FU).support =
      (annihilator F).support.preimage U.ι.continuous by
    simpa [FU] using annihilator_pullback_support_eq_preimage U.ι F]
  change U.ι (genericPoint U.toScheme) ∈ (annihilator F).support
  rw [genericPoint_eq_of_isOpenImmersion U.ι]
  exact hη

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.DivFamily

variable {S X : Scheme.{u}} (T : Over S) (π : X ⟶ S)

private theorem generic_avoidance_fiber
    [GeometricallyIntegral π]
    (x : DivFamily π T) (t : (T.left : Scheme.{u})) :
    genericPoint ((pullback.snd π T.hom).fiber t) ∉
      (Modules.annihilator
        ((pullback.snd π T.hom).fiberModule t x.F)).support := by
  let f := pullback.snd π T.hom
  let C := f.fiber t
  let g := f.fiberι t
  let unitX := SheafOfModules.unit X.ringCatSheaf
  let unitC := SheafOfModules.unit C.ringCatSheaf
  let L := f.fiberModule t (kernel x.q)
  let Ft := f.fiberModule t x.F
  let eO₀ :
      (Modules.pullback (pullback.fst π T.hom)).obj unitX ≅
        SheafOfModules.unit (pullback π T.hom).ringCatSheaf :=
    Modules.pullbackUnitIso (pullback.fst π T.hom)
  let eO :
      (Modules.pullback g).obj
          ((Modules.pullback (pullback.fst π T.hom)).obj unitX) ≅ unitC :=
    (Modules.pullback g).mapIso eO₀ ≪≫ Modules.pullbackUnitIso g
  let j : L ⟶ unitC :=
    (Modules.pullback g).map (kernel.ι x.q) ≫ eO.hom
  let q : unitC ⟶ Ft :=
    eO.inv ≫ (Modules.pullback g).map x.q
  haveI hCIntegral : IsIntegral C := by
    dsimp [C, f]
    infer_instance
  haveI hjRawMono : Mono ((Modules.pullback g).map (kernel.ι x.q)) := by
    dsimp [g, f]
    exact x.mono_fiber_kernel_ι t
  haveI hjMono : Mono j := by
    dsimp [j]
    exact @mono_comp _ _ _ _ _
      ((Modules.pullback g).map (kernel.ι x.q)) hjRawMono
      eO.hom (IsIso.mono_of_iso _)
  haveI hpres : PreservesColimitsOfSize.{u, u} (Modules.pullback g) :=
    (Modules.pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits
  haveI hqMapEpi : Epi ((Modules.pullback g).map x.q) :=
    @Functor.map_epi _ _ _ _ (Modules.pullback g)
      inferInstance _ _ x.q x.epi
  haveI hqEpi : Epi q := by
    dsimp [q]
    exact @epi_comp _ _ _ _ _ eO.inv (IsIso.epi_of_iso _)
      ((Modules.pullback g).map x.q) hqMapEpi
  haveI hFtFp : Ft.IsFinitePresentation := by
    dsimp [Ft, Scheme.Hom.fiberModule]
    exact Modules.pullback_isFinitePresentation g x.F x.isFinitePresentation
  have hL : LineBundle.IsLocallyTrivial L := by
    exact LineBundle.IsLocallyTrivial.of_iso
      (x.fiberKernelIso t).symm
      (x.isLocallyTrivial_fiber_kernel t)
  have hcancel :
      ((Modules.pullback g).map (kernel.ι x.q) ≫ eO.hom) ≫
          (eO.inv ≫ (Modules.pullback g).map x.q) =
        (Modules.pullback g).map (kernel.ι x.q) ≫
          (Modules.pullback g).map x.q := by
    simp
  have hjq : j ≫ q = 0 := by
    calc
      j ≫ q =
          (Modules.pullback g).map (kernel.ι x.q) ≫
            (Modules.pullback g).map x.q := hcancel
      _ = (Modules.pullback g).map (kernel.ι x.q ≫ x.q) := by
        rw [Functor.map_comp]
      _ = 0 := by
        rw [kernel.condition, Functor.map_zero]
  exact Modules.genericPoint_not_mem_annihilator_support j q hjq hL

/-- The schematic support of a relative effective Cartier divisor on a proper
smooth geometrically integral curve has finite set-theoretic fibres. -/
theorem finite_fiber_support_of_curve
    [SmoothOfRelativeDimension 1 π] [GeometricallyIntegral π] [IsProper π]
    (x : DivFamily π T) (t : (T.left : Scheme.{u})) :
    ((Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) ⁻¹' {t}).Finite := by
  let f := pullback.snd π T.hom
  let C := f.fiber t
  let Ft : C.Modules := (Modules.pullback (f.fiberι t)).obj x.F
  letI : x.F.IsFinitePresentation := x.isFinitePresentation
  letI : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI hπT : SmoothOfRelativeDimension 1 f :=
    MorphismProperty.pullback_snd _ _
      (inferInstance : SmoothOfRelativeDimension 1 π)
  haveI hCtSmooth : SmoothOfRelativeDimension 1
      (f.fiberToSpecResidueField t) :=
    MorphismProperty.pullback_snd _ _
      (inferInstance : SmoothOfRelativeDimension 1 f)
  haveI hπTProper : IsProper f :=
    MorphismProperty.pullback_snd _ _ (inferInstance : IsProper π)
  haveI hCtProper : IsProper (f.fiberToSpecResidueField t) :=
    MorphismProperty.pullback_snd _ _ (inferInstance : IsProper f)
  haveI hCtIntegral : IsIntegral C := by
    dsimp [C]
    infer_instance
  haveI hCtLocNoeth : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField t)
  haveI hCtCompact : CompactSpace C :=
    QuasiCompact.compactSpace_of_compactSpace (f.fiberToSpecResidueField t)
  haveI hCtNoeth : IsNoetherian C := { }
  have hgen : ∀ a b : C, b ⤳ a → b = genericPoint C ∨ b = a :=
    fun a b h => @SmoothOfRelativeDimension.specializes_eq_genericPoint_or_eq
      C (T.left.residueField t) inferInstance
      (f.fiberToSpecResidueField t) hCtSmooth hCtIntegral a b h
  have hSuppFinite :
      ((Modules.annihilator Ft).support : Set C).Finite :=
    Scheme.finite_of_isClosed_of_notMem_genericPoint hgen
      (Modules.annihilator Ft).support.isClosed
      (by
        simpa [C, Ft, f, Scheme.Hom.fiberModule] using
          generic_avoidance_fiber T π x t)
  let s : Set (Modules.schematicSupport x.F) :=
    (Modules.schematicSupportι x.F ≫ f) ⁻¹' {t}
  let liftToFiber : s → C := fun z =>
    (f.fiberHomeo t).symm ⟨Modules.schematicSupportι x.F z.1, by
      change f (Modules.schematicSupportι x.F z.1) = t
      exact z.2⟩
  have hlift_mem (z : s) :
      liftToFiber z ∈ (Modules.annihilator Ft).support := by
    rw [show (Modules.annihilator Ft).support =
      (Modules.annihilator x.F).support.preimage (f.fiberι t).continuous by
        simpa [Ft] using
          (Modules.annihilator_pullback_support_eq_preimage (f.fiberι t) x.F)]
    change f.fiberι t (liftToFiber z) ∈ (Modules.annihilator x.F).support
    have hset : Set.range (Modules.schematicSupportι x.F) =
        (Modules.annihilator x.F).support :=
      (Modules.annihilator x.F).range_subschemeι
    have hrange : Modules.schematicSupportι x.F z.1 ∈
        Set.range (Modules.schematicSupportι x.F) := ⟨z.1, rfl⟩
    have hmem : Modules.schematicSupportι x.F z.1 ∈
        (Modules.annihilator x.F).support :=
      (Set.ext_iff.mp hset (Modules.schematicSupportι x.F z.1)).mp hrange
    simpa [liftToFiber] using hmem
  let lift : s → (Modules.annihilator Ft).support :=
    fun z => ⟨liftToFiber z, hlift_mem z⟩
  have hlift_inj : Function.Injective lift := by
    intro z₁ z₂ h
    apply Subtype.ext
    have hfiber : liftToFiber z₁ = liftToFiber z₂ :=
      congrArg Subtype.val h
    have hamb := congrArg (fun c : C => f.fiberι t c) hfiber
    have hi : Function.Injective (Modules.schematicSupportι x.F) :=
      (Modules.isPreimmersion_schematicSupportι x.F).isEmbedding.injective
    apply hi
    simpa [liftToFiber] using hamb
  letI : Fintype (Modules.annihilator Ft).support := hSuppFinite.fintype
  letI : Finite s := Finite.of_injective lift hlift_inj
  change s.Finite
  exact Set.finite_coe_iff.mp inferInstance

/-- The support morphism of a relative effective Cartier divisor on a proper
smooth geometrically integral curve is locally quasi-finite. -/
theorem locallyQuasiFinite_support_of_curve
    [SmoothOfRelativeDimension 1 π] [GeometricallyIntegral π] [IsProper π]
    (x : DivFamily π T) :
    LocallyQuasiFinite
      (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) :=
  x.locallyQuasiFinite_of_finite_fibers
    (finite_fiber_support_of_curve T π x)

instance instLocallyQuasiFiniteSupportOfCurve
    [SmoothOfRelativeDimension 1 π] [GeometricallyIntegral π] [IsProper π]
    (x : DivFamily π T) :
    LocallyQuasiFinite
      (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) :=
  locallyQuasiFinite_support_of_curve T π x

end AlgebraicGeometry.Scheme.DivFamily
