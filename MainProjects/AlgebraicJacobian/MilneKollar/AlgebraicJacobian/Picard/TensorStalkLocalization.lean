/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.TensorSectionFormula
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# Stalk localization for the tensor presheaf

Basic-open localization of a presheaf on an affine open implies that its map from
affine sections to a stalk is localization at the corresponding prime ideal.  The
final theorem applies this generic result to the tensor presheaf of two
quasi-coherent modules.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace PresheafOfModules

variable {Y : TopCat.{u}} {R : Y.Presheaf CommRingCat.{u}}

/-- The germ map of a presheaf of modules, linear over the ring of sections on
the source open. -/
noncomputable def germLinearMap
    (P : PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) {U : Opens Y} (x : U) :
    letI : Module (R.stalk x)
        (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) := by
      infer_instance
    letI : Module (R.obj (op U))
        (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
      Module.compHom _ (R.germ U x x.2).hom
    P.obj (op U) →ₗ[R.obj (op U)]
      (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) := by
  letI : Module (R.stalk x)
      (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) := by
    infer_instance
  letI : Module (R.obj (op U))
      (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
    Module.compHom _ (R.germ U x x.2).hom
  refine
    { toFun := ConcreteCategory.hom (TopCat.Presheaf.germ P.presheaf U x x.2)
      map_add' := map_add _
      map_smul' := fun r m => ?_ }
  exact P.germ_smul x U x.2 r m

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The canonical module structure of a module-presheaf stalk over the
structure-presheaf stalk. -/
noncomputable abbrev presheafStalkModule
    (P : X.PresheafOfModules) (x : X) :
    Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) := by
  change _root_.PresheafOfModules.{u}
    (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) at P
  exact
    _root_.PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      P x

/-- The germ map of an `O_X`-module presheaf as a linear map over the ring of
sections on the source open. -/
noncomputable def presheafGermLinearMap
    (P : X.PresheafOfModules) {U : X.Opens} (x : U) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
      presheafStalkModule P x
    letI : Module Γ(X, U)
        (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
      Module.compHom _ (X.presheaf.germ U x x.2).hom
    P.obj (op U) →ₗ[Γ(X, U)]
      (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) := by
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
    presheafStalkModule P x
  letI : Module Γ(X, U)
      (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
    Module.compHom _ (X.presheaf.germ U x x.2).hom
  exact _root_.PresheafOfModules.germLinearMap (R := X.presheaf) P x

/-- Sheafification preserves the stalk of a presheaf of modules. -/
theorem sheafificationUnit_stalk_isIso
    (P : X.PresheafOfModules) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P))) := by
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    x AddCommGrpCat P.presheaf

/-- On an affine open, basic-open localization of a module presheaf implies
localization of its affine-section germ map at every point. -/
theorem isLocalizedModule_presheafGermLinearMap
    (P : X.PresheafOfModules) {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (H : ∀ f : Γ(X, U),
      letI : Module Γ(X, U) (P.obj (op (X.basicOpen f))) :=
        Module.compHom _
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
      IsLocalizedModule (Submonoid.powers f)
        (ModuleCat.Hom.hom
          (P.map (homOfLE (X.basicOpen_le f)).op))) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
      presheafStalkModule P x
    letI : Module Γ(X, U)
        (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
      Module.compHom _ (X.presheaf.germ U x x.2).hom
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl
      (presheafGermLinearMap P x) := by
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
    presheafStalkModule P x
  letI : Module Γ(X, U)
      (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
    Module.compHom _ (X.presheaf.germ U x x.2).hom
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hxs : x.1 ∈ X.basicOpen (s : Γ(X, U)) := by
      have hp : hU.primeIdealOf x ∈ PrimeSpectrum.basicOpen (s : Γ(X, U)) :=
        (PrimeSpectrum.mem_basicOpen _ _).2 s.property
      rw [← hU.fromSpec_preimage_basicOpen] at hp
      change hU.fromSpec (hU.primeIdealOf x) ∈ X.basicOpen (s : Γ(X, U)) at hp
      simpa only [hU.fromSpec_primeIdealOf] using hp
    have hs : IsUnit
        ((ConcreteCategory.hom (X.presheaf.germ U x x.2)) (s : Γ(X, U))) :=
      (X.mem_basicOpen (s : Γ(X, U)) x x.2).mp hxs
    rw [Module.End.isUnit_iff]
    have heq :
        (⇑(algebraMap Γ(X, U)
          (Module.End Γ(X, U)
            (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u)) (s : Γ(X, U)))) =
          (fun a => (ConcreteCategory.hom (X.presheaf.germ U x x.2))
            (s : Γ(X, U)) • a) := by
      funext a
      rw [Module.algebraMap_end_apply]
      rfl
    rw [heq]
    exact hs.smul_bijective
  · intro y
    obtain ⟨W, hWU, hxW, a, ha⟩ :=
      TopCat.Presheaf.exists_le_germ_eq P.presheaf y x.2
    obtain ⟨f, hfW, hxf⟩ :=
      hU.exists_basicOpen_le (⟨x, hxW⟩ : W) x.2
    let iDU : X.basicOpen f ⟶ U := homOfLE (X.basicOpen_le f)
    let iDW : X.basicOpen f ⟶ W := homOfLE hfW
    let aD : P.obj (op (X.basicOpen f)) :=
      P.presheaf.map iDW.op a
    letI : Module Γ(X, U) (P.obj (op (X.basicOpen f))) :=
      Module.compHom _ (X.presheaf.map iDU.op).hom
    haveI hloc : IsLocalizedModule (Submonoid.powers f)
        (ModuleCat.Hom.hom (P.map iDU.op)) := H f
    obtain ⟨q, hq⟩ := hloc.surj aD
    have hfnot : f ∉ (hU.primeIdealOf x).asIdeal := by
      rw [← PrimeSpectrum.mem_basicOpen]
      rw [← hU.fromSpec_preimage_basicOpen]
      change hU.fromSpec (hU.primeIdealOf x) ∈ X.basicOpen f
      rw [hU.fromSpec_primeIdealOf]
      exact hxf
    have hqnot : (q.2 : Γ(X, U)) ∉ (hU.primeIdealOf x).asIdeal := by
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp q.2.property
      intro hmem
      apply hfnot
      apply (hU.primeIdealOf x).isPrime.mem_of_pow_mem n
      rwa [hn]
    let c : (hU.primeIdealOf x).asIdeal.primeCompl := ⟨q.2, hqnot⟩
    refine ⟨⟨q.1, c⟩, ?_⟩
    have haD :
        (ConcreteCategory.hom
          (TopCat.Presheaf.germ P.presheaf (X.basicOpen f) x hxf)) aD = y := by
      change (ConcreteCategory.hom
        (TopCat.Presheaf.germ P.presheaf (X.basicOpen f) x hxf))
          ((ConcreteCategory.hom (P.presheaf.map iDW.op)) a) = y
      rw [TopCat.Presheaf.germ_res_apply]
      exact ha
    have hq' :
        (ConcreteCategory.hom (X.presheaf.map iDU.op)) (q.2 : Γ(X, U)) • aD =
          (ConcreteCategory.hom (P.presheaf.map iDU.op)) q.1 := by
      exact hq
    change (ConcreteCategory.hom (X.presheaf.germ U x x.2)) (q.2 : Γ(X, U)) • y =
      (ConcreteCategory.hom (TopCat.Presheaf.germ P.presheaf U x x.2)) q.1
    rw [← haD, ← TopCat.Presheaf.germ_res_apply X.presheaf iDU x hxf (q.2 : Γ(X, U))]
    exact (P.germ_smul x (X.basicOpen f) hxf _ aD).symm.trans <|
      congrArg (ConcreteCategory.hom
        (TopCat.Presheaf.germ P.presheaf (X.basicOpen f) x hxf)) hq' |>.trans <|
      TopCat.Presheaf.germ_res_apply P.presheaf iDU x hxf q.1
  · intro a b hab
    change (ConcreteCategory.hom (TopCat.Presheaf.germ P.presheaf U x x.2)) a =
      (ConcreteCategory.hom (TopCat.Presheaf.germ P.presheaf U x x.2)) b at hab
    obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ :=
      TopCat.Presheaf.germ_eq P.presheaf x x.2 x.2 a b hab
    obtain ⟨f, hfW, hxf⟩ :=
      hU.exists_basicOpen_le (⟨x, hxW⟩ : W) x.2
    let iDU : X.basicOpen f ⟶ U := homOfLE (X.basicOpen_le f)
    let iDW : X.basicOpen f ⟶ W := homOfLE hfW
    have hres :
        (ConcreteCategory.hom (P.presheaf.map iDU.op)) a =
          (ConcreteCategory.hom (P.presheaf.map iDU.op)) b := by
      have e := congrArg
        (ConcreteCategory.hom (P.presheaf.map iDW.op)) heq
      have hcomp₁ : iDW ≫ iWU₁ = iDU := Subsingleton.elim _ _
      have hcomp₂ : iDW ≫ iWU₂ = iDU := Subsingleton.elim _ _
      simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
        hcomp₁, hcomp₂] using e
    letI : Module Γ(X, U) (P.obj (op (X.basicOpen f))) :=
      Module.compHom _ (X.presheaf.map iDU.op).hom
    haveI hloc : IsLocalizedModule (Submonoid.powers f)
        (ModuleCat.Hom.hom (P.map iDU.op)) := H f
    obtain ⟨q, hq⟩ := hloc.exists_of_eq hres
    have hfnot : f ∉ (hU.primeIdealOf x).asIdeal := by
      rw [← PrimeSpectrum.mem_basicOpen]
      rw [← hU.fromSpec_preimage_basicOpen]
      change hU.fromSpec (hU.primeIdealOf x) ∈ X.basicOpen f
      rw [hU.fromSpec_primeIdealOf]
      exact hxf
    have hqnot : (q : Γ(X, U)) ∉ (hU.primeIdealOf x).asIdeal := by
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp q.property
      intro hmem
      apply hfnot
      apply (hU.primeIdealOf x).isPrime.mem_of_pow_mem n
      rwa [hn]
    exact ⟨⟨q, hqnot⟩, hq⟩

/-- The tensor presheaf of two quasi-coherent modules localizes from affine
sections to every stalk. -/
theorem isLocalizedModule_tensorPresheafGermLinearMap
    (A B : X.Modules) [A.IsQuasicoherent] [B.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (x : U) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk (tensorPresheaf A B).presheaf x) : Type u) :=
      presheafStalkModule (tensorPresheaf A B) x
    letI : Module Γ(X, U)
        (↑(TopCat.Presheaf.stalk (tensorPresheaf A B).presheaf x) : Type u) :=
      Module.compHom _ (X.presheaf.germ U x x.2).hom
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl
      (presheafGermLinearMap (tensorPresheaf A B) x) := by
  apply isLocalizedModule_presheafGermLinearMap (tensorPresheaf A B) hU x
  intro f
  exact isLocalizedModule_tensorPresheaf_basicOpen A B hU f

/-! ## The localized tensor-section model of the sheaf tensor stalk -/

/-- Sheafification identifies the stalk of the tensor presheaf with the stalk of
the sheaf tensor product.  This is the `O_{X,x}`-linear form of
`sheafificationUnit_stalk_isIso`. -/
noncomputable def tensorSheafificationStalkLinearEquiv
    (A B : X.Modules) (x : X) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk (tensorPresheaf A B).presheaf x) : Type u) :=
      presheafStalkModule (tensorPresheaf A B) x
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf x) : Type u) :=
      presheafStalkModule (tensorObj A B).val x
    (↑(TopCat.Presheaf.stalk (tensorPresheaf A B).presheaf x) : Type u) ≃ₗ[X.presheaf.stalk x]
      (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf x) : Type u) := by
  let eta := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (tensorPresheaf A B)
  exact PresheafOfModules.stalkLinearEquivOfIsIso eta x
    (sheafificationUnit_stalk_isIso (tensorPresheaf A B) x)

/-- On an affine open `U`, the stalk of the sheaf tensor product at `x in U` is
the localization of the tensor-presheaf sections on `U` at the complement of
the prime corresponding to `x`.  The construction first uses localization
uniqueness for the tensor-presheaf germ map, then the sheafification equivalence
on stalks. -/
noncomputable def localizedTensorSectionsStalkLinearEquiv
    (A B : X.Modules) [A.IsQuasicoherent] [B.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (x : U) :
    let S := (hU.primeIdealOf x).asIdeal.primeCompl
    let P := tensorPresheaf A B
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
      presheafStalkModule P x
    letI : Module Γ(X, U)
        (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
      Module.compHom _ (X.presheaf.germ U x x.2).hom
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf x) : Type u) :=
      presheafStalkModule (tensorObj A B).val x
    letI : Module Γ(X, U)
        (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf x) : Type u) :=
      Module.compHom _ (X.presheaf.germ U x x.2).hom
    LocalizedModule S (P.obj (op U)) ≃ₗ[Γ(X, U)]
      (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf x) : Type u) := by
  let S := (hU.primeIdealOf x).asIdeal.primeCompl
  let P := tensorPresheaf A B
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
    presheafStalkModule P x
  letI : Module Γ(X, U)
      (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) :=
    Module.compHom _ (X.presheaf.germ U x x.2).hom
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf x) : Type u) :=
    presheafStalkModule (tensorObj A B).val x
  letI : Module Γ(X, U)
      (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf x) : Type u) :=
    Module.compHom _ (X.presheaf.germ U x x.2).hom
  haveI hloc : IsLocalizedModule S (presheafGermLinearMap P x) :=
    isLocalizedModule_tensorPresheafGermLinearMap A B hU x
  let e := tensorSheafificationStalkLinearEquiv A B x
  let eGamma : (↑(TopCat.Presheaf.stalk P.presheaf x) : Type u) ≃ₗ[Γ(X, U)]
      (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf x) : Type u) :=
    { e.toEquiv with
      map_add' := e.map_add
      map_smul' := fun r m => e.map_smul
        (ConcreteCategory.hom (X.presheaf.germ U x x.2) r) m }
  exact IsLocalizedModule.linearEquiv S
      (LocalizedModule.mkLinearMap S (P.obj (op U)))
      (presheafGermLinearMap P x) ≪≫ₗ eGamma

/-- The localized tensor-section equivalence sends a numerator section to the
germ of its image under `tensorSectionHom`.  This is the pointwise rewrite used
by fibre comparisons. -/
@[simp]
theorem localizedTensorSectionsStalkLinearEquiv_mkLinearMap
    (A B : X.Modules) [A.IsQuasicoherent] [B.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (m : (tensorPresheaf A B).obj (op U)) :
    localizedTensorSectionsStalkLinearEquiv A B hU x
        (LocalizedModule.mkLinearMap
          (hU.primeIdealOf x).asIdeal.primeCompl ((tensorPresheaf A B).obj (op U)) m) =
      (ConcreteCategory.hom
        (TopCat.Presheaf.germ (tensorObj A B).val.presheaf U x x.2))
          (tensorSectionHom A B U m) := by
  rw [localizedTensorSectionsStalkLinearEquiv,
    LinearEquiv.trans_apply, IsLocalizedModule.linearEquiv_apply]
  exact PresheafOfModules.stalkLinearMap_germ
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app (tensorPresheaf A B)) x U x.2 m

/-- The composite of `tensorSectionHom` with the germ map of the sheaf tensor
product is a localization map.  Thus the actual sheaf-tensor stalk, together
with the map from affine tensor-presheaf sections, satisfies the universal
property of localization at the point's prime complement. -/
theorem isLocalizedModule_tensorSectionHom_stalk
    (A B : X.Modules) [A.IsQuasicoherent] [B.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (x : U) :
    letI : Module (X.presheaf.stalk x)
        (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf x) : Type u) :=
      presheafStalkModule (tensorObj A B).val x
    letI : Module Γ(X, U)
        (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf x) : Type u) :=
      Module.compHom _ (X.presheaf.germ U x x.2).hom
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl
      ((presheafGermLinearMap (tensorObj A B).val x).comp
        (ModuleCat.Hom.hom (tensorSectionHom A B U))) := by
  letI : Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf x) : Type u) :=
    presheafStalkModule (tensorObj A B).val x
  letI : Module Γ(X, U)
      (↑(TopCat.Presheaf.stalk (tensorObj A B).val.presheaf x) : Type u) :=
    Module.compHom _ (X.presheaf.germ U x x.2).hom
  let S := (hU.primeIdealOf x).asIdeal.primeCompl
  let f := LocalizedModule.mkLinearMap S ((tensorPresheaf A B).obj (op U))
  let e := localizedTensorSectionsStalkLinearEquiv A B hU x
  have heq :
      (presheafGermLinearMap (tensorObj A B).val x).comp
          (ModuleCat.Hom.hom (tensorSectionHom A B U)) =
        e.toLinearMap.comp f := by
    apply LinearMap.ext
    intro m
    exact (localizedTensorSectionsStalkLinearEquiv_mkLinearMap A B hU x m).symm
  rw [heq]
  exact IsLocalizedModule.of_linearEquiv S f e

end AlgebraicGeometry.Scheme.Modules
