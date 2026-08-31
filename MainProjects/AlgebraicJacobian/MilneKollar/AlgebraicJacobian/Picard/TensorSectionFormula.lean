/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.TensorObjSubstrate
import AlgebraicJacobian.Picard.SectionGradedRing
import AlgebraicJacobian.Picard.QuotScheme

/-!
# Affine tensor-section substrate (`TensorSectionFormula`)

This file collects the substrate for the affine tensor-section
formula that feeds the quasi-coherent case of
`Scheme.Modules.pullbackTensorMap_isIso` ([Stacks 01CD]; the section formula is
[Stacks 01CD]/[Stacks 01CA] read on a basis of affine opens).

For `A B : X.Modules` the substrate tensor `Scheme.Modules.tensorObj A B`
(`Picard/TensorObjSubstrate.lean`) is the sheafification of the presheaf-of-modules
tensor `P := PresheafOfModules.Monoidal.tensorObj A.val B.val` of the underlying
presheaves.  Objectwise, `P(V) = Γ(A, V) ⊗_{Γ(X, V)} Γ(B, V)`
(`tensorPresheaf_obj`), so the sheafification unit provides a canonical
`Γ(X, V)`-linear **section comparison**

  `tensorSectionHom A B V : Γ(A, V) ⊗_{Γ(X, V)} Γ(B, V) ⟶ Γ(tensorObj A B, V)`

for every open `V` (`tensorSectionHom`), natural in restriction
(`tensorSectionHom_naturality_apply`).  Over the total space it is exactly the
section multiplication `sectionsMul` of the graded-ring machinery
(`tensorSectionHom_top_eq_sectionsMul`), and the substrate `tensorObj` and the
section-graded `sheafTensorObj` are the same object
(`tensorObjIsoSheafTensorObj`, definitional).

## Contents

* `tensorPresheaf` — the presheaf-of-modules tensor of the underlying presheaves.
* `tensorSectionHom` — the section comparison map at an open `V`.
* `tensorPresheaf_obj` — the objectwise identification of the domain as
  `Γ(A, V) ⊗ Γ(B, V)`.
* `tensorSectionHom_naturality_apply` — restriction naturality.
* `tensorSectionHom_top_eq_sectionsMul` — the `⊤`-value is `sectionsMul`.
* `tensorObjIsoSheafTensorObj` — the (definitional) `tensorObj ≅ sheafTensorObj`
  bridge.
* `isIso_sheafification_tensorSectionUnit` — the categorical crux: sheafifying the
  presheaf comparison unit is an isomorphism (the reflective localization inverts
  the unit), which is why the affine formula reduces to the presheaf-tensor
  localization on a basis of affine opens.
* `localizedTensorProductEquiv` / `localizedTensorProductBaseChangeEquiv` — the
  algebraic localization heart, first over `R` and then over `Localization S`.
* `localizedTensorProductBaseChangeEquiv_mkLinearMap_tmul` — the named pure-tensor
  formula for the exact base-change equivalence.
* `localizedTensorProductMap` / `isLocalizedModule_localizedTensorProductMap` — the
  same result for arbitrary localization maps into an arbitrary localization algebra.

## Downstream affine closure

The localization computation assembled below is consumed by
`Picard/AffineOpenStalkLocalization.lean`.  There,
`tensorSectionHom_isIso` proves that `tensorSectionHom A B V` is an isomorphism
for quasi-coherent `A B` and every affine open `V`, and
`tensorObj_isQuasicoherent` deduces quasi-coherence of the sheaf tensor product.
The proof reconstructs affine sections from their prime-complement stalk
localizations and introduces no hypothesis beyond quasi-coherence of the two
factors.

The separate arbitrary-sheaf statement `Modules.pullbackTensorMap_isIso` remains
outside this affine computation; its quasi-coherent consumers can use the affine
section and quasi-coherence theorems above.

### On the generality of `pullbackTensorMap_isIso`

`Modules.pullbackTensorMap_isIso` is stated for *arbitrary* `A B` (no
quasi-coherence hypothesis), matching the general [Stacks 01CD] statement for
ringed spaces, whereas the chart chase above only closes the *quasi-coherent*
case.  Its sole consumer (`pullback_moduleTensorPow_iso`) already carries
`[F.IsQuasicoherent] [L.IsQuasicoherent]`, so a quasi-coherent variant assuming
`[A.IsQuasicoherent] [B.IsQuasicoherent]` would be enough for that consumer and
would avoid the general ringed-space stalk machinery.
-/

universe u v w uA vM vN

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The presheaf-of-modules tensor of the underlying presheaves of `A B : X.Modules`;
objectwise `Γ(A, V) ⊗_{Γ(X, V)} Γ(B, V)`.  Its sheafification is
`Scheme.Modules.tensorObj A B`. -/
noncomputable abbrev tensorPresheaf (A B : X.Modules) : X.PresheafOfModules :=
  PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) A.val B.val

/-- The **section comparison** at an open `V`: the `Γ(X, V)`-linear map
`Γ(A, V) ⊗_{Γ(X, V)} Γ(B, V) ⟶ Γ(tensorObj A B, V)`, defined as the `V`-component of
the sheafification-adjunction unit at the presheaf tensor.  On the total space it is
the section multiplication `sectionsMul`; for quasi-coherent `A B` and affine `V` it
is an isomorphism (the affine tensor-section formula — see the module docstring). -/
noncomputable def tensorSectionHom (A B : X.Modules) (V : X.Opens) :
    (tensorPresheaf A B).obj (op V) ⟶ (tensorObj A B).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (tensorPresheaf A B)).app (op V)

/-- The domain of `tensorSectionHom` over `V` is the `Γ(X, V)`-module tensor product
`Γ(A, V) ⊗ Γ(B, V)` (the objectwise formula for the presheaf-of-modules tensor). -/
lemma tensorPresheaf_obj (A B : X.Modules) (V : X.Opens) :
    (tensorPresheaf A B).obj (op V) =
      MonoidalCategory.tensorObj (C := ModuleCat (X.presheaf.obj (op V)))
        (A.val.obj (op V)) (B.val.obj (op V)) := rfl

/-- Restriction naturality of the section comparison (element-wise): the comparison
commutes with restriction of sections along an inclusion `V ⊆ W`. -/
lemma tensorSectionHom_naturality_apply (A B : X.Modules) {V W : X.Opens} (i : op W ⟶ op V)
    (x : (tensorPresheaf A B).obj (op W)) :
    tensorSectionHom A B V ((tensorPresheaf A B).map i x) =
      (tensorObj A B).val.map i (tensorSectionHom A B W x) :=
  PresheafOfModules.naturality_apply _ i x

/-- Over the total space `⊤`, the section comparison is the section multiplication
`sectionsMul` of the graded-ring machinery (definitional). -/
lemma tensorSectionHom_top_eq_sectionsMul (A B : X.Modules) :
    tensorSectionHom A B ⊤ = sectionsMul A B := rfl

/-- **Bridge (bonus).**  The substrate tensor `Scheme.Modules.tensorObj` (the object
in which `pullbackTensorMap_isIso` is stated) and the section-graded
`Scheme.Modules.sheafTensorObj` are the *same* object: both sheafify the
presheaf-of-modules tensor of the underlying presheaves. -/
noncomputable def tensorObjIsoSheafTensorObj (A B : X.Modules) :
    tensorObj A B ≅ sheafTensorObj A B := Iso.refl _

/-- **Categorical crux.**  Sheafifying the underlying presheaf comparison unit is an
isomorphism: the reflective sheafification inverts the localization unit of
`tensorPresheaf A B`.  This is the reason the affine section formula reduces to the
presheaf-tensor localization on a basis of affine opens. -/
lemma isIso_sheafification_tensorSectionUnit (A B : X.Modules) :
    IsIso (sheafification.map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app (tensorPresheaf A B))) :=
  isIso_sheafification_map_unit _

/-! ## The module-localization heart -/

/-- **Localization commutes with tensor product, in the form needed on basic opens.**
The tensor product of the two canonical localization maps
`M → S⁻¹M` and `N → S⁻¹N` is itself a localization map. Therefore its
codomain is canonically equivalent to `S⁻¹(M ⊗_R N)`.

The codomain here is the tensor product over `R`. For the affine section formula,
compose with `IsLocalization.moduleTensorEquiv` to replace it by the tensor product
over `Localization S`. This separates the localized-module universal property from
the scalar-change bookkeeping. -/
noncomputable def localizedTensorProductEquiv
    {R : Type u} [CommSemiring R] (S : Submonoid R)
    (M : Type v) (N : Type w) [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] :
    LocalizedModule S (TensorProduct R M N) ≃ₗ[R]
      TensorProduct R (LocalizedModule S M) (LocalizedModule S N) :=
  IsLocalizedModule.linearEquiv S
    (LocalizedModule.mkLinearMap S (TensorProduct R M N))
    (TensorProduct.map (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N))

/-- On numerator pure tensors, `localizedTensorProductEquiv` is the tensor product
of the two canonical localization maps. This is the formula used to identify the
basic-open restriction map of the tensor presheaf. -/
@[simp]
lemma localizedTensorProductEquiv_mkLinearMap_tmul
    {R : Type u} [CommSemiring R] (S : Submonoid R)
    (M : Type v) (N : Type w) [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (m : M) (n : N) :
    localizedTensorProductEquiv S M N
        (LocalizedModule.mkLinearMap S (TensorProduct R M N) (m ⊗ₜ[R] n)) =
      LocalizedModule.mkLinearMap S M m ⊗ₜ[R] LocalizedModule.mkLinearMap S N n := by
  apply IsLocalizedModule.linearEquiv_apply

/-- **The exact base-change form of tensor localization.** As an `R`-linear
equivalence, localizing `M ⊗_R N` is the tensor product of `S⁻¹M` and `S⁻¹N`
over `S⁻¹R = Localization S`. This is the algebraic formula consumed by the
basic-open section chase. -/
noncomputable def localizedTensorProductBaseChangeEquiv
    {R : Type u} [CommSemiring R] (S : Submonoid R)
    (M : Type v) (N : Type w) [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] :
    LocalizedModule S (TensorProduct R M N) ≃ₗ[R]
      TensorProduct (Localization S) (LocalizedModule S M) (LocalizedModule S N) :=
  localizedTensorProductEquiv S M N ≪≫ₗ
    (IsLocalization.moduleTensorEquiv S (Localization S)
      (LocalizedModule S M) (LocalizedModule S N)).symm.restrictScalars R

/-- The exact base-change equivalence sends a numerator pure tensor to the tensor of
the two numerator classes.  Keeping this formula named avoids making affine section
proofs unfold `TensorProduct.equivOfCompatibleSMul`. -/
@[simp]
lemma localizedTensorProductBaseChangeEquiv_mkLinearMap_tmul
    {R : Type u} [CommSemiring R] (S : Submonoid R)
    (M : Type v) (N : Type w) [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (m : M) (n : N) :
    localizedTensorProductBaseChangeEquiv S M N
        (LocalizedModule.mkLinearMap S (TensorProduct R M N) (m ⊗ₜ[R] n)) =
      LocalizedModule.mkLinearMap S M m ⊗ₜ[Localization S]
        LocalizedModule.mkLinearMap S N n := by
  rw [localizedTensorProductBaseChangeEquiv, LinearEquiv.trans_apply,
    localizedTensorProductEquiv_mkLinearMap_tmul]
  rfl

/-- The tensor product of two localization maps, with the codomain tensor product
taken over an arbitrary localization algebra `A`.  This is the exact algebraic map
underlying restriction from an affine open to a basic open: unlike
`localizedTensorProductBaseChangeEquiv`, it does not require replacing the target
modules by the canonical `LocalizedModule` model. -/
noncomputable def localizedTensorProductMap
    {R : Type u} [CommSemiring R] (S : Submonoid R)
    (A : Type uA) [CommSemiring A] [Algebra R A] [IsLocalization S A]
    {M : Type v} {M' : Type vM} {N : Type w} {N' : Type vN}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
    [AddCommMonoid N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    TensorProduct R M N →ₗ[R] TensorProduct A M' N' :=
  ((IsLocalization.moduleTensorEquiv S A M' N').symm.restrictScalars R :
      TensorProduct R M' N' ≃ₗ[R] TensorProduct A M' N').toLinearMap.comp
    (TensorProduct.map f g)

/-- `localizedTensorProductMap` sends a pure tensor to the tensor of the two
localized sections. -/
@[simp]
lemma localizedTensorProductMap_tmul
    {R : Type u} [CommSemiring R] (S : Submonoid R)
    (A : Type uA) [CommSemiring A] [Algebra R A] [IsLocalization S A]
    {M : Type v} {M' : Type vM} {N : Type w} {N' : Type vN}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
    [AddCommMonoid N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') (m : M) (n : N) :
    localizedTensorProductMap S A f g (m ⊗ₜ[R] n) = f m ⊗ₜ[A] g n := by
  rfl

/-- Tensoring two module-localization maps and changing the tensor base to the
localization algebra is again a module localization.  This is the producer needed
to combine the two quasi-coherent basic-open restriction theorems. -/
theorem isLocalizedModule_localizedTensorProductMap
    {R : Type u} [CommSemiring R] (S : Submonoid R)
    (A : Type uA) [CommSemiring A] [Algebra R A] [IsLocalization S A]
    {M : Type v} {M' : Type vM} {N : Type w} {N' : Type vN}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
    [AddCommMonoid N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (localizedTensorProductMap S A f g) := by
  exact IsLocalizedModule.of_linearEquiv S (TensorProduct.map f g)
    ((IsLocalization.moduleTensorEquiv S A M' N').symm.restrictScalars R)

/-- **The tensor presheaf is localizing on affine basic opens.**  If `A` and `B`
are quasi-coherent, then restriction of their presheaf tensor from an affine open
`U` to `D(f)` exhibits the target as the localization of the source at `powers f`.

The two factor restrictions are localizations by
`isLocalizedModule_basicOpen`.  On pure tensors the restriction map of
`tensorPresheaf A B` is definitionally their tensor product, hence it agrees with
`localizedTensorProductMap`; the algebraic theorem above supplies the resulting
localization. -/
theorem isLocalizedModule_tensorPresheaf_basicOpen (A B : X.Modules)
    [A.IsQuasicoherent] [B.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) :
    IsLocalizedModule (Submonoid.powers f)
      (ModuleCat.Hom.hom
        ((tensorPresheaf A B).map (homOfLE (X.basicOpen_le f)).op)) := by
  letI : Module Γ(X, U) Γ(A, X.basicOpen f) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(A, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : Module Γ(X, U) Γ(B, X.basicOpen f) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(B, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI := hU.isLocalization_basicOpen f
  haveI hA : IsLocalizedModule (Submonoid.powers f) (restrictBasicOpenₗ A f) :=
    isLocalizedModule_basicOpen A hU f
  haveI hB : IsLocalizedModule (Submonoid.powers f) (restrictBasicOpenₗ B f) :=
    isLocalizedModule_basicOpen B hU f
  let g := localizedTensorProductMap (Submonoid.powers f) Γ(X, X.basicOpen f)
    (restrictBasicOpenₗ A f) (restrictBasicOpenₗ B f)
  have hg : ∀ x, ModuleCat.Hom.hom
      ((tensorPresheaf A B).map (homOfLE (X.basicOpen_le f)).op) x = g x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
        exact (ModuleCat.Hom.hom
          ((tensorPresheaf A B).map (homOfLE (X.basicOpen_le f)).op)).map_zero.trans
            g.map_zero.symm
    | tmul a b => rfl
    | add x y hx hy =>
        exact (ModuleCat.Hom.hom
          ((tensorPresheaf A B).map (homOfLE (X.basicOpen_le f)).op)).map_add x y |>.trans
            ((congrArg₂ (· + ·) hx hy).trans (g.map_add x y).symm)
  let hgLoc : IsLocalizedModule (Submonoid.powers f) g :=
    isLocalizedModule_localizedTensorProductMap
      (Submonoid.powers f) Γ(X, X.basicOpen f)
      (restrictBasicOpenₗ A f) (restrictBasicOpenₗ B f)
  refine ⟨hgLoc.map_units, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := hgLoc.surj y
    exact ⟨x, hx.trans (hg x.1).symm⟩
  · intro x₁ x₂ hx
    exact hgLoc.exists_of_eq ((hg x₁).symm.trans (hx.trans (hg x₂)))

/-! ## Quasi-coherence from basic-open section localization

The affine tensor-section formula (see the module docstring) would give, for
`A B : X.Modules` quasi-coherent and `V` affine, the fact that the section restriction
`Γ(A ⊗ B, V) → Γ(A ⊗ B, D(f))` is `IsLocalizedModule (powers f)` (the affine tensor-section
formula composed with the module-localization heart
`(M ⊗_R N)_f ≅ M_f ⊗_{R_f} N_f`, via `localizedTensorProductBaseChangeEquiv`).
The lemma below
packages the *converse* direction of `Scheme.Modules.isLocalizedModule_basicOpen`
(`QuotScheme.lean`): a sheaf of modules whose section restrictions are localizations on all
basic opens of all affine opens is quasi-coherent.  It is the general form of the
pushforward-specialised assembly `pushforward_isQuasicoherent`/
`pushforward_isQuasicoherent_over_affine`, and is exactly the criterion the 01CB
(`tensorObj`/`sheafTensorObj`) instance feeds once the affine section-localization is in hand. -/

open TopologicalSpace in
/-- The family of all affine opens covers a scheme (for the opens Grothendieck topology).
Reconstruction of the `private` `QuotScheme.coversTop_affineOpens`. -/
private theorem coversTop_affineOpens' (S : Scheme.{u}) :
    (Opens.grothendieckTopology ↥S).CoversTop
      (fun U : S.affineOpens => U.1) := by
  intro W y hy
  obtain ⟨V, hVaff, hyV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S) hy
  refine ⟨V, homOfLE hVW, ?_, hyV⟩
  rw [CategoryTheory.Sieve.mem_ofObjects_iff]
  exact ⟨⟨V, hVaff⟩, ⟨𝟙 V⟩⟩

set_option maxHeartbeats 1600000 in
-- The tilde-presentation transport + affine-cover `of_coversTop` assembly (mirroring
-- `QuotScheme.pushforward_isQuasicoherent_over_affine`) needs heartbeat/instance headroom.
set_option synthInstance.maxHeartbeats 800000 in
/-- **Quasi-coherence from basic-open section localization** (the converse of
`Scheme.Modules.isLocalizedModule_basicOpen`).  If for every affine open `U` and every
`f : Γ(X, U)` the section restriction `restrictBasicOpenₗ M f : Γ(M, U) → Γ(M, X.basicOpen f)`
exhibits the target as the localization of the source at `powers f`, then `M` is quasi-coherent.

Quasi-coherence is local (`SheafOfModules.IsQuasicoherent.of_coversTop`) on the affine-opens
cover; on each affine `U` the hypothesis feeds
`isIso_fromTildeΓ_pullback_fromSpec_of_isLocalizedModule` to produce the P1 datum
`IsIso (fromTildeΓ ((pullback hU.fromSpec).obj M))`, whose tilde presentation transports along
`U.ι = isoSpec.hom ≫ fromSpec` back to the geometric slice (`overRestrictPresentationInv`).
This is the pushforward-free form of `Scheme.Modules.pushforward_isQuasicoherent`. -/
theorem isQuasicoherent_of_isLocalizedModule_basicOpen (M : X.Modules)
    (H : ∀ (U : X.Opens), IsAffineOpen U → ∀ (f : Γ(X, U)),
      letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
        Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
      letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
        IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      IsLocalizedModule (Submonoid.powers f) (Scheme.Modules.restrictBasicOpenₗ M f)) :
    M.IsQuasicoherent := by
  haveI hslice : ∀ U : X.affineOpens, (M.over U.1).IsQuasicoherent := by
    intro U
    haveI hP1 : IsIso (Scheme.Modules.fromTildeΓ
        ((Scheme.Modules.pullback U.2.fromSpec).obj M)) :=
      Scheme.Modules.isIso_fromTildeΓ_pullback_fromSpec_of_isLocalizedModule M U.2
        (fun f' => H U.1 U.2 f')
    -- global presentation of the `fromSpec`-pullback, via the tilde presentation
    let eT' : tilde ((modulesSpecToSheaf.obj
          ((Scheme.Modules.pullback U.2.fromSpec).obj M)).presheaf.obj (Opposite.op ⊤))
        ≅ (Scheme.Modules.pullback U.2.fromSpec).obj M :=
      @asIso _ _ _ _
        (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pullback U.2.fromSpec).obj M)) hP1
    have P_M' : ((Scheme.Modules.pullback U.2.fromSpec).obj M).Presentation :=
      SheafOfModules.Presentation.ofIsIso.{u} eT'.hom
        (AlgebraicGeometry.presentationTilde.{u} _ Set.univ (by simp) _ (Submodule.span_eq _))
    -- transport along `U.ι = isoSpec.hom ≫ fromSpec`
    have hcomp : U.2.isoSpec.hom ≫ U.2.fromSpec = U.1.ι := by
      rw [← U.2.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
    have P_ι : ((Scheme.Modules.pullback U.1.ι).obj M).Presentation :=
      SheafOfModules.Presentation.ofIsIso.{u, u, u}
        ((Scheme.Modules.pullbackComp U.2.isoSpec.hom U.2.fromSpec).app M ≪≫
          (Scheme.Modules.pullbackCongr hcomp).app M).hom
        (Scheme.Modules.presentationPullbackOfSchemeIso U.2.isoSpec.symm
          ((Scheme.Modules.pullback U.2.fromSpec).obj M) P_M')
    exact (Scheme.Modules.overRestrictPresentationInv U.1 M P_ι).isQuasicoherent
  exact SheafOfModules.IsQuasicoherent.of_coversTop M
    (fun U : X.affineOpens => U.1) (coversTop_affineOpens' X)

end AlgebraicGeometry.Scheme.Modules
