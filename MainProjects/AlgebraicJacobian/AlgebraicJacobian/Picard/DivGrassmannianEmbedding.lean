/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivPushforwardFlat
import AlgebraicJacobian.Picard.DivGrassmannianClass
import AlgebraicJacobian.Picard.CurveProjectivity
import AlgebraicJacobian.Picard.GrassmannianRepresentability
import AlgebraicJacobian.Picard.RigidPushforwardP1Sheaf
import AlgebraicJacobian.Picard.RigidPushforwardRank
import AlgebraicJacobian.Picard.SerreTwistSections
import AlgebraicJacobian.Picard.TwoTermFiniteFree
import AlgebraicJacobian.Cohomology.QcohTildeSections
import AlgebraicJacobian.RiemannRoch.Ledger.FixedFiberDegree
import AlgebraicJacobian.RiemannRoch.Ledger.UniformRiemannRoch

/-!
# The divisor-to-Grassmannian comparison

This file begins campaign milestone D2': a divisor family is twisted by a fixed
module on the curve, and the pullback--pushforward base-change map followed by
the divisor quotient gives the canonical evaluation morphism used by the
Grassmannian construction.

The core definitions are unconditional and live in
`DivGrassmannianClass`.  In particular,
`DivFamily.grassmannianEval` exists before the Riemann--Roch argument proves it
epimorphic.  Keeping the map separate from its eventual `Epi` proof prevents
uniform generation from becoming an assumption in the definition of the
comparison.

The second section records two affine algebra bridges used to turn finite flat
pushforwards into the rank-indexed local-freeness predicate expected by
`Scheme.LocallyFreeQuotient`.  They do not introduce a representability gate:
their inputs are ordinary finite-presentation, finiteness, and projectivity
properties with producers elsewhere in the Picard development.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme

namespace DivFamily

variable {S X : Scheme.{u}} {π : X ⟶ S} {T : Over S}

private lemma map_tensorHom_comp2 {C D : Type*} [Category C] [MonoidalCategory C]
    [Category D] (F : C ⥤ D) {a₀ a₁ a₂ b₀ b₁ b₂ : C}
    (a : a₀ ⟶ a₁) (b : a₁ ⟶ a₂) (d : b₀ ⟶ b₁) (e : b₁ ⟶ b₂) :
    F.map (MonoidalCategory.tensorHom a d) ≫ F.map (MonoidalCategory.tensorHom b e) =
      F.map (MonoidalCategory.tensorHom (a ≫ b) (d ≫ e)) := by
  rw [← F.map_comp, MonoidalCategory.tensorHom_comp_tensorHom]

/-- Equivalent divisor families have isomorphic twists, compatibly with the
twisted quotient maps.  This is the representative-level descent input for
the D2' Grassmannian comparison. -/
lemma twistQuotientMap_rel (L : X.Modules) {x y : DivFamily π T} (h : x.Rel y) :
    ∃ f : x.twist L ≅ y.twist L,
      x.twistQuotientMap L ≫ f.hom = y.twistQuotientMap L := by
  obtain ⟨f, hf⟩ := h
  refine ⟨Modules.tensorObjIsoOfIso (Iso.refl _) f, ?_⟩
  change ((Modules.tensorObj_right_unitor _).inv ≫
      Modules.tensorObj_functoriality (𝟙 _)
        ((Modules.pullbackUnitIso (pullback.fst π T.hom)).inv ≫ x.q)) ≫
      Modules.tensorObj_functoriality (𝟙 _) f.hom =
    (Modules.tensorObj_right_unitor _).inv ≫
      Modules.tensorObj_functoriality (𝟙 _)
        ((Modules.pullbackUnitIso (pullback.fst π T.hom)).inv ≫ y.q)
  rw [Category.assoc]
  rw [show Modules.tensorObj_functoriality (𝟙 _) _ ≫
        Modules.tensorObj_functoriality (𝟙 _) f.hom =
      Modules.tensorObj_functoriality ((𝟙 _) ≫ (𝟙 _))
        (((Modules.pullbackUnitIso (pullback.fst π T.hom)).inv ≫ x.q) ≫ f.hom) by
    simp only [Modules.tensorObj_functoriality]
    exact map_tensorHom_comp2
      (C := _root_.PresheafOfModules
        ((pullback π T.hom).presheaf ⋙ forget₂ CommRingCat RingCat))
      _ _ _ _ _]
  simp only [Category.id_comp]
  rw [Category.assoc, hf]

/-- Equivalent divisor families have isomorphic evaluation targets, and the
isomorphism commutes with the D2' evaluation maps. -/
lemma grassmannianEval_rel (L : X.Modules) {x y : DivFamily π T} (h : x.Rel y) :
    ∃ f : (Modules.pushforward (pullback.snd π T.hom)).obj (x.twist L) ≅
        (Modules.pushforward (pullback.snd π T.hom)).obj (y.twist L),
      x.grassmannianEval L ≫ f.hom = y.grassmannianEval L := by
  obtain ⟨f, hf⟩ := twistQuotientMap_rel L h
  refine ⟨(Modules.pushforward (pullback.snd π T.hom)).mapIso f, ?_⟩
  change (pushforwardBaseChangeMap π T.hom (pullback.snd π T.hom)
      (pullback.fst π T.hom) pullback.condition L ≫
        (Modules.pushforward (pullback.snd π T.hom)).map (x.twistQuotientMap L)) ≫
      (Modules.pushforward (pullback.snd π T.hom)).map f.hom =
    pushforwardBaseChangeMap π T.hom (pullback.snd π T.hom)
      (pullback.fst π T.hom) pullback.condition L ≫
        (Modules.pushforward (pullback.snd π T.hom)).map (y.twistQuotientMap L)
  rw [Category.assoc, ← Functor.map_comp, hf]

/-- Epimorphy of the D2' evaluation map is invariant under
`DivFamily.Rel`. -/
lemma grassmannianEval_epi_of_rel (L : X.Modules) {x y : DivFamily π T}
    (h : x.Rel y) (hx : Epi (x.grassmannianEval L)) :
    Epi (y.grassmannianEval L) := by
  obtain ⟨f, hf⟩ := grassmannianEval_rel L h
  letI := hx
  rw [← hf]
  infer_instance

/-- The rank-local-freeness obligation on the D2' evaluation target is
invariant under `DivFamily.Rel`. -/
lemma grassmannianTarget_isLocallyFreeOfRank_of_rel
    (L : X.Modules) {x y : DivFamily π T} (hxy : x.Rel y) {d : ℕ}
    (hx : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward (pullback.snd π T.hom)).obj (x.twist L)) d) :
    SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward (pullback.snd π T.hom)).obj (y.twist L)) d := by
  obtain ⟨f, _⟩ := grassmannianEval_rel L hxy
  obtain ⟨ι, U, hU, hloc⟩ := hx
  exact ⟨ι, U, hU, fun i =>
    ⟨(Modules.pullback (U i).ι).mapIso f.symm ≪≫ (hloc i).some⟩⟩

/-- The conditional D2' quotient datum respects the divisor-family
equivalence relation.  The epi and rank witnesses on the second representative
are transported from the first, rather than assumed again. -/
lemma grassmannianQuotient_rel
    (L : X.Modules) {x y : DivFamily π T} [IsLocallyNoetherian S] {d : ℕ}
    (hxy : x.Rel y) (hxEpi : Epi (x.grassmannianEval L))
    (hxLocFree : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward (pullback.snd π T.hom)).obj (x.twist L)) d) :
    (grassmannianQuotient L x hxEpi hxLocFree).Rel
      (grassmannianQuotient L y
        (grassmannianEval_epi_of_rel L hxy hxEpi)
        (grassmannianTarget_isLocallyFreeOfRank_of_rel L hxy hxLocFree)) := by
  obtain ⟨f, hf⟩ := grassmannianEval_rel L hxy
  exact ⟨f, hf⟩

/-- The D2' Grassmannian class is well-defined on `DivFamily.Rel`.  Both
analytic obligations are transported along the relation witness, so this
descent theorem introduces no additional hypotheses. -/
theorem grassmannianClass_eq_of_rel
    (L : X.Modules) {x y : DivFamily π T} [IsLocallyNoetherian S] {d : ℕ}
    (hxy : x.Rel y) (hxEpi : Epi (x.grassmannianEval L))
    (hxLocFree : SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward (pullback.snd π T.hom)).obj (x.twist L)) d) :
    grassmannianClass L x hxEpi hxLocFree =
      grassmannianClass L y
        (grassmannianEval_epi_of_rel L hxy hxEpi)
        (grassmannianTarget_isLocallyFreeOfRank_of_rel L hxy hxLocFree) :=
  Quotient.sound (grassmannianQuotient_rel L hxy hxEpi hxLocFree)

end DivFamily

namespace Modules

/-- **Tensoring on the right preserves epimorphisms in `Scheme.Modules`.**

An epimorphism of module sheaves is locally surjective after forgetting to
abelian-group sheaves.  The presheaf tensor preserves local surjectivity in
either variable by right-exactness of tensor products, and sheafification
turns that local surjectivity back into an epimorphism.  This avoids the false
intermediate claim that a sheaf epimorphism is pointwise epi as a presheaf. -/
theorem tensorObj_functoriality_epi_right
    {X : Scheme.{u}} {M N N' : X.Modules} (g : N ⟶ N') [hg : Epi g] :
    Epi (tensorObj_functoriality (𝟙 M) g) := by
  let J := Opens.grothendieckTopology X
  letI : (SheafOfModules.toSheaf X.ringCatSheaf).PreservesEpimorphisms :=
    AlgebraicGeometry.toSheaf_preservesEpimorphisms X.ringCatSheaf
  have hgSheaf : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map g) :=
    @Functor.map_epi _ _ _ _ (SheafOfModules.toSheaf X.ringCatSheaf) _ _ _ g hg
  have hgLoc : PresheafOfModules.IsLocallySurjective J g.val := by
    exact (Sheaf.isLocallySurjective_iff_epi'
      AddCommGrpCat ((SheafOfModules.toSheaf X.ringCatSheaf).map g)).mpr hgSheaf
  let M' : _root_.PresheafOfModules
      (X.presheaf ⋙ forget₂ CommRingCat RingCat) := M.val
  let g' : MonoidalCategory.tensorObj M' N.val ⟶
      MonoidalCategory.tensorObj M' N'.val := M' ◁ g.val
  have htLoc : PresheafOfModules.IsLocallySurjective J g' :=
    PresheafOfModules.isLocallySurjective_whiskerLeft M' g.val hgLoc
  have htSheafLoc : Sheaf.IsLocallySurjective
      ((presheafToSheaf J AddCommGrpCat).map
        ((PresheafOfModules.toPresheaf
          (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map g')) := by
    rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
    exact htLoc
  have htSheafEpi : Epi
      ((presheafToSheaf J AddCommGrpCat).map
        ((PresheafOfModules.toPresheaf
          (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map g')) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} _).mp htSheafLoc
  have hmap : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (tensorObj_functoriality (𝟙 M) g)) := by
    change Epi ((presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map g'))
    exact htSheafEpi
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map hmap

/-- On an affine scheme, surjectivity on global sections reflects to an
epimorphism between quasi-coherent module sheaves.

The affine tilde--Gamma counits identify the sheaves with the tildes of their
global-section modules.  Naturality of the counit then transports the module
epimorphism back to the original sheaf morphism. -/
theorem epi_of_globalSections_surjective
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (q : M ⟶ N)
    (hq : Function.Surjective
      ((moduleSpecΓFunctor (R := R)).map q).hom) :
    Epi q := by
  have hM : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_quasicoherent M
  have hN : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_quasicoherent N
  haveI hqΓ : Epi ((moduleSpecΓFunctor (R := R)).map q) := by
    rw [ModuleCat.epi_iff_surjective]
    exact hq
  haveI hqtilde : Epi
      ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map q)) := by
    infer_instance
  haveI : IsIso M.fromTildeΓ := hM
  haveI : IsIso N.fromTildeΓ := hN
  have key : M.fromTildeΓ ≫ q =
      (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map q) ≫
        N.fromTildeΓ :=
    ((fromTildeΓNatTrans (R := R)).naturality q).symm
  rw [← epi_comp_iff_of_epi M.fromTildeΓ]
  rw [key]
  exact epi_comp' hqtilde
    (@IsIso.epi_of_iso _ _ _ _ N.fromTildeΓ hN)

/-- **Affine fibrewise-surjectivity criterion.**  A morphism of quasi-coherent
modules on `Spec R` is epi when its global-section cokernel is finite and the
global-section map becomes surjective after base change to every maximal
residue field.

This is the Nakayama globalization needed by the D2 evaluation map: it turns
fieldwise generation into an epimorphism over an arbitrary affine test base,
without a noetherian, representability, or rational-point hypothesis. -/
theorem epi_of_baseChange_surjective
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (q : M ⟶ N)
    [Module.Finite R
      ((moduleSpecΓFunctor (R := R)).obj N ⧸
        LinearMap.range ((moduleSpecΓFunctor (R := R)).map q).hom)]
    (hfib : ∀ (m : Ideal R), m.IsMaximal →
      Function.Surjective
        (((moduleSpecΓFunctor (R := R)).map q).hom.baseChange (R ⧸ m))) :
    Epi q := by
  apply epi_of_globalSections_surjective q
  exact AlgebraicJacobian.TwoTerm.surjective_of_baseChange_quotient_surjective hfib

/-- Finite global sections of the target automatically supply the finite
cokernel in `epi_of_baseChange_surjective`. -/
theorem epi_of_baseChange_surjective_of_finite
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (q : M ⟶ N)
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj N)]
    (hfib : ∀ (m : Ideal R), m.IsMaximal →
      Function.Surjective
        (((moduleSpecΓFunctor (R := R)).map q).hom.baseChange (R ⧸ m))) :
    Epi q := by
  apply epi_of_baseChange_surjective q
  exact hfib

set_option backward.isDefEq.respectTransparency false in
/-- Top-section-ring form of `epi_of_baseChange_surjective`.

This spelling uses the native `Gamma(Spec R, top)`-linear map carried by a
sheaf morphism.  It interfaces directly with residue-field evaluation on the
test scheme and with the existing affine pullback section formula, avoiding
an extra transport through `GammaSpecIso` in geometric fibre arguments. -/
theorem epi_of_appTop_baseChange_surjective
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (q : M ⟶ N)
    [Module.Finite Γ(Spec R, (⊤ : (Spec R).Opens))
      (Γ(N, (⊤ : (Spec R).Opens)) ⧸
        LinearMap.range (q.val.app (.op (⊤ : (Spec R).Opens))).hom)]
    (hfib : ∀ (m : Ideal Γ(Spec R, (⊤ : (Spec R).Opens))), m.IsMaximal →
      Function.Surjective
        ((show Γ(M, (⊤ : (Spec R).Opens)) →ₗ[Γ(Spec R, (⊤ : (Spec R).Opens))]
            Γ(N, (⊤ : (Spec R).Opens)) from
          (q.val.app (.op (⊤ : (Spec R).Opens))).hom).baseChange
            (Γ(Spec R, (⊤ : (Spec R).Opens)) ⧸ m))) :
    Epi q := by
  apply epi_of_globalSections_surjective q
  change Function.Surjective (q.val.app (.op (⊤ : (Spec R).Opens))).hom
  exact AlgebraicJacobian.TwoTerm.surjective_of_baseChange_quotient_surjective
    (A := Γ(Spec R, (⊤ : (Spec R).Opens)))
    (d := (show Γ(M, (⊤ : (Spec R).Opens)) →ₗ[Γ(Spec R, (⊤ : (Spec R).Opens))]
      Γ(N, (⊤ : (Spec R).Opens)) from
        (q.val.app (.op (⊤ : (Spec R).Opens))).hom)) hfib

set_option backward.isDefEq.respectTransparency false in
/-- Finite target sections discharge the cokernel condition in the native
top-section-ring fibrewise-surjectivity criterion. -/
theorem epi_of_appTop_baseChange_surjective_of_finite
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (q : M ⟶ N)
    [Module.Finite Γ(Spec R, (⊤ : (Spec R).Opens))
      Γ(N, (⊤ : (Spec R).Opens))]
    (hfib : ∀ (m : Ideal Γ(Spec R, (⊤ : (Spec R).Opens))), m.IsMaximal →
      Function.Surjective
        ((show Γ(M, (⊤ : (Spec R).Opens)) →ₗ[Γ(Spec R, (⊤ : (Spec R).Opens))]
            Γ(N, (⊤ : (Spec R).Opens)) from
          (q.val.app (.op (⊤ : (Spec R).Opens))).hom).baseChange
            (Γ(Spec R, (⊤ : (Spec R).Opens)) ⧸ m))) :
    Epi q := by
  apply epi_of_appTop_baseChange_surjective q
  exact hfib

set_option backward.isDefEq.respectTransparency false in
/-- **Affine pullback conjugacy for the fibrewise epi criterion.**  For a
morphism between affine schemes, scalar-extension surjectivity of a map on
global sections is equivalent to surjectivity on global sections after
pulling back the corresponding quasi-coherent sheaf map.

The two affine pullback section equivalences conjugate the maps.  Their
naturality is checked on pure tensors and extended by tensor induction.  This
is the morphism-level bridge from residue-ring algebra to geometric fibres
needed by `epi_of_appTop_baseChange_surjective`. -/
theorem baseChange_surjective_iff_pullback_appTop
    {R R' : CommRingCat.{u}} (g : Spec R' ⟶ Spec R)
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (q : M ⟶ N) :
    letI : Algebra Γ(Spec R, (⊤ : (Spec R).Opens))
        Γ(Spec R', (⊤ : (Spec R').Opens)) :=
      (g.appLE ⊤ ⊤ le_top).hom.toAlgebra
    Function.Surjective
        ((show Γ(M, (⊤ : (Spec R).Opens)) →ₗ[Γ(Spec R, (⊤ : (Spec R).Opens))]
            Γ(N, (⊤ : (Spec R).Opens)) from
          (q.val.app (.op (⊤ : (Spec R).Opens))).hom).baseChange
            Γ(Spec R', (⊤ : (Spec R').Opens))) ↔
      Function.Surjective
        (Hom.app ((pullback g).map q) (⊤ : (Spec R').Opens)).hom := by
  letI aAB : Algebra Γ(Spec R, (⊤ : (Spec R).Opens))
      Γ(Spec R', (⊤ : (Spec R').Opens)) :=
    (g.appLE ⊤ ⊤ le_top).hom.toAlgebra
  let d : Γ(M, (⊤ : (Spec R).Opens)) →ₗ[Γ(Spec R, (⊤ : (Spec R).Opens))]
      Γ(N, (⊤ : (Spec R).Opens)) :=
    (q.val.app (.op (⊤ : (Spec R).Opens))).hom
  obtain ⟨⟨eM, heM⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv g M
      (isAffineOpen_top (Spec R')) (isAffineOpen_top (Spec R)) le_top
  obtain ⟨⟨eN, heN⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv g N
      (isAffineOpen_top (Spec R')) (isAffineOpen_top (Spec R)) le_top
  have hcomm : ∀ w : TensorProduct Γ(Spec R, ⊤) Γ(Spec R', ⊤) Γ(M, ⊤),
      (Hom.app ((pullback g).map q) ⊤).hom (eM w) =
        eN (d.baseChange Γ(Spec R', ⊤) w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b x =>
        have hbM : (b ⊗ₜ[Γ(Spec R, ⊤)] x :
            TensorProduct Γ(Spec R, ⊤) Γ(Spec R', ⊤) Γ(M, ⊤)) =
            b • ((1 : Γ(Spec R', ⊤)) ⊗ₜ[Γ(Spec R, ⊤)] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have hbN : (b ⊗ₜ[Γ(Spec R, ⊤)] d x :
            TensorProduct Γ(Spec R, ⊤) Γ(Spec R', ⊤) Γ(N, ⊤)) =
            b • ((1 : Γ(Spec R', ⊤)) ⊗ₜ[Γ(Spec R, ⊤)] d x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have hsmM : eM (b ⊗ₜ[Γ(Spec R, ⊤)] x) =
            b • pullback_app_isoTensor_baseMap g M le_top x := by
          rw [hbM, _root_.map_smul, heM]
        have hsmN : eN (b ⊗ₜ[Γ(Spec R, ⊤)] d x) =
            b • pullback_app_isoTensor_baseMap g N le_top (d x) := by
          rw [hbN, _root_.map_smul, heN]
        rw [LinearMap.baseChange_tmul, hsmM, hsmN, Hom.app_smul]
        exact congrArg (fun y => b • y)
          (pullback_map_app_isoTensor_baseMap g q le_top x)
  constructor
  · intro hd y
    obtain ⟨z, rfl⟩ := eN.surjective y
    obtain ⟨w, hw⟩ := hd z
    refine ⟨eM w, ?_⟩
    rw [hcomm w, hw]
  · intro hp z
    obtain ⟨y, hy⟩ := hp (eN z)
    obtain ⟨w, rfl⟩ := eM.surjective y
    refine ⟨w, eN.injective ?_⟩
    rw [← hcomm w, hy]

set_option synthInstance.maxHeartbeats 1000000 in
-- Normalizing the shrunken presentation data traverses nested subtype and
-- slice-site equivalences.
set_option maxRecDepth 10000 in
-- Slice-site presentation transport also traverses two cover refinements and
-- the open-restriction equivalence.
set_option maxHeartbeats 2000000 in
/-- Tensoring a finitely presented module sheaf on the left by a locally
trivial line bundle preserves finite presentation.  The proof refines a
finite-presentation cover for `F` by a trivializing cover for `L`; on every
intersection the tensor product is isomorphic to `F`, so its finite
presentation transports across that isomorphism. -/
theorem isFinitePresentation_tensorObj_left_of_isLocallyTrivial
    {X : Scheme.{u}} (L F : X.Modules)
    (hL : LineBundle.IsLocallyTrivial L) (hF : F.IsFinitePresentation) :
    (tensorObj L F).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := hF.exists_quasicoherentData
  obtain ⟨I, U, _hUaff, hUtop, hUiso⟩ := hL.exists_trivializing_cover
  let W : q.I × I → X.Opens := fun ij => q.X ij.1 ⊓ U ij.2
  have hWcover : (Opens.grothendieckTopology X).CoversTop W := by
    intro V x hx
    obtain ⟨V', fV, hf, hxV'⟩ := q.coversTop ⊤ x (by trivial)
    obtain ⟨i, ⟨gi⟩⟩ := hf
    have hxq : x ∈ q.X i := (leOfHom gi) hxV'
    have hxU : x ∈ iSup U := by rw [hUtop]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hxU
    obtain ⟨j, hxj⟩ := hxU
    exact ⟨V ⊓ W (i, j), homOfLE inf_le_left,
      ⟨(i, j), ⟨homOfLE inf_le_right⟩⟩, ⟨hx, ⟨hxq, hxj⟩⟩⟩
  let P : ∀ ij, ((tensorObj L F).over (W ij)).Presentation := fun ij => by
    let PF : (F.over (W ij)).Presentation :=
      presentationOverOpens (W ij) F (q.X ij.1)
        (q.presentation ij.1) inf_le_left
    let eL : L.restrict (W ij).ι ≅
        SheafOfModules.unit (W ij : Scheme).ringCatSheaf :=
      restrictIsoUnitOfLE inf_le_right (hUiso ij.2).some
    let eRes : (tensorObj L F).restrict (W ij).ι ≅ F.restrict (W ij).ι :=
      tensorObj_restrict_iso (W ij).ι L F ≪≫
        tensorObjIsoOfIso eL (Iso.refl _) ≪≫
        tensorObj_left_unitor _
    let eOver : (tensorObj L F).over (W ij) ≅ F.over (W ij) :=
      (restrictOverIso (W ij) (tensorObj L F)).symm ≪≫
        (overEquivalence (W ij)).functor.mapIso eRes ≪≫
        restrictOverIso (W ij) F
    exact SheafOfModules.Presentation.ofIsIso.{u, u, u}
      eOver.inv PF
  let qT : (tensorObj L F).QuasicoherentData :=
    { I := q.I × I
      X := W
      coversTop := hWcover
      presentation := P }
  have hP : ∀ ij, (P ij).IsFinite := by
    intro ij
    dsimp only [P]
    letI : (q.presentation ij.1).IsFinite := hq.isFinite_presentation _
    infer_instance
  have hqT : qT.IsFinitePresentation := by
    apply SheafOfModules.QuasicoherentData.IsFinitePresentation.mk
    intro ij
    exact hP ij
  have hsh : qT.shrink.IsFinitePresentation :=
    { isFinite_presentation := fun ij =>
        hqT.isFinite_presentation (Exists.choose ij.property) }
  exact { exists_quasicoherentData := ⟨qT.shrink, hsh⟩ }

set_option maxHeartbeats 2500000 in
-- The affine-locality engine refines both source and base covers through
-- basic opens before transporting the local section equivalence.
/-- Tensoring a quasi-coherent flat sheaf on the left by a locally trivial line
bundle preserves flatness over an arbitrary base morphism.  The affine-cover
criterion is fed by affine trivialising charts of the line bundle; on each
chart the tensor is identified with the original sheaf. -/
theorem coherentSheafFlat_tensorObj_left_of_isLocallyTrivial
    {T X : Scheme.{u}} (q : X ⟶ T) (L F : X.Modules)
    (hL : LineBundle.IsLocallyTrivial L)
    (hFp : F.IsFinitePresentation)
    (hF : CoherentSheafFlat q F) :
    CoherentSheafFlat q (tensorObj L F) := by
  letI : F.IsFinitePresentation := hFp
  letI : (tensorObj L F).IsFinitePresentation :=
    isFinitePresentation_tensorObj_left_of_isLocallyTrivial L F hL hFp
  choose U hUaff hxU _hUtop using fun x : X =>
    exists_isAffineOpen_mem_and_subset (x := q.base x)
      (U := (⊤ : T.Opens)) (by trivial)
  choose W hxW hWaff hWle hWiso using fun x : X =>
    hL.exists_affine_trivializing_le (x := x) (W := q ⁻¹ᵁ U x) (hxU x)
  intro U0 hU0 W0 hW0 e0
  refine flat_section_of_affine_cover q (tensorObj L F) W hWaff U hUaff hWle
    (fun x => ⟨x, hxW x⟩) ?_ hU0 hW0 e0
  intro x
  letI : Module Γ(T, U x) Γ((tensorObj L F), W x) :=
    Module.compHom _ (q.appLE (U x) (W x) (hWle x)).hom
  letI : Module Γ(T, U x) Γ(F, W x) :=
    Module.compHom _ (q.appLE (U x) (W x) (hWle x)).hom
  haveI : Module.Flat Γ(T, U x) Γ(F, W x) := hF (hUaff x) (hWaff x) (hWle x)
  let eL : L.restrict (W x).ι ≅
      SheafOfModules.unit (W x : Scheme).ringCatSheaf := (hWiso x).some
  let eRes : (tensorObj L F).restrict (W x).ι ≅ F.restrict (W x).ι :=
    tensorObj_restrict_iso (W x).ι L F ≪≫
      tensorObjIsoOfIso eL (Iso.refl _) ≪≫
      tensorObj_left_unitor _
  let eX := sectionLinearEquivOfRestrictIso (W x) eRes
  letI : Algebra Γ(T, U x) Γ(X, W x) :=
    (q.appLE (U x) (W x) (hWle x)).hom.toAlgebra
  letI : IsScalarTower Γ(T, U x) Γ(X, W x) Γ(F, W x) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower Γ(T, U x) Γ(X, W x)
      Γ((tensorObj L F), W x) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : LinearMap.CompatibleSMul Γ((tensorObj L F), W x) Γ(F, W x)
      Γ(T, U x) Γ(X, W x) :=
    ⟨fun f c z => by
      rw [← IsScalarTower.algebraMap_smul (Γ(X, W x)) c z,
        ← IsScalarTower.algebraMap_smul (Γ(X, W x)) c (f z), f.map_smul]⟩
  exact Module.Flat.of_linearEquiv (M := Γ(F, W x))
    (eX.restrictScalars (Γ(T, U x)))

/-- Isomorphic module sheaves have the same annihilator ideal sheaf.  This is
the scheme-level transport needed to make schematic support, hence proper
support, invariant under isomorphism. -/
theorem annihilator_eq_of_iso
    {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    annihilator F = annihilator G := by
  unfold annihilator
  congr 1
  funext U
  let eU : Γ(F, U.1) ≃ₗ[Γ(X, U.1)] Γ(G, U.1) :=
    ((toPresheafOfModules X ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj
        (Opposite.op U.1)).mapIso e).toLinearEquiv
  ext r
  constructor
  · intro hr
    rw [Module.mem_annihilator] at hr ⊢
    intro x
    obtain ⟨y, rfl⟩ := eU.surjective x
    rw [← eU.map_smul, hr, map_zero]
  · intro hr
    rw [Module.mem_annihilator] at hr ⊢
    intro x
    apply eU.injective
    rw [eU.map_zero, eU.map_smul, hr]

/-- The annihilator of the left tensor factor annihilates the canonical tensor
product.  This transports the existing sheaf-tensor inclusion across the
comparison isomorphism. -/
theorem annihilator_le_annihilator_tensorObj_left
    {X : Scheme.{u}} (A B : X.Modules) :
    annihilator A ≤ annihilator (tensorObj A B) := by
  rw [annihilator_eq_of_iso (tensorObjIsoSheafTensorObj A B)]
  exact annihilator_le_annihilator_sheafTensorObj A B

/-- The annihilator of the right tensor factor also annihilates the canonical
tensor product, by symmetry. -/
theorem annihilator_le_annihilator_tensorObj_right
    {X : Scheme.{u}} (A B : X.Modules) :
    annihilator B ≤ annihilator (tensorObj A B) := by
  calc
    annihilator B ≤ annihilator (tensorObj B A) :=
      annihilator_le_annihilator_tensorObj_left B A
    _ = annihilator (tensorObj A B) :=
      annihilator_eq_of_iso (tensorObj_braiding B A)

/-- Tensoring on the left by a line bundle preserves the annihilator exactly.
The reverse inclusion tensors once more by a tensor inverse of the line bundle
and contracts the inverse pair. -/
theorem annihilator_tensorObj_eq_right_of_isLocallyTrivial
    {X : Scheme.{u}} (L F : X.Modules)
    (hL : LineBundle.IsLocallyTrivial L) :
    annihilator (tensorObj L F) = annihilator F := by
  obtain ⟨Linv, _hLinv, ⟨e⟩⟩ := exists_tensorObj_inverse hL
  apply le_antisymm
  · calc
      annihilator (tensorObj L F) ≤
          annihilator (tensorObj Linv (tensorObj L F)) :=
        annihilator_le_annihilator_tensorObj_right Linv (tensorObj L F)
      _ = annihilator F := annihilator_eq_of_iso
        (tensorObj_assoc_iso.symm ≪≫
          tensorObjIsoOfIso (tensorObj_braiding Linv L ≪≫ e) (Iso.refl F) ≪≫
          tensorObj_left_unitor F)
  · exact annihilator_le_annihilator_tensorObj_right L F

/-- Proper schematic support is invariant under an isomorphism of module
sheaves. -/
theorem HasProperSupport.of_iso {X S : Scheme.{u}} (f : X ⟶ S)
    {A C : X.Modules} (e : A ≅ C) (hA : HasProperSupport f A) :
    HasProperSupport f C := by
  change IsProper ((annihilator C).subschemeι ≫ f)
  rw [← annihilator_eq_of_iso e]
  exact hA

/-- Proper support transfers through the right factor of the canonical tensor.
The existing annihilator argument is left-sided; tensor symmetry supplies the
right-sided form without any flatness or finiteness hypothesis. -/
theorem hasProperSupport_tensorObj_right
    {X S : Scheme.{u}} (f : X ⟶ S) (A : X.Modules) {B : X.Modules}
    (hB : HasProperSupport f B) :
    HasProperSupport f (tensorObj A B) := by
  have hBAsh : HasProperSupport f (sheafTensorObj B A) :=
    hasProperSupport_sheafTensorObj f A hB
  have hBAt : HasProperSupport f (tensorObj B A) :=
    HasProperSupport.of_iso f (tensorObjIsoSheafTensorObj B A).symm hBAsh
  exact HasProperSupport.of_iso f (tensorObj_braiding B A) hBAt

/-- The same right-factor support transfer for the sheaf-tensor spelling. -/
theorem hasProperSupport_sheafTensorObj_right
    {X S : Scheme.{u}} (f : X ⟶ S) (A : X.Modules) {B : X.Modules}
    (hB : HasProperSupport f B) :
    HasProperSupport f (sheafTensorObj A B) :=
  HasProperSupport.of_iso f (tensorObjIsoSheafTensorObj A B)
    (hasProperSupport_tensorObj_right f A hB)

/-- Locally quasi-finite support is unchanged by tensoring on the left with a
locally trivial line bundle.  The statement is deliberately phrased for an
arbitrary morphism so it can feed both the affine rank bridge and arbitrary
test-base descent. -/
theorem locallyQuasiFinite_tensorObj_left_iff
    {X S : Scheme.{u}} (f : X ⟶ S) (L F : X.Modules)
    (hL : LineBundle.IsLocallyTrivial L) :
    LocallyQuasiFinite (schematicSupportι (tensorObj L F) ≫ f) ↔
      LocallyQuasiFinite (schematicSupportι F ≫ f) := by
  change LocallyQuasiFinite ((annihilator (tensorObj L F)).subschemeι ≫ f) ↔
    LocallyQuasiFinite ((annihilator F).subschemeι ≫ f)
  rw [annihilator_tensorObj_eq_right_of_isLocallyTrivial L F hL]

/-- The finite-support morphism property is likewise preserved by a locally
trivial tensor factor. -/
theorem isFinite_tensorObj_left_iff
    {X S : Scheme.{u}} (f : X ⟶ S) (L F : X.Modules)
    (hL : LineBundle.IsLocallyTrivial L) :
    IsFinite (schematicSupportι (tensorObj L F) ≫ f) ↔
      IsFinite (schematicSupportι F ≫ f) := by
  change IsFinite ((annihilator (tensorObj L F)).subschemeι ≫ f) ↔
    IsFinite ((annihilator F).subschemeι ≫ f)
  rw [annihilator_tensorObj_eq_right_of_isLocallyTrivial L F hL]

set_option backward.isDefEq.respectTransparency false in
/-- A finite global presentation of a module sheaf on `Spec R` induces a
finite presentation of its module of global sections.

The proof reconstructs the finite module cokernel underlying the sheaf
presentation.  Full faithfulness of `tilde` identifies that cokernel with the
global-section module, without any noetherian hypothesis on `R`. -/
theorem module_finitePresentation_top_of_presentation
    {R : CommRingCat.{u}} (M : (Spec R).Modules) (P : M.Presentation)
    [P.IsFinite] :
    Module.FinitePresentation R Γ(M, (⊤ : (Spec R).Opens)) := by
  let g := (tilde.functor R).preimage <|
    (tildeFinsupp _).hom ≫ P.relations.π ≫ kernel.ι _ ≫ (tildeFinsupp _).inv
  let Q := (P.generators.I →₀ R) ⧸ LinearMap.range g.hom
  have hQ : Module.FinitePresentation R Q := by
    apply Module.finitePresentation_of_surjective
      (Submodule.mkQ (LinearMap.range g.hom)) (Submodule.mkQ_surjective _)
    rw [Submodule.ker_mkQ]
    simpa only [LinearMap.range_eq_map] using Module.Finite.fg_top.map g.hom
  let iso : cokernel ((tilde.functor R).map g) ≅
      cokernel (P.relations.π ≫ kernel.ι _) := by
    refine cokernel.mapIso _ _ (tildeFinsupp _) (tildeFinsupp _) ?_
    simp only [g, (tilde.functor R).map_preimage]
    simp
  let eC : tilde (cokernel g) ≅ M :=
    PreservesCokernel.iso (tilde.functor R) g ≪≫ iso ≪≫
      IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) P.isColimit
  let eQ : tilde (ModuleCat.of R Q) ≅ M :=
    (tilde.functor R).mapIso (ModuleCat.cokernelIsoRangeQuotient g).symm ≪≫ eC
  haveI : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_presentation M P
  let eΓ : ModuleCat.of R Q ≅ moduleSpecΓFunctor.obj M :=
    (tilde.functor R).preimageIso (eQ ≪≫ qcoh_iso_tilde_sections M)
  exact eΓ.toLinearEquiv.finitePresentation_iff.mp hQ

/-- On an affine scheme, finite projective global sections of constant stalk
rank produce the project-local rank-indexed freeness predicate used by the
Grassmannian functor. -/
theorem isLocallyFreeOfRank_of_finite_projective_sections
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (hfin : Module.Finite R Γ(M, (⊤ : (Spec R).Opens)))
    (hproj : Module.Projective R Γ(M, (⊤ : (Spec R).Opens)))
    {d : ℕ} (hrank : ∀ t : PrimeSpectrum R, sectionsRankAtStalk M t = d) :
    SheafOfModules.IsLocallyFreeOfRank M d := by
  choose U htU hfree using fun t =>
    exists_free_restrict_of_finite_projective_sections' M hfin hproj t
  refine ⟨PrimeSpectrum R, U, ?_, fun t => ?_⟩
  · rw [eq_top_iff]
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, htU t⟩
  · exact (hrank t) ▸ hfree t

set_option maxHeartbeats 1600000 in
-- Support descent expands two affine base-change transports; the default budget
-- times out before the affine-instance reduction finishes.
set_option synthInstance.maxHeartbeats 400000 in
/-- **Finite-support base change.**  A quasi-coherent module whose schematic
support is finite over the base has the expected arbitrary base-change
isomorphism.  The support descent presentation turns the statement into the
affine base-change theorem twice: once for the finite support map and once for
its closed immersion into the ambient scheme.  No flatness of the base change
is used. -/
noncomputable def pullbackPushforwardIso_of_isFinite_schematicSupport
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) (F : X.Modules) [F.IsQuasicoherent]
    (hfin : IsFinite (schematicSupportι F ≫ f)) :
    (pullback g).obj ((pushforward f).obj F) ≅
      (pushforward f').obj ((pullback g').obj F) := by
  let i := schematicSupportι F
  let N := (pullback i).obj F
  haveI : IsAffineHom i :=
    inferInstanceAs (IsAffineHom F.annihilator.subschemeι)
  haveI : IsFinite (i ≫ f) := hfin
  haveI : IsAffineHom (i ≫ f) := inferInstance
  have sq₁ : IsPullback (Limits.pullback.fst i g') (Limits.pullback.snd i g') i g' :=
    IsPullback.of_hasPullback _ _
  have sqZ : IsPullback (Limits.pullback.fst i g')
      (Limits.pullback.snd i g' ≫ f') (i ≫ f) g :=
    sq₁.paste_vert sq
  haveI : IsAffineHom (Limits.pullback.snd i g') :=
    MorphismProperty.pullback_snd _ _ (inferInstance : IsAffineHom i)
  haveI : IsAffineHom (Limits.pullback.snd i g' ≫ f') :=
    MorphismProperty.of_isPullback sqZ inferInstance
  haveI : N.IsQuasicoherent := pullback_isQuasicoherent_hom i F inferInstance
  let hdesc : F ≅ (pushforward i).obj N := schematicSupportDescentIso F
  let eSupport := AlgebraicGeometry.pushforwardPullbackBaseChangeIso sqZ N
  let eImmersion := AlgebraicGeometry.pushforwardPullbackBaseChangeIso sq₁ N
  exact (pullback g).mapIso
      ((pushforward f).mapIso hdesc ≪≫
        ((pushforwardComp i f).app N).symm) ≪≫
    eSupport ≪≫
    (pushforwardComp (Limits.pullback.snd i g') f').app _ ≪≫
    (pushforward f').mapIso
      (eImmersion.symm ≪≫ (pullback g').mapIso hdesc.symm)

set_option backward.isDefEq.respectTransparency false in
/-- The fibre of affine global sections computes fibre `H⁰` once pushforward
commutes with the residue-field base change. -/
theorem fiberRank_gammaTop_eq_fiberH0_of_iso
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    (F : X.Modules) [F.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f]
    (t : PrimeSpectrum R)
    (e : (Scheme.Modules.pullback
          ((Spec R).fromSpecResidueField (t : Spec R))).obj
          ((pushforward f).obj F) ≅
        (pushforward (f.fiberToSpecResidueField t)).obj (f.fiberModule t F)) :
    Module.finrank t.asIdeal.ResidueField
        (t.asIdeal.Fiber
          Γ((pushforward f).obj F, (⊤ : (Spec R).Opens))) =
      f.fiberH0 F t := by
  let M := (pushforward f).obj F
  haveI : M.IsQuasicoherent := pushforward_isQuasicoherent f F
  letI aRK : Algebra Γ(Spec R, ⊤)
      Γ(Spec ((Spec R).residueField t), ⊤) :=
    (((Spec R).fromSpecResidueField t).appLE ⊤ ⊤ le_top).hom.toAlgebra
  have step₁ : Module.finrank t.asIdeal.ResidueField
        (t.asIdeal.Fiber Γ(M, (⊤ : (Spec R).Opens))) =
      Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
        (TensorProduct Γ(Spec R, ⊤)
          Γ(Spec ((Spec R).residueField t), ⊤) Γ(M, ⊤)) := by
    refine finrank_tensor_eq_of_ringEquiv
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
      (specResidueFieldRingEquiv R t) ?_ (AddEquiv.refl _) ?_
    · intro r
      have h := appLE_fromSpecResidueField_apply R t
        ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm r)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm
    · intro r n
      rw [smul_gammaSpecTop M r n]
      rfl
  obtain ⟨⟨ePull, -⟩⟩ := pullback_app_isoTensor_baseMap_sectionLinearEquiv
    ((Spec R).fromSpecResidueField (t : Spec R)) M (isAffineOpen_top _)
      (isAffineOpen_top _) le_top
  letI fiberBase := (f.fiberToSpecResidueField t).baseSectionsModule
    (f.fiberModule t F) (⊤ : (f.fiber t).Opens)
  let eSheaf : Γ(((Scheme.Modules.pullback
      ((Spec R).fromSpecResidueField t)).obj M), ⊤) ≃ₗ[
        Γ(Spec ((Spec R).residueField t), ⊤)]
      Γ(((Scheme.Modules.pushforward (f.fiberToSpecResidueField t)).obj
        (f.fiberModule t F)), ⊤) := by
    let eAdd := ((toPresheafOfModules (Spec ((Spec R).residueField t)) ⋙
      PresheafOfModules.evaluation (Spec ((Spec R).residueField t)).ringCatSheaf.obj
        (Opposite.op ⊤)).mapIso e).toLinearEquiv.toAddEquiv
    refine eAdd.toLinearEquiv ?_
    intro r x
    exact Scheme.Modules.Hom.app_smul e.hom r x
  let ePush := Scheme.Modules.pushforwardTopEquivBaseSections
    (f.fiberToSpecResidueField t) (f.fiberModule t F)
  let eΓ := eSheaf.trans ePush
  have step₂ : Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
        (TensorProduct Γ(Spec R, ⊤)
          Γ(Spec ((Spec R).residueField t), ⊤) Γ(M, ⊤)) =
      Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
        Γ((f.fiberModule t F), ⊤) := by
    exact (LinearEquiv.finrank_eq ePull).trans (LinearEquiv.finrank_eq eΓ)
  have step₃ : Module.finrank Γ(Spec ((Spec R).residueField t), ⊤)
        Γ((f.fiberModule t F), ⊤) = f.fiberH0 F t := by
    letI := f.fiberSectionsModule t (f.fiberModule t F)
    refine finrank_eq_of_ringEquiv_addEquiv
      (Scheme.ΓSpecIso ((Spec R).residueField t)).commRingCatIsoToRingEquiv
      (AddEquiv.refl _) ?_
    intro r m
    change r • m = _
    rw [Scheme.Hom.baseSectionsModule_smul_def]
    change _ = ((f.fiberResidueMap t).hom
      ((Scheme.ΓSpecIso ((Spec R).residueField t)).commRingCatIsoToRingEquiv r)) • m
    congr 1
    simp only [Scheme.Hom.fiberResidueMap, CommRingCat.hom_comp, RingHom.comp_apply]
    have hLE : (f.fiberToSpecResidueField t).appLE ⊤ ⊤ le_top =
        (f.fiberToSpecResidueField t).appTop := Scheme.Hom.appLE_eq_app _
    rw [hLE]
    congr 1
    have h₁ := congrArg (fun φ : Γ(Spec ((Spec R).residueField t), ⊤) ⟶
        Γ(Spec ((Spec R).residueField t), ⊤) => φ.hom r)
      (Scheme.ΓSpecIso ((Spec R).residueField t)).hom_inv_id
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at h₁
    exact h₁.symm
  exact step₁.trans (step₂.trans step₃)

theorem fiberRank_gammaTop_eq_fiberH0_of_isFinite_schematicSupport
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    (F : X.Modules) [F.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f]
    (hfin : IsFinite (schematicSupportι F ≫ f)) (t : PrimeSpectrum R) :
    Module.finrank t.asIdeal.ResidueField
        (t.asIdeal.Fiber
          Γ((pushforward f).obj F, (⊤ : (Spec R).Opens))) =
      f.fiberH0 F t :=
  fiberRank_gammaTop_eq_fiberH0_of_iso f F t
    (pullbackPushforwardIso_of_isFinite_schematicSupport
      (IsPullback.of_hasPullback f
        ((Spec R).fromSpecResidueField (t : Spec R))) F hfin)

end Modules

namespace DivFamily

variable {S X : Scheme.{u}} {π : X ⟶ S} {T : Over S}

/-- The divisor quotient remains epi after tensoring with any module.

This is the pre-pushforward epimorphism in the D2' evaluation map.  It uses
only the `DivFamily` quotient's existing epimorphism; global generation after
pushforward remains the separate curve-theoretic obligation. -/
theorem twistQuotientMap_epi (L : X.Modules) (x : DivFamily π T) :
    Epi (x.twistQuotientMap L) := by
  letI := x.epi
  haveI : Epi (Modules.tensorObj_functoriality
      (𝟙 ((Modules.pullback (pullback.fst π T.hom)).obj L))
      ((Modules.pullbackUnitIso (pullback.fst π T.hom)).inv ≫ x.q)) :=
    Modules.tensorObj_functoriality_epi_right _
  change Epi ((Modules.tensorObj_right_unitor
    ((Modules.pullback (pullback.fst π T.hom)).obj L)).inv ≫
      Modules.tensorObj_functoriality
        (𝟙 ((Modules.pullback (pullback.fst π T.hom)).obj L))
        ((Modules.pullbackUnitIso (pullback.fst π T.hom)).inv ≫ x.q))
  letI : Epi (Modules.tensorObj_right_unitor
      ((Modules.pullback (pullback.fst π T.hom)).obj L)).inv := inferInstance
  infer_instance

/-- The D2 twist is finitely presented whenever the fixed twist is a line
bundle.  Both antecedents are already produced by the construction: local
triviality survives pullback, and a divisor family carries finite
presentation of its structure module. -/
theorem twist_isFinitePresentation
    (L : X.Modules) (hL : LineBundle.IsLocallyTrivial L)
    (x : DivFamily π T) :
    (x.twist L).IsFinitePresentation := by
  dsimp [twist]
  exact Modules.isFinitePresentation_tensorObj_left_of_isLocallyTrivial _ _
    (hL.pullback (pullback.fst π T.hom)) x.isFinitePresentation

/-- Quasi-coherence of the D2 twist, obtained from its finite presentation. -/
theorem twist_isQuasicoherent
    (L : X.Modules) (hL : LineBundle.IsLocallyTrivial L)
    (x : DivFamily π T) :
    (x.twist L).IsQuasicoherent := by
  letI : (x.twist L).IsFinitePresentation := x.twist_isFinitePresentation L hL
  infer_instance

/-- Flatness of the D2 twist over the test base.  This is inherited from the
divisor family's flat structure sheaf through the local line-bundle charts. -/
theorem twist_isCoherentSheafFlat
    (L : X.Modules) (hL : LineBundle.IsLocallyTrivial L)
    (x : DivFamily π T) :
    CoherentSheafFlat (pullback.snd π T.hom) (x.twist L) := by
  dsimp [twist]
  exact Modules.coherentSheafFlat_tensorObj_left_of_isLocallyTrivial
    (pullback.snd π T.hom)
    ((Modules.pullback (pullback.fst π T.hom)).obj L) x.F
    (hL.pullback (pullback.fst π T.hom)) x.isFinitePresentation x.flat

/-- The D2 twist has proper support whenever the divisor structure sheaf does.
This is unconditional in the twist module: it is the right-factor support
transport, so no rational point, representability, or flatness hypothesis is
introduced here. -/
theorem twist_hasProperSupport (L : X.Modules) (x : DivFamily π T) :
    Modules.HasProperSupport (pullback.snd π T.hom) (x.twist L) := by
  dsimp [twist]
  exact Modules.hasProperSupport_tensorObj_right
    (pullback.snd π T.hom)
    ((Modules.pullback (pullback.fst π T.hom)).obj L) x.properSupport

/-- Tensoring a divisor module by a line bundle preserves its schematic
support, hence preserves the locally-quasi-finite support condition in both
directions. -/
theorem twist_locallyQuasiFinite_iff
    (L : X.Modules) (hL : LineBundle.IsLocallyTrivial L)
    (x : DivFamily π T) :
    LocallyQuasiFinite
        (Modules.schematicSupportι (x.twist L) ≫ pullback.snd π T.hom) ↔
      LocallyQuasiFinite
        (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) := by
  dsimp [twist]
  change LocallyQuasiFinite
      ((Modules.annihilator
        (Modules.tensorObj
          ((Modules.pullback (pullback.fst π T.hom)).obj L) x.F)).subschemeι ≫
        pullback.snd π T.hom) ↔
    LocallyQuasiFinite
      ((Modules.annihilator x.F).subschemeι ≫ pullback.snd π T.hom)
  rw [Modules.annihilator_tensorObj_eq_right_of_isLocallyTrivial
    ((Modules.pullback (pullback.fst π T.hom)).obj L) x.F
    (hL.pullback (pullback.fst π T.hom))]

/-- A locally trivial twist has exactly the divisor's annihilator ideal.  Thus
the D2 target has the same schematic support as the original divisor family,
not merely a closed subscheme of it. -/
theorem twist_annihilator_eq_of_isLocallyTrivial
    (L : X.Modules) (hL : LineBundle.IsLocallyTrivial L)
    (x : DivFamily π T) :
    Modules.annihilator (x.twist L) = Modules.annihilator x.F := by
  dsimp [twist]
  exact Modules.annihilator_tensorObj_eq_right_of_isLocallyTrivial _ _
    (hL.pullback (pullback.fst π T.hom))

/-- Finiteness of the schematic support is unchanged by the D2 line-bundle
twist. -/
theorem twist_isFiniteSupport_iff
    (L : X.Modules) (hL : LineBundle.IsLocallyTrivial L)
    (x : DivFamily π T) :
    IsFinite (Modules.schematicSupportι (x.twist L) ≫ pullback.snd π T.hom) ↔
      IsFinite (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) := by
  dsimp [twist]
  exact Modules.isFinite_tensorObj_left_iff
    (pullback.snd π T.hom)
    ((Modules.pullback (pullback.fst π T.hom)).obj L) x.F
    (hL.pullback (pullback.fst π T.hom))

/-- The finite-support producer for the twisted D2 target.  It spends only the
same locally-quasi-finite support binder already carried by the divisor row;
properness comes from `DivFamily.properSupport`, and exact support preservation
then transports finiteness to the twist. -/
theorem twist_isFiniteSupport
    (L : X.Modules) (hL : LineBundle.IsLocallyTrivial L)
    (x : DivFamily π T)
    [LocallyQuasiFinite
      (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom)] :
    IsFinite (Modules.schematicSupportι (x.twist L) ≫ pullback.snd π T.hom) := by
  rw [twist_isFiniteSupport_iff L hL x]
  haveI : IsProper
      (Modules.schematicSupportι x.F ≫ pullback.snd π T.hom) := x.properSupport
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

set_option backward.isDefEq.respectTransparency false in
/-- On an affine test base, a finite-flat divisor pushforward is locally free
of the divisor's fibre degree.  The proof supplies finite presentation and
projectivity from the existing pushforward producers; the rank is computed by
the finite-support base-change bridge above, not assumed separately.

This is the available affine/noetherian bridge: it still requires the explicit
`LocallyQuasiFinite` support instance and `[IsNoetherianRing R]`.  It is not yet
the arbitrary-`Over S` producer for the twisted D2' target. -/
theorem pushforward_isLocallyFreeOfRank
    {R : CommRingCat.{u}} {S X : Scheme.{u}} {π : X ⟶ S}
    [IsProper π] (f : Spec R ⟶ S) [IsNoetherianRing R]
    (x : DivFamily π (Over.mk f))
    [LocallyQuasiFinite
      (Modules.schematicSupportι x.F ≫ pullback.snd π (Over.mk f).hom)]
    {d : ℕ} (hx : x.HasFiberDeg d) :
    SheafOfModules.IsLocallyFreeOfRank
      ((Modules.pushforward (pullback.snd π f)).obj x.F) d := by
  letI : IsLocallyNoetherian (Over.mk f).left := by
    change IsLocallyNoetherian (Spec R)
    infer_instance
  letI : x.F.IsFinitePresentation := x.isFinitePresentation
  letI : x.F.IsQuasicoherent := by
    exact inferInstance
  let q := pullback.snd π (Over.mk f).hom
  let M : (Spec R).Modules := (Modules.pushforward q).obj x.F
  haveI : QuasiCompact q := by
    dsimp [q]
    infer_instance
  haveI : QuasiSeparated q := by
    dsimp [q]
    infer_instance
  haveI : M.IsFinitePresentation := x.isFinitePresentation_pushforward
  haveI : M.IsQuasicoherent := x.isQuasicoherent_pushforward
  letI baseM := ((𝟙 (Spec R)) : Spec R ⟶ Spec R).baseSectionsModule M
    (⊤ : (Spec R).Opens)
  haveI : IsNoetherianRing Γ(Spec R, (⊤ : (Spec R).Opens)) :=
    isNoetherianRing_of_ringEquiv R
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
  have hfinΓ : Module.Finite Γ(Spec R, (⊤ : (Spec R).Opens))
      Γ(M, (⊤ : (Spec R).Opens)) :=
    Modules.module_finite_sections_of_isFinitePresentation M
      ⟨⊤, isAffineOpen_top (Spec R)⟩
  have hfin : Module.Finite R Γ(M, (⊤ : (Spec R).Opens)) :=
    module_finite_top_of_gammaSpecTop M hfinΓ
  letI : Module.Finite Γ(Spec R, (⊤ : (Spec R).Opens))
      Γ(M, (⊤ : (Spec R).Opens)) := hfinΓ
  have hflatΓ : Module.Flat Γ(Spec R, (⊤ : (Spec R).Opens))
      Γ(M, (⊤ : (Spec R).Opens)) :=
    Modules.flat_sections_of_coherentSheafFlat_id
      x.coherentSheafFlat_id_pushforward (isAffineOpen_top (Spec R))
  letI : Module.Flat Γ(Spec R, (⊤ : (Spec R).Opens))
      Γ(M, (⊤ : (Spec R).Opens)) := hflatΓ
  letI : Module.FinitePresentation Γ(Spec R, (⊤ : (Spec R).Opens))
      Γ(M, (⊤ : (Spec R).Opens)) :=
    Module.finitePresentation_of_finite Γ(Spec R, (⊤ : (Spec R).Opens)) _
  have hprojΓ : Module.Projective Γ(Spec R, (⊤ : (Spec R).Opens))
      Γ(M, (⊤ : (Spec R).Opens)) :=
    Module.Flat.projective_of_finitePresentation
  have hproj : Module.Projective R Γ(M, (⊤ : (Spec R).Opens)) :=
    module_projective_top_of_gammaSpecTop M hprojΓ
  letI : Module.Projective R Γ(M, (⊤ : (Spec R).Opens)) := hproj
  letI : Module.Flat R Γ(M, (⊤ : (Spec R).Opens)) := Module.Flat.of_projective
  apply Modules.isLocallyFreeOfRank_of_finite_projective_sections M hfin inferInstance
  intro t
  change Module.rankAtStalk Γ(M, (⊤ : (Spec R).Opens)) t = d
  rw [Module.rankAtStalk_eq]
  haveI : IsProper (Modules.schematicSupportι x.F ≫ q) := x.properSupport
  have hsupport : IsFinite (Modules.schematicSupportι x.F ≫ q) :=
    IsFinite.of_isProper_of_locallyQuasiFinite _
  exact (Modules.fiberRank_gammaTop_eq_fiberH0_of_isFinite_schematicSupport
    q x.F hsupport t).trans (hx t)

end DivFamily

end Scheme

namespace FiberCoordinateData

/-- Extension-uniform global generation for every campaign curve.

The fixed coordinate construction supplies the `UniformBaseDivisor` witness
that the generation theorem needs, so this endpoint has only the standard
smooth, proper, geometrically integral curve assumptions.  It is the
fieldwise generation input for the D2' evaluation map; passing from all
geometric fibres to an epi over an arbitrary test base is a separate descent
step. -/
theorem uniformGeneration_fixedCoordinate
    {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIntegral C.hom] :
    UniformGeneration C :=
  uniformGeneration_of_uniformBaseDivisor C
    (uniformBaseDivisor_fixedCoordinate C)

end FiberCoordinateData

namespace Adelic

/-- A concrete D2' twist witness, selected from the projectivity theorem for a
smooth proper geometrically integral curve.  Keeping the choice named makes
the projective input consumable by later Grassmannian constructions without
adding a rational-point binder or another representability class.

At this mathlib pin `IsProjectiveWith` is Scheme-`0`-valued, so this named
witness is the small-universe (`k : Type`) route rather than a universe-polymorphic
seam witness. -/
noncomputable def d2ProjectiveTwist
    {k : Type} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : C.left.Modules :=
  Classical.choose (exists_isProjectiveWith_of_smoothProperGeometricallyIntegral C)

theorem d2ProjectiveTwist_isProjectiveWith
    {k : Type} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    C.hom.IsProjectiveWith (d2ProjectiveTwist C) :=
  Classical.choose_spec (exists_isProjectiveWith_of_smoothProperGeometricallyIntegral C)

theorem d2ProjectiveTwist_isLocallyTrivial
    {k : Type} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    Scheme.LineBundle.IsLocallyTrivial (d2ProjectiveTwist C) := by
  obtain ⟨n, hn, i, hi, hcomp, ⟨e⟩⟩ :=
    d2ProjectiveTwist_isProjectiveWith C
  letI : Finite n := hn
  exact Scheme.LineBundle.IsLocallyTrivial.of_iso e.symm
    ((ProjTwist.twistingSheaf_isLocallyTrivial n
      (Spec (CommRingCat.of k)) 1).pullback i)

end Adelic

end AlgebraicGeometry
