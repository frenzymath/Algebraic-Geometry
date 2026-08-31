/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RelPic
import AlgebraicJacobian.Picard.CechPicToPicNaturality
import AlgebraicJacobian.Picard.DivisorFamilyAffFace
import Mathlib.RingTheory.Localization.Free

/-!
# Base-local triviality: relPicMk-equality localizes to on-the-nose equality

Two Čech Picard classes `L, L'` on the relative curve `C ⊗ Spec B` with equal image in the
relative Picard group `relPic C (overSpec k B)` differ by a class pulled back from the base
along the second projection (`relPicMk_eq_relPicMk_iff`).  A base class is, through the
Čech–Picard dictionary of the affine scheme `Spec B` (`Scheme.CechPic.toPic`), an invertible
`B`-module; invertible modules are finite projective, hence free at the stalk of every prime
`q`, and freeness spreads from the stalk to a basic open `D(f) ∋ q`
(`Module.FinitePresentation.exists_free_localizedModule_powers`).  So the base discrepancy
dies after localizing at `f`, and the two classes agree on the nose after base change to
`Localization.Away f`.

## Main declarations

* `CommRing.Pic.exists_notMem_mapAlgebra_eq_one` — Zariski-local triviality of the Picard
  group of a commutative ring: near every prime some basic-open localization kills a given
  Picard class.
* `AlgebraicGeometry.exists_notMem_cechPicMap_specMap_eq_one` — the same statement for Čech
  Picard classes of `Spec B`, through `toPic` and its naturality (`toPic_map`).
* `AlgebraicGeometry.exists_notMem_cechPicMap_eq_of_relPicMk_eq` — **base-discrepancy
  localization**: `relPicMk`-equal Čech classes on the relative curve agree on the nose
  after base change to `Localization.Away f` for some `f ∉ q`, for every prime `q` of the
  test ring.
* `AlgebraicGeometry.DivFamZarAff.exists_notMem_picClass_map_eq_of_relPicMk_eq` — the
  consumer form for widened divisor families: `relPicMk`-equal `picClass`es become equal
  `picClass`es of the `mapAlgHom`-restricted families near every prime.
-/

set_option autoImplicit false
/- Statements mix the `relCurve C B` spelling with the product spelling
`(C ⊗ overSpec k B).left` (see `AlgebraicJacobian.Cohomology.RelativeTwoCover`). -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

/-! ## Zariski-local triviality of the Picard group of a ring -/

/-- **Zariski-local triviality of the Picard group**: for every Picard class `P` of a
commutative ring `B` and every prime `q` there is an `f ∉ q` such that `P` dies in
`Pic (Localization.Away f)`.  The representative invertible module is finite projective,
hence free at the stalk of `q` (`Module.free_of_flat_of_isLocalRing`), and freeness spreads
from the stalk to a basic open
(`Module.FinitePresentation.exists_free_localizedModule_powers`). -/
theorem CommRing.Pic.exists_notMem_mapAlgebra_eq_one {B : Type u} [CommRing B]
    (P : CommRing.Pic B) (q : PrimeSpectrum B) :
    ∃ f : B, f ∉ q.asIdeal ∧
      CommRing.Pic.mapAlgebra B (Localization.Away f) P = 1 := by
  haveI : Module.FinitePresentation B P.AsModule :=
    Module.finitePresentation_of_projective B P.AsModule
  haveI : Module.Free (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl P.AsModule) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl P.AsModule)
      (Localization.AtPrime q.asIdeal)
  refine ⟨f, hf, ?_⟩
  haveI := hfree
  rw [CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff_free]
  exact Module.Free.of_equiv
    (LocalizedModule.equivTensorProduct (Submonoid.powers f) P.AsModule)

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

/-! ## Local triviality for Čech Picard classes of an affine base -/

/-- **Zariski-local triviality of the Čech Picard group of `Spec B`**: every Čech Picard
class of the affine base dies after pullback along `Spec` of a localization
`B → Localization.Away f` with `f` outside a given prime — `toPic` naturality
(`Scheme.CechPic.toPic_map`) plus injectivity of `toPic` on the target transports
`CommRing.Pic.exists_notMem_mapAlgebra_eq_one` through the `ΓSpecIso` bridge. -/
theorem exists_notMem_cechPicMap_specMap_eq_one {B : Type u} [CommRing B]
    (N : (Spec (CommRingCat.of B)).CechPic) (q : PrimeSpectrum B) :
    ∃ f : B, f ∉ q.asIdeal ∧
      Scheme.CechPic.map (Spec.map (CommRingCat.ofHom
        (algebraMap B (Localization.Away f)))) N = 1 := by
  obtain ⟨f, hf, hone⟩ := CommRing.Pic.exists_notMem_mapAlgebra_eq_one
    (CommRing.Pic.mapRingHom (Scheme.ΓSpecIso (.of B)).hom.hom
      (Scheme.CechPic.toPic (Spec (.of B)) N)) q
  refine ⟨f, hf, ?_⟩
  set φ : CommRingCat.of B ⟶ CommRingCat.of (Localization.Away f) :=
    CommRingCat.ofHom (algebraMap B (Localization.Away f)) with hφ
  -- the descent homomorphism of the (affine) target is injective
  apply Scheme.CechPic.toPic_injective
  rw [map_one, Scheme.CechPic.toPic_map]
  -- inject further along the ring isomorphism `Γ(Spec (Away f), ⊤) ≃ Away f`
  have hΓinv : (Scheme.ΓSpecIso (.of (Localization.Away f))).inv.hom.comp
      (Scheme.ΓSpecIso (.of (Localization.Away f))).hom.hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]
  have hinj : Function.Injective
      (CommRing.Pic.mapRingHom (Scheme.ΓSpecIso (.of (Localization.Away f))).hom.hom) := by
    intro x y hxy
    have h2 := congrArg
      (CommRing.Pic.mapRingHom (Scheme.ΓSpecIso (.of (Localization.Away f))).inv.hom) hxy
    rwa [CommRing.Pic.mapRingHom_mapRingHom, CommRing.Pic.mapRingHom_mapRingHom, hΓinv,
      CommRing.Pic.mapRingHom_id_apply, CommRing.Pic.mapRingHom_id_apply] at h2
  apply hinj
  -- naturality of `ΓSpecIso` turns the global-sections square into the algebra map
  have hnat : (Scheme.ΓSpecIso (.of (Localization.Away f))).hom.hom.comp
      (Spec.map φ).appTop.hom = φ.hom.comp (Scheme.ΓSpecIso (.of B)).hom.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality]
  rw [map_one, CommRing.Pic.mapRingHom_mapRingHom, hnat,
    ← CommRing.Pic.mapRingHom_mapRingHom, hφ, CommRingCat.hom_ofHom,
    CommRing.Pic.mapRingHom_algebraMap]
  exact hone

/-! ## Base-discrepancy localization on the relative curve -/

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- **Base-discrepancy localization**: two Čech Picard classes on the relative curve
`C ⊗ Spec B` with equal image in the relative Picard group agree on the nose after base
change to `Localization.Away f`, for some `f` outside any given prime `q` of the test ring.

The discrepancy `L / L'` is pulled back from the base (`relPicMk_eq_relPicMk_iff`), and base
classes die Zariski-locally (`exists_notMem_cechPicMap_specMap_eq_one`); the commuting square
`relCurveMap_snd` transports the vanishing along the second projections. -/
theorem exists_notMem_cechPicMap_eq_of_relPicMk_eq
    {B : Type u} [CommRing B] [Algebra k B] {L L' : (relCurve C B).CechPic}
    (h : relPicMk C (overSpec k B) L = relPicMk C (overSpec k B) L')
    (q : PrimeSpectrum B) :
    ∃ f : B, f ∉ q.asIdeal ∧
      Scheme.CechPic.map (relCurveMap C B (Localization.Away f)) L
        = Scheme.CechPic.map (relCurveMap C B (Localization.Away f)) L' := by
  obtain ⟨N, hN⟩ := (mem_picFromBase_iff C).mp ((relPicMk_eq_relPicMk_iff C).mp h)
  obtain ⟨f, hf, hkill⟩ := exists_notMem_cechPicMap_specMap_eq_one N q
  refine ⟨f, hf, ?_⟩
  -- respell the base-change morphism at the `Over`-product spelling, so that every
  -- rewrite below is homogeneous (`relCurveMap` and `Spec.map (algebraMap …)` are the
  -- same morphisms after unfolding `relCurve`/`overSpecMap_left`, definitionally)
  have hkill' : Scheme.CechPic.map
      (overSpecMap (k := k) B (Localization.Away f)).left N = 1 := hkill
  have hsq : (C ◁ overSpecMap (k := k) B (Localization.Away f)).left
        ≫ (snd C (overSpec k B)).left
      = (snd C (overSpec k (Localization.Away f))).left
        ≫ (overSpecMap (k := k) B (Localization.Away f)).left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  change Scheme.CechPic.map (C ◁ overSpecMap (k := k) B (Localization.Away f)).left L
      = Scheme.CechPic.map (C ◁ overSpecMap (k := k) B (Localization.Away f)).left L'
  rw [← div_eq_one, ← map_div, ← hN, ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
    hsq, Scheme.CechPic.map_comp, MonoidHom.comp_apply, hkill', map_one]

/-- **Base-discrepancy localization for widened divisor families** (the `picClass`
consumer): if two widened locally certified families of degree `genus C` over `B` have
`relPicMk`-equal Picard classes, then near every prime of `B` their `mapAlgHom`-restrictions
to a basic-open localization have equal Picard classes on the nose. -/
theorem DivFamZarAff.exists_notMem_picClass_map_eq_of_relPicMk_eq
    {B : Type u} [CommRing B] [Algebra k B] (F F' : DivFamZarAff C B (genus C))
    (h : relPicMk C (overSpec k B) F.picClass = relPicMk C (overSpec k B) F'.picClass)
    (q : PrimeSpectrum B) :
    ∃ f : B, f ∉ q.asIdeal ∧
      (DivFamZarAff.mapAlgHom (IsScalarTower.toAlgHom k B (Localization.Away f)) F).picClass
        = (DivFamZarAff.mapAlgHom
            (IsScalarTower.toAlgHom k B (Localization.Away f)) F').picClass := by
  obtain ⟨f, hf, hmap⟩ := exists_notMem_cechPicMap_eq_of_relPicMk_eq h q
  refine ⟨f, hf, ?_⟩
  rw [DivFamZarAff.mapAlgHom_eq_mapAlg (IsScalarTower.toAlgHom k B (Localization.Away f))
      (fun _ => rfl) F,
    DivFamZarAff.mapAlgHom_eq_mapAlg (IsScalarTower.toAlgHom k B (Localization.Away f))
      (fun _ => rfl) F',
    DivFamZarAff.picClass_mapAlg, DivFamZarAff.picClass_mapAlg, hmap]

end AlgebraicGeometry
