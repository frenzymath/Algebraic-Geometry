/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.ProjectiveSpace
import AlgebraicJacobian.Picard.GlueDescent
import AlgebraicJacobian.Picard.GrassmannianQuot
import AlgebraicJacobian.Picard.TensorObjSubstrate

/-!
# The Serre twisting sheaf `O(m)` on the integral model of projective space

Mathlib v4.31 has no twisted structure sheaf on `Proj`.  This file constructs
`O(m)` on the integral model `Proj ℤ[Xᵢ : i ∈ n]` of projective space as a
`SheafOfModules`, by gluing the trivial line bundles on the basic opens
`D₊(Xᵢ)` along the transition units `(Xᵢ/Xⱼ)^m`, through the project descent
engine `AlgebraicGeometry.Scheme.Modules.glue` (`Picard/GlueDescent.lean`) —
the same pattern as the Grassmannian universal quotient
(`Picard/GrassmannianQuot.lean`), in rank one.

Main definitions:

* `ProjTwist.basicOpenCover n` — the open cover of `Proj ℤ[Xᵢ]` by the
  `D₊(Xᵢ)`;
* `ProjTwist.awayUnit n i j` — the unit `Xᵢ/Xⱼ` of the degree-zero localized
  ring `(ℤ[Xᵢ]_{XᵢXⱼ})₀`, and `ProjTwist.overlapUnit n i j` its image in
  `Γ(V(i,j), O)` on the scheme-theoretic overlap of the cover;
* `ProjTwist.twistTransition n m i j` — the rank-one transition isomorphism
  multiplication by `(Xᵢ/Xⱼ)^m`, conjugated by the structure-sheaf pullback
  comparison `Modules.pullbackUnitIso`;
* `ProjTwist.serreTwist n m` — `O(m)` on `Proj ℤ[Xᵢ : i ∈ n]`, the glued
  sheaf of modules transported along the cover isomorphism `fromGlued`.

The convention is that the transition *from* the `i`-th trivialisation *to*
the `j`-th multiplies by `(Xᵢ/Xⱼ)^m`, corresponding to the local generator
`Xᵢ^m` of `O(m)` on `D₊(Xᵢ)`.

Blueprint: `def:serre_twist`, `lem:serre_twist_transition_unit`,
`lem:serre_twist_cocycle` (`blueprint/src/chapters/Picard_QuotScheme.tex`).
-/

open CategoryTheory Limits MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.Grassmannian (scalarEnd scalarEnd_one scalarEnd_comp)

noncomputable section

namespace AlgebraicGeometry

universe u

/-! ## Rank-one pullback coherences

The Serre-twist cocycle transports rank-one transition isomorphisms of the shape
`pullbackUnitIso a ≪≫ unitScalarIso v ≪≫ (pullbackUnitIso b).symm` to a triple
overlap.  The next block is the rank-one mirror of the free-sheaf coherence stack
of `GrassmannianQuot.lean` / `GlueDescent.lean` (`pullbackFreeIso_comp`,
`matrixEnd_pullback`, the `pullbackCongr` endpoint absorptions): with
`SheafOfModules.unit` in place of `SheafOfModules.free (Fin d)`, `scalarEnd` in
place of `matrixEnd`, and `pullbackUnitIso` in place of `pullbackFreeIso`.  Each
is immediate from an already-proven unit-level atom. -/

namespace Scheme.Modules

open AlgebraicGeometry.Grassmannian (scalarEnd scalarEnd_pullback)

/-- Rank-one `map_comp` coherence (analogue of `pullbackFreeIso_comp`): the
structure-sheaf pullback comparison at a composite `b ≫ a` factors through the
pseudofunctor composition `pullbackComp`.  Immediate from the unit coherence
`gr_pullbackObjUnitToUnit_comp` (`(pullbackUnitIso f).hom = pullbackObjUnitToUnit f`). -/
lemma pullbackUnitIso_comp {Tx Ty Tz : Scheme.{u}} (a : Ty ⟶ Tx) (b : Tz ⟶ Ty) :
    (pullbackComp b a).hom.app (SheafOfModules.unit Tx.ringCatSheaf) ≫
        (pullbackUnitIso (b ≫ a)).hom
      = (pullback b).map (pullbackUnitIso a).hom ≫ (pullbackUnitIso b).hom :=
  gr_pullbackObjUnitToUnit_comp a b

/-- Iso-conjugated form of the scalar-endomorphism pullback atom `scalarEnd_pullback`:
`(pullback p).map (scalarEnd a) = Q.hom ≫ scalarEnd (p.appTop a) ≫ Q.inv`, with
`Q = pullbackUnitIso p`.  The rank-one analogue of `matrixEnd_pullback`. -/
lemma scalarEnd_pullback_iso {T S : Scheme.{0}} (p : T ⟶ S) (a : Γ(S, ⊤)) :
    (pullback p).map (scalarEnd a)
      = (pullbackUnitIso p).hom ≫ scalarEnd (p.appTop a) ≫ (pullbackUnitIso p).inv := by
  have key : (pullback p).map (scalarEnd a) ≫ (pullbackUnitIso p).hom
      = (pullbackUnitIso p).hom ≫ scalarEnd (p.appTop a) :=
    scalarEnd_pullback p a
  rw [← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Closed zig-zag: `Q_φ⁻¹ ≫ pullbackCongr(h).app ≫ Q_ψ = 𝟙` for equal base
morphisms `φ = ψ`.  Rank-one mirror of `pullbackFreeIso_inv_congr_hom`. -/
@[reassoc]
lemma pullbackUnitIso_inv_congr_hom {T' T : Scheme.{u}} {φ ψ : T' ⟶ T} (h : φ = ψ) :
    (pullbackUnitIso φ).inv ≫
        ((pullbackCongr h).app (SheafOfModules.unit T.ringCatSheaf)).hom ≫
        (pullbackUnitIso ψ).hom
      = 𝟙 _ := by
  subst h; simp [pullbackCongr]

/-- Left absorption: `pullbackCongr(h).app ≫ Q_ψ = Q_φ` for equal base morphisms
`φ = ψ`.  Rank-one mirror of `pullbackCongr_hom_app_free`. -/
@[reassoc]
lemma pullbackCongr_hom_app_unit {T' T : Scheme.{u}} {φ ψ : T' ⟶ T} (h : φ = ψ) :
    ((pullbackCongr h).app (SheafOfModules.unit T.ringCatSheaf)).hom ≫
        (pullbackUnitIso ψ).hom
      = (pullbackUnitIso φ).hom := by
  subst h; simp [pullbackCongr]

/-- Right absorption: `Q_φ⁻¹ ≫ pullbackCongr(h).app = Q_ψ⁻¹` for equal base
morphisms `φ = ψ`.  Rank-one mirror of `pullbackFreeIso_inv_congr`. -/
@[reassoc]
lemma pullbackUnitIso_inv_congr {T' T : Scheme.{u}} {φ ψ : T' ⟶ T} (h : φ = ψ) :
    (pullbackUnitIso φ).inv ≫
        ((pullbackCongr h).app (SheafOfModules.unit T.ringCatSheaf)).hom
      = (pullbackUnitIso ψ).inv := by
  subst h; simp [pullbackCongr]

end Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- `topIso` naturality under `homOfLE` / structure-sheaf restriction: on a scheme `X`,
restriction of a global section from `V` to `U ⊆ V` commutes with the identifications
`Γ(U, ⊤) ≅ Γ(X, U)`. -/
lemma topIso_inv_homOfLE_appTop {X : Scheme.{u}} {U V : X.Opens} (e : U ≤ V) :
    V.topIso.inv ≫ (X.homOfLE e).appTop
      = X.presheaf.map (homOfLE e).op ≫ U.topIso.inv := by
  simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop, ← Functor.map_comp, ← op_comp]
  exact congrArg _ (Subsingleton.elim _ _)

namespace ProjTwist

variable (n : Type u)

/-- The variable `Xᵢ` is homogeneous of degree `1`. -/
lemma X_mem_deg_one (i : n) :
    (X i : MvPolynomial n (ULift.{u} ℤ)) ∈ homogeneousSubmodule n (ULift.{u} ℤ) 1 :=
  isHomogeneous_X _ _

/-- The product `XᵢXⱼ` is homogeneous of degree `2`. -/
lemma X_mul_X_mem_deg_two (i j : n) :
    (X i * X j : MvPolynomial n (ULift.{u} ℤ)) ∈
      homogeneousSubmodule n (ULift.{u} ℤ) 2 :=
  SetLike.mul_mem_graded (X_mem_deg_one n i) (X_mem_deg_one n j)

/-- The basic opens `D₊(Xᵢ)` cover `Proj ℤ[Xᵢ : i ∈ n]`: the variables
generate the coordinate ring over its degree-zero part. -/
lemma iSup_basicOpen_X_eq_top :
    ⨆ i, Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' _ _ (fun i => ⟨1, X_mem_deg_one n i⟩) ?_
  rw [eq_top_iff]
  rintro a -
  have ha : a ∈ Algebra.adjoin (ULift.{u} ℤ)
      (Set.range (X : n → MvPolynomial n (ULift.{u} ℤ))) := by
    rw [MvPolynomial.adjoin_range_X]; trivial
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
      have hr : (algebraMap (ULift.{u} ℤ) (MvPolynomial n (ULift.{u} ℤ))) r
          ∈ homogeneousSubmodule n (ULift.{u} ℤ) 0 := by
        rw [MvPolynomial.algebraMap_eq]
        exact isHomogeneous_C _ _
      exact Subalgebra.algebraMap_mem
        (Algebra.adjoin (homogeneousSubmodule n (ULift.{u} ℤ) 0)
          (Set.range (X : n → MvPolynomial n (ULift.{u} ℤ))))
        (⟨_, hr⟩ : homogeneousSubmodule n (ULift.{u} ℤ) 0)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

/-- The open cover of the integral model by the basic opens `D₊(Xᵢ)`. -/
def basicOpenCover :
    (Proj (homogeneousSubmodule n (ULift.{u} ℤ))).OpenCover where
  I₀ := n
  X i := (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i)).toScheme
  f i := (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i)).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    have : x ∈ ⨆ i, Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i) := by
      rw [iSup_basicOpen_X_eq_top]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    exact ⟨i, ⟨x, hi⟩, rfl⟩

/-- The glue datum of the basic-open cover of the integral model. -/
@[reducible] def glueData : Scheme.GlueData.{u} := (basicOpenCover n).gluedCover

/-- The fraction `Xᵢ/Xⱼ = Xᵢ²/(XᵢXⱼ)` as an element of the degree-zero
localized ring `(ℤ[X]_{XᵢXⱼ})₀`. -/
def awayFraction (i j : n) :
    Away (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j) :=
  Away.mk _ (X_mul_X_mem_deg_two n i j) 1 (X i * X i)
    (by simpa using X_mul_X_mem_deg_two n i i)

/-- The fraction `Xⱼ/Xᵢ = Xⱼ²/(XᵢXⱼ)` in the *same* localized ring
`(ℤ[X]_{XᵢXⱼ})₀` — the inverse of `awayFraction`. -/
def awayFractionInv (i j : n) :
    Away (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j) :=
  Away.mk _ (X_mul_X_mem_deg_two n i j) 1 (X j * X j)
    (by simpa using X_mul_X_mem_deg_two n j j)

lemma awayFraction_mul_inv (i j : n) :
    awayFraction n i j * awayFractionInv n i j = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    awayFraction, awayFractionInv, Away.val_mk, Away.val_mk, Localization.mk_mul]
  have hnum : (X i * X i) * (X j * X j)
      = ((X i * X j) ^ 1 * (X i * X j) ^ 1 : MvPolynomial n (ULift.{u} ℤ)) := by
    ring
  rw [hnum]
  exact Localization.mk_self
    ((⟨(X i * X j) ^ 1, 1, rfl⟩ :
        Submonoid.powers (X i * X j : MvPolynomial n (ULift.{u} ℤ))) *
      (⟨(X i * X j) ^ 1, 1, rfl⟩ :
        Submonoid.powers (X i * X j : MvPolynomial n (ULift.{u} ℤ))))

/-- The fraction `Xᵢ/Xⱼ` as a unit of `(ℤ[X]_{XᵢXⱼ})₀`, with inverse
`Xⱼ/Xᵢ`. -/
def awayUnit (i j : n) :
    (Away (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j))ˣ where
  val := awayFraction n i j
  inv := awayFractionInv n i j
  val_inv := awayFraction_mul_inv n i j
  inv_val := (mul_comm _ _).trans (awayFraction_mul_inv n i j)

/-! ## The transition units on the scheme-theoretic overlaps -/

/-- The scheme-theoretic overlap of the glue datum factors through the basic
open `D₊(XᵢXⱼ) = D₊(Xᵢ) ⊓ D₊(Xⱼ)`. -/
lemma range_overlap_le (i j : n) :
    Set.range (pullback.fst ((basicOpenCover n).f i) ((basicOpenCover n).f j) ≫
        (basicOpenCover n).f i).base ⊆
      Set.range ((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ))
        (X i * X j)).ι).base := by
  rw [Scheme.Opens.range_ι, Proj.basicOpen_mul]
  rintro _ ⟨v, rfl⟩
  refine ⟨?_, ?_⟩
  · have hx : ((pullback.fst _ _ ≫ (basicOpenCover n).f i) v : Proj _) ∈
        Set.range ⇑((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ))
          (X i)).ι) := by
      rw [Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact (Scheme.Opens.range_ι _) ▸ hx
  · have hcond := congrArg (fun (φ : pullback ((basicOpenCover n).f i)
        ((basicOpenCover n).f j) ⟶ Proj (homogeneousSubmodule n (ULift.{u} ℤ))) =>
          φ.base v) pullback.condition
    simp only at hcond
    rw [hcond]
    have hx : ((pullback.snd _ _ ≫ (basicOpenCover n).f j) v : Proj _) ∈
        Set.range ⇑((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ))
          (X j)).ι) := by
      rw [Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact (Scheme.Opens.range_ι _) ▸ hx

/-- The canonical morphism from the scheme-theoretic overlap of the `i`-th and
`j`-th charts to the basic open `D₊(XᵢXⱼ)`. -/
def overlapHom (i j : n) :
    pullback ((basicOpenCover n).f i) ((basicOpenCover n).f j) ⟶
      (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j)).toScheme :=
  IsOpenImmersion.lift
    ((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j)).ι)
    (pullback.fst ((basicOpenCover n).f i) ((basicOpenCover n).f j) ≫
      (basicOpenCover n).f i)
    (range_overlap_le n i j)

/-- The ring homomorphism carrying degree-zero fractions over `XᵢXⱼ` to
sections of the structure sheaf on the scheme-theoretic overlap. -/
def overlapRingHom (i j : n) :
    Away (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j) →+*
      Γ(pullback ((basicOpenCover n).f i) ((basicOpenCover n).f j), ⊤) :=
  ((overlapHom n i j).appTop.hom.comp
    ((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ))
      (X i * X j)).topIso.inv.hom)).comp
    (Proj.awayToSection (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j)).hom

/-- The transition unit `(Xᵢ/Xⱼ)` as a unit of the sections of the structure
sheaf on the scheme-theoretic overlap of the `i`-th and `j`-th charts. -/
def overlapUnit (i j : n) :
    Γ(pullback ((basicOpenCover n).f i) ((basicOpenCover n).f j), ⊤)ˣ :=
  Units.map (overlapRingHom n i j).toMonoidHom (awayUnit n i j)

/-! ## Rank-one transitions -/

/-- A unit of the global sections induces an automorphism of the structure
sheaf, multiplication by the unit (rank-one `matrixToFreeIso`). -/
def unitScalarIso {Y : Scheme.{u}} (v : Γ(Y, ⊤)ˣ) :
    SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf where
  hom := scalarEnd v.val
  inv := scalarEnd v.inv
  hom_inv_id := by rw [scalarEnd_comp, v.val_inv, scalarEnd_one]
  inv_hom_id := by rw [scalarEnd_comp, v.inv_val, scalarEnd_one]

@[simp]
lemma unitScalarIso_hom {Y : Scheme.{u}} (v : Γ(Y, ⊤)ˣ) :
    (unitScalarIso v).hom = scalarEnd v.val := rfl

@[simp]
lemma unitScalarIso_one {Y : Scheme.{u}} :
    unitScalarIso (1 : Γ(Y, ⊤)ˣ) = Iso.refl _ :=
  Iso.ext (by rw [Iso.refl_hom]; exact (congrArg scalarEnd Units.val_one).trans scalarEnd_one)

/-- Iso-level structure-sheaf-pullback cancellation: for equal base morphisms,
`pullbackUnitIso φ ≪≫ (pullbackUnitIso ψ).symm` is the `eqToIso` transport
(the rank-one analogue of `pullbackFreeIso_trans_symm_eqToIso`). -/
lemma pullbackUnitIso_trans_symm_eqToIso {T' T : Scheme.{u}} {φ ψ : T' ⟶ T} (h : φ = ψ) :
    Scheme.Modules.pullbackUnitIso φ ≪≫ (Scheme.Modules.pullbackUnitIso ψ).symm
      = eqToIso (congrArg
          (fun α => (Scheme.Modules.pullback α).obj
            (SheafOfModules.unit T.ringCatSheaf)) h) := by
  subst h; simp

/-- The fraction `Xᵢ/Xᵢ` is `1`. -/
lemma awayFraction_self (i : n) : awayFraction n i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_one, awayFraction, Away.val_mk]
  have hden : (⟨(X i * X i) ^ 1, 1, rfl⟩ :
      Submonoid.powers (X i * X i : MvPolynomial n (ULift.{u} ℤ)))
      = ⟨X i * X i, 1, pow_one _⟩ := Subtype.ext (pow_one _)
  rw [hden]
  exact Localization.mk_self_mk _ _

lemma awayUnit_self (i : n) : awayUnit n i i = 1 :=
  Units.ext (awayFraction_self n i)

lemma overlapUnit_self (i : n) : overlapUnit n i i = 1 := by
  rw [overlapUnit, awayUnit_self, map_one]

/-- The rank-one transition isomorphism of the Serre twist `O(m)`:
multiplication by `(Xᵢ/Xⱼ)^m`, conjugated by the structure-sheaf pullback
comparisons on the scheme-theoretic overlap. -/
def twistTransition (m : ℕ) (i j : n) :
    (Scheme.Modules.pullback ((glueData n).f i j)).obj
        (SheafOfModules.unit ((glueData n).U i).ringCatSheaf) ≅
      (Scheme.Modules.pullback ((glueData n).t i j ≫ (glueData n).f j i)).obj
        (SheafOfModules.unit ((glueData n).U j).ringCatSheaf) :=
  Scheme.Modules.pullbackUnitIso ((glueData n).f i j) ≪≫
    unitScalarIso ((overlapUnit n i j) ^ m) ≪≫
    (Scheme.Modules.pullbackUnitIso ((glueData n).t i j ≫ (glueData n).f j i)).symm

/-- **(C1)** The diagonal transition of the Serre twist is the canonical
cast: `Xᵢ/Xᵢ = 1`, so the scalar automorphism is the identity and the two
pullback comparisons cancel. -/
lemma twistTransition_self (m : ℕ) (i : n) :
    twistTransition n m i i
      = eqToIso (congrArg
          (fun φ => (Scheme.Modules.pullback φ).obj
            (SheafOfModules.unit ((glueData n).U i).ringCatSheaf))
          (show (glueData n).f i i = (glueData n).t i i ≫ (glueData n).f i i by
            rw [(glueData n).t_id i, Category.id_comp])) := by
  have hmid : unitScalarIso ((overlapUnit n i i) ^ m)
      = Iso.refl (SheafOfModules.unit
          (pullback ((basicOpenCover n).f i) ((basicOpenCover n).f i)).ringCatSheaf) := by
    rw [overlapUnit_self, one_pow, unitScalarIso_one]
  calc twistTransition n m i i
      = Scheme.Modules.pullbackUnitIso ((glueData n).f i i) ≪≫
          unitScalarIso ((overlapUnit n i i) ^ m) ≪≫
          (Scheme.Modules.pullbackUnitIso
            ((glueData n).t i i ≫ (glueData n).f i i)).symm := rfl
    _ = Scheme.Modules.pullbackUnitIso ((glueData n).f i i) ≪≫
          (Scheme.Modules.pullbackUnitIso
            ((glueData n).t i i ≫ (glueData n).f i i)).symm := by
        refine (congrArg (fun e =>
          Scheme.Modules.pullbackUnitIso ((glueData n).f i i) ≪≫ e ≪≫
            (Scheme.Modules.pullbackUnitIso
              ((glueData n).t i i ≫ (glueData n).f i i)).symm) hmid).trans ?_
        exact congrArg (fun e => Scheme.Modules.pullbackUnitIso ((glueData n).f i i) ≪≫ e)
          (Iso.refl_trans _)
    _ = eqToIso (congrArg
          (fun φ => (Scheme.Modules.pullback φ).obj
            (SheafOfModules.unit ((glueData n).U i).ringCatSheaf))
          (show (glueData n).f i i = (glueData n).t i i ≫ (glueData n).f i i by
            rw [(glueData n).t_id i, Category.id_comp])) :=
      pullbackUnitIso_trans_symm_eqToIso
        (show (glueData n).f i i = (glueData n).t i i ≫ (glueData n).f i i by
          rw [(glueData n).t_id i, Category.id_comp])

/-- **The `m = 0` transition carries no twist.** The scalar automorphism
`(Xᵢ/Xⱼ)^0 = 1` is the identity, so the transition of `O(0)` is the bare
structure-sheaf comparison
`pullbackUnitIso fᵢⱼ ≪≫ (pullbackUnitIso (tᵢⱼ ≫ fⱼᵢ)).symm` — exactly the
descent datum of the structure sheaf `𝒪 = O(0)`.  This is the all-indices
companion of `twistTransition_self` (which handles only the diagonal `i = j`)
and the algebraic core of `O(0) ≅ 𝒪`, validating the O(1) sign convention:
`m = 0` contributes no `Xᵢ/Xⱼ` factor. -/
lemma twistTransition_zero (i j : n) :
    twistTransition n 0 i j
      = Scheme.Modules.pullbackUnitIso ((glueData n).f i j) ≪≫
        (Scheme.Modules.pullbackUnitIso ((glueData n).t i j ≫ (glueData n).f j i)).symm := by
  have hmid : unitScalarIso ((overlapUnit n i j) ^ 0) = Iso.refl _ := by
    rw [pow_zero, unitScalarIso_one]
  calc twistTransition n 0 i j
      = Scheme.Modules.pullbackUnitIso ((glueData n).f i j) ≪≫
          unitScalarIso ((overlapUnit n i j) ^ 0) ≪≫
          (Scheme.Modules.pullbackUnitIso
            ((glueData n).t i j ≫ (glueData n).f j i)).symm := rfl
    _ = Scheme.Modules.pullbackUnitIso ((glueData n).f i j) ≪≫
          (Scheme.Modules.pullbackUnitIso
            ((glueData n).t i j ≫ (glueData n).f j i)).symm := by
        refine (congrArg (fun e =>
          Scheme.Modules.pullbackUnitIso ((glueData n).f i j) ≪≫ e ≪≫
            (Scheme.Modules.pullbackUnitIso
              ((glueData n).t i j ≫ (glueData n).f j i)).symm) hmid).trans ?_
        exact congrArg (fun e =>
          Scheme.Modules.pullbackUnitIso ((glueData n).f i j) ≪≫ e) (Iso.refl_trans _)

/-- **Transport of a rank-one scalar automorphism through
`pullbackBaseChangeTransport`** — the reusable abstract core of the Serre-twist
cocycle, the rank-one analogue of `pullbackBaseChangeTransport_matrixToFreeIso`
(`GrassmannianQuot.lean`).  A transition isomorphism of the twist shape
`pullbackUnitIso a ≪≫ unitScalarIso v ≪≫ (pullbackUnitIso b).symm` (multiplication
by a unit `v` of `Γ(V, ⊤)`, conjugated to the overlap pullbacks) transports along
`p : W ⟶ V` to the same shape over `p ≫ a` / `p ≫ b`, the scalar base-changed by
the comorphism `p.appTop`.  Combines the scalar-naturality atom
`scalarEnd_pullback_iso` with the pseudofunctor coherence `pullbackUnitIso_comp`. -/
lemma pullbackBaseChangeTransport_unitScalarIso {W V : Scheme.{0}} (p : W ⟶ V)
    {Yi Yj : Scheme.{0}} (a : V ⟶ Yi) (b : V ⟶ Yj) (v : Γ(V, ⊤)ˣ) :
    (Scheme.Modules.pullbackBaseChangeTransport p a b
        (Scheme.Modules.pullbackUnitIso a ≪≫ unitScalarIso v ≪≫
          (Scheme.Modules.pullbackUnitIso b).symm)).hom
      = (Scheme.Modules.pullbackUnitIso (p ≫ a)).hom ≫
        scalarEnd (p.appTop v.val) ≫
        (Scheme.Modules.pullbackUnitIso (p ≫ b)).inv := by
  simp only [Scheme.Modules.pullbackBaseChangeTransport, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, unitScalarIso_hom]
  -- Front coherence: the `pullbackComp` cast + the `a`-leg comparison assemble into the
  -- composite comparison `Q_{p≫a}` (pseudofunctoriality, `pullbackUnitIso_comp`).
  have hfront : ((Scheme.Modules.pullbackComp p a).symm.app
          (SheafOfModules.unit Yi.ringCatSheaf)).hom ≫
        (Scheme.Modules.pullback p).map (Scheme.Modules.pullbackUnitIso a).hom ≫
          (Scheme.Modules.pullbackUnitIso p).hom
      = (Scheme.Modules.pullbackUnitIso (p ≫ a)).hom := by
    erw [← Scheme.Modules.pullbackUnitIso_comp a p]
    simp only [Iso.app_hom, Iso.symm_hom]
    rw [Iso.inv_hom_id_app_assoc]
  -- Back coherence: the inverse `b`-leg comparison + the `pullbackComp` cast assemble into
  -- the inverse composite comparison `Q_{p≫b}⁻¹`.
  have hback : (Scheme.Modules.pullbackUnitIso p).inv ≫
        (Scheme.Modules.pullback p).map (Scheme.Modules.pullbackUnitIso b).inv ≫
          ((Scheme.Modules.pullbackComp p b).app (SheafOfModules.unit Yj.ringCatSheaf)).hom
      = (Scheme.Modules.pullbackUnitIso (p ≫ b)).inv := by
    have hiso : (Scheme.Modules.pullbackComp p b).app (SheafOfModules.unit Yj.ringCatSheaf) ≪≫
          Scheme.Modules.pullbackUnitIso (p ≫ b)
        = (Scheme.Modules.pullback p).mapIso (Scheme.Modules.pullbackUnitIso b) ≪≫
          Scheme.Modules.pullbackUnitIso p := by
      apply Iso.ext
      simpa using Scheme.Modules.pullbackUnitIso_comp b p
    have hinv := congrArg Iso.inv hiso
    simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at hinv
    rw [← Category.assoc, ← hinv, Iso.app_hom]
    erw [Category.assoc, Iso.inv_hom_id_app]
    rw [Category.comp_id]
  -- Distribute `pullback p` over the conjugated scalar automorphism and apply the atom.
  rw [Functor.map_comp, Functor.map_comp, Scheme.Modules.scalarEnd_pullback_iso]
  rw [← hfront, ← hback]
  rfl

/-! ## The Serre twisting sheaf

The descent engine `Scheme.Modules.glue` (`Picard/GlueDescent.lean`) is
universe-monomorphic at `Scheme.GlueData.{0}` (see the NOTE at
`GlueDescent.lean:934`), so the glued sheaf itself is only available for a
`Type 0` index — which covers the intended consumers `n = Fin (m + 1)`
(`ℙ^m`).  The cover, units and transitions above stay universe-polymorphic
for a future generalisation of the engine. -/

/-! ## Substrate for the transported overlap cocycle

The base cocycle `overlapUnit_cocycle_transport` (below) factors all three transition
units through a common map `V(i,j,k) ⟶ D₊(XᵢXⱼXₖ)` and reduces to the fraction identity
`(Xᵢ/Xⱼ)(Xⱼ/Xₖ) = Xᵢ/Xₖ` in `A⁰_{XᵢXⱼXₖ}`.  The pieces below build that common map
(`commonHom`), the three chart-factorisations (`fact_ij/ik/jk`), the section-restriction
transport (`section_restrict`) and the fraction identity (`awayMap_awayFraction_cocycle`). -/

/-- The away-map fraction cocycle in `Away 𝒜 (XᵢXⱼXₖ)`:
`(Xᵢ/Xⱼ)(Xⱼ/Xₖ) = Xᵢ/Xₖ` after mapping the three transition fractions into the common
degree-zero localised ring over `XᵢXⱼXₖ`. -/
lemma awayMap_awayFraction_cocycle (i j k : n) :
    awayMap (homogeneousSubmodule n (ULift.{u} ℤ)) (X_mem_deg_one n k)
        (show X i * X j * X k = (X i * X j) * X k from rfl) (awayFraction n i j) *
      awayMap (homogeneousSubmodule n (ULift.{u} ℤ)) (X_mem_deg_one n i)
        (show X i * X j * X k = (X j * X k) * X i from by rw [mul_assoc, mul_comm])
        (awayFraction n j k)
      = awayMap (homogeneousSubmodule n (ULift.{u} ℤ)) (X_mem_deg_one n j)
        (show X i * X j * X k = (X i * X k) * X j from
          by rw [mul_assoc, mul_comm (X j) (X k), ← mul_assoc]) (awayFraction n i k) := by
  rw [awayFraction, awayFraction, awayFraction, awayMap_mk, awayMap_mk, awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- The glue-datum overlap immersion `f_ij` unfolds to the first pullback projection. -/
lemma gd_f (i j : n) :
    (glueData n).f i j = pullback.fst ((basicOpenCover n).f i) ((basicOpenCover n).f j) := by
  simp only [glueData, Scheme.Cover.gluedCover_f]

/-- The glue-datum swap `t_ij` unfolds to the pullback symmetry. -/
lemma gd_t (i j : n) :
    (glueData n).t i j
      = (pullbackSymmetry ((basicOpenCover n).f i) ((basicOpenCover n).f j)).hom := by
  simp only [glueData, Scheme.Cover.gluedCover_t]

set_option backward.isDefEq.respectTransparency false in
/-- The cover glue condition `t_ij ≫ f_ji ≫ ι_j = f_ij ≫ ι_i` into `Proj`. -/
lemma glue_cover_condition (i j : n) :
    (glueData n).t i j ≫ (glueData n).f j i ≫ (basicOpenCover n).f j
      = (glueData n).f i j ≫ (basicOpenCover n).f i := by
  rw [gd_t, gd_f, gd_f, pullbackSymmetry_hom_comp_fst_assoc, pullback.condition]

set_option backward.isDefEq.respectTransparency false in
/-- `f_ij ≫ ι_i = p₂ ≫ ι_j` on the double overlap. -/
lemma chart_overlap_swap (i j : n) :
    (glueData n).f i j ≫ (basicOpenCover n).f i
      = pullback.snd ((basicOpenCover n).f i) ((basicOpenCover n).f j) ≫
        (basicOpenCover n).f j := by
  rw [gd_f, pullback.condition]

set_option backward.isDefEq.respectTransparency false in
/-- The triple-overlap inclusion `T ⟶ Proj` lands in `D₊(XᵢXⱼXₖ)`. -/
lemma triple_range_le (i j k : n) :
    Set.range (pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫
        (glueData n).f i j ≫ (basicOpenCover n).f i).base ⊆
      Set.range ((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ))
        (X i * X j * X k)).ι).base := by
  have fi : pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫
        (glueData n).f i j ≫ (basicOpenCover n).f i
      = (pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫ (glueData n).f i j) ≫
          (basicOpenCover n).f i := by rw [Category.assoc]
  have fj : pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫
        (glueData n).f i j ≫ (basicOpenCover n).f i
      = (pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫
          pullback.snd ((basicOpenCover n).f i) ((basicOpenCover n).f j)) ≫
          (basicOpenCover n).f j := by
    rw [chart_overlap_swap n i j, ← Category.assoc]
  have fk : pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫
        (glueData n).f i j ≫ (basicOpenCover n).f i
      = (pullback.snd ((glueData n).f i j) ((glueData n).f i k) ≫
          pullback.snd ((basicOpenCover n).f i) ((basicOpenCover n).f k)) ≫
          (basicOpenCover n).f k := by
    rw [← Category.assoc, pullback.condition, Category.assoc, chart_overlap_swap n i k,
      ← Category.assoc]
  rw [Scheme.Opens.range_ι, Proj.basicOpen_mul, Proj.basicOpen_mul,
    TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_inf]
  refine Set.subset_inter (Set.subset_inter ?_ ?_) ?_
  · rw [← Scheme.Opens.range_ι ((Proj.basicOpen _ (X i))), fi, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp]
    exact Set.image_subset_range _ _
  · rw [← Scheme.Opens.range_ι ((Proj.basicOpen _ (X j))), fj, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp]
    exact Set.image_subset_range _ _
  · rw [← Scheme.Opens.range_ι ((Proj.basicOpen _ (X k))), fk, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp]
    exact Set.image_subset_range _ _

/-- The common map from the triple overlap `T` to the affine chart `D₊(XᵢXⱼXₖ)`. -/
def commonHom (i j k : n) :
    pullback ((glueData n).f i j) ((glueData n).f i k) ⟶
      (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j * X k)).toScheme :=
  IsOpenImmersion.lift
    (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j * X k)).ι
    (pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫
      (glueData n).f i j ≫ (basicOpenCover n).f i)
    (triple_range_le n i j k)

lemma commonHom_ι (i j k : n) :
    commonHom n i j k ≫ (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ))
        (X i * X j * X k)).ι
      = pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫
        (glueData n).f i j ≫ (basicOpenCover n).f i :=
  IsOpenImmersion.lift_fac _ _ _

lemma overlapHom_ι (i j : n) :
    overlapHom n i j ≫ (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j)).ι
      = (glueData n).f i j ≫ (basicOpenCover n).f i := by
  rw [gd_f]; exact IsOpenImmersion.lift_fac _ _ _

/-- The `jk`-leg of the triple overlap includes into Proj the same way as the `ij`-leg
(from `glueData_bridge_mid` and the cover glue condition). -/
lemma jk_incl (i j k : n) :
    (glueData n).t' i j k ≫ pullback.fst ((glueData n).f j k) ((glueData n).f j i) ≫
        (glueData n).f j k ≫ (basicOpenCover n).f j
      = pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫
        (glueData n).f i j ≫ (basicOpenCover n).f i := by
  have h1 := Scheme.Modules.glueData_bridge_mid (glueData n) i j k
  have h2 := glue_cover_condition n i j
  calc (glueData n).t' i j k ≫ pullback.fst ((glueData n).f j k) ((glueData n).f j i) ≫
          (glueData n).f j k ≫ (basicOpenCover n).f j
      = (((glueData n).t' i j k ≫ pullback.fst ((glueData n).f j k) ((glueData n).f j i)) ≫
          (glueData n).f j k) ≫ (basicOpenCover n).f j := by
        rw [Category.assoc, Category.assoc]
    _ = (pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫
          ((glueData n).t i j ≫ (glueData n).f j i)) ≫ (basicOpenCover n).f j := by rw [← h1]
    _ = pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫
          ((glueData n).t i j ≫ (glueData n).f j i ≫ (basicOpenCover n).f j) := by
        rw [Category.assoc, Category.assoc]
    _ = pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫
          (glueData n).f i j ≫ (basicOpenCover n).f i := by rw [h2]

set_option backward.isDefEq.respectTransparency false in
lemma fact_ij (i j k : n)
    (le : Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j * X k)
      ≤ Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j)) :
    pullback.fst ((glueData n).f i j) ((glueData n).f i k) ≫ overlapHom n i j
      = commonHom n i j k ≫ (Proj (homogeneousSubmodule n (ULift.{u} ℤ))).homOfLE le := by
  rw [← cancel_mono (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j)).ι]
  simp only [Category.assoc]
  rw [overlapHom_ι, Scheme.homOfLE_ι, commonHom_ι]

set_option backward.isDefEq.respectTransparency false in
lemma fact_ik (i j k : n)
    (le : Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j * X k)
      ≤ Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X k)) :
    pullback.snd ((glueData n).f i j) ((glueData n).f i k) ≫ overlapHom n i k
      = commonHom n i j k ≫ (Proj (homogeneousSubmodule n (ULift.{u} ℤ))).homOfLE le := by
  rw [← cancel_mono (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X k)).ι]
  simp only [Category.assoc]
  rw [overlapHom_ι, Scheme.homOfLE_ι, commonHom_ι, ← Category.assoc, ← Category.assoc,
    ← pullback.condition]

set_option backward.isDefEq.respectTransparency false in
lemma fact_jk (i j k : n)
    (le : Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j * X k)
      ≤ Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X j * X k)) :
    ((glueData n).t' i j k ≫ pullback.fst ((glueData n).f j k) ((glueData n).f j i)) ≫
        overlapHom n j k
      = commonHom n i j k ≫ (Proj (homogeneousSubmodule n (ULift.{u} ℤ))).homOfLE le := by
  rw [← cancel_mono (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X j * X k)).ι]
  simp only [Category.assoc]
  rw [overlapHom_ι, Scheme.homOfLE_ι, commonHom_ι]
  exact jk_incl n i j k

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of an away-section from `D₊(xf)` to `D₊(xt)` (`xt = xf·xg`) transported
through the `topIso`s is the away-map. -/
lemma section_restrict {d : ℕ} (xf xg : MvPolynomial n (ULift.{u} ℤ))
    (hg : xg ∈ homogeneousSubmodule n (ULift.{u} ℤ) d)
    (xt : MvPolynomial n (ULift.{u} ℤ)) (hx : xt = xf * xg)
    (le : Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) xt
      ≤ Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) xf)
    (a : HomogeneousLocalization.Away (homogeneousSubmodule n (ULift.{u} ℤ)) xf) :
    ((Proj (homogeneousSubmodule n (ULift.{u} ℤ))).homOfLE le).appTop
        ((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) xf).topIso.inv
          (Proj.awayToSection (homogeneousSubmodule n (ULift.{u} ℤ)) xf a))
      = (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) xt).topIso.inv
          (Proj.awayToSection (homogeneousSubmodule n (ULift.{u} ℤ)) xt
            (awayMap (homogeneousSubmodule n (ULift.{u} ℤ)) hg hx a)) := by
  have hnat := congrArg (fun (φ : _ ⟶ _) =>
      (CommRingCat.Hom.hom φ) (Proj.awayToSection (homogeneousSubmodule n (ULift.{u} ℤ)) xf a))
    (topIso_inv_homOfLE_appTop (X := Proj (homogeneousSubmodule n (ULift.{u} ℤ))) le)
  simp only [CommRingCat.comp_apply] at hnat
  rw [hnat]
  congr 1
  exact (congrArg (fun (m : _ ⟶ _) => (ConcreteCategory.hom m) a)
    (Proj.awayMap_awayToSection (𝒜 := homogeneousSubmodule n (ULift.{u} ℤ)) hg hx)).symm

/-- The transition unit `Xᵢ/Xⱼ` as a section of the overlap, unfolded through the
overlap immersion and the away-to-section identification. -/
lemma overlapUnit_val_eq (i j : n) :
    (overlapUnit n i j).val
      = (overlapHom n i j).appTop
          ((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j)).topIso.inv
            (Proj.awayToSection (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j)
              (awayFraction n i j))) := rfl

section Universe0

variable (n₀ : Type)

/-- **Base cocycle of the transported overlap units** (`m = 1`): in
`Γ(V(i,j,k), O)`, the images of the three transition units `Xᵢ/Xⱼ`, `Xⱼ/Xₖ`,
`Xᵢ/Xₖ` under the base-change comorphisms to the common triple overlap satisfy
`p_IJ^♯(Xᵢ/Xⱼ) · p_JK^♯(Xⱼ/Xₖ) = p_IK^♯(Xᵢ/Xₖ)`.  This is the geometric heart of
the Serre-twist cocycle: it factors all three units through a common map
`V(i,j,k) ⟶ D₊(XᵢXⱼXₖ)` and reduces to the fraction identity
`(Xᵢ/Xⱼ)(Xⱼ/Xₖ) = Xᵢ/Xₖ` in `A⁰_{XᵢXⱼXₖ}` via `Proj.awayMap_awayToSection`. -/
lemma overlapUnit_cocycle_transport (i j k : n₀) :
    (Scheme.Hom.appTop (pullback.fst ((glueData n₀).f i j) ((glueData n₀).f i k)))
        (overlapUnit n₀ i j).val *
      (Scheme.Hom.appTop ((glueData n₀).t' i j k ≫
          pullback.fst ((glueData n₀).f j k) ((glueData n₀).f j i)))
        (overlapUnit n₀ j k).val
    = (Scheme.Hom.appTop (pullback.snd ((glueData n₀).f i j) ((glueData n₀).f i k)))
        (overlapUnit n₀ i k).val := by
  have le_ij : Proj.basicOpen (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X j * X k)
      ≤ Proj.basicOpen (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X j) := by
    rw [Proj.basicOpen_mul]; exact inf_le_left
  have le_jk : Proj.basicOpen (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X j * X k)
      ≤ Proj.basicOpen (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X j * X k) := by
    rw [show (X i * X j * X k : MvPolynomial n₀ (ULift.{0} ℤ)) = (X j * X k) * X i from
      by rw [mul_assoc, mul_comm], Proj.basicOpen_mul]; exact inf_le_left
  have le_ik : Proj.basicOpen (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X j * X k)
      ≤ Proj.basicOpen (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X k) := by
    rw [show (X i * X j * X k : MvPolynomial n₀ (ULift.{0} ℤ)) = (X i * X k) * X j from
      by rw [mul_assoc, mul_comm (X j) (X k), ← mul_assoc], Proj.basicOpen_mul]; exact inf_le_left
  have hIJ : (Scheme.Hom.appTop (pullback.fst ((glueData n₀).f i j) ((glueData n₀).f i k)))
        (overlapUnit n₀ i j).val
      = (Scheme.Hom.appTop (commonHom n₀ i j k))
          ((Proj.basicOpen (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X j * X k)).topIso.inv
            (Proj.awayToSection (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X j * X k)
              (awayMap (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X_mem_deg_one n₀ k)
                (show X i * X j * X k = (X i * X j) * X k from rfl) (awayFraction n₀ i j)))) := by
    rw [overlapUnit_val_eq]
    have hmor : Scheme.Hom.appTop (overlapHom n₀ i j) ≫
          Scheme.Hom.appTop (pullback.fst ((glueData n₀).f i j) ((glueData n₀).f i k))
        = Scheme.Hom.appTop ((Proj (homogeneousSubmodule n₀ (ULift.{0} ℤ))).homOfLE le_ij) ≫
          Scheme.Hom.appTop (commonHom n₀ i j k) := by
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
      exact congrArg Scheme.Hom.appTop (fact_ij n₀ i j k le_ij)
    refine (congrArg (fun (m : _ ⟶ _) => (ConcreteCategory.hom m)
        ((Proj.basicOpen (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X j)).topIso.inv
          (Proj.awayToSection (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X j)
            (awayFraction n₀ i j)))) hmor).trans ?_
    simp only [ConcreteCategory.comp_apply]
    exact congrArg (fun z => (ConcreteCategory.hom (Scheme.Hom.appTop (commonHom n₀ i j k))) z)
      (section_restrict n₀ (X i * X j) (X k) (X_mem_deg_one n₀ k) (X i * X j * X k)
        (show X i * X j * X k = (X i * X j) * X k from rfl) le_ij (awayFraction n₀ i j))
  have hJK : (Scheme.Hom.appTop ((glueData n₀).t' i j k ≫
          pullback.fst ((glueData n₀).f j k) ((glueData n₀).f j i)))
        (overlapUnit n₀ j k).val
      = (Scheme.Hom.appTop (commonHom n₀ i j k))
          ((Proj.basicOpen (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X j * X k)).topIso.inv
            (Proj.awayToSection (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X j * X k)
              (awayMap (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X_mem_deg_one n₀ i)
                (show X i * X j * X k = (X j * X k) * X i from by rw [mul_assoc, mul_comm])
                (awayFraction n₀ j k)))) := by
    rw [overlapUnit_val_eq]
    have hmor : Scheme.Hom.appTop (overlapHom n₀ j k) ≫
          Scheme.Hom.appTop ((glueData n₀).t' i j k ≫
            pullback.fst ((glueData n₀).f j k) ((glueData n₀).f j i))
        = Scheme.Hom.appTop ((Proj (homogeneousSubmodule n₀ (ULift.{0} ℤ))).homOfLE le_jk) ≫
          Scheme.Hom.appTop (commonHom n₀ i j k) := by
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
      exact congrArg Scheme.Hom.appTop (fact_jk n₀ i j k le_jk)
    refine (congrArg (fun (m : _ ⟶ _) => (ConcreteCategory.hom m)
        ((Proj.basicOpen (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X j * X k)).topIso.inv
          (Proj.awayToSection (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X j * X k)
            (awayFraction n₀ j k)))) hmor).trans ?_
    simp only [ConcreteCategory.comp_apply]
    exact congrArg (fun z => (ConcreteCategory.hom (Scheme.Hom.appTop (commonHom n₀ i j k))) z)
      (section_restrict n₀ (X j * X k) (X i) (X_mem_deg_one n₀ i) (X i * X j * X k)
        (show X i * X j * X k = (X j * X k) * X i from by rw [mul_assoc, mul_comm]) le_jk
        (awayFraction n₀ j k))
  have hIK : (Scheme.Hom.appTop (pullback.snd ((glueData n₀).f i j) ((glueData n₀).f i k)))
        (overlapUnit n₀ i k).val
      = (Scheme.Hom.appTop (commonHom n₀ i j k))
          ((Proj.basicOpen (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X j * X k)).topIso.inv
            (Proj.awayToSection (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X j * X k)
              (awayMap (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X_mem_deg_one n₀ j)
                (show X i * X j * X k = (X i * X k) * X j from
                  by rw [mul_assoc, mul_comm (X j) (X k), ← mul_assoc])
                (awayFraction n₀ i k)))) := by
    rw [overlapUnit_val_eq]
    have hmor : Scheme.Hom.appTop (overlapHom n₀ i k) ≫
          Scheme.Hom.appTop (pullback.snd ((glueData n₀).f i j) ((glueData n₀).f i k))
        = Scheme.Hom.appTop ((Proj (homogeneousSubmodule n₀ (ULift.{0} ℤ))).homOfLE le_ik) ≫
          Scheme.Hom.appTop (commonHom n₀ i j k) := by
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
      exact congrArg Scheme.Hom.appTop (fact_ik n₀ i j k le_ik)
    refine (congrArg (fun (m : _ ⟶ _) => (ConcreteCategory.hom m)
        ((Proj.basicOpen (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X k)).topIso.inv
          (Proj.awayToSection (homogeneousSubmodule n₀ (ULift.{0} ℤ)) (X i * X k)
            (awayFraction n₀ i k)))) hmor).trans ?_
    simp only [ConcreteCategory.comp_apply]
    exact congrArg (fun z => (ConcreteCategory.hom (Scheme.Hom.appTop (commonHom n₀ i j k))) z)
      (section_restrict n₀ (X i * X k) (X j) (X_mem_deg_one n₀ j) (X i * X j * X k)
        (show X i * X j * X k = (X i * X k) * X j from
          by rw [mul_assoc, mul_comm (X j) (X k), ← mul_assoc]) le_ik (awayFraction n₀ i k))
  rw [hIJ, hJK, hIK, ← map_mul]
  congr 1
  rw [← map_mul, ← map_mul, awayMap_awayFraction_cocycle]

set_option backward.isDefEq.respectTransparency false in
/-- The `m`-th power form of the transported overlap cocycle, as consumed by
`twistTransition_cocycle`.  Immediate from `overlapUnit_cocycle_transport` since the
comorphisms are ring homomorphisms and `Γ(V(i,j,k), O)` is commutative
(`(Aᵐ)(Bᵐ) = (AB)ᵐ`).

`set_option backward.isDefEq.respectTransparency false`: the transported units carry
`pullback ((glueData n₀).f ..) ..` whose index `(glueData n₀).J` is `n₀` only up to
reducible transparency, so `rw`/`simp` motive-building must relax the instance wall. -/
lemma overlapUnit_cocycle_transport_pow (m : ℕ) (i j k : n₀) :
    (Scheme.Hom.appTop (pullback.fst ((glueData n₀).f i j) ((glueData n₀).f i k)))
        ((overlapUnit n₀ i j ^ m).val) *
      (Scheme.Hom.appTop ((glueData n₀).t' i j k ≫
          pullback.fst ((glueData n₀).f j k) ((glueData n₀).f j i)))
        ((overlapUnit n₀ j k ^ m).val)
    = (Scheme.Hom.appTop (pullback.snd ((glueData n₀).f i j) ((glueData n₀).f i k)))
        ((overlapUnit n₀ i k ^ m).val) := by
  simp only [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, overlapUnit_cocycle_transport]

set_option backward.isDefEq.respectTransparency false in
/-- **(C2)** The triple-overlap cocycle condition for the Serre-twist
transitions, in the exact form consumed by `Scheme.Modules.glue`.  At the
level of transition units this is the identity
`(Xᵢ/Xⱼ)^m (Xⱼ/Xₖ)^m = (Xᵢ/Xₖ)^m` in `Γ(V(i,j,k), O)`; the transport of the
conjugated scalar isomorphisms to the triple overlap runs through the
`pullbackUnitIso` coherences (the rank-one analogue of
`bundleTransition_cocycle_transport`, `GrassmannianQuot.lean`).

The engine `Scheme.Modules.glue` is universe-monomorphic at `Scheme.GlueData.{0}`,
so the cocycle is proved here at `n₀ : Type` (the only regime that feeds the
glued sheaf); the rank-one scalar-transport core
`pullbackBaseChangeTransport_unitScalarIso` above stays generic. -/
lemma twistTransition_cocycle (m : ℕ) (i j k : n₀) :
    Scheme.Modules.pullbackBaseChangeTransport
        (pullback.fst ((glueData n₀).f i j) ((glueData n₀).f i k)) ((glueData n₀).f i j)
        ((glueData n₀).t i j ≫ (glueData n₀).f j i) (twistTransition n₀ m i j) ≪≫
      (Scheme.Modules.pullbackCongr
        (Scheme.Modules.glueData_bridge_mid (glueData n₀) i j k)).app
          (SheafOfModules.unit ((glueData n₀).U j).ringCatSheaf) ≪≫
      Scheme.Modules.pullbackBaseChangeTransport
        ((glueData n₀).t' i j k ≫ pullback.fst ((glueData n₀).f j k) ((glueData n₀).f j i))
        ((glueData n₀).f j k) ((glueData n₀).t j k ≫ (glueData n₀).f k j)
        (twistTransition n₀ m j k) ≪≫
      (Scheme.Modules.pullbackCongr
        (Scheme.Modules.glueData_bridge_tgt (glueData n₀) i j k)).app
          (SheafOfModules.unit ((glueData n₀).U k).ringCatSheaf)
    = (Scheme.Modules.pullbackCongr
        (Scheme.Modules.glueData_bridge_src (glueData n₀) i j k)).app
          (SheafOfModules.unit ((glueData n₀).U i).ringCatSheaf) ≪≫
      Scheme.Modules.pullbackBaseChangeTransport
        (pullback.snd ((glueData n₀).f i j) ((glueData n₀).f i k)) ((glueData n₀).f i k)
        ((glueData n₀).t i k ≫ (glueData n₀).f k i) (twistTransition n₀ m i k) := by
  apply Iso.ext
  simp only [Iso.trans_hom, twistTransition]
  rw [pullbackBaseChangeTransport_unitScalarIso, pullbackBaseChangeTransport_unitScalarIso,
    pullbackBaseChangeTransport_unitScalarIso]
  simp only [Category.assoc]
  rw [Scheme.Modules.pullbackUnitIso_inv_congr_hom_assoc
      (Scheme.Modules.glueData_bridge_mid (glueData n₀) i j k),
    Scheme.Modules.pullbackCongr_hom_app_unit_assoc
      (Scheme.Modules.glueData_bridge_src (glueData n₀) i j k),
    Scheme.Modules.pullbackUnitIso_inv_congr
      (Scheme.Modules.glueData_bridge_tgt (glueData n₀) i j k)]
  -- The endpoints (`Q_front`/`Q_back`) now match; fuse the two transported scalars via
  -- `scalarEnd_comp` and close with the base cocycle `overlapUnit_cocycle_transport`.
  rw [reassoc_of% scalarEnd_comp,
    overlapUnit_cocycle_transport_pow n₀ m i j k]

/-- The Serre twist `O(m)` on the glued total space of the basic-open cover. -/
def serreTwistGlued (m : ℕ) : (glueData n₀).glued.Modules :=
  Scheme.Modules.glue (glueData n₀)
    (fun i => SheafOfModules.unit ((glueData n₀).U i).ringCatSheaf)
    (fun i j => twistTransition n₀ m i j)
    (fun i => twistTransition_self n₀ m i)
    (fun i j k => twistTransition_cocycle n₀ m i j k)

/-- **The Serre twisting sheaf `O(m)`** on the integral model
`Proj ℤ[Xᵢ : i ∈ n₀]` of projective space: the glued sheaf transported along
the canonical isomorphism `fromGlued`. -/
def serreTwist (m : ℕ) :
    (Proj (homogeneousSubmodule n₀ (ULift.{0} ℤ))).Modules :=
  (Scheme.Modules.pullback (inv (basicOpenCover n₀).fromGlued)).obj
    (serreTwistGlued n₀ m)

end Universe0

end ProjTwist

end AlgebraicGeometry
