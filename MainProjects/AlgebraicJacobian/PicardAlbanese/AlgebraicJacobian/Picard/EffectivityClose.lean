/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EffectivitySplice
import AlgebraicJacobian.Picard.EffectivityMoving
import AlgebraicJacobian.Picard.EffectivityTrivialization
import AlgebraicJacobian.Picard.RelPicCoverInjective
import AlgebraicJacobian.Picard.NormalizedComparisonExists

/-!
# The (C2) effectivity theorem and the surjectivity close

**The campaign close.**  The fppf-effectivity theorem of the (C2) campaign (Kleiman,
*The Picard Scheme*, `th:cmp` Part 2 recast on the cocycle model) and the resulting
bijectivity of the unit of the étale plus construction over section-admitting field
tests:

* `Over.exists_cechPic_map_whiskerLeft_eq_of_pieces` — effectivity for an arbitrary
  faithfully flat `A → B`, given a covering family of trivialized pieces: a rigidified
  class on the cover curve whose two coprojection pullbacks agree on the nose descends
  along the cover inclusion `cg`.  The σ-normalized comparison exists unconditionally
  (E1); flat trivializations come from the trivialized pieces by localize-and-flatten;
  the refinement splice assembles the descent.
* `Over.exists_cechPic_map_whiskerLeft_eq` — **the (C2) effectivity theorem** for a
  module-finite faithfully flat cover: the covering family of trivialized pieces is
  produced *unconditionally* by the moving lemma
  (`AlgebraicJacobian.Picard.EffectivityMoving`).  Module-finiteness is honest: for a
  merely quasi-finite étale cover the bare restricted class need not trivialize on any
  saturated piece (see the moving lemma's docstring); the close below reaches arbitrary
  étale covers of a field test through the field cofinality of étale covers.
* `PicEtAff.unit_surjective_of_section` — **the headline**: over a field test `K`
  admitting a curve point `σ : Spec K ⟶ C`, the unit of the étale plus construction is
  surjective.  A plus class is represented on a finite separable field-extension cover
  (`Algebra.EtaleCover.exists_finiteSeparableField_algHom`); the rigidification layer
  (G1 + the rigidified transport keystone) puts the representative in the effectivity
  theorem's hypotheses; the descended class maps to the original by `mk`-calculus.
* `PicEtAff.unitEquiv_of_section` — with the (C1) injectivity (étale separatedness),
  the unit is a group isomorphism `relPic C (Spec K) ≃* PicEtAff C K`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable (C : Over (Spec (.of k)))
variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

section effectivity

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

set_option quotPrecheck false in
local notation "XA" => (C ⊗ overSpec k A).left
set_option quotPrecheck false in
local notation "XB" => (C ⊗ overSpec k B).left
set_option quotPrecheck false in
local notation "u₁" => (C ◁ Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "u₂" => (C ◁ Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "cg" => (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left

namespace Over

variable [Module.FaithfullyFlat A B] (σ : overSpec k A ⟶ C)

/-- **(C2) effectivity from a covering family of trivialized pieces** (arbitrary
faithfully flat cover): a class on the cover curve represented by `γ`, rigidified along
the base-changed section and with equal coprojection pullbacks on the nose, descends
along `cg` — provided every point of the base curve lies in an affine piece on which
the representing cocycle trivializes. -/
theorem exists_cechPic_map_whiskerLeft_eq_of_pieces
    (𝒩 : (XB).PointedCover) (γ : (XB).unitsCocycle 𝒩)
    (hrig : Over.IsRigidified
      (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k) ≫ σ)
      (Scheme.CechPic.mk 𝒩 γ.class))
    (hdesc : Scheme.CechPic.map (u₁) (Scheme.CechPic.mk 𝒩 γ.class)
        = Scheme.CechPic.map (u₂) (Scheme.CechPic.mk 𝒩 γ.class))
    (hpieces : ∀ x : XA, ∃ (V : (XA).Opens) (_ : IsAffineOpen V), x ∈ V ∧
      Nonempty (PieceTrivialization C 𝒩 γ V)) :
    ∃ M : (XA).CechPic,
      Scheme.CechPic.map (cg) M = Scheme.CechPic.mk 𝒩 γ.class := by
  obtain ⟨W⟩ := exists_normalizedCechComparison C σ 𝒩 γ hrig hdesc
  refine exists_cechPic_map_whiskerLeft_eq_of_flat C σ W fun x => ?_
  obtain ⟨V₁, hV₁, hxV₁, ⟨T₁⟩⟩ := hpieces x
  obtain ⟨V, hV, hxV, T, hT⟩ :=
    exists_flat_pieceTrivialization_of_le C σ W hV₁ T₁ hxV₁
  exact ⟨V, hV, hxV, T, hT⟩

/-- **The (C2) effectivity theorem** (recon §0.3; Kleiman `th:cmp` Part 2, the descent
of the rigidified pair): for a module-finite faithfully flat cover `A → B` of the test
algebra of a curve point `σ`, every Čech Picard class on the cover curve `X_B` that is
rigidified along the base-changed section (`hrig`) and has equal coprojection pullbacks
on the curve over `B ⊗[A] B` (`hdesc`) descends along the cover inclusion:
`∃ M, cg^* M = L`. -/
theorem exists_cechPic_map_whiskerLeft_eq [Module.Finite A B]
    (L : (XB).CechPic)
    (hrig : Over.IsRigidified
      (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k) ≫ σ) L)
    (hdesc : Scheme.CechPic.map (u₁) L = Scheme.CechPic.map (u₂) L) :
    ∃ M : (XA).CechPic, Scheme.CechPic.map (cg) M = L := by
  induction L using Scheme.CechPic.ind with | _ 𝒩 a
  induction a using Quot.ind with | _ γ
  rw [show (Quot.mk _ γ : (XB).unitsH1 𝒩)
    = CategoryTheory.PresheafOfGroups.OneCocycle.class γ from rfl] at hrig hdesc ⊢
  refine exists_cechPic_map_whiskerLeft_eq_of_pieces C σ 𝒩 γ hrig hdesc fun x => ?_
  obtain ⟨V, hV, hxV, h1⟩ := Over.exists_isAffineOpen_cechPicMap_preimage_eq_one
    (B := B) C (Scheme.CechPic.mk 𝒩 γ.class) x
  exact ⟨V, hV, hxV, Over.pieceTrivialization_of_cechPicMap_eq_one C V h1⟩

end Over

end effectivity

/-! ## The surjectivity close (recon §0.2) -/

section close

variable (K : Type u) [Field K] [Algebra k K]

/-- **Surjectivity of the unit of the étale plus construction over a section-admitting
field test** (Kleiman 2.5(2), axiom (C2) — the campaign headline): if the curve admits
a `K`-point `σ`, every class of `PicEtAff C K` comes from a relative Picard class.

A representative on an étale cover of `Spec K` is refined to a finite separable field
extension (field cofinality); the rigidification layer produces a rigidified Čech
representative whose descent equation holds on the nose; the (C2) effectivity theorem
descends it along the cover inclusion; and the `relPicMk`/`mk`-calculus identifies the
descended class's unit with the original plus class. -/
theorem PicEtAff.unit_surjective_of_section (σ : overSpec k K ⟶ C) :
    Function.Surjective (PicEtAff.unit C K) := by
  intro q
  induction q using PicEtAff.ind with | _ E x
  classical
  -- ### refine the representing cover to a finite separable field extension
  obtain ⟨L, hLfield, hLalg, hLfin, hLsep, ⟨f⟩⟩ :=
    E.exists_finiteSeparableField_algHom
  set F : Algebra.EtaleCover K := Algebra.EtaleCover.ofField (K := K) L with hF
  set g : E.Carrier →ₐ[K] F.Carrier :=
    ((Algebra.EtaleCover.ofFieldEquiv (K := K) L).symm.toAlgHom).comp f with hg
  set y : descentClasses C F := descentMap C g x with hy
  have hq : PicEtAff.mk C E x = PicEtAff.mk C F y :=
    (PicEtAff.mk_descentMap C g x).symm
  haveI : Module.Finite K F.Carrier :=
    Module.Finite.equiv (R := K) (M := L)
      (Algebra.EtaleCover.ofFieldEquiv (K := K) L).symm.toLinearEquiv
  -- ### a rigidified representative of the descent class (G1)
  obtain ⟨Lc, hrig, hLcrep⟩ := relPic.exists_isRigidified_rep
    (Over.overSpecMap ((Algebra.ofId K F.Carrier).restrictScalars k) ≫ σ)
    (y : relPic C (overSpec k F.Carrier))
  have hmem : relPicMk C (overSpec k F.Carrier) Lc ∈ descentClasses C F := by
    rw [hLcrep]
    exact y.2
  -- ### the on-the-nose descent equation (the rigidified transport keystone)
  have hdesc0 := Over.IsRigidified.cechPicMap_doubleInl_eq_doubleInr σ hmem hrig
  have hinl : doubleInl (k := k) F = tensorInl (k := k) (A := K) (B := F.Carrier) :=
    AlgHom.ext fun _ => rfl
  have hinr : doubleInr (k := k) F = tensorInr (k := k) (A := K) (B := F.Carrier) :=
    AlgHom.ext fun _ => rfl
  rw [hinl, hinr] at hdesc0
  -- ### the effectivity theorem
  obtain ⟨M, hM⟩ := Over.exists_cechPic_map_whiskerLeft_eq C σ Lc hrig hdesc0
  refine ⟨relPicMk C (overSpec k K) M, ?_⟩
  -- ### the `mk`-calculus close
  rw [PicEtAff.unit_eq_mk C F (relPicMk C (overSpec k K) M)]
  rw [hq]
  refine congrArg (PicEtAff.mk C F) (Subtype.ext ?_)
  change relPicAlgMap C ((Algebra.ofId K F.Carrier).restrictScalars k)
      (relPicMk C (overSpec k K) M) = (y : relPic C (overSpec k F.Carrier))
  rw [relPicAlgMap, relPicMap_mk, hM, hLcrep]

/-- **The unit of the étale plus construction is an isomorphism over a
section-admitting field test** — étale separatedness (C1) plus effectivity (C2):
`relPic C (Spec K) ≃* PicEtAff C K`. -/
noncomputable def PicEtAff.unitEquiv_of_section (σ : overSpec k K ⟶ C) :
    relPic C (overSpec k K) ≃* PicEtAff C K :=
  MulEquiv.ofBijective (PicEtAff.unit C K)
    ⟨PicEtAff.unit_injective C K, PicEtAff.unit_surjective_of_section C K σ⟩

end close

end AlgebraicGeometry
