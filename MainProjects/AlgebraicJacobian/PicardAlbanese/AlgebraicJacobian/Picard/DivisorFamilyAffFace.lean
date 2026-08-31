/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffMapAlg
import AlgebraicJacobian.Picard.DivisorFamilyZarVehicle

/-!
# The widened carrier's EXPLICIT-MAP face: `DivFamZarAff.mapAlgHom`

`DivFamZarAff.mapAlg` (`…AffMapAlg.lean`) base-changes the widened class along an algebra
**tower instance pack** `[Algebra R R'] [IsScalarTower k R R']`.  That is the right form
whenever a tower is already in scope, and it is what the S5b Zariski keystones are stated at.

It is **not** the form the divisor vehicle consumes.  `divFamZar`
(`DivisorFamilyZarVehicle.lean`) indexes its compatibility condition by the section-restriction
maps `Over.resAlgHom T h`, which are bare `AlgHom`s carrying no tower instance, so the vehicle
and hence `divFunctor` are stated entirely at `DivFamZar.mapAlgHom`.  Until the widened carrier
has that same face, a widened class exists only at an affine test and nothing carries it to a
general one — measured at HEAD: outside the `DivisorFamilyAff*` files the name `DivFamZarAff`
appeared nowhere in the tree.

So this file is the missing half of the base-change layer, and it is deliberately a *verbatim*
transcription of the chart-typed one: same names modulo `Aff`, same statements, same proofs.
Nothing here is new mathematics — `mapAlgHom` is `mapAlg` at `RingHom.toAlgebra` of the map,
and the two functor laws come from `mapAlg_id` / `mapAlg_comp` at the induced towers.  The
value of writing it is that the *consumer* side becomes typeable at all.

## Why `[IsProper C.hom]` appears here and not in the chart-typed file

`DivFamZarAff.mapAlg` needs it (`…AffMapAlg.lean` §Transport): properness is what makes
`AffCoverData.HasAffineOverlaps` free, and the widened certificate transport needs overlap
affineness because an arbitrary affine open's overlaps are not affine by fiat the way basic
opens of a fixed affine chart were.  It is a hypothesis the DD-R lane carries everywhere, so
this costs no generality — but it is stated rather than hidden, since it is exactly one of the
things I-0492 clause 4(ii) warns the old typing was silently supplying.

## Main declarations

* `AlgebraicGeometry.DivFamZarAff.mapAlgHom` — the explicit-map face.
* `DivFamZarAff.mapAlgHom_id`, `mapAlgHom_comp` — the functor laws on that face.
* `DivFamZarAff.mapAlg_congr`, `mapAlgHom_eq_mapAlg` — the face-change bridge, so a statement
  proved at a tower can be consumed at a restriction map and conversely.
* `DivFamZarAff.picClass_mapAlgHom` — the Abel hook on that face.
* `DivFamZarAff.congr` — transport along an isomorphism of test algebras.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom] {n : ℕ}

noncomputable section

namespace DivFamZarAff

variable {A A' A'' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']
  [CommRing A''] [Algebra k A'']

/-- **Base change of a widened locally certified class along an explicit `k`-algebra map** of
affine tests: `DivFamZarAff.mapAlg` at the algebra structure `RingHom.toAlgebra` of the map.

The instance-parameterized `DivFamZarAff.mapAlg` remains the preferred form whenever a scalar
tower is already in scope; this face exists because the vehicle's compatibility condition is
indexed by `Over.resAlgHom`, which is a bare `AlgHom`. -/
def mapAlgHom (φ : A →ₐ[k] A') : DivFamZarAff C A n → DivFamZarAff C A' n :=
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' := .of_algebraMap_eq fun a => (φ.commutes a).symm
  DivFamZarAff.mapAlg A' n

/-- `mapAlgHom` along the identity is the identity (`DivFamZarAff.mapAlg_id`). -/
theorem mapAlgHom_id (F : DivFamZarAff C A n) : mapAlgHom (AlgHom.id k A) F = F :=
  DivFamZarAff.mapAlg_id n F

/-- `mapAlgHom` along a composite is the composite of the base changes
(`DivFamZarAff.mapAlg_comp`). -/
theorem mapAlgHom_comp (φ : A →ₐ[k] A') (ψ : A' →ₐ[k] A'') (F : DivFamZarAff C A n) :
    mapAlgHom (ψ.comp φ) F = mapAlgHom ψ (mapAlgHom φ F) :=
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' := .of_algebraMap_eq fun x => (φ.commutes x).symm
  letI : Algebra A' A'' := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower k A' A'' := .of_algebraMap_eq fun x => (ψ.commutes x).symm
  letI : Algebra A A'' := (ψ.comp φ).toRingHom.toAlgebra
  haveI : IsScalarTower k A A'' := .of_algebraMap_eq fun x => ((ψ.comp φ).commutes x).symm
  haveI : IsScalarTower A A' A'' := .of_algebraMap_eq fun _ => rfl
  (DivFamZarAff.mapAlg_comp A' n A'' F).symm

/-! ### The face-change bridge -/

/-- `DivFamZarAff.mapAlg` depends on the `A`-algebra structure of the target only through the
structure itself: equal algebra structures give equal base changes (the scalar-tower witnesses
are proof-irrelevant).  The congruence backing `mapAlgHom_eq_mapAlg`.

**DO NOT DELETE THIS AS A TAUTOLOGY.**  `#check` renders it as
`mapAlg A' n F = mapAlg A' n F`, because the two sides differ *only* in the suppressed
`Algebra A A'` instance argument — which is why the statement below is written with explicit
`@`-applications.  It is a real lemma (`subst h; rfl` on distinct instance arguments) and
`mapAlgHom_eq_mapAlg` genuinely needs it.  Flagged because an audit reading `#check` output alone
would score it as vacuous (reviewer note, run 0070 s0010). -/
theorem mapAlg_congr {a₁ a₂ : Algebra A A'} (h : a₁ = a₂)
    (t₁ : @IsScalarTower k A A' Algebra.toSMul a₁.toSMul Algebra.toSMul)
    (t₂ : @IsScalarTower k A A' Algebra.toSMul a₂.toSMul Algebra.toSMul)
    (F : DivFamZarAff C A n) :
    @DivFamZarAff.mapAlg k _ C A _ _ A' _ _ a₁ t₁ n _ F
      = @DivFamZarAff.mapAlg k _ C A _ _ A' _ _ a₂ t₂ n _ F := by
  subst h
  rfl

/-- **The face-change bridge**: `mapAlgHom` along an algebra map that agrees with the structure
map of a scalar tower in scope is the instance-based `DivFamZarAff.mapAlg` of the tower.

This is how the widened vehicle statements (spelled at `Over.resAlgHom`) consume the widened
S5b keystones (spelled at localization instance packs) — and in the reverse direction, how
`eq_of_away_eq` becomes usable from the vehicle. -/
theorem mapAlgHom_eq_mapAlg [Algebra A A'] [IsScalarTower k A A'] (φ : A →ₐ[k] A')
    (hφ : ∀ a, φ a = algebraMap A A' a) (F : DivFamZarAff C A n) :
    mapAlgHom φ F = DivFamZarAff.mapAlg A' n F := by
  unfold mapAlgHom
  exact mapAlg_congr (Algebra.algebra_ext _ _ hφ) _ _ F

/-! ### The Abel hook on the explicit face -/

/-- **The Abel-hook class law on the explicit face**: `𝒪(φ^*D) = φ^*𝒪(D)`.  `picClass_mapAlg`
at the induced tower — the class never saw the cover, so the widening is invisible here. -/
lemma picClass_mapAlgHom (φ : A →ₐ[k] A') (F : DivFamZarAff C A n) :
    (mapAlgHom φ F).picClass
      = letI : Algebra A A' := φ.toRingHom.toAlgebra
        haveI : IsScalarTower k A A' := .of_algebraMap_eq fun a => (φ.commutes a).symm
        Scheme.CechPic.map (relCurveMap C A A') F.picClass :=
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' := .of_algebraMap_eq fun a => (φ.commutes a).symm
  DivFamZarAff.picClass_mapAlg A' n F

/-! ### Transport along an isomorphism of test algebras -/

/-- Transport of widened locally certified classes along an isomorphism of test algebras. -/
def congr (e : A ≃ₐ[k] A') : DivFamZarAff C A n ≃ DivFamZarAff C A' n where
  toFun := mapAlgHom e.toAlgHom
  invFun := mapAlgHom e.symm.toAlgHom
  left_inv F := by
    rw [← mapAlgHom_comp, show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id k A from
      AlgHom.ext fun a => e.symm_apply_apply a, mapAlgHom_id]
  right_inv F := by
    rw [← mapAlgHom_comp, show e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id k A' from
      AlgHom.ext fun a => e.apply_symm_apply a, mapAlgHom_id]

/-- The transport along an isomorphism is `mapAlgHom` of its underlying map. -/
@[simp]
lemma congr_apply (e : A ≃ₐ[k] A') (F : DivFamZarAff C A n) :
    congr e F = mapAlgHom e.toAlgHom F :=
  rfl

/-- The inverse transport along an isomorphism is `mapAlgHom` of the inverse map. -/
@[simp]
lemma congr_symm_apply (e : A ≃ₐ[k] A') (F : DivFamZarAff C A' n) :
    (congr e).symm F = mapAlgHom e.symm.toAlgHom F :=
  rfl

end DivFamZarAff

/-! ## The chart-typed value maps into the widened one on the explicit face

`DivFamZar.toAff_mapAlg` (`…AffMapAlg.lean`) is the naturality of `toAff` at a tower.  The
explicit face of that statement is what a vehicle-level comparison needs, and it follows by
unfolding both faces at the induced tower. -/

/-- **`toAff` is natural on the explicit face**: the widened value receives the chart-typed one
compatibly with base change along an arbitrary `k`-algebra map of affine tests. -/
lemma DivFamZar.toAff_mapAlgHom {π : C.left ⟶ P1 k} [IsAffineHom π]
    {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']
    (φ : A →ₐ[k] A') (F : DivFamZar C A π n) :
    (DivFamZar.mapAlgHom φ F).toAff = DivFamZarAff.mapAlgHom φ F.toAff :=
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' := .of_algebraMap_eq fun a => (φ.commutes a).symm
  DivFamZar.toAff_mapAlg A' n F

end

end AlgebraicGeometry
