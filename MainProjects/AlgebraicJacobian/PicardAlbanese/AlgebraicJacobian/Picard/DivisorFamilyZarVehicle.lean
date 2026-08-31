/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZarMapAlg
import AlgebraicJacobian.Picard.DivisorFamilyVehicle

/-!
# The locally certified divisor functor on all test objects: the vehicle (DD-2 stage S6a)

The Addendum-2 divisor-functor value on an affine test is `DivFamZar C R π n`
(`AlgebraicJacobian.Picard.DivisorFamilyZar`), with base change `DivFamZar.mapAlg`
along arbitrary test changes (`AlgebraicJacobian.Picard.DivisorFamilyZarMapAlg`).
This file extends it to **all** of `Over (Spec k)` by the bespoke affine-opens limit,
mirroring the globally certified vehicle `AlgebraicJacobian.Picard.DivisorFamilyVehicle`
clause for clause:

* `AlgebraicGeometry.DivFamZar.mapAlgHom`: base change of locally certified divisor
  classes along an **explicit** `k`-algebra map — `DivFamZar.mapAlg` at the induced
  algebra tower, with the functor laws `DivFamZar.mapAlgHom_id`/`DivFamZar.mapAlgHom_comp`
  from the S5b laws `DivFamZar.mapAlg_id`/`DivFamZar.mapAlg_comp`.
* `AlgebraicGeometry.DivFamZar.mapAlgHom_eq_mapAlg`: **the face-change bridge** — along
  an algebra map agreeing with a scalar-tower structure map, the explicit face is the
  instance face (`DivFamZar.mapAlg_congr`, algebra structures with equal structure maps
  are equal).  This is how the S6 general-test statements consume the S5b keystones
  `DivFamZar.eq_of_away_eq`/`DivFamZar.exists_glue_of_away_compat`, which are spelled in
  the instance face.
* `AlgebraicGeometry.DivFamZar.congr`: transport along an isomorphism of test algebras.
* `AlgebraicGeometry.divFamZar C π n T`: **the vehicle** — compatible families of
  locally certified divisor classes over the affine opens of `T.left`, with
  `divFamZar.eval` the evaluation at an affine open.
* `AlgebraicGeometry.divFamZarAffineEquiv C π n R`: **the affine comparison** — on an
  affine test `overSpec k R` the vehicle collapses by evaluation at the top affine open
  to `DivFamZar C R π n` (the `divFamAffineEquiv` template, clause for clause).
* `AlgebraicGeometry.divFam.toZarVehicle`: **the comparison from the globally certified
  vehicle** — componentwise `DivFam.toZar`, compatible by `DivFam.toZar_mapAlg`
  (packaged on the explicit face as `DivFam.toZar_mapAlgHom`); it intertwines the two
  affine comparisons (`divFamZarAffineEquiv_toZarVehicle`).

Functoriality in `T` along an *arbitrary* morphism of test objects (glued values over
basic-open refinements, the `picEtMap` pattern) is
`AlgebraicJacobian.Picard.DivisorFamilyZarMap`; the sheaf statements at arbitrary tests
are `AlgebraicJacobian.Picard.DivisorFamilyZarSheaf`.

The `k`-algebra structure on section rings is `Over.sectionsAlgebra` and the algebra
structures on the relative curve's section rings are `Scheme.overModule`/
`Scheme.overSectionsAlgebra` (LOCAL instances, house rule) — consumers must activate
the same instances.
-/

set_option autoImplicit false
/- Statements mix the section rings `Γ(T.left, ·)` with the locally certified
divisor-functor values over them, which are stated on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}

noncomputable section

/-! ## Base change of locally certified classes along an explicit algebra map

`DivFamZar.mapAlg` (`AlgebraicJacobian.Picard.DivisorFamilyZarMapAlg`) is parameterized
by an algebra-tower instance pack `[Algebra R R'] [IsScalarTower k R R']`.  The vehicle
indexes its compatibilities by the section-restriction maps `Over.resAlgHom`, so it
consumes the explicit-map face — the `DivFam.mapAlgHom` packaging of
`AlgebraicJacobian.Picard.DivisorFamilyVehicle`, verbatim. -/

namespace DivFamZar

variable {A A' A'' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']
  [CommRing A''] [Algebra k A'']

/-- Base change of locally certified divisor classes along an explicit `k`-algebra map
of affine tests: `DivFamZar.mapAlg` at the algebra structure `RingHom.toAlgebra` of the
map.  The instance-parameterized `DivFamZar.mapAlg` remains the preferred form whenever
a scalar tower is already in scope. -/
def mapAlgHom (φ : A →ₐ[k] A') : DivFamZar C A π n → DivFamZar C A' π n :=
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' := .of_algebraMap_eq fun a => (φ.commutes a).symm
  DivFamZar.mapAlg A' n

/-- `mapAlgHom` along the identity is the identity (`DivFamZar.mapAlg_id`). -/
theorem mapAlgHom_id (F : DivFamZar C A π n) : mapAlgHom (AlgHom.id k A) F = F :=
  DivFamZar.mapAlg_id n F

/-- `mapAlgHom` along a composite is the composite of the base changes
(`DivFamZar.mapAlg_comp`). -/
theorem mapAlgHom_comp (φ : A →ₐ[k] A') (ψ : A' →ₐ[k] A'') (F : DivFamZar C A π n) :
    mapAlgHom (ψ.comp φ) F = mapAlgHom ψ (mapAlgHom φ F) :=
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' := .of_algebraMap_eq fun x => (φ.commutes x).symm
  letI : Algebra A' A'' := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower k A' A'' := .of_algebraMap_eq fun x => (ψ.commutes x).symm
  letI : Algebra A A'' := (ψ.comp φ).toRingHom.toAlgebra
  haveI : IsScalarTower k A A'' := .of_algebraMap_eq fun x => ((ψ.comp φ).commutes x).symm
  haveI : IsScalarTower A A' A'' := .of_algebraMap_eq fun _ => rfl
  (DivFamZar.mapAlg_comp A' n A'' F).symm

/-! ### The face-change bridge -/

/-- `DivFamZar.mapAlg` depends on the `A`-algebra structure of the target only through
the structure itself: equal algebra structures give equal base changes (the scalar-tower
witnesses are proof-irrelevant).  The congruence backing the face-change bridge
`mapAlgHom_eq_mapAlg`. -/
theorem mapAlg_congr {a₁ a₂ : Algebra A A'} (h : a₁ = a₂)
    (t₁ : @IsScalarTower k A A' Algebra.toSMul a₁.toSMul Algebra.toSMul)
    (t₂ : @IsScalarTower k A A' Algebra.toSMul a₂.toSMul Algebra.toSMul)
    (F : DivFamZar C A π n) :
    @DivFamZar.mapAlg k _ C A _ _ π _ A' _ _ a₁ t₁ n F
      = @DivFamZar.mapAlg k _ C A _ _ π _ A' _ _ a₂ t₂ n F := by
  subst h
  rfl

/-- **The face-change bridge**: `mapAlgHom` along an algebra map that agrees with the
structure map of a scalar tower in scope is the instance-based `DivFamZar.mapAlg` of the
tower.  This is how the vehicle statements (spelled at `Over.resAlgHom`) consume the S5b
Zariski keystones (spelled at localization instance packs). -/
theorem mapAlgHom_eq_mapAlg [Algebra A A'] [IsScalarTower k A A'] (φ : A →ₐ[k] A')
    (hφ : ∀ a, φ a = algebraMap A A' a) (F : DivFamZar C A π n) :
    mapAlgHom φ F = DivFamZar.mapAlg A' n F := by
  unfold mapAlgHom
  exact mapAlg_congr (Algebra.algebra_ext _ _ hφ) _ _ F

/-! ### Transport along an isomorphism of test algebras -/

/-- Transport of locally certified divisor classes along an isomorphism of test
algebras. -/
def congr (e : A ≃ₐ[k] A') : DivFamZar C A π n ≃ DivFamZar C A' π n where
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
lemma congr_apply (e : A ≃ₐ[k] A') (F : DivFamZar C A π n) :
    congr e F = mapAlgHom e.toAlgHom F :=
  rfl

/-- The inverse transport along an isomorphism is `mapAlgHom` of the inverse map. -/
@[simp]
lemma congr_symm_apply (e : A ≃ₐ[k] A') (F : DivFamZar C A' π n) :
    (congr e).symm F = mapAlgHom e.symm.toAlgHom F :=
  rfl

end DivFamZar

/-- **`toZar` intertwines the explicit-face base changes**: the comparison from
globally certified to locally certified classes is natural in the test algebra along an
explicit `k`-algebra map — `DivFam.toZar_mapAlg` at the induced tower. -/
lemma DivFam.toZar_mapAlgHom {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A']
    [Algebra k A'] (φ : A →ₐ[k] A') (F : DivFam C A π n) :
    (DivFam.mapAlgHom φ F).toZar = DivFamZar.mapAlgHom φ F.toZar :=
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' := .of_algebraMap_eq fun a => (φ.commutes a).symm
  DivFam.toZar_mapAlg A' n F

/-! ## The affine-opens limit -/

variable (C π n)

/-- **The locally certified divisor functor at an arbitrary test object**
(`informal/spec-dd-2.md` §6 on the Addendum-2 carrier; the `divFam` vehicle):
compatible families of locally certified divisor classes over the affine opens of
`T.left` — the value at a smaller affine open is the base change of the value at a
larger one along the section-restriction algebra map.  On affine tests this is
`DivFamZar` itself (`divFamZarAffineEquiv`); on general tests it is its canonical
Zariski-continuous extension. -/
def divFamZar (T : Over (Spec (.of k))) : Type u :=
  {s : Π U : T.left.affineOpens, DivFamZar C Γ(T.left, U.1) π n //
    ∀ (U V : T.left.affineOpens) (h : U.1 ≤ V.1),
      DivFamZar.mapAlgHom (Over.resAlgHom T h) (s V) = s U}

namespace divFamZar

variable {C π n} {T : Over (Spec (.of k))}

/-- The compatibility of a section of `divFamZar` along an inclusion of affine opens. -/
lemma compat (s : divFamZar C π n T) (U V : T.left.affineOpens) (h : U.1 ≤ V.1) :
    DivFamZar.mapAlgHom (Over.resAlgHom T h) (s.1 V) = s.1 U :=
  s.2 U V h

/-- Two sections of `divFamZar` agreeing at every affine open are equal. -/
@[ext]
lemma ext {s t : divFamZar C π n T} (h : ∀ U : T.left.affineOpens, s.1 U = t.1 U) :
    s = t :=
  Subtype.ext (funext h)

variable (C π n T) in
/-- Evaluation of a section of `divFamZar` at an affine open. -/
def eval (U : T.left.affineOpens) : divFamZar C π n T → DivFamZar C Γ(T.left, U.1) π n :=
  fun s => s.1 U

/-- Evaluation is projection to the component at the affine open. -/
@[simp]
lemma eval_apply (U : T.left.affineOpens) (s : divFamZar C π n T) :
    eval C π n T U s = s.1 U :=
  rfl

end divFamZar

/-! ## The affine comparison -/

section Affine

variable (R : Type u) [CommRing R] [Algebra k R]

/-- Evaluation at the top affine open of an affine test, composed with the
`ΓSpecIso`-transport into the test algebra: the forward direction of the affine
comparison. -/
def divFamZarToAff : divFamZar C π n (overSpec k R) → DivFamZar C R π n :=
  fun s => DivFamZar.congr (Over.overSpecΓTopAlgEquiv k R) (s.1 (overSpecTopAffine R))

/-- The section of `divFamZar` over an affine test determined by a locally certified
divisor class of the test algebra: restrict from the top affine open — the inverse
direction of the affine comparison. -/
def divFamZarOfAff : DivFamZar C R π n → divFamZar C π n (overSpec k R) :=
  fun x =>
    ⟨fun U => DivFamZar.mapAlgHom
      ((Over.resAlgHom (overSpec k R) le_top).comp
        (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom) x,
      fun U V h => by rw [← DivFamZar.mapAlgHom_comp, ← AlgHom.comp_assoc,
        Over.resAlgHom_comp]⟩

/-- The value of `divFamZarOfAff` at every affine open is the restricted transported
class. -/
lemma divFamZarOfAff_val (x : DivFamZar C R π n) (U : (overSpec k R).left.affineOpens) :
    (divFamZarOfAff C π n R x).1 U
      = DivFamZar.mapAlgHom
          ((Over.resAlgHom (overSpec k R) le_top).comp
            (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom) x :=
  rfl

/-- Round trip on the vehicle side: restricting the transported top value recovers every
component, by the compatibility of the section. -/
private lemma divFamZarOfAff_divFamZarToAff (s : divFamZar C π n (overSpec k R)) :
    divFamZarOfAff C π n R (divFamZarToAff C π n R s) = s := by
  refine divFamZar.ext fun U => ?_
  calc (divFamZarOfAff C π n R (divFamZarToAff C π n R s)).1 U
      = DivFamZar.mapAlgHom
          (((Over.resAlgHom (overSpec k R) le_top).comp
              (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom).comp
            (Over.overSpecΓTopAlgEquiv k R).toAlgHom)
          (s.1 (overSpecTopAffine R)) :=
        (DivFamZar.mapAlgHom_comp _ _ _).symm
    _ = DivFamZar.mapAlgHom (Over.resAlgHom (overSpec k R) le_top)
          (s.1 (overSpecTopAffine R)) := by
        rw [AlgHom.comp_assoc,
          show (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom.comp
              (Over.overSpecΓTopAlgEquiv k R).toAlgHom
            = AlgHom.id k Γ((overSpec k R).left, ⊤) from
            AlgHom.ext fun a => (Over.overSpecΓTopAlgEquiv k R).symm_apply_apply a,
          AlgHom.comp_id]
    _ = s.1 U := s.compat U (overSpecTopAffine R) le_top

/-- Round trip on the algebra side: the two `ΓSpecIso` transports and the trivial
restriction collapse to the identity (`DivFamZar.mapAlgHom_id`). -/
private lemma divFamZarToAff_divFamZarOfAff (x : DivFamZar C R π n) :
    divFamZarToAff C π n R (divFamZarOfAff C π n R x) = x := by
  calc divFamZarToAff C π n R (divFamZarOfAff C π n R x)
      = DivFamZar.mapAlgHom
          ((Over.overSpecΓTopAlgEquiv k R).toAlgHom.comp
            ((Over.resAlgHom (overSpec k R) le_top).comp
              (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom)) x :=
        (DivFamZar.mapAlgHom_comp _ _ _).symm
    _ = DivFamZar.mapAlgHom (AlgHom.id k R) x := by
        rw [show Over.resAlgHom (overSpec k R) (le_top :
              (⊤ : (overSpec k R).left.Opens) ≤ (⊤ : (overSpec k R).left.Opens))
            = AlgHom.id k Γ((overSpec k R).left, ⊤) from Over.resAlgHom_rfl _ le_top,
          AlgHom.id_comp,
          show (Over.overSpecΓTopAlgEquiv k R).toAlgHom.comp
              (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom
            = AlgHom.id k R from
            AlgHom.ext fun a => (Over.overSpecΓTopAlgEquiv k R).apply_symm_apply a]
    _ = x := DivFamZar.mapAlgHom_id x

/-- **The affine comparison equivalence** (`informal/spec-dd-2.md` §6, Addendum 2): on
an affine test `overSpec k R`, the affine-opens limit `divFamZar` collapses by
evaluation at the terminal element `⊤` of the affine-opens poset to the locally
certified divisor-functor value `DivFamZar C R π n` of the test algebra (the
`divFamAffineEquiv` template). -/
def divFamZarAffineEquiv : divFamZar C π n (overSpec k R) ≃ DivFamZar C R π n where
  toFun := divFamZarToAff C π n R
  invFun := divFamZarOfAff C π n R
  left_inv := divFamZarOfAff_divFamZarToAff C π n R
  right_inv := divFamZarToAff_divFamZarOfAff C π n R

/-- The affine comparison evaluates at the top affine open and transports along
`Over.overSpecΓTopAlgEquiv`. -/
@[simp]
lemma divFamZarAffineEquiv_apply (s : divFamZar C π n (overSpec k R)) :
    divFamZarAffineEquiv C π n R s
      = DivFamZar.mapAlgHom (Over.overSpecΓTopAlgEquiv k R).toAlgHom
          (s.1 (overSpecTopAffine R)) :=
  rfl

/-- The inverse affine comparison restricts the transported class from the top affine
open. -/
@[simp]
lemma divFamZarAffineEquiv_symm_apply_val (x : DivFamZar C R π n)
    (U : (overSpec k R).left.affineOpens) :
    ((divFamZarAffineEquiv C π n R).symm x).1 U
      = DivFamZar.mapAlgHom
          ((Over.resAlgHom (overSpec k R) le_top).comp
            (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom) x :=
  rfl

end Affine

/-! ## The comparison from the globally certified vehicle -/

variable {C π n} in
/-- **The comparison from the globally certified vehicle**: componentwise
`DivFam.toZar`, compatible under restriction by `DivFam.toZar_mapAlg`
(`DivFam.toZar_mapAlgHom` on the explicit face).  Over a field the two vehicles agree
componentwise; over a general test this is the sheafification-of-value comparison. -/
def divFam.toZarVehicle {T : Over (Spec (.of k))} (s : divFam C π n T) :
    divFamZar C π n T :=
  ⟨fun U => (s.1 U).toZar,
    fun U V h => by
      beta_reduce
      rw [← s.compat U V h, DivFam.toZar_mapAlgHom]⟩

/-- The value of the comparison at an affine open is the comparison of the value. -/
@[simp]
lemma divFam.toZarVehicle_val {T : Over (Spec (.of k))} (s : divFam C π n T)
    (U : T.left.affineOpens) :
    (divFam.toZarVehicle s).1 U = (s.1 U).toZar :=
  rfl

/-- **The comparison intertwines the affine comparisons**: on an affine test, passing
to the locally certified vehicle and collapsing agrees with collapsing and passing to
the locally certified value. -/
lemma divFamZarAffineEquiv_toZarVehicle (R : Type u) [CommRing R] [Algebra k R]
    (s : divFam C π n (overSpec k R)) :
    divFamZarAffineEquiv C π n R (divFam.toZarVehicle s)
      = (divFamAffineEquiv C π n R s).toZar := by
  rw [divFamZarAffineEquiv_apply, divFamAffineEquiv_apply, divFam.toZarVehicle_val,
    DivFam.toZar_mapAlgHom]

end

end AlgebraicGeometry
