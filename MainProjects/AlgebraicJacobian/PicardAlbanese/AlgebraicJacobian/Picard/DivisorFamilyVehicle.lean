/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyMapAlg
import AlgebraicJacobian.Picard.PicEt

/-!
# The divisor functor on all test objects: the affine-opens-limit vehicle (DD-2 stage S3)

The divisor functor's value on an affine test is `DivFam C R π n`
(`AlgebraicJacobian.Picard.DivisorFamily`), with base change `DivFam.mapAlg` along
arbitrary test changes (`AlgebraicJacobian.Picard.DivisorFamilyMapAlg`).  The frozen
carrier spelling (`informal/spec-dd-1.md` §1e) extends it to **all** of `Over (Spec k)`
by the bespoke affine-opens limit of `AlgebraicJacobian.Picard.PicEt`: a section over a
test object `T` is a compatible family of divisor classes over the affine opens of
`T.left`, valued in `DivFam C Γ(T.left, U) π n` via the section-ring algebras
`Over.sectionsAlgebra`.  The index poset is `Type u`-small, which is the point of the
vehicle.

* `AlgebraicGeometry.DivFam.mapAlgHom`: base change of divisor classes along an
  **explicit** `k`-algebra map — `DivFam.mapAlg` at the induced algebra tower (the
  `PicEtAff.mapAlg`-over-`PicEtAff.map` packaging), with the functor laws
  `DivFam.mapAlgHom_id`/`DivFam.mapAlgHom_comp` from `DivFam.mapAlg_id`/
  `DivFam.mapAlg_comp`.
* `AlgebraicGeometry.DivFam.congr`: transport of divisor classes along an isomorphism
  of test algebras.
* `AlgebraicGeometry.divFam C π n T`: **the vehicle** — the limit, as the subtype of the
  product over `T.left.affineOpens` cut out by compatibility under restriction;
  `divFam.eval` is evaluation at an affine open.
* `AlgebraicGeometry.divFamAffineEquiv C π n R`: **the affine comparison** — on an
  affine test `overSpec k R`, evaluation at the top affine open is an equivalence
  `divFam C π n (overSpec k R) ≃ DivFam C R π n` (the affine-opens poset of an affine
  test has a terminal element, so the limit collapses; the `picEtAffineEquiv` template).
* `AlgebraicGeometry.divFam.map C π n f`: restriction of vehicle sections along a
  morphism `f : T' ⟶ T` of test objects **whose underlying morphism is an open
  immersion** — the image of an affine open under an open immersion is affine, so the
  restricted family needs no gluing.

Functoriality in `T` along an *arbitrary* morphism of test objects — where the image of
an affine open need not lie in any affine open of the target, so the value must be glued
over a basic-open refinement — is stage S6's business, exactly as `picEtMap`
(`AlgebraicJacobian.Picard.PicEtMap`) is built on the Zariski sheaf property of
`PicEtAff` and not provided by `AlgebraicJacobian.Picard.PicEt` itself
(`informal/spec-dd-2.md` §3/§6).

The `k`-algebra structure on section rings is `Over.sectionsAlgebra` and the `R`-algebra
structure on the relative curve's section rings is `Scheme.overSectionsAlgebra` (LOCAL
instances, house rule) — consumers must activate the same instances.
-/

set_option autoImplicit false
/- Statements mix the section rings `Γ(T.left, ·)` (presented on the
`TopCat.Presheaf`/`Opens ↥T.left` spellings) with the divisor-functor values over them;
see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}

noncomputable section

/-! ## Base change of divisor classes along an explicit algebra map

`DivFam.mapAlg` (`AlgebraicJacobian.Picard.DivisorFamilyMapAlg`) is parameterized by an
algebra-tower instance pack `[Algebra R R'] [IsScalarTower k R R']`.  The vehicle indexes
its compatibilities by the section-restriction maps `Over.resAlgHom`, so it consumes the
explicit-map face: `DivFam.mapAlg` at the tower induced by a `k`-algebra map — the
`PicEtAff.mapAlg`-over-`PicEtAff.map` packaging, verbatim. -/

namespace DivFam

variable {A A' A'' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']
  [CommRing A''] [Algebra k A'']

/-- Base change of divisor classes along an explicit `k`-algebra map of affine tests:
`DivFam.mapAlg` at the algebra structure `RingHom.toAlgebra` of the map.  The
instance-parameterized `DivFam.mapAlg` remains the preferred form whenever a scalar
tower is already in scope. -/
def mapAlgHom (φ : A →ₐ[k] A') : DivFam C A π n → DivFam C A' π n :=
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' := .of_algebraMap_eq fun a => (φ.commutes a).symm
  DivFam.mapAlg A' n

/-- `mapAlgHom` along the identity is the identity (`DivFam.mapAlg_id`). -/
theorem mapAlgHom_id (F : DivFam C A π n) : mapAlgHom (AlgHom.id k A) F = F :=
  DivFam.mapAlg_id n F

/-- `mapAlgHom` along a composite is the composite of the base changes
(`DivFam.mapAlg_comp`). -/
theorem mapAlgHom_comp (φ : A →ₐ[k] A') (ψ : A' →ₐ[k] A'') (F : DivFam C A π n) :
    mapAlgHom (ψ.comp φ) F = mapAlgHom ψ (mapAlgHom φ F) :=
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' := .of_algebraMap_eq fun x => (φ.commutes x).symm
  letI : Algebra A' A'' := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower k A' A'' := .of_algebraMap_eq fun x => (ψ.commutes x).symm
  letI : Algebra A A'' := (ψ.comp φ).toRingHom.toAlgebra
  haveI : IsScalarTower k A A'' := .of_algebraMap_eq fun x => ((ψ.comp φ).commutes x).symm
  haveI : IsScalarTower A A' A'' := .of_algebraMap_eq fun _ => rfl
  (DivFam.mapAlg_comp A' n A'' F).symm

/-- Transport of divisor classes along an isomorphism of test algebras. -/
def congr (e : A ≃ₐ[k] A') : DivFam C A π n ≃ DivFam C A' π n where
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
lemma congr_apply (e : A ≃ₐ[k] A') (F : DivFam C A π n) :
    congr e F = mapAlgHom e.toAlgHom F :=
  rfl

/-- The inverse transport along an isomorphism is `mapAlgHom` of the inverse map. -/
@[simp]
lemma congr_symm_apply (e : A ≃ₐ[k] A') (F : DivFam C A' π n) :
    (congr e).symm F = mapAlgHom e.symm.toAlgHom F :=
  rfl

end DivFam

/-! ## The affine-opens limit -/

variable (C π n)

/-- **The divisor functor at an arbitrary test object** (`informal/spec-dd-1.md` §1e,
the `picEt` vehicle): compatible families of divisor classes over the affine opens of
`T.left` — the value at a smaller affine open is the base change of the value at a
larger one along the section-restriction algebra map.  On affine tests this is `DivFam`
itself (`divFamAffineEquiv`); on general tests it is its canonical Zariski-continuous
extension. -/
def divFam (T : Over (Spec (.of k))) : Type u :=
  {s : Π U : T.left.affineOpens, DivFam C Γ(T.left, U.1) π n //
    ∀ (U V : T.left.affineOpens) (h : U.1 ≤ V.1),
      DivFam.mapAlgHom (Over.resAlgHom T h) (s V) = s U}

namespace divFam

variable {C π n} {T : Over (Spec (.of k))}

/-- The compatibility of a section of `divFam` along an inclusion of affine opens. -/
lemma compat (s : divFam C π n T) (U V : T.left.affineOpens) (h : U.1 ≤ V.1) :
    DivFam.mapAlgHom (Over.resAlgHom T h) (s.1 V) = s.1 U :=
  s.2 U V h

/-- Two sections of `divFam` agreeing at every affine open are equal. -/
@[ext]
lemma ext {s t : divFam C π n T} (h : ∀ U : T.left.affineOpens, s.1 U = t.1 U) : s = t :=
  Subtype.ext (funext h)

variable (C π n T) in
/-- Evaluation of a section of `divFam` at an affine open. -/
def eval (U : T.left.affineOpens) : divFam C π n T → DivFam C Γ(T.left, U.1) π n :=
  fun s => s.1 U

/-- Evaluation is projection to the component at the affine open. -/
@[simp]
lemma eval_apply (U : T.left.affineOpens) (s : divFam C π n T) : eval C π n T U s = s.1 U :=
  rfl

end divFam

/-! ## The affine comparison -/

section Affine

variable (R : Type u) [CommRing R] [Algebra k R]

/-- Evaluation at the top affine open of an affine test, composed with the
`ΓSpecIso`-transport into the test algebra: the forward direction of the affine
comparison. -/
def divFamToAff : divFam C π n (overSpec k R) → DivFam C R π n :=
  fun s => DivFam.congr (Over.overSpecΓTopAlgEquiv k R) (s.1 (overSpecTopAffine R))

/-- The section of `divFam` over an affine test determined by a divisor class of the
test algebra: restrict from the top affine open — the inverse direction of the affine
comparison. -/
def divFamOfAff : DivFam C R π n → divFam C π n (overSpec k R) :=
  fun x =>
    ⟨fun U => DivFam.mapAlgHom
      ((Over.resAlgHom (overSpec k R) le_top).comp
        (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom) x,
      fun U V h => by rw [← DivFam.mapAlgHom_comp, ← AlgHom.comp_assoc,
        Over.resAlgHom_comp]⟩

/-- The value of `divFamOfAff` at every affine open is the restricted transported
class. -/
lemma divFamOfAff_val (x : DivFam C R π n) (U : (overSpec k R).left.affineOpens) :
    (divFamOfAff C π n R x).1 U
      = DivFam.mapAlgHom
          ((Over.resAlgHom (overSpec k R) le_top).comp
            (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom) x :=
  rfl

/-- Round trip on the vehicle side: restricting the transported top value recovers every
component, by the compatibility of the section. -/
private lemma divFamOfAff_divFamToAff (s : divFam C π n (overSpec k R)) :
    divFamOfAff C π n R (divFamToAff C π n R s) = s := by
  refine divFam.ext fun U => ?_
  calc (divFamOfAff C π n R (divFamToAff C π n R s)).1 U
      = DivFam.mapAlgHom
          (((Over.resAlgHom (overSpec k R) le_top).comp
              (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom).comp
            (Over.overSpecΓTopAlgEquiv k R).toAlgHom)
          (s.1 (overSpecTopAffine R)) :=
        (DivFam.mapAlgHom_comp _ _ _).symm
    _ = DivFam.mapAlgHom (Over.resAlgHom (overSpec k R) le_top)
          (s.1 (overSpecTopAffine R)) := by
        rw [AlgHom.comp_assoc,
          show (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom.comp
              (Over.overSpecΓTopAlgEquiv k R).toAlgHom
            = AlgHom.id k Γ((overSpec k R).left, ⊤) from
            AlgHom.ext fun a => (Over.overSpecΓTopAlgEquiv k R).symm_apply_apply a,
          AlgHom.comp_id]
    _ = s.1 U := s.compat U (overSpecTopAffine R) le_top

/-- Round trip on the algebra side: the two `ΓSpecIso` transports and the trivial
restriction collapse to the identity (`DivFam.mapAlgHom_id`). -/
private lemma divFamToAff_divFamOfAff (x : DivFam C R π n) :
    divFamToAff C π n R (divFamOfAff C π n R x) = x := by
  calc divFamToAff C π n R (divFamOfAff C π n R x)
      = DivFam.mapAlgHom
          ((Over.overSpecΓTopAlgEquiv k R).toAlgHom.comp
            ((Over.resAlgHom (overSpec k R) le_top).comp
              (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom)) x :=
        (DivFam.mapAlgHom_comp _ _ _).symm
    _ = DivFam.mapAlgHom (AlgHom.id k R) x := by
        rw [show Over.resAlgHom (overSpec k R) (le_top :
              (⊤ : (overSpec k R).left.Opens) ≤ (⊤ : (overSpec k R).left.Opens))
            = AlgHom.id k Γ((overSpec k R).left, ⊤) from Over.resAlgHom_rfl _ le_top,
          AlgHom.id_comp,
          show (Over.overSpecΓTopAlgEquiv k R).toAlgHom.comp
              (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom
            = AlgHom.id k R from
            AlgHom.ext fun a => (Over.overSpecΓTopAlgEquiv k R).apply_symm_apply a]
    _ = x := DivFam.mapAlgHom_id x

/-- **The affine comparison equivalence**: on an affine test `overSpec k R`, the
affine-opens limit `divFam` collapses by evaluation at the terminal element `⊤` of the
affine-opens poset to the divisor-functor value `DivFam C R π n` of the test algebra
(`informal/spec-dd-1.md` §1e; the `picEtAffineEquiv` template). -/
def divFamAffineEquiv : divFam C π n (overSpec k R) ≃ DivFam C R π n where
  toFun := divFamToAff C π n R
  invFun := divFamOfAff C π n R
  left_inv := divFamOfAff_divFamToAff C π n R
  right_inv := divFamToAff_divFamOfAff C π n R

/-- The affine comparison evaluates at the top affine open and transports along
`Over.overSpecΓTopAlgEquiv`. -/
@[simp]
lemma divFamAffineEquiv_apply (s : divFam C π n (overSpec k R)) :
    divFamAffineEquiv C π n R s
      = DivFam.mapAlgHom (Over.overSpecΓTopAlgEquiv k R).toAlgHom
          (s.1 (overSpecTopAffine R)) :=
  rfl

/-- The inverse affine comparison restricts the transported class from the top affine
open. -/
@[simp]
lemma divFamAffineEquiv_symm_apply_val (x : DivFam C R π n)
    (U : (overSpec k R).left.affineOpens) :
    ((divFamAffineEquiv C π n R).symm x).1 U
      = DivFam.mapAlgHom
          ((Over.resAlgHom (overSpec k R) le_top).comp
            (Over.overSpecΓTopAlgEquiv k R).symm.toAlgHom) x :=
  rfl

end Affine

/-! ## Restriction along an open immersion of test objects

The no-gluing slice of the vehicle's functoriality in `T` (`informal/spec-dd-2.md` §3):
along a test morphism whose underlying morphism is an open immersion, the image of an
affine open is an affine open, so the restricted family is defined affine-open-wise —
no value has to be glued.  The general-test restriction (arbitrary `f`, glued values
over basic-open refinements, the `picEtMap` pattern) is stage S6's business. -/

namespace divFam

variable {T T' : Over (Spec (.of k))}

/-- The image of an affine open under an open immersion of test objects, as an affine
open of the target. -/
def imageAffineOpens (f : T' ⟶ T) [IsOpenImmersion f.left] (U : T'.left.affineOpens) :
    T.left.affineOpens :=
  ⟨f.left ''ᵁ U.1, U.2.image_of_isOpenImmersion f.left⟩

/-- The underlying open of the image affine open is the image open. -/
@[simp]
lemma imageAffineOpens_coe (f : T' ⟶ T) [IsOpenImmersion f.left]
    (U : T'.left.affineOpens) :
    (imageAffineOpens f U).1 = f.left ''ᵁ U.1 :=
  rfl

/-- **Restriction of vehicle sections along an open immersion of test objects**: the
value at an affine open `U` is the pullback of the value at the image affine open
`f ''ᵁ U` along the section pullback `Over.appLEAlgHom` (an isomorphism onto `U`).
Compatibility composes the pullback with the restriction on either side
(`Over.resAlgHom_comp_appLEAlgHom`/`Over.appLEAlgHom_comp_resAlgHom` through
`DivFam.mapAlgHom_comp`). -/
def map (f : T' ⟶ T) [IsOpenImmersion f.left] : divFam C π n T → divFam C π n T' :=
  fun s =>
    ⟨fun U => DivFam.mapAlgHom
      (Over.appLEAlgHom f (f.left ''ᵁ U.1) U.1 (f.left.preimage_image_eq U.1).ge)
      (s.1 (imageAffineOpens f U)),
      fun U V h => by
        beta_reduce
        rw [← DivFam.mapAlgHom_comp,
          Over.resAlgHom_comp_appLEAlgHom f (f.left ''ᵁ V.1)
            (f.left.preimage_image_eq V.1).ge h,
          ← s.compat (imageAffineOpens f U) (imageAffineOpens f V)
            (f.left.image_mono h),
          ← DivFam.mapAlgHom_comp,
          Over.appLEAlgHom_comp_resAlgHom f U.1 (f.left.image_mono h)
            (f.left.preimage_image_eq U.1).ge
            (h.trans (f.left.preimage_image_eq V.1).ge)]⟩

/-- The value of the restricted section at an affine open: pullback of the value at the
image affine open. -/
lemma map_val (f : T' ⟶ T) [IsOpenImmersion f.left] (s : divFam C π n T)
    (U : T'.left.affineOpens) :
    (map C π n f s).1 U
      = DivFam.mapAlgHom
          (Over.appLEAlgHom f (f.left ''ᵁ U.1) U.1 (f.left.preimage_image_eq U.1).ge)
          (s.1 (imageAffineOpens f U)) :=
  rfl

end divFam

end

end AlgebraicGeometry
