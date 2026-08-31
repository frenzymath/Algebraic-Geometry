/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DegreeZero
import AlgebraicJacobian.Picard.PicEtMap

/-!
# The degree at field points and the degree-zero Picard functor (G-D6/G-D7, SB-7)

For the challenge curve `C` over `k`, an étale Picard class `λ : picEt C T` on an
arbitrary test object restricts along any field point `t : overSpec k K ⟶ T` to a class
of the affine étale Picard group of `Spec K`, which collapses through the affine
comparison `picEtAffineEquiv` to a plus class in `PicEtAff C K` — whose degree
`PicEtAff.degAff` (SB-6) is an honest integer.

* `AlgebraicGeometry.degAt λ t` — **the degree of an étale Picard class at a field
  point** (gap G-D6): the plus-class degree of the restriction of `λ` along `t`.
* `AlgebraicGeometry.degAt_picEtMap` / `degAt_picEtFunctor_map` — functoriality: the
  degree of a restricted class at a field point is the degree of the original class at
  the composed field point.  Pure `picEtMap_comp` rewriting, which is what makes the
  degree-zero subfunctor stability definitional.
* `AlgebraicGeometry.pic0Subgroup C T` — the subgroup of classes of degree zero at
  *every* field point of `T` (membership: `mem_pic0Subgroup_iff`).
* `AlgebraicGeometry.pic0Functor C : (Over (Spec k))ᵒᵖ ⥤ CommGrpCat` — **the
  degree-zero relative Picard functor `Pic⁰_{C/k}`** (gap G-D7): the subgroup
  subfunctor of `picEtFunctor C` cut out by the degree-zero condition, the binding
  carrier of the Wave-4 representability statement (`RepresentableBy`, design §2.7).
  The restriction maps are `pic0Map`, with underlying-class equation `pic0Map_coe`
  (the naturality square of the inclusion, element form) and the bundled inclusion
  natural transformation `pic0Inclusion : pic0Functor C ⟶ picEtFunctor C`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The degree at a field point -/

/-- **The degree of an étale Picard class at a field point** (gap G-D6): restrict along
`t : overSpec k K ⟶ T`, collapse by the affine comparison to a plus class of the test
algebra `K`, and take its degree (SB-6).  Well-defined in the representative of the
restricted class by the zigzag (WD) underlying `PicEtAff.degAff`. -/
def degAt {T : Over (Spec (.of k))} (lam : picEt C T) {K : Type u} [Field K]
    [Algebra k K] (t : overSpec k K ⟶ T) : ℤ :=
  PicEtAff.degAff K (picEtAffineEquiv C K (picEtMap C t lam))

section DegAt

variable {T T' : Over (Spec (.of k))} {K : Type u} [Field K] [Algebra k K]

/-- The trivial class has degree zero at every field point. -/
@[simp]
theorem degAt_one (t : overSpec k K ⟶ T) : degAt (1 : picEt C T) t = 0 := by
  change PicEtAff.degAff K (picEtAffineEquiv C K (picEtMap C t 1)) = 0
  rw [map_one, map_one, PicEtAff.degAff_one]

/-- The degree at a field point of a product of classes is the sum of the degrees. -/
theorem degAt_mul (lam mu : picEt C T) (t : overSpec k K ⟶ T) :
    degAt (lam * mu) t = degAt lam t + degAt mu t := by
  change PicEtAff.degAff K (picEtAffineEquiv C K (picEtMap C t (lam * mu)))
      = PicEtAff.degAff K (picEtAffineEquiv C K (picEtMap C t lam))
        + PicEtAff.degAff K (picEtAffineEquiv C K (picEtMap C t mu))
  rw [map_mul, map_mul, PicEtAff.degAff_mul]

/-- The degree at a field point of an inverse class is the negation of the degree. -/
theorem degAt_inv (lam : picEt C T) (t : overSpec k K ⟶ T) :
    degAt lam⁻¹ t = -degAt lam t := by
  change PicEtAff.degAff K (picEtAffineEquiv C K (picEtMap C t lam⁻¹)) = -degAt lam t
  rw [map_inv, map_inv, PicEtAff.degAff_inv]
  rfl

/-- **Functoriality of the degree at field points** (restriction form): the degree of a
restricted class at a field point is the degree of the original class at the composed
field point.  Pure `picEtMap_comp` rewriting — this is what makes the stability of the
degree-zero subfunctor definitional. -/
theorem degAt_picEtMap (f : T' ⟶ T) (lam : picEt C T) (t' : overSpec k K ⟶ T') :
    degAt (picEtMap C f lam) t' = degAt lam (t' ≫ f) := by
  change PicEtAff.degAff K (picEtAffineEquiv C K (picEtMap C t' (picEtMap C f lam)))
      = PicEtAff.degAff K (picEtAffineEquiv C K (picEtMap C (t' ≫ f) lam))
  rw [← picEtMap_comp]

/-- Functoriality of the degree at field points, functor form. -/
theorem degAt_picEtFunctor_map (f : T' ⟶ T) (lam : picEt C T)
    (t' : overSpec k K ⟶ T') :
    degAt ((picEtFunctor C).map f.op lam) t' = degAt lam (t' ≫ f) :=
  degAt_picEtMap f lam t'

end DegAt

/-! ## The degree-zero subfunctor -/

variable (C) in
/-- **The degree-zero subgroup** of the étale Picard group of a test object: the
classes of degree zero at every field point of the test.  The object part of the
degree-zero Picard functor `pic0Functor` (gap G-D7). -/
def pic0Subgroup (T : Over (Spec (.of k))) : Subgroup (picEt C T) where
  carrier := {lam | ∀ (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ T),
    degAt lam t = 0}
  one_mem' := by
    intro K _ _ t
    exact degAt_one t
  mul_mem' := by
    intro a b ha hb K _ _ t
    rw [degAt_mul, ha K t, hb K t, add_zero]
  inv_mem' := by
    intro a ha K _ _ t
    rw [degAt_inv, ha K t, neg_zero]

/-- Membership in the degree-zero subgroup: degree zero at every field point. -/
theorem mem_pic0Subgroup_iff {T : Over (Spec (.of k))} {lam : picEt C T} :
    lam ∈ pic0Subgroup C T
      ↔ ∀ (K : Type u) [Field K] [Algebra k K] (t : overSpec k K ⟶ T),
          degAt lam t = 0 :=
  Iff.rfl

variable (C) in
/-- Restriction of degree-zero classes along a morphism of test objects: the map part
of the degree-zero Picard functor.  The stability of the degree-zero condition is
definitional through the functoriality `degAt_picEtMap` of the degree at field
points. -/
def pic0Map {T T' : Over (Spec (.of k))} (f : T' ⟶ T) :
    pic0Subgroup C T →* pic0Subgroup C T' :=
  ((picEtMap C f).comp (pic0Subgroup C T).subtype).codRestrict (pic0Subgroup C T')
    fun lam K _ _ t' => (degAt_picEtMap f (lam : picEt C T) t').trans (lam.2 K (t' ≫ f))

/-- The underlying étale Picard class of a restricted degree-zero class — the
naturality square of the subfunctor inclusion, element form. -/
@[simp]
theorem pic0Map_coe {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (lam : pic0Subgroup C T) :
    (pic0Map C f lam : picEt C T') = picEtMap C f (lam : picEt C T) :=
  rfl

variable (C) in
/-- **The degree-zero relative Picard functor `Pic⁰_{C/k}`** (gap G-D7): the subgroup
subfunctor of the étale-sheafified relative Picard functor `picEtFunctor C` of classes
of degree zero at every field point of the test object.  This is the binding carrier of
the Wave-4 representability statement (design §2.7): the Jacobian represents *this*
functor. -/
def pic0Functor : (Over (Spec (.of k)))ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (pic0Subgroup C T.unop)
  map g := CommGrpCat.ofHom (pic0Map C g.unop)
  map_id T := by
    ext lam U
    exact congrArg (fun z : picEt C T.unop => z.1 U) (picEtMap_id C (lam : picEt C T.unop))
  map_comp g h := by
    ext lam U
    exact congrArg (fun z => z.1 U) (picEtMap_comp C g.unop h.unop (lam : picEt C _))

@[simp]
theorem pic0Functor_obj (T : (Over (Spec (.of k)))ᵒᵖ) :
    (pic0Functor C).obj T = CommGrpCat.of (pic0Subgroup C T.unop) :=
  rfl

@[simp]
theorem pic0Functor_map {T T' : (Over (Spec (.of k)))ᵒᵖ} (g : T ⟶ T')
    (lam : pic0Subgroup C T.unop) :
    (pic0Functor C).map g lam = pic0Map C g.unop lam :=
  rfl

variable (C) in
/-- The inclusion of the degree-zero subfunctor into the étale-sheafified relative
Picard functor, as a natural transformation — the naturality square consumers cite
(bundled form of `pic0Map_coe`). -/
def pic0Inclusion : pic0Functor C ⟶ picEtFunctor C where
  app T := CommGrpCat.ofHom (pic0Subgroup C T.unop).subtype
  naturality _ _ _ := rfl

end

end AlgebraicGeometry
