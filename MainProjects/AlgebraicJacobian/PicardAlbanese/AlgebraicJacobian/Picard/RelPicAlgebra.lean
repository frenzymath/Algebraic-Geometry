/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RelPic
import AlgebraicJacobian.Cohomology.SectionsBaseChange

/-!
# The relative Picard functor on affine test algebras

The étale sheafification of the relative Picard functor is computed over *affine* test
objects, where a test object is `Spec` of a `k`-algebra `A` (the landed
`AlgebraicGeometry.overSpec k A : Over (Spec k)`) and a test map is `Spec` of a `k`-algebra
map.  This file provides the algebra-indexed face of the relative Picard functor:

* `AlgebraicGeometry.Over.overSpecMap f`: `Spec` of a `k`-algebra map `f : A →ₐ[k] B`, as a
  morphism `overSpec k B ⟶ overSpec k A` of `Over (Spec k)`, strictly functorial
  (`overSpecMap_id`, `overSpecMap_comp`).
* `AlgebraicGeometry.relPicAlgMap C f`: restriction of relative Picard classes along
  `Spec f`, a group homomorphism `relPic C (overSpec k A) →* relPic C (overSpec k B)`,
  covariantly functorial in the algebra (`relPicAlgMap_id`, `relPicAlgMap_comp`).

The étale plus construction (`Picard/PicEtAff.lean`) consumes only this interface: descent
classes on an étale cover are an equalizer of two `relPicAlgMap`s, and all refinement
transports are `relPicAlgMap`s of `A`-algebra maps restricted to `k`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

section OverSpecMap

variable {k : Type u} [CommRing k]
variable {A B C' D : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C'] [Algebra k C'] [CommRing D] [Algebra k D]

/-- `Spec` of a `k`-algebra map, as a morphism of `Over (Spec k)`. -/
noncomputable def Over.overSpecMap (f : A →ₐ[k] B) : overSpec k B ⟶ overSpec k A :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    dsimp
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

@[simp]
lemma Over.overSpecMap_left (f : A →ₐ[k] B) :
    (Over.overSpecMap f).left = Spec.map (CommRingCat.ofHom f.toRingHom) :=
  rfl

private lemma spec_map_id_alg :
    Spec.map (CommRingCat.ofHom (AlgHom.id k A).toRingHom) = 𝟙 (Spec (CommRingCat.of A)) := by
  rw [show CommRingCat.ofHom (AlgHom.id k A).toRingHom = 𝟙 (CommRingCat.of A) from rfl,
    Spec.map_id]

private lemma spec_map_comp_alg (f : A →ₐ[k] B) (g : B →ₐ[k] C') :
    Spec.map (CommRingCat.ofHom (g.comp f).toRingHom)
      = (Spec.map (CommRingCat.ofHom g.toRingHom) :
            Spec (CommRingCat.of C') ⟶ Spec (CommRingCat.of B))
          ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

@[simp]
lemma Over.overSpecMap_id : Over.overSpecMap (AlgHom.id k A) = 𝟙 (overSpec k A) := by
  ext : 1
  exact spec_map_id_alg

@[simp]
lemma Over.overSpecMap_comp (f : A →ₐ[k] B) (g : B →ₐ[k] C') :
    Over.overSpecMap (g.comp f) = Over.overSpecMap g ≫ Over.overSpecMap f := by
  ext : 1
  exact spec_map_comp_alg f g

end OverSpecMap

section RelPicAlgMap

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable {A B C' : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C'] [Algebra k C']

/-- Restriction of relative Picard classes along `Spec` of a `k`-algebra map: the
algebra-indexed face of the relative Picard functor, covariant in the algebra. -/
noncomputable def relPicAlgMap (f : A →ₐ[k] B) :
    relPic C (overSpec k A) →* relPic C (overSpec k B) :=
  relPicMap C (Over.overSpecMap f)

@[simp]
lemma relPicAlgMap_id (x : relPic C (overSpec k A)) :
    relPicAlgMap C (AlgHom.id k A) x = x := by
  rw [relPicAlgMap, Over.overSpecMap_id]
  exact relPicMap_id C x

lemma relPicAlgMap_comp (f : A →ₐ[k] B) (g : B →ₐ[k] C') (x : relPic C (overSpec k A)) :
    relPicAlgMap C (g.comp f) x = relPicAlgMap C g (relPicAlgMap C f x) := by
  rw [relPicAlgMap, Over.overSpecMap_comp]
  exact relPicMap_comp C (Over.overSpecMap f) (Over.overSpecMap g) x

end RelPicAlgMap

end AlgebraicGeometry
