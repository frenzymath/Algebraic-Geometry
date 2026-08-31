/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtSections
import AlgebraicJacobian.Picard.PicEtAffMap

/-!
# The étale-sheafified relative Picard functor on all test objects: the object level

For a curve `C` over `k`, the étale-sheafified relative Picard group of an **affine**
test is the one-step plus construction `PicEtAff C A` (étale-separatedness of the
relative Picard presheaf makes one plus suffice — axiom (C1),
`AlgebraicJacobian.Picard.CechKernelLemma`).  The frozen group-object interface forces
the functor to exist on **all** of `Over (Spec k)`; following the resolution of the
Layer-2 vehicle question (inbox I-0140), the extension is the *bespoke affine-opens
limit*: a section over a test object `T` is a compatible family of plus classes over the
affine opens of `T.left`, valued in `PicEtAff C Γ(T.left, U)` via the section-ring
algebras of `AlgebraicJacobian.Picard.PicEtSections`.  The index poset is `Type u`-small,
which is the point of the vehicle.

* `AlgebraicGeometry.picEt C T`: the limit, as the subgroup of the product over
  `T.left.affineOpens` cut out by compatibility under restriction, with its `CommGroup`
  structure; `picEt.eval` is evaluation at an affine open.
* `AlgebraicGeometry.PicEtAff.congr C e`: transport of plus classes along an isomorphism
  of test algebras.
* `AlgebraicGeometry.picEtAffineEquiv C A`: **the affine comparison** — on an affine
  test `overSpec k A`, evaluation at the top affine open is a group isomorphism
  `picEt C (overSpec k A) ≃* PicEtAff C A` (the affine-opens poset of an affine test has
  a terminal element, so the limit collapses).

Functoriality in `T` — restriction along an arbitrary morphism of test objects, by
gluing over basic-open refinements, licensed by (C1)-separatedness — is built on top of
the Zariski sheaf property of `PicEtAff` in `AlgebraicJacobian.Picard.PicEtMap`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

attribute [local instance] Over.sectionsAlgebra

noncomputable section

/-! ## Transport of plus classes along an isomorphism of test algebras -/

namespace PicEtAff

variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- Transport of étale-plus Picard classes along an isomorphism of test algebras. -/
def congr (e : A ≃ₐ[k] B) : PicEtAff C A ≃* PicEtAff C B where
  toFun := mapAlg C e.toAlgHom
  invFun := mapAlg C e.symm.toAlgHom
  left_inv x := by
    rw [← mapAlg_comp, show (e.symm.toAlgHom.comp e.toAlgHom) = AlgHom.id k A from
      AlgHom.ext fun a => e.symm_apply_apply a]
    exact mapAlg_id C x
  right_inv x := by
    rw [← mapAlg_comp, show (e.toAlgHom.comp e.symm.toAlgHom) = AlgHom.id k B from
      AlgHom.ext fun b => e.apply_symm_apply b]
    exact mapAlg_id C x
  map_mul' x y := map_mul (mapAlg C e.toAlgHom) x y

@[simp]
lemma congr_apply (e : A ≃ₐ[k] B) (x : PicEtAff C A) :
    congr C e x = mapAlg C e.toAlgHom x :=
  rfl

@[simp]
lemma congr_symm_apply (e : A ≃ₐ[k] B) (x : PicEtAff C B) :
    (congr C e).symm x = mapAlg C e.symm.toAlgHom x :=
  rfl

end PicEtAff

/-! ## The affine-opens limit -/

variable (T : Over (Spec (.of k)))

/-- The compatible families over the affine opens of the test object, as a subgroup of
the product of the affine-level plus groups: the value at a smaller affine open is the
restriction of the value at a larger one. -/
def picEtSubgroup :
    Subgroup (Π U : T.left.affineOpens, PicEtAff C Γ(T.left, U.1)) where
  carrier := {s | ∀ (U V : T.left.affineOpens) (h : U.1 ≤ V.1),
    PicEtAff.mapAlg C (Over.resAlgHom T h) (s V) = s U}
  one_mem' := fun U V h => by rw [Pi.one_apply, Pi.one_apply, map_one]
  mul_mem' {a b} ha hb := fun U V h => by
    rw [Pi.mul_apply, Pi.mul_apply, map_mul, ha U V h, hb U V h]
  inv_mem' {a} ha := fun U V h => by rw [Pi.inv_apply, Pi.inv_apply, map_inv, ha U V h]

/-- **The étale-sheafified relative Picard functor at an arbitrary test object**, object
level: compatible families of affine-level plus classes over the affine opens of
`T.left` — the bespoke affine-opens limit of `PicEtAff C ∘ Γ(T.left, ·)`.  On affine
tests this is `PicEtAff` itself (`picEtAffineEquiv`); on general tests it is its
canonical Zariski-continuous extension. -/
def picEt : Type u :=
  picEtSubgroup C T

noncomputable instance : CommGroup (picEt C T) :=
  inferInstanceAs (CommGroup (picEtSubgroup C T))

namespace picEt

variable {C T}

/-- The compatibility of a section of `picEt` along an inclusion of affine opens. -/
lemma compat (s : picEt C T) (U V : T.left.affineOpens) (h : U.1 ≤ V.1) :
    PicEtAff.mapAlg C (Over.resAlgHom T h) (s.1 V) = s.1 U :=
  s.2 U V h

@[ext]
lemma ext {s t : picEt C T} (h : ∀ U : T.left.affineOpens, s.1 U = t.1 U) : s = t :=
  Subtype.ext (funext h)

variable (C T) in
/-- Evaluation of a section of `picEt` at an affine open, as a group homomorphism. -/
def eval (U : T.left.affineOpens) : picEt C T →* PicEtAff C Γ(T.left, U.1) :=
  (Pi.evalMonoidHom (fun V : T.left.affineOpens => PicEtAff C Γ(T.left, V.1)) U).comp
    (picEtSubgroup C T).subtype

@[simp]
lemma eval_apply (U : T.left.affineOpens) (s : picEt C T) : eval C T U s = s.1 U :=
  rfl

@[simp]
lemma mul_val (s t : picEt C T) (U : T.left.affineOpens) :
    (s * t).1 U = s.1 U * t.1 U :=
  rfl

@[simp]
lemma one_val (U : T.left.affineOpens) : (1 : picEt C T).1 U = 1 :=
  rfl

@[simp]
lemma inv_val (s : picEt C T) (U : T.left.affineOpens) : (s⁻¹).1 U = (s.1 U)⁻¹ :=
  rfl

end picEt

/-! ## The affine comparison -/

section Affine

variable (A : Type u) [CommRing A] [Algebra k A]

/-- The top affine open of an affine test object. -/
def overSpecTopAffine : (overSpec k A).left.affineOpens :=
  ⟨⊤, isAffineOpen_top_overSpec k A⟩

/-- Evaluation at the top affine open of an affine test, composed with the
`ΓSpecIso`-transport into the test algebra: the forward direction of the affine
comparison. -/
def picEtToAff : picEt C (overSpec k A) →* PicEtAff C A :=
  (PicEtAff.congr C (Over.overSpecΓTopAlgEquiv k A)).toMonoidHom.comp
    (picEt.eval C (overSpec k A) (overSpecTopAffine A))

lemma picEtToAff_apply (s : picEt C (overSpec k A)) :
    picEtToAff C A s
      = PicEtAff.mapAlg C (Over.overSpecΓTopAlgEquiv k A).toAlgHom
          (s.1 (overSpecTopAffine A)) :=
  rfl

/-- The section of `picEt` over an affine test determined by a plus class of the test
algebra: restrict from the top affine open — the inverse direction of the affine
comparison. -/
def picEtOfAff : PicEtAff C A →* picEt C (overSpec k A) where
  toFun x :=
    ⟨fun U => PicEtAff.mapAlg C
      ((Over.resAlgHom (overSpec k A) le_top).comp
        (Over.overSpecΓTopAlgEquiv k A).symm.toAlgHom) x,
      fun U V h => by rw [← PicEtAff.mapAlg_comp, ← AlgHom.comp_assoc,
        Over.resAlgHom_comp]⟩
  map_one' := picEt.ext fun U => map_one (PicEtAff.mapAlg C _)
  map_mul' x y := picEt.ext fun U => map_mul (PicEtAff.mapAlg C _) x y

lemma picEtOfAff_val (x : PicEtAff C A) (U : (overSpec k A).left.affineOpens) :
    (picEtOfAff C A x).1 U
      = PicEtAff.mapAlg C
          ((Over.resAlgHom (overSpec k A) le_top).comp
            (Over.overSpecΓTopAlgEquiv k A).symm.toAlgHom) x :=
  rfl

private lemma picEtOfAff_comp_picEtToAff :
    (picEtOfAff C A).comp (picEtToAff C A) = MonoidHom.id (picEt C (overSpec k A)) := by
  refine MonoidHom.ext fun s => picEt.ext fun U => ?_
  calc ((picEtOfAff C A) (picEtToAff C A s)).1 U
      = PicEtAff.mapAlg C
          (((Over.resAlgHom (overSpec k A) le_top).comp
              (Over.overSpecΓTopAlgEquiv k A).symm.toAlgHom).comp
            (Over.overSpecΓTopAlgEquiv k A).toAlgHom)
          (s.1 (overSpecTopAffine A)) :=
        (PicEtAff.mapAlg_comp C _ _ _).symm
    _ = PicEtAff.mapAlg C (Over.resAlgHom (overSpec k A) le_top)
          (s.1 (overSpecTopAffine A)) := by
        rw [AlgHom.comp_assoc,
          show (Over.overSpecΓTopAlgEquiv k A).symm.toAlgHom.comp
              (Over.overSpecΓTopAlgEquiv k A).toAlgHom
            = AlgHom.id k Γ((overSpec k A).left, ⊤) from
            AlgHom.ext fun a => (Over.overSpecΓTopAlgEquiv k A).symm_apply_apply a,
          AlgHom.comp_id]
    _ = s.1 U := s.compat U (overSpecTopAffine A) le_top

private lemma picEtToAff_comp_picEtOfAff :
    (picEtToAff C A).comp (picEtOfAff C A) = MonoidHom.id (PicEtAff C A) := by
  refine MonoidHom.ext fun x => ?_
  calc (picEtToAff C A) (picEtOfAff C A x)
      = PicEtAff.mapAlg C
          ((Over.overSpecΓTopAlgEquiv k A).toAlgHom.comp
            ((Over.resAlgHom (overSpec k A) le_top).comp
              (Over.overSpecΓTopAlgEquiv k A).symm.toAlgHom)) x :=
        (PicEtAff.mapAlg_comp C _ _ _).symm
    _ = PicEtAff.mapAlg C (AlgHom.id k A) x := by
        rw [show Over.resAlgHom (overSpec k A) (le_top :
              (⊤ : (overSpec k A).left.Opens) ≤ (⊤ : (overSpec k A).left.Opens))
            = AlgHom.id k Γ((overSpec k A).left, ⊤) from Over.resAlgHom_rfl _ le_top,
          AlgHom.id_comp,
          show (Over.overSpecΓTopAlgEquiv k A).toAlgHom.comp
              (Over.overSpecΓTopAlgEquiv k A).symm.toAlgHom
            = AlgHom.id k A from
            AlgHom.ext fun a => (Over.overSpecΓTopAlgEquiv k A).apply_symm_apply a]
    _ = x := PicEtAff.mapAlg_id C x

/-- **The affine comparison isomorphism**: on an affine test `overSpec k A`, the
affine-opens limit `picEt` collapses by evaluation at the terminal element `⊤` of the
affine-opens poset to the one-step plus `PicEtAff C A` of the test algebra. -/
def picEtAffineEquiv : picEt C (overSpec k A) ≃* PicEtAff C A :=
  MonoidHom.toMulEquiv (picEtToAff C A) (picEtOfAff C A)
    (picEtOfAff_comp_picEtToAff C A) (picEtToAff_comp_picEtOfAff C A)

@[simp]
lemma picEtAffineEquiv_apply (s : picEt C (overSpec k A)) :
    picEtAffineEquiv C A s
      = PicEtAff.mapAlg C (Over.overSpecΓTopAlgEquiv k A).toAlgHom
          (s.1 (overSpecTopAffine A)) :=
  rfl

@[simp]
lemma picEtAffineEquiv_symm_apply_val (x : PicEtAff C A)
    (U : (overSpec k A).left.affineOpens) :
    ((picEtAffineEquiv C A).symm x).1 U
      = PicEtAff.mapAlg C
          ((Over.resAlgHom (overSpec k A) le_top).comp
            (Over.overSpecΓTopAlgEquiv k A).symm.toAlgHom) x :=
  rfl

end Affine

end

end AlgebraicGeometry
