/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEt
import Mathlib.RingTheory.Grassmannian

/-!
# The small Grassmannian functor on test objects (DD-3, stage 3b)

The D2 functor of the DD-3 port (`informal/spec-dd-3.md` §0/§2; worksheet
`informal/dat-d-worksheet.md` §2.2): the value at a `k`-algebra `R` is mathlib's
`Module.Grassmannian R (R ⊗[k] H) d` — the SET of submodules of `R ⊗[k] H` whose
quotient is finite projective of constant fibre rank `d`.  No setoid: the ℤ-model's
`RankQuotient.Rel` is dissolved by the submodule spelling, and the entire
right-exactness base-change campaign is mathlib's `Module.Grassmannian.map`.

At a general test object `T : Over (Spec k)` the value is the **affine-opens-limit
vehicle** (the `picEt` pattern): a compatible family of affine values over
`T.left.affineOpens`, with compatibility along `Module.Grassmannian.map` of the
section-ring restrictions.  Restriction along arbitrary test morphisms is deferred to
the DD-R seam; only the affine-opens compatibility lives here.

Statements mention the `Over.sectionsAlgebra` structures; consumers must activate the
same local instance (`attribute [local instance] Over.sectionsAlgebra`, the
SectionsBaseChange house rule).

* `AlgebraicGeometry.Grassmannian.grFunctorAff`: the affine functor value
  `G(d, R ⊗[k] H; R)`.
* `AlgebraicGeometry.Grassmannian.grFunctor`: the vehicle value at a test object, with
  `eval`, `ext`, and the compatibility lemma.
* `AlgebraicGeometry.Grassmannian.grFunctorAffineEquiv`: **the affine comparison** — on
  an affine test `overSpec k A`, evaluation at the top affine open is a bijection with
  the affine value `G(d, A ⊗[k] H; A)` (the affine-opens poset has a top element, so
  the limit collapses; the `picEtAffineEquiv` pattern).
-/

set_option autoImplicit false

universe u

open CategoryTheory TensorProduct

namespace AlgebraicGeometry.Grassmannian

attribute [local instance] Over.sectionsAlgebra

/-- The **affine Grassmannian functor value** (the D2 spelling, consumed from mathlib):
for a `k`-algebra `R`, the set of submodules `K ⊆ R ⊗[k] H` whose quotient is a finite
projective `R`-module of constant fibre rank `d`.  The map action along `R →ₐ[k] R'`
is `Module.Grassmannian.map`. -/
abbrev grFunctorAff (k : Type u) [Field k] (H : Type u) [AddCommGroup H] [Module k H]
    (d : ℕ) (R : Type u) [CommRing R] [Algebra k R] : Type u :=
  Module.Grassmannian R (TensorProduct k R H) d

/-- **The Grassmannian functor value at a test object** `T : Over (Spec k)`: the
affine-opens-limit vehicle — a compatible family of affine Grassmannian points over
the affine opens of `T.left`, compatible along `Module.Grassmannian.map` of the
section-ring restrictions.  `Type u`-small by construction. -/
def grFunctor (k : Type u) [Field k] (H : Type u) [AddCommGroup H] [Module k H]
    (d : ℕ) (T : Over (Spec (CommRingCat.of k))) : Type u :=
  {s : ∀ U : T.left.affineOpens, grFunctorAff k H d Γ(T.left, U.1) //
    ∀ (U V : T.left.affineOpens) (h : U.1 ≤ V.1),
      Module.Grassmannian.map (Over.resAlgHom T h) (s V) = s U}

namespace grFunctor

variable {k : Type u} [Field k] {H : Type u} [AddCommGroup H] [Module k H] {d : ℕ}
variable {T : Over (Spec (CommRingCat.of k))}

/-- The compatibility of a section of `grFunctor` along an inclusion of affine opens. -/
lemma compat (s : grFunctor k H d T) (U V : T.left.affineOpens) (h : U.1 ≤ V.1) :
    Module.Grassmannian.map (Over.resAlgHom T h) (s.1 V) = s.1 U :=
  s.2 U V h

@[ext]
lemma ext {s t : grFunctor k H d T} (h : ∀ U : T.left.affineOpens, s.1 U = t.1 U) :
    s = t :=
  Subtype.ext (funext h)

variable (k H d T) in
/-- Evaluation of a section of `grFunctor` at an affine open. -/
def eval (U : T.left.affineOpens) (s : grFunctor k H d T) :
    grFunctorAff k H d Γ(T.left, U.1) :=
  s.1 U

@[simp]
lemma eval_apply (U : T.left.affineOpens) (s : grFunctor k H d T) :
    eval k H d T U s = s.1 U :=
  rfl

end grFunctor

section Affine

variable {k : Type u} [Field k] {H : Type u} [AddCommGroup H] [Module k H] {d : ℕ}
variable (A : Type u) [CommRing A] [Algebra k A]

/-- `Module.Grassmannian.map` along the identity of a plain `k`-algebra is the
identity (the `CommAlgCat`-free form of mathlib's `Module.Grassmannian.map_id`). -/
lemma grFunctorAff_map_id (N : grFunctorAff k H d A) :
    Module.Grassmannian.map (AlgHom.id k A) N = N :=
  Module.Grassmannian.map_id d (CommAlgCat.of k A) N

variable (k H d)

/-- Forward direction of the affine comparison: evaluate at the top affine open and
transport along the `ΓSpecIso`-identification `Γ(Spec A, ⊤) ≃ₐ[k] A`. -/
noncomputable def grFunctorToAff (s : grFunctor k H d (overSpec k A)) :
    grFunctorAff k H d A :=
  Module.Grassmannian.map (Over.overSpecΓTopAlgEquiv k A).toAlgHom
    (s.1 (overSpecTopAffine A))

/-- Inverse direction of the affine comparison: spread an affine Grassmannian point
over all affine opens by restriction from the top. -/
noncomputable def grFunctorOfAff (N : grFunctorAff k H d A) :
    grFunctor k H d (overSpec k A) where
  val U := Module.Grassmannian.map
    ((Over.resAlgHom (overSpec k A) le_top).comp
      (Over.overSpecΓTopAlgEquiv k A).symm.toAlgHom) N
  property U V h := by
    rw [← Module.Grassmannian.map_comp, ← AlgHom.comp_assoc, Over.resAlgHom_comp]

/-- **The affine comparison**: on an affine test `overSpec k A`, the vehicle value of
the Grassmannian functor is the affine value `G(d, A ⊗[k] H; A)` — the affine-opens
poset has a top element, so the limit collapses (the `picEtAffineEquiv` pattern). -/
noncomputable def grFunctorAffineEquiv :
    grFunctor k H d (overSpec k A) ≃ grFunctorAff k H d A where
  toFun := grFunctorToAff k H d A
  invFun := grFunctorOfAff k H d A
  left_inv s := by
    refine grFunctor.ext fun U => ?_
    change Module.Grassmannian.map
        ((Over.resAlgHom (overSpec k A) le_top).comp
          (Over.overSpecΓTopAlgEquiv k A).symm.toAlgHom)
        (Module.Grassmannian.map (Over.overSpecΓTopAlgEquiv k A).toAlgHom
          (s.1 (overSpecTopAffine A)))
      = s.1 U
    rw [← Module.Grassmannian.map_comp, AlgHom.comp_assoc,
      show (Over.overSpecΓTopAlgEquiv k A).symm.toAlgHom.comp
          (Over.overSpecΓTopAlgEquiv k A).toAlgHom
        = AlgHom.id k Γ((overSpec k A).left, ⊤) from
        AlgHom.ext fun x => (Over.overSpecΓTopAlgEquiv k A).symm_apply_apply x,
      AlgHom.comp_id]
    exact s.compat U (overSpecTopAffine A) le_top
  right_inv N := by
    change Module.Grassmannian.map (Over.overSpecΓTopAlgEquiv k A).toAlgHom
        (Module.Grassmannian.map
          ((Over.resAlgHom (overSpec k A) le_top).comp
            (Over.overSpecΓTopAlgEquiv k A).symm.toAlgHom) N)
      = N
    rw [← Module.Grassmannian.map_comp, ← AlgHom.comp_assoc, Over.resAlgHom_rfl,
      AlgHom.comp_id,
      show (Over.overSpecΓTopAlgEquiv k A).toAlgHom.comp
          (Over.overSpecΓTopAlgEquiv k A).symm.toAlgHom
        = AlgHom.id k A from
        AlgHom.ext fun x => (Over.overSpecΓTopAlgEquiv k A).apply_symm_apply x]
    exact grFunctorAff_map_id A N

end Affine

end AlgebraicGeometry.Grassmannian
