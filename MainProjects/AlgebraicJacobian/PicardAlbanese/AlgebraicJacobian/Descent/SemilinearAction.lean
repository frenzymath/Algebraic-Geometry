/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.Galois.Basic

/-!
# Semilinear actions on schemes

This is the scheme-level action vocabulary used by finite-Galois descent.  It
matches the API of the quotient engine in the sibling Algebraic Jacobian
project so that engine can be ported without a parallel set of conventions.

The inversion in `toSpecAut` is forced by contravariance of `Spec` and by the
group law on categorical automorphisms.  `SemilinearGalAction` then records an
action on a scheme whose structural morphism covers this action on the base.

## Main declarations

* `AlgebraicJacobian.GaloisDescent.toSpecAut`: the action induced on a spectrum.
* `AlgebraicJacobian.GaloisDescent.SemilinearGalAction`: a semilinear action on
  a scheme over a field extension.
* `SemilinearGalAction.OrbitsInAffineOpen`: the exact geometric condition used
  by the scheme quotient construction.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicJacobian.GaloisDescent

section SpecAut

variable (G : Type*) [Group G] (A : Type u) [CommRing A]
  [MulSemiringAction G A]

lemma toRingHom_comp (gamma tau : G) :
    (MulSemiringAction.toRingHom G A gamma).comp
        (MulSemiringAction.toRingHom G A tau) =
      MulSemiringAction.toRingHom G A (gamma * tau) :=
  RingHom.ext fun x => (mul_smul gamma tau x).symm

lemma toRingHom_one :
    MulSemiringAction.toRingHom G A (1 : G) = RingHom.id A :=
  RingHom.ext fun x => one_smul G x

/-- A group acting on a commutative ring acts on its spectrum.  The inverse in
the ring action makes this a group homomorphism after contravariance of `Spec`.
-/
noncomputable def toSpecAut : G →* Aut (Spec (CommRingCat.of A)) :=
  MonoidHom.mk'
    (fun gamma =>
      { hom := Spec.map
          (CommRingCat.ofHom (MulSemiringAction.toRingHom G A gamma⁻¹))
        inv := Spec.map
          (CommRingCat.ofHom (MulSemiringAction.toRingHom G A gamma))
        hom_inv_id := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toRingHom_comp,
            inv_mul_cancel, toRingHom_one, CommRingCat.ofHom_id, Spec.map_id]
        inv_hom_id := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toRingHom_comp,
            mul_inv_cancel, toRingHom_one, CommRingCat.ofHom_id, Spec.map_id] })
    (fun gamma tau => by
      refine Iso.ext ?_
      change Spec.map
          (CommRingCat.ofHom
            (MulSemiringAction.toRingHom G A (gamma * tau)⁻¹)) =
        Spec.map
            (CommRingCat.ofHom
              (MulSemiringAction.toRingHom G A tau⁻¹)) ≫
          Spec.map
            (CommRingCat.ofHom
              (MulSemiringAction.toRingHom G A gamma⁻¹))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toRingHom_comp,
        ← mul_inv_rev])

lemma toSpecAut_hom (gamma : G) :
    (toSpecAut G A gamma).hom =
      Spec.map
        (CommRingCat.ofHom (MulSemiringAction.toRingHom G A gamma⁻¹)) :=
  rfl

lemma toSpecAut_mul_hom (gamma tau : G) :
    (toSpecAut G A (gamma * tau)).hom =
      (toSpecAut G A tau).hom ≫ (toSpecAut G A gamma).hom := by
  rw [map_mul]
  rfl

lemma toSpecAut_inv_hom (gamma : G) :
    (toSpecAut G A gamma⁻¹).hom = (toSpecAut G A gamma).inv := by
  rw [map_inv]
  rfl

@[reassoc (attr := simp)]
lemma toSpecAut_hom_inv_hom (gamma : G) :
    (toSpecAut G A gamma).hom ≫ (toSpecAut G A gamma⁻¹).hom = 𝟙 _ := by
  rw [toSpecAut_inv_hom, Iso.hom_inv_id]

@[reassoc (attr := simp)]
lemma toSpecAut_inv_hom_hom (gamma : G) :
    (toSpecAut G A gamma⁻¹).hom ≫ (toSpecAut G A gamma).hom = 𝟙 _ := by
  rw [toSpecAut_inv_hom, Iso.inv_hom_id]

end SpecAut

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- A semilinear action of the `K`-algebra automorphisms of `L` on an
`L`-scheme.  Each automorphism of the total space covers the corresponding
automorphism of `Spec L`. -/
structure SemilinearGalAction (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of L)) where
  act : (L ≃ₐ[K] L) →* Aut X
  compat (gamma : L ≃ₐ[K] L) :
    (act gamma).hom ≫ f =
      f ≫ (toSpecAut (L ≃ₐ[K] L) L gamma).hom

namespace SemilinearGalAction

variable {K L} {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}

/-- Equivariance of a morphism between semilinearly acted schemes. -/
def IsEquivariant {X' : Scheme.{u}}
    {f' : X' ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    (rho' : SemilinearGalAction K L X' f') (h : X ⟶ X') : Prop :=
  ∀ gamma : L ≃ₐ[K] L,
    (rho.act gamma).hom ≫ h = h ≫ (rho'.act gamma).hom

/-- The orbit of a point under a semilinear action. -/
def orbit (rho : SemilinearGalAction K L X f) (x : X) : Set X :=
  Set.range fun gamma : L ≃ₐ[K] L => (rho.act gamma).hom.base x

/-- The geometric condition required for the finite-Galois quotient to remain
a scheme: every orbit lies in one affine open. -/
class OrbitsInAffineOpen (rho : SemilinearGalAction K L X f) : Prop where
  exists_affineOpen (x : X) :
    ∃ U : X.affineOpens,
      ∀ gamma : L ≃ₐ[K] L, (rho.act gamma).hom.base x ∈ U.1

/-- A stable open subset of a semilinearly acted scheme. -/
def IsStableOpen (rho : SemilinearGalAction K L X f) (U : X.Opens) : Prop :=
  ∀ gamma : L ≃ₐ[K] L, (rho.act gamma).hom ⁻¹ᵁ U = U

end SemilinearGalAction

/-- A stable affine neighbourhood of every point.  The quotient engine derives
this from `OrbitsInAffineOpen` for finite Galois extensions. -/
class HasStableAffineCover {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f) : Prop where
  exists_stable_affineOpen (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ rho.IsStableOpen U

end AlgebraicJacobian.GaloisDescent
