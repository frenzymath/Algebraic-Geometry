/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.ModuleDescent

/-!
# Faithfully flat descent of commutative algebras

This file upgrades the existing effectivity theorem for module descent to
commutative algebras.  It is the affine-local algebraic input for effective
descent of schemes.

## Main declarations

* `Algebra.DescentDatum`: a module descent datum whose coaction preserves one
  and multiplication.
* `Algebra.DescentDatum.descended`: the equalizer subalgebra.
* `Algebra.DescentDatum.comparison_bijective`: effectivity of flat descent for
  commutative algebras.
* `Algebra.DescentDatum.descentEquiv`: the resulting algebra equivalence
  `B ⊗[A] R₀ ≃ₐ[B] R`.
* `Algebra.DescentDatum.Hom.descendedMap`: functoriality of the equalizer
  construction for morphisms compatible with the descent coactions.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace Algebra

variable (A B R : Type u) [CommRing A] [CommRing B] [CommRing R]
  [Algebra A B] [Algebra A R] [Algebra B R] [IsScalarTower A B R]

/-- A commutative-algebra descent datum over `A -> B`: a module descent datum
whose coaction preserves one and multiplication. -/
structure DescentDatum extends Module.DescentDatum A B R where
  coaction_one : coaction 1 = 1
  coaction_mul (x y : R) : coaction (x * y) = coaction x * coaction y

namespace DescentDatum

variable {A B R}

/-- The algebra homomorphism underlying an algebra descent coaction. -/
noncomputable def coactionAlgHom (D : DescentDatum A B R) :
    R →ₐ[B] B ⊗[A] R :=
  AlgHom.ofLinearMap D.coaction D.coaction_one D.coaction_mul

/-- The descended `A`-algebra, defined as the equalizer of the coaction and
the canonical map `r |-> 1 tensor r`. -/
noncomputable def descended (D : DescentDatum A B R) : Subalgebra A R :=
  AlgHom.equalizer (D.coactionAlgHom.restrictScalars A)
    Algebra.TensorProduct.includeRight

/-- Membership in the descended algebra is the same equalizer condition as
membership in the descended underlying module. -/
theorem mem_descended (D : DescentDatum A B R) {x : R} :
    x ∈ D.descended ↔ x ∈ D.toDescentDatum.descended := by
  rw [descended, AlgHom.mem_equalizer, Module.DescentDatum.mem_descended,
    Algebra.TensorProduct.includeRight_apply]
  rfl

/-- The underlying module of the descended algebra is exactly the module
descended by `Module.DescentDatum`. -/
theorem descended_toSubmodule (D : DescentDatum A B R) :
    D.descended.toSubmodule = D.toDescentDatum.descended := by
  ext x
  exact D.mem_descended

/-- The tautological linear equivalence between the two equalizer carriers. -/
noncomputable def descendedLinearEquiv (D : DescentDatum A B R) :
    D.descended ≃ₗ[A] D.toDescentDatum.descended :=
  LinearEquiv.ofEq _ _ D.descended_toSubmodule

/-- The comparison map from the base change of the descended algebra to the
original algebra. -/
noncomputable def comparison (D : DescentDatum A B R) :
    B ⊗[A] D.descended →ₐ[B] R :=
  Algebra.TensorProduct.lift (Algebra.ofId B R) D.descended.val
    (fun _ _ => Commute.all _ _)

@[simp]
theorem comparison_tmul (D : DescentDatum A B R) (b : B) (x : D.descended) :
    D.comparison (b ⊗ₜ x) = b • (x : R) := by
  simp [comparison, Algebra.smul_def]

/-- The algebra comparison has the same underlying function as the module
comparison, after identifying the two equalizer carriers. -/
theorem comparison_eq_moduleComparison (D : DescentDatum A B R)
    (x : B ⊗[A] D.descended) :
    D.comparison x =
      D.toDescentDatum.comparison (D.descendedLinearEquiv.lTensor B x) := by
  induction x with
  | zero => simp
  | tmul b x =>
      rw [comparison_tmul, LinearEquiv.lTensor_tmul,
        Module.DescentDatum.comparison_tmul]
      rfl
  | add x y hx hy => simp [hx, hy]

/-- Effectivity of flat descent for commutative algebras: the comparison from
the base change of the equalizer algebra is bijective. -/
theorem comparison_bijective (D : DescentDatum A B R) [Module.Flat A B] :
    Function.Bijective D.comparison := by
  have hfun :
      (D.comparison : B ⊗[A] D.descended → R) =
        D.toDescentDatum.comparison ∘ D.descendedLinearEquiv.lTensor B := by
    funext x
    exact D.comparison_eq_moduleComparison x
  rw [hfun]
  exact D.toDescentDatum.comparison_bijective.comp
    (D.descendedLinearEquiv.lTensor B).bijective

/-- The canonical algebra equivalence supplied by effective flat descent. -/
noncomputable def descentEquiv (D : DescentDatum A B R) [Module.Flat A B] :
    B ⊗[A] D.descended ≃ₐ[B] R :=
  AlgEquiv.ofBijective D.comparison D.comparison_bijective

@[simp]
theorem descentEquiv_tmul (D : DescentDatum A B R) [Module.Flat A B]
    (b : B) (x : D.descended) :
    D.descentEquiv (b ⊗ₜ x) = b • (x : R) :=
  D.comparison_tmul b x

variable {S T : Type u} [CommRing S] [CommRing T]
  [Algebra A S] [Algebra B S] [IsScalarTower A B S]
  [Algebra A T] [Algebra B T] [IsScalarTower A B T]

/-- A morphism of commutative-algebra descent data: a `B`-algebra map that
intertwines the two coactions. -/
structure Hom (D₁ : DescentDatum A B R) (D₂ : DescentDatum A B S) where
  hom : R →ₐ[B] S
  coaction_comm (x : R) :
    D₂.coaction (hom x) =
      Algebra.TensorProduct.map (AlgHom.id A B) (hom.restrictScalars A)
        (D₁.coaction x)

namespace Hom

variable {D₁ : DescentDatum A B R} {D₂ : DescentDatum A B S}
  {D₃ : DescentDatum A B T}

@[ext]
theorem ext {f g : Hom D₁ D₂} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity morphism of an algebra descent datum. -/
def id (D : DescentDatum A B R) : Hom D D where
  hom := AlgHom.id B R
  coaction_comm x := by
    have h : (AlgHom.id B R).restrictScalars A = AlgHom.id A R := by
      ext
      rfl
    rw [h, Algebra.TensorProduct.map_id]
    rfl

/-- Composition of morphisms of algebra descent data. -/
def comp (f : Hom D₁ D₂) (g : Hom D₂ D₃) : Hom D₁ D₃ where
  hom := g.hom.comp f.hom
  coaction_comm x := by
    change D₃.coaction (g.hom (f.hom x)) =
      Algebra.TensorProduct.map (AlgHom.id A B)
        ((g.hom.comp f.hom).restrictScalars A) (D₁.coaction x)
    rw [g.coaction_comm, f.coaction_comm]
    have h :
        (g.hom.comp f.hom).restrictScalars A =
          (g.hom.restrictScalars A).comp (f.hom.restrictScalars A) := by
      ext
      rfl
    rw [h, Algebra.TensorProduct.map_id_comp]
    rfl

@[simp]
theorem id_hom (D : DescentDatum A B R) : (id D).hom = AlgHom.id B R := rfl

@[simp]
theorem comp_hom (f : Hom D₁ D₂) (g : Hom D₂ D₃) :
    (comp f g).hom = g.hom.comp f.hom := rfl

@[simp]
theorem id_comp (f : Hom D₁ D₂) : comp (id D₁) f = f := by
  ext
  rfl

@[simp]
theorem comp_id (f : Hom D₁ D₂) : comp f (id D₂) = f := by
  ext
  rfl

@[simp]
theorem comp_assoc {U : Type u} [CommRing U]
    [Algebra A U] [Algebra B U] [IsScalarTower A B U]
    {D₄ : DescentDatum A B U} (f : Hom D₁ D₂) (g : Hom D₂ D₃)
    (h : Hom D₃ D₄) :
    comp (comp f g) h = comp f (comp g h) := by
  ext
  rfl

/-- A morphism of descent data restricts to an `A`-algebra map between the
equalizer algebras. -/
noncomputable def descendedMap (f : Hom D₁ D₂) :
    D₁.descended →ₐ[A] D₂.descended :=
  ((f.hom.restrictScalars A).comp D₁.descended.val).codRestrict
    D₂.descended fun x => by
      change f.hom (x : R) ∈ D₂.descended
      rw [D₂.mem_descended, Module.DescentDatum.mem_descended,
        f.coaction_comm]
      rw [(Module.DescentDatum.mem_descended D₁.toDescentDatum).mp
        (D₁.mem_descended.mp x.2)]
      simp

@[simp]
theorem descendedMap_apply (f : Hom D₁ D₂) (x : D₁.descended) :
    (f.descendedMap x : S) = f.hom x := rfl

@[simp]
theorem descendedMap_id :
    (id D₁).descendedMap = AlgHom.id A D₁.descended := by
  ext
  rfl

@[simp]
theorem descendedMap_comp (f : Hom D₁ D₂) (g : Hom D₂ D₃) :
    (comp f g).descendedMap = g.descendedMap.comp f.descendedMap := by
  ext
  rfl

/-- Naturality of the algebra comparison map with respect to a morphism of
descent data. -/
theorem comparison_naturality (f : Hom D₁ D₂)
    (x : B ⊗[A] D₁.descended) :
    D₂.comparison
        (Algebra.TensorProduct.map (AlgHom.id A B) f.descendedMap x) =
      f.hom (D₁.comparison x) := by
  induction x with
  | zero => simp
  | tmul b x => simp [Algebra.smul_def]
  | add x y hx hy => simp [hx, hy]

/-- Naturality of effective descent after promoting the comparison maps to
algebra equivalences. -/
theorem descentEquiv_naturality (f : Hom D₁ D₂) [Module.Flat A B]
    (x : B ⊗[A] D₁.descended) :
    D₂.descentEquiv
        (Algebra.TensorProduct.map (AlgHom.id A B) f.descendedMap x) =
      f.hom (D₁.descentEquiv x) :=
  f.comparison_naturality x

end Hom

end DescentDatum

end Algebra
