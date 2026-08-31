/-
Copyright (c) 2026 The StacksPart06Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart06Lib Contributors
-/

import StacksPart06Lib.TangentSpace

/-!
# Tangent modules for test functors

This file packages the extra algebraic structure which is needed when a
set-valued test functor has a module-valued tangent space.  Product
preservation is recorded separately from the module structure: the latter is
an explicit hypothesis, so no representability or additivity is hidden in the
API.  The records below are deliberately lightweight scaffolding: they do not
yet encode the morphism action or the coherence data of the categorical
functor in the Stacks statement.
-/

namespace StacksPart06Lib

universe u v

/-- Object-level evaluation data for a test functor.

The record stores a chosen terminal point and objectwise product
comparisons.  It intentionally omits the action on morphisms and all
naturality/coherence laws, so it should not be read as a complete categorical
functor. -/
structure ProductPreservingTestFunctor where
  F : Type u → Type v
  zero : F PUnit
  productEquiv : ∀ (A B : Type u), F (A × B) ≃ F A × F B

/-- Explicit algebraic data making the tangent evaluation of a test functor an
    `R`-module.  This is deliberately bundled as input: product preservation
    alone does not canonically choose addition on a set-valued functor. -/
class TangentModuleData (R : Type u)
    [CommRing R] (P : ProductPreservingTestFunctor) extends
    AddCommGroup (tangentSpace R P.F) where
  tangentModule : Module R (tangentSpace R P.F)

namespace TangentModuleData

variable {R : Type u} [CommRing R]
variable {P : ProductPreservingTestFunctor}

instance (D : TangentModuleData R P) : Module R (tangentSpace R P.F) :=
  D.tangentModule

theorem smul_add (D : TangentModuleData R P) (r : R)
    (x y : tangentSpace R P.F) :
    r • (x + y) = r • x + r • y := by
  letI := D.toAddCommGroup
  letI := D.tangentModule
  exact _root_.smul_add r x y

theorem add_smul (D : TangentModuleData R P) (r s : R)
    (x : tangentSpace R P.F) :
    (r + s) • x = r • x + s • x := by
  letI := D.toAddCommGroup
  letI := D.tangentModule
  exact _root_.add_smul r s x

theorem one_smul (D : TangentModuleData R P) (x : tangentSpace R P.F) :
    (1 : R) • x = x := by
  letI := D.toAddCommGroup
  letI := D.tangentModule
  exact _root_.one_smul R x

end TangentModuleData

/-- A pointwise tangent-map certificate for chosen module structures.

This supplies components and a linear tangent evaluation.  Naturality of the
components is not part of this lightweight record; that categorical layer is
left for the full 06IA formalization. -/
structure TangentModuleMorphism {R : Type u} [CommRing R]
    (P Q : ProductPreservingTestFunctor)
    (DP : TangentModuleData R P) (DQ : TangentModuleData R Q) where
  component : ∀ A : Type u, P.F A → Q.F A
  tangentLinear : tangentSpace R P.F →ₗ[R] tangentSpace R Q.F
  tangentLinear_eq :
    tangentLinear = tangentMap R component

namespace TangentModuleMorphism

variable {R : Type u} [CommRing R]
variable {P Q : ProductPreservingTestFunctor}
variable {DP : TangentModuleData R P} {DQ : TangentModuleData R Q}

@[simp] theorem tangentLinear_apply (φ : TangentModuleMorphism P Q DP DQ)
    (x : tangentSpace R P.F) :
    φ.tangentLinear x = tangentMap R φ.component x := by
  rw [φ.tangentLinear_eq]

theorem map_add (φ : TangentModuleMorphism P Q DP DQ)
    (x y : tangentSpace R P.F) :
    tangentMap R φ.component (x + y) =
      tangentMap R φ.component x + tangentMap R φ.component y := by
  rw [← φ.tangentLinear_apply, ← φ.tangentLinear_apply, ← φ.tangentLinear_apply]
  exact _root_.map_add φ.tangentLinear x y

theorem map_smul (φ : TangentModuleMorphism P Q DP DQ) (r : R)
    (x : tangentSpace R P.F) :
    tangentMap R φ.component (r • x) = r • tangentMap R φ.component x := by
  rw [← φ.tangentLinear_apply, ← φ.tangentLinear_apply]
  exact _root_.map_smul φ.tangentLinear r x

end TangentModuleMorphism

end StacksPart06Lib
