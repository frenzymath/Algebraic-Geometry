/-
Copyright (c) 2026 The StacksPart06Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart06Lib Contributors
-/

import StacksPart06Lib.TangentModule

/-!
# Functoriality of tangent-module morphisms

The lightweight tangent-module certificate supports identity and composition.
These constructions only use the chosen linear tangent evaluations; they do
not add the naturality or coherence data of the full deformation functor.
-/

namespace StacksPart06Lib

universe u v

namespace TangentModuleMorphism

variable {R : Type u} [CommRing R]
variable {P Q S : ProductPreservingTestFunctor}
variable {DP : TangentModuleData R P} {DQ : TangentModuleData R Q}
variable {DS : TangentModuleData R S}

/-- The identity certificate on a tangent-module datum. -/
def id (DP : TangentModuleData R P) : TangentModuleMorphism P P DP DP where
  component := fun _ x => x
  tangentLinear := LinearMap.id
  tangentLinear_eq := by
    ext x
    rfl

@[simp]
theorem id_component (DP : TangentModuleData R P) (A : Type u)
    (x : P.F A) : (id DP).component A x = x :=
  rfl

@[simp]
theorem id_tangentLinear_apply (DP : TangentModuleData R P)
    (x : tangentSpace R P.F) : (id DP).tangentLinear x = x :=
  rfl

/-- Composition of tangent-module certificates. -/
def comp (ψ : TangentModuleMorphism Q S DQ DS)
    (φ : TangentModuleMorphism P Q DP DQ) :
    TangentModuleMorphism P S DP DS where
  component := fun A x => ψ.component A (φ.component A x)
  tangentLinear := ψ.tangentLinear.comp φ.tangentLinear
  tangentLinear_eq := by
    ext x
    change ψ.tangentLinear (φ.tangentLinear x) =
      tangentMap R (fun A y => ψ.component A (φ.component A y)) x
    rw [φ.tangentLinear_apply, ψ.tangentLinear_apply]
    rfl

@[simp]
theorem comp_component (ψ : TangentModuleMorphism Q S DQ DS)
    (φ : TangentModuleMorphism P Q DP DQ) (A : Type u) (x : P.F A) :
    (comp ψ φ).component A x = ψ.component A (φ.component A x) :=
  rfl

@[simp]
theorem comp_tangentLinear_apply (ψ : TangentModuleMorphism Q S DQ DS)
    (φ : TangentModuleMorphism P Q DP DQ) (x : tangentSpace R P.F) :
    (comp ψ φ).tangentLinear x =
      ψ.tangentLinear (φ.tangentLinear x) :=
  rfl

end TangentModuleMorphism

end StacksPart06Lib
