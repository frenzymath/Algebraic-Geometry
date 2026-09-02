/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped TensorProduct

namespace StacksPart01Lib

/-- Finite ring maps remain finite after arbitrary base change
(Stacks, Tag `02JK`).  The base-changed map is the canonical inclusion of
the new base ring into the tensor product. -/
theorem ringHom_finite_baseChange
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    (hf : (algebraMap R S).Finite) :
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := R') (B := S)).Finite := by
  letI : Module.Finite R S := RingHom.finite_algebraMap.mp hf
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- Integral ring maps remain integral after arbitrary base change
(Stacks, Tag `02JK`). -/
theorem ringHom_isIntegral_baseChange
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    (hf : (algebraMap R S).IsIntegral) :
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := R') (B := S)).IsIntegral := by
  letI : Algebra.IsIntegral R S := ⟨hf⟩
  exact Algebra.IsIntegral.isIntegral

end StacksPart01Lib
