/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.GaloisQuotientUniqueness
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Geometry of finite Galois quotients

Geometric properties of the structure morphism descend from a scheme with a
finite Galois action to any scheme satisfying the quotient predicate.  Local
finite type descends fpqc-locally.  Quasi-compactness follows directly from the
surjective quotient projection and compactness of the acted scheme.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicJacobian.GaloisDescent

universe u

set_option autoImplicit false

namespace IsGaloisQuotient

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {X Y : Scheme.{u}}
variable {f : X ⟶ Spec (CommRingCat.of L)}
variable {g : Y ⟶ Spec (CommRingCat.of K)}
variable {rho : SemilinearGalAction K L X f}

/-- Local finite type descends from the acted scheme to a finite Galois
quotient. -/
theorem locallyOfFiniteType (h : IsGaloisQuotient rho g)
    [LocallyOfFiniteType f] : LocallyOfFiniteType g := by
  let w := h.witness
  apply MorphismProperty.of_isPullback_of_descendsAlong
    (P := @LocallyOfFiniteType)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (IsPullback.of_hasPullback g
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).flip
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · rw [← w.over,
      MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType)]
    infer_instance

/-- Quasi-compactness descends from the acted scheme to a finite Galois
quotient. -/
theorem quasiCompact (h : IsGaloisQuotient rho g) [QuasiCompact f] :
    QuasiCompact g := by
  let w := h.witness
  let p : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let q : X ⟶ Y := w.e.inv ≫ pullback.fst g p
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hq : Function.Surjective q := by
    letI : Surjective p := by
      dsimp [p]
      infer_instance
    letI : Surjective (pullback.fst g p) := inferInstance
    letI : Surjective q := inferInstance
    exact Surjective.surj
  letI : CompactSpace Y :=
    ⟨hq.range_eq ▸ isCompact_range q.continuous⟩
  exact (quasiCompact_iff_compactSpace g).2 inferInstance

end IsGaloisQuotient

end AlgebraicJacobian.GaloisDescent
