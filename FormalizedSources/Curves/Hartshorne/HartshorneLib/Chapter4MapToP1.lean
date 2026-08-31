/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4P1Structure

/-!
# Zariski-main wrappers for maps to the projective line

These declarations isolate the formal Zariski-main step used by the finite-map-to-`P1`
argument.  They upgrade a locally quasi-finite map to a finite map when its composite with a
separated morphism is proper.  In this project the separatedness of the chosen `P1` structure
morphism is supplied at the use site, since no global instance has been formalized here.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A locally quasi-finite morphism whose composite with a separated morphism is proper is
finite.  This is the cancellation form of Zariski's main theorem. -/
theorem IsFinite.of_locallyQuasiFinite_of_comp {X Y S : Scheme.{u}}
    (π : X ⟶ Y) (g : Y ⟶ S) [LocallyQuasiFinite π] [IsSeparated g]
    [IsProper (π ≫ g)] :
    IsFinite π := by
  letI : IsProper π := IsProper.of_comp π g
  exact IsFinite.of_isProper_of_locallyQuasiFinite π

variable {k : Type u} [Field k]

section ZMT

variable {X : Scheme.{u}}

/-- A locally quasi-finite map from a scheme proper over `k` to `P1 k` is finite, provided the
structure morphism of `P1 k` is separated. -/
theorem isFinite_toP1_of_locallyQuasiFinite
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (π : X ⟶ P1 k) [LocallyQuasiFinite π]
    [IsSeparated (P1.structureMap k)]
    (hπ : π ≫ P1.structureMap k = f) :
    IsFinite π := by
  letI : IsProper (π ≫ P1.structureMap k) := hπ ▸ inferInstance
  exact IsFinite.of_locallyQuasiFinite_of_comp π (P1.structureMap k)

end ZMT

/-- If a `k`-morphism from a proper scheme to `P1 k` is locally quasi-finite, then it is finite.
The locally quasi-finite map itself remains an explicit input; this theorem does not claim that
such a map exists. -/
theorem exists_isFinite_toP1_of_locallyQuasiFinite
    {C : Over (Spec (.of k))} [IsProper C.hom]
    [IsSeparated (P1.structureMap k)]
    (h : ∃ π : C.left ⟶ P1 k,
      LocallyQuasiFinite π ∧ π ≫ P1.structureMap k = C.hom) :
    ∃ π : C.left ⟶ P1 k,
      IsFinite π ∧ π ≫ P1.structureMap k = C.hom := by
  obtain ⟨π, hqf, hcomp⟩ := h
  letI : LocallyQuasiFinite π := hqf
  exact ⟨π, isFinite_toP1_of_locallyQuasiFinite C.hom π hcomp, hcomp⟩

end AlgebraicGeometry
