/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.MapToP1
import AlgebraicJacobian.RiemannRoch.CurveBaseChange

/-!
# A fixed finite map to the projective line over every field extension

For a smooth proper geometrically irreducible curve `C/k`, `Ledger/MapToP1.lean` constructs a
finite dominant map `C ⟶ P1 k`. This file chooses that map once over `k` and base-changes the
same map along every field extension `κ/k`.

The target is the literal pullback

`(P1 k)_κ := P1 k ×_{Spec k} Spec κ`,

not yet Ledger's separately constructed `P1 κ`. The resulting map is finite and surjective,
hence dominant. Thus the map itself is pinned over `k`. To feed the current fiber-divisor stack,
one may either prove a `Proj` base-change comparison with `P1 κ`, or more economically factor that
stack through its source-side two-chart coordinate data and base-change those charts and sections.

## Main declarations

* `fixedFiniteMapToP1` — one chosen finite dominant map over `k`.
* `P1FieldBaseChange` / `p1FieldBaseChangeOver` — the pullback target over `κ`.
* `fixedFiniteMapToP1BaseChange` — the cartesian base change of the fixed map.
* `isPullback_fixedFiniteMapToP1BaseChange` and the finite, surjective, and dominant instances.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k]

section FixedMap

variable (C : Over (Spec (CommRingCat.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- A single chosen finite dominant map from `C` to Ledger's projective line over the base
field. All extension maps below are base changes of this one choice. -/
noncomputable def fixedFiniteMapToP1 : C.left ⟶ P1 k :=
  (exists_isFinite_isDominant_toP1 (k := k) (C := C)).choose

instance isFinite_fixedFiniteMapToP1 : IsFinite (fixedFiniteMapToP1 C) := by
  unfold fixedFiniteMapToP1
  exact (exists_isFinite_isDominant_toP1 (k := k) (C := C)).choose_spec.1

instance isDominant_fixedFiniteMapToP1 : IsDominant (fixedFiniteMapToP1 C) := by
  unfold fixedFiniteMapToP1
  exact (exists_isFinite_isDominant_toP1 (k := k) (C := C)).choose_spec.2.1

@[reassoc (attr := simp)]
lemma fixedFiniteMapToP1_comp_structureMap :
    fixedFiniteMapToP1 C ≫ P1.structureMap k = C.hom := by
  unfold fixedFiniteMapToP1
  exact (exists_isFinite_isDominant_toP1 (k := k) (C := C)).choose_spec.2.2

/-- A finite dominant map from a proper source is surjective: finite morphisms have closed
range, while dominance makes that range dense. -/
instance surjective_fixedFiniteMapToP1 : Surjective (fixedFiniteMapToP1 C) :=
  surjective_of_isDominant_of_isClosed_range _
    (fixedFiniteMapToP1 C).isClosedMap.isClosed_range

end FixedMap

section FieldBaseChange

variable (k : Type u) [Field k] (κ : Type u) [Field κ] [Algebra k κ]

/-- The scheme morphism `Spec κ ⟶ Spec k` associated to the field extension. -/
noncomputable abbrev fieldExtensionMap :
    Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k κ))

/-- The literal field base change `(P1 k)_κ = P1 k ×_{Spec k} Spec κ`. -/
noncomputable abbrev P1FieldBaseChange : Scheme.{u} :=
  pullback (P1.structureMap k) (fieldExtensionMap k κ)

/-- The field-base-changed projective line as an object over `Spec κ`. -/
noncomputable def p1FieldBaseChangeOver : Over (Spec (CommRingCat.of κ)) :=
  Over.mk (pullback.snd (P1.structureMap k) (fieldExtensionMap k κ))

end FieldBaseChange

section FixedMapBaseChange

variable (C : Over (Spec (CommRingCat.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable (κ : Type u) [Field κ] [Algebra k κ]

/-- The map `C_κ ⟶ (P1 k)_κ` obtained by base-changing the single map
`fixedFiniteMapToP1 C`. -/
noncomputable def fixedFiniteMapToP1BaseChange :
    pullback C.hom (fieldExtensionMap k κ) ⟶ P1FieldBaseChange k κ :=
  pullback.map C.hom (fieldExtensionMap k κ)
    (P1.structureMap k) (fieldExtensionMap k κ)
    (fixedFiniteMapToP1 C) (𝟙 _) (𝟙 _)
    (by
      rw [Category.comp_id]
      exact (fixedFiniteMapToP1_comp_structureMap C).symm)
    (by simp)

/-- The base-changed map is a morphism over `Spec κ`. -/
@[reassoc (attr := simp)]
lemma fixedFiniteMapToP1BaseChange_snd :
    fixedFiniteMapToP1BaseChange C κ ≫
        pullback.snd (P1.structureMap k) (fieldExtensionMap k κ) =
      pullback.snd C.hom (fieldExtensionMap k κ) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The base-changed map covers the fixed map over the first projections. -/
@[reassoc (attr := simp)]
lemma fixedFiniteMapToP1BaseChange_fst :
    fixedFiniteMapToP1BaseChange C κ ≫
        pullback.fst (P1.structureMap k) (fieldExtensionMap k κ) =
      pullback.fst C.hom (fieldExtensionMap k κ) ≫ fixedFiniteMapToP1 C :=
  pullback.lift_fst _ _ _

/-- The square comparing the base-changed map with `fixedFiniteMapToP1 C` is cartesian. -/
lemma isPullback_fixedFiniteMapToP1BaseChange :
    IsPullback (pullback.fst C.hom (fieldExtensionMap k κ))
      (fixedFiniteMapToP1BaseChange C κ)
      (fixedFiniteMapToP1 C)
      (pullback.fst (P1.structureMap k) (fieldExtensionMap k κ)) := by
  have hs : IsPullback
      (pullback.fst C.hom (fieldExtensionMap k κ))
      (fixedFiniteMapToP1BaseChange C κ ≫
        pullback.snd (P1.structureMap k) (fieldExtensionMap k κ))
      (fixedFiniteMapToP1 C ≫ P1.structureMap k)
      (fieldExtensionMap k κ) := by
    rw [fixedFiniteMapToP1BaseChange_snd, fixedFiniteMapToP1_comp_structureMap]
    exact IsPullback.of_hasPullback C.hom (fieldExtensionMap k κ)
  exact IsPullback.of_bot hs (fixedFiniteMapToP1BaseChange_fst C κ).symm
    (IsPullback.of_hasPullback (P1.structureMap k) (fieldExtensionMap k κ))

/-- Finiteness is preserved by the cartesian base change. -/
instance isFinite_fixedFiniteMapToP1BaseChange :
    IsFinite (fixedFiniteMapToP1BaseChange C κ) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite)
    (isPullback_fixedFiniteMapToP1BaseChange C κ) inferInstance

/-- Surjectivity is preserved by the cartesian base change. -/
instance surjective_fixedFiniteMapToP1BaseChange :
    Surjective (fixedFiniteMapToP1BaseChange C κ) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
    (isPullback_fixedFiniteMapToP1BaseChange C κ) inferInstance

/-- Dominance follows from surjectivity of the base-changed map. -/
instance isDominant_fixedFiniteMapToP1BaseChange :
    IsDominant (fixedFiniteMapToP1BaseChange C κ) := inferInstance

/-- Bundled form of the base-changed fixed map in the over-category over `Spec κ`. -/
noncomputable def fixedFiniteMapToP1BaseChangeOver :
    Scheme.baseChangeField C κ ⟶ p1FieldBaseChangeOver k κ :=
  Over.homMk (fixedFiniteMapToP1BaseChange C κ)
    (fixedFiniteMapToP1BaseChange_snd C κ)

end FixedMapBaseChange

end AlgebraicGeometry
