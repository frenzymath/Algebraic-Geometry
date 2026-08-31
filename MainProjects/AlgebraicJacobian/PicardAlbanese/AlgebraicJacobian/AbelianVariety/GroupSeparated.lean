/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianData

/-!
# Group schemes are separated (Kleiman `lem:agps`(1), Wave-5 X1)

A group scheme over a field is separated: the diagonal
`Δ : G ⟶ G ⊗ G` is the pullback of the unit section `η[G]` along the *difference map*
`fst ⋅ snd⁻¹ : G ⊗ G ⟶ G` ("`(x, y) ↦ x y⁻¹`"), and the unit section of a group scheme
over a field is a closed immersion (mathlib, `AlgebraicGeometry/Group/Abelian.lean`), so
the diagonal is a closed immersion by stability under base change.

Stated as reusable infrastructure, in three layers:

* `CategoryTheory.GrpObj.isPullback_diagonal` — the purely categorical half, for a group
  object in ANY cartesian monoidal category: the square

  ```
        G ------ lift (𝟙 G) (𝟙 G) -----> G ⊗ G
        |                                  |
     toUnit G                       fst G G * (snd G G)⁻¹
        |                                  |
        v                                  v
      𝟙_ C ---------- η[G] -------------> G
  ```

  is a pullback (the Hom-group calculus of `Mathlib/CategoryTheory/Monoidal/Cartesian`
  does all the work).
* `AlgebraicGeometry.isSeparated_of_isClosedImmersion_one` — a group scheme over an
  ARBITRARY base scheme whose unit section is a closed immersion is separated.  Note:
  no finiteness hypothesis whatsoever (`LocallyOfFiniteType` is NOT needed).
* `AlgebraicGeometry.isSeparated_of_grpObj` (instance) — over a field the closed-
  immersion hypothesis is mathlib's instance, so every group scheme over a field is
  separated.

The Wave-5 datum corollary `AlgebraicGeometry.JacobianData.isSeparated` closes the
file: `d.J.hom` is separated for every Jacobian datum `d` — one of the two inputs of
the properness assembly P3 (`IsProper = IsSeparated + UniversallyClosed + lft`).
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe v₁ u₁ u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory

section Categorical

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

/-- **The diagonal of a group object is the pullback of the unit along the difference
map** (Kleiman `lem:agps`(1), categorical half): for a group object `G` in a cartesian
monoidal category, the square with top `Δ = lift (𝟙 G) (𝟙 G)`, left `toUnit G`, right
the difference map `fst ⋅ snd⁻¹ : G ⊗ G ⟶ G`, and bottom the unit `η[G]` is a
pullback.  Here `⋅`/`⁻¹` are the Hom-group operations on `G ⊗ G ⟶ G` (scoped in
`CategoryTheory.MonObj`), so the difference map is `lift (fst G G) (snd G G ≫ ι) ≫ μ`
definitionally. -/
theorem GrpObj.isPullback_diagonal (G : C) [GrpObj G] :
    IsPullback (toUnit G) (lift (𝟙 G) (𝟙 G)) η[G] (fst G G * (snd G G)⁻¹) where
  w := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, mul_inv_cancel, Hom.one_def]
  isLimit' := Nonempty.intro <| PullbackCone.IsLimit.mk _
    (fun s => s.snd ≫ fst G G)
    (fun s => toUnit_unique _ _)
    (fun s => by
      -- the cone condition says `(s.snd ≫ fst) ⋅ (s.snd ≫ snd)⁻¹ = 1` in the Hom-group
      have key : s.snd ≫ fst G G = s.snd ≫ snd G G := by
        have h := s.condition.symm
        rw [MonObj.comp_mul, GrpObj.comp_inv, toUnit_unique s.fst (toUnit _),
          ← Hom.one_def] at h
        exact mul_inv_eq_one.mp h
      exact CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simpa using key))
    (fun s m hm₁ hm₂ => by
      have := hm₂ =≫ fst G G
      simpa using this)

end Categorical

end CategoryTheory

namespace AlgebraicGeometry

/-- **A group scheme with closed unit section is separated** (Kleiman `lem:agps`(1)):
for a group object `G` of `Over S`, `S` any base scheme, if the unit section
`η[G].left : S ⟶ G.left` is a closed immersion then `G.hom` is separated.  The
diagonal is the base change of `η[G].left` along the difference map
(`GrpObj.isPullback_diagonal`, pushed to schemes by `Over.forget`), and closed
immersions are stable under base change.  No finiteness hypothesis is needed. -/
theorem isSeparated_of_isClosedImmersion_one {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [IsClosedImmersion η[G].left] : IsSeparated G.hom := by
  constructor
  have sq := (GrpObj.isPullback_diagonal G).map (Over.forget S)
  have h : IsClosedImmersion (lift (𝟙 G) (𝟙 G)).left :=
    MorphismProperty.of_isPullback sq ‹IsClosedImmersion η[G].left›
  exact h

/-- **A group scheme over a field is separated** (Kleiman `lem:agps`(1)): the unit
section is a closed immersion by mathlib's group-scheme instance
(`AlgebraicGeometry/Group/Abelian.lean`), and `isSeparated_of_isClosedImmersion_one`
applies.  No `LocallyOfFiniteType` hypothesis is needed. -/
instance isSeparated_of_grpObj {K : Type u} [Field K] (G : Over (Spec (.of K)))
    [GrpObj G] : IsSeparated G.hom :=
  isSeparated_of_isClosedImmersion_one G

/-- **Wave-5 X1, datum corollary**: the representing object of every Jacobian datum is
separated over `k`.  Feeds the properness assembly P3
(`IsProper = IsSeparated + UniversallyClosed + LocallyOfFiniteType`). -/
theorem JacobianData.isSeparated {k : Type u} [Field k] {C : Over (Spec (.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (d : JacobianData C) : IsSeparated d.J.hom :=
  letI := d.grpObj
  isSeparated_of_grpObj d.J

end AlgebraicGeometry
