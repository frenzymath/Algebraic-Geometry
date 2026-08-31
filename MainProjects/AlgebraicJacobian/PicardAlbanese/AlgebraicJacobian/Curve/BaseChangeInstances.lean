/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.SectionsBaseChange
import AlgebraicJacobian.RiemannRoch.Degree

/-!
# Base-change instances for the curve over an extension field (gap G-D5(a))

For the challenge curve `C : Over (Spec k)` (smooth of relative dimension one, proper and
geometrically irreducible over the field `k`) and a field extension `K` of `k`
(`[Field K] [Algebra k K]`), this file installs — **as instances that fire by typeclass
resolution** — every hypothesis of the landed degree/Riemann–Roch stack
(`AlgebraicJacobian.RiemannRoch.Degree`) for the base-changed curve

`C_K := (C ⊗ overSpec k K).left`,

viewed as a `K`-scheme via the **second projection** `(snd C (overSpec k K)).left`. This is
exactly the `Over`-instance spelling that `Cohomology.RelativeTwoCover.relCurve.instOver`
uses (`.ofHom (snd C (overSpec k K)).left`), but keyed on the `(C ⊗ overSpec k K).left`
spelling that the Riemann–Roch files consume, rather than on the `relCurve C K` `def`.

The single geometric input is the pullback bridge `AlgebraicGeometry.Over.isPullback_left`
(`Cohomology.SectionsBaseChange`): the second projection `(snd C (overSpec k K)).left` is the
base change of the structure morphism `C.hom` along `overSpec k K ⟶ Spec k`. Every morphism
property then transports by `MorphismProperty.IsStableUnderBaseChange` (smooth of relative
dimension one, proper, geometrically irreducible), and integrality of `C_K` is
`isIntegral_left_of_geometricallyReduced` applied to the base change (geometric
irreducibility is transported; geometric reducedness comes for free from smoothness).

## Main instances (keyed for the Riemann–Roch stack)

* `AlgebraicGeometry.instOverBaseChange` — item 1: `(C ⊗ overSpec k K).left` is a `K`-scheme
  via the second projection; `(C ⊗ overSpec k K).left ↘ Spec K = (snd C (overSpec k K)).left`
  definitionally (`baseChange_over_eq_snd_left`).
* `AlgebraicGeometry.instSmoothOfRelativeDimensionSndLeft`,
  `AlgebraicGeometry.instIsProperSndLeft`,
  `AlgebraicGeometry.instGeometricallyIrreducibleSndLeft` — the base-change transport of the
  standing bundle onto the raw morphism `(snd C (overSpec k K)).left`.
* `AlgebraicGeometry.instSmoothOfRelativeDimensionBaseChange` (item 2),
  `AlgebraicGeometry.instIsProperBaseChange`,
  `AlgebraicGeometry.instQuasiCompactBaseChange` (item 4) — the same properties in the
  `↘`-spelling `(C ⊗ overSpec k K).left ↘ Spec K` that `classDeg` queries.
* `AlgebraicGeometry.instIsIntegralBaseChange` (item 3): `C_K` is integral.
* `AlgebraicGeometry.instModuleFiniteHModuleZeroBaseChange`,
  `AlgebraicGeometry.instModuleFiniteHModuleOneBaseChange` (item 5): the two structure-sheaf
  cohomology finiteness instances over `K`.

The acceptance smoke test (item 6) verifies that the landed `classDeg K` typechecks on `C_K`
with every hypothesis inferred by resolution.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  (K : Type u) [Field K] [Algebra k K]

/-! ## Item 1: the `K`-scheme structure via the second projection -/

/-- **Item 1.** The base-changed curve `C_K := (C ⊗ overSpec k K).left` is a scheme over
`Spec K` via the **second projection** `(snd C (overSpec k K)).left`. This is the same
structure morphism that `Cohomology.RelativeTwoCover.relCurve.instOver` installs, but keyed on
the `(C ⊗ overSpec k K).left` spelling consumed by the Riemann–Roch/degree stack (rather than
on the `relCurve C K` `def`). -/
noncomputable instance instOverBaseChange :
    ((C ⊗ overSpec k K).left).Over (Spec (CommRingCat.of K)) :=
  .ofHom (snd C (overSpec k K)).left

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- The structure morphism installed by `instOverBaseChange` is, definitionally, the second
projection `(snd C (overSpec k K)).left`. This equation is `rfl`; it lets a consumer rewrite
the `↘`-spelling that `classDeg` uses into the raw projection the base-change lemmas produce
(and back), and pins the alignment with `relCurve.instOver`. -/
theorem baseChange_over_eq_snd_left :
    ((C ⊗ overSpec k K).left ↘ Spec (CommRingCat.of K)) = (snd C (overSpec k K)).left :=
  rfl

/-! ## Transport of the standing bundle onto the raw second projection

Every property is transported from `C.hom` along the base-change square
`Over.isPullback_left C (overSpec k K)`, whose right leg is the second projection. These are
keyed on the raw morphism `(snd C (overSpec k K)).left`, which is what the bundled curve
`Over.mk (snd C (overSpec k K)).left` feeds to the landed curve-level instances
(`isIntegral_left_of_geometricallyReduced`, `moduleFinite_hModule_zero`/`_one`). -/

/-- **Base change of smooth-of-relative-dimension-one.** The second projection is smooth of
relative dimension one over `K`, by `smoothOfRelativeDimension_isStableUnderBaseChange`. -/
instance instSmoothOfRelativeDimensionSndLeft :
    SmoothOfRelativeDimension 1 (snd C (overSpec k K)).left :=
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
    (Over.isPullback_left C (overSpec k K)) inferInstance

/-- **Base change of properness.** The second projection is proper over `K`
(`IsProper.isStableUnderBaseChange`). -/
instance instIsProperSndLeft : IsProper (snd C (overSpec k K)).left :=
  MorphismProperty.of_isPullback (P := @IsProper)
    (Over.isPullback_left C (overSpec k K)) inferInstance

/-- **Base change of geometric irreducibility.** The second projection is geometrically
irreducible over `K` (`GeometricallyIrreducible` is stable under base change). -/
instance instGeometricallyIrreducibleSndLeft :
    GeometricallyIrreducible (snd C (overSpec k K)).left :=
  MorphismProperty.of_isPullback (P := @GeometricallyIrreducible)
    (Over.isPullback_left C (overSpec k K)) inferInstance

/-! ## The properties in the `↘`-spelling consumed by `classDeg`

The degree stack phrases smoothness and quasi-compactness on `X ↘ Spec K`. Since
`(C ⊗ overSpec k K).left ↘ Spec K` is definitionally `(snd C (overSpec k K)).left`
(`baseChange_over_eq_snd_left`), these bridge instances are the transported raw instances,
now discoverable under the `↘`-key. -/

/-- **Item 2.** `C_K` is smooth of relative dimension one over `K`, in the `↘`-spelling. -/
instance instSmoothOfRelativeDimensionBaseChange :
    SmoothOfRelativeDimension 1 ((C ⊗ overSpec k K).left ↘ Spec (CommRingCat.of K)) :=
  inferInstanceAs (SmoothOfRelativeDimension 1 (snd C (overSpec k K)).left)

/-- **Item 4a.** `C_K` is proper over `K`, in the `↘`-spelling. -/
instance instIsProperBaseChange :
    IsProper ((C ⊗ overSpec k K).left ↘ Spec (CommRingCat.of K)) :=
  inferInstanceAs (IsProper (snd C (overSpec k K)).left)

/-- **Item 4b.** `C_K` is quasi-compact over `K`, in the `↘`-spelling (properness gives
quasi-compactness through `UniversallyClosed`). -/
instance instQuasiCompactBaseChange :
    QuasiCompact ((C ⊗ overSpec k K).left ↘ Spec (CommRingCat.of K)) :=
  inferInstanceAs (QuasiCompact (snd C (overSpec k K)).left)

/-! ## Item 3: integrality of the base-changed curve

Geometric irreducibility (transported above) together with geometric reducedness (free from
smoothness, `Smooth.geometricallyReduced`) gives integrality, via the landed
`isIntegral_left_of_geometricallyReduced` applied to the bundled base-changed curve. -/

/-- **Item 3.** The base-changed curve `C_K` is integral: it is geometrically irreducible and
geometrically reduced over `K`. This is the genuine content of gap G-D5(a) — the definition of
geometric irreducibility/reducedness of `C/k` gives integrality of `C ⊗_k K` for *every* field
extension `K`. The bundled curve `Over.mk (snd …)` reroutes the raw-morphism instances above to
the `X.hom` shape that `isIntegral_left_of_geometricallyReduced` reads (geometric reducedness is
free from smoothness). -/
instance instIsIntegralBaseChange : IsIntegral ((C ⊗ overSpec k K).left) :=
  let bundled : Over (Spec (CommRingCat.of K)) := Over.mk (snd C (overSpec k K)).left
  haveI : GeometricallyIrreducible bundled.hom := instGeometricallyIrreducibleSndLeft C K
  haveI : GeometricallyReduced bundled.hom :=
    (inferInstance : GeometricallyReduced (snd C (overSpec k K)).left)
  isIntegral_left_of_geometricallyReduced bundled

/-! ## Item 5: structure-sheaf cohomology finiteness over `K`

The landed curve-level finiteness instances `moduleFinite_hModule_zero`/`_one`, applied to the
bundled base-changed curve `Over.mk (snd C (overSpec k K)).left` (whose structure morphism is
the raw second projection carrying the transported standing bundle), keyed for the
`(C ⊗ overSpec k K).left.moduleKSheaf K` spelling that `classDeg` queries. -/

/-- **Item 5a.** `H⁰(C_K, 𝒪)` is a finite `K`-module. -/
instance instModuleFiniteHModuleZeroBaseChange :
    Module.Finite K (Sheaf.HModule ((C ⊗ overSpec k K).left.moduleKSheaf K) 0) :=
  let bundled : Over (Spec (CommRingCat.of K)) := Over.mk (snd C (overSpec k K)).left
  haveI : IsProper bundled.hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 bundled.hom := instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible bundled.hom := instGeometricallyIrreducibleSndLeft C K
  moduleFinite_hModule_zero bundled

/-- **Item 5b.** `H¹(C_K, 𝒪)` is a finite `K`-module. -/
instance instModuleFiniteHModuleOneBaseChange :
    Module.Finite K (Sheaf.HModule ((C ⊗ overSpec k K).left.moduleKSheaf K) 1) :=
  let bundled : Over (Spec (CommRingCat.of K)) := Over.mk (snd C (overSpec k K)).left
  haveI : IsProper bundled.hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 bundled.hom := instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible bundled.hom := instGeometricallyIrreducibleSndLeft C K
  moduleFinite_hModule_one bundled

/-! ## Item 6: acceptance smoke test

The landed degree homomorphism `classDeg K` typechecks on the base-changed curve `C_K` with
**every** hypothesis discharged by typeclass resolution from the instances above — no manual
`haveI`/`letI`. This is the brick's acceptance criterion; the `degAt` (G-D6) spec-writer
consumes exactly this. -/

/-- **Item 6 (smoke test).** `classDeg K` applies to `C_K = (C ⊗ overSpec k K).left` with all
six instance hypotheses of the degree stack inferred automatically. -/
private noncomputable def classDegBaseChangeSmoke :
    Additive ((C ⊗ overSpec k K).left.CechPic) →+ ℤ :=
  classDeg K

end AlgebraicGeometry
