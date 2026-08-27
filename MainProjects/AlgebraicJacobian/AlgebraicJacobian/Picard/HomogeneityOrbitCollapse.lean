/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.GroupSchemeHomogeneity

/-!
# The orbit condition collapses the dimension: `htrans → dim = 0`

`Picard/GroupSchemeHomogeneity.lean` reduces the A.3 dimension statement
`dim Pic⁰_{C/k} = g(C)` to three local inputs, one of which is the **orbit condition**

```
htrans : ∀ z, ∃ x y : 𝟙_ (Over (Spec k)) ⟶ Pic0Scheme C,
           (pointTranslationIso (Pic0Scheme C) x y).hom.base e = z
```

("every point of `Pic⁰` is a `k`-rational translate of the identity"), recorded there as "the
honest gap" — a statement about *points* rather than about dimension theory, expected to be
cheap over `k̄` and a descent question in general.

**That reading is wrong, and this file proves it.** The orbit condition is not a weak
point-counting hypothesis waiting for a descent argument: it is strong enough to force

```
topologicalKrullDim Pic⁰_{C/k} = 0,
```

so `topologicalKrullDim_eq_genus_of_homogeneous` and
`isAbelianVariety_of_dimension_genus` are, on their `htrans` hypothesis, only ever
inhabited when `g(C) = 0`. For a genus `≥ 1` curve — the entire point of the A.3 leg,
whose gate `thm:nonempty_jacobianWitness` is stated for `g(C) ≥ 1` — the hypothesis set of
those two theorems is **contradictory**. They are true, and vacuous where it matters.

## Why (three steps, all proved below)

1. `pointTranslationIso` is an **isomorphism of schemes**, so its base map is a homeomorphism
   (`Scheme.homeoOfIso`). A homeomorphism carries closed points to closed points.
2. The identity point `e` **is** a closed point: it is the image of the section
   `identitySection : Spec k ⟶ Pic⁰`, and a section of a morphism to `Spec k` is a closed
   immersion (`isClosedImmersion_of_comp_eq_id`, using `Subsingleton (Spec k)`), whose range is
   that single point. So `htrans` says every point of `Pic⁰` is a homeomorphic image of a
   *closed* point, i.e. every singleton is closed: `Pic⁰` is `T1`.
3. A scheme is sober, and in a **sober `T1`** space the irreducible closeds are
   order-isomorphic to the points under the specialization order
   (`irreducibleSetEquivPoints`), which `T1` makes trivial (`Specializes.eq`). A poset with no
   strict `<` has `krullDim = 0`. Hence `topologicalKrullDim = 0`.

Step 3 is the reusable half: `topologicalKrullDim_eq_zero_of_t1Space` below holds for any
nonempty sober `T1` space and is stated separately for that reason.

## What this does and does not say

It does **not** refute `dim Pic⁰ = g`, which is true. It refutes the *reduction*: passing
through a `k`-rational orbit condition cannot reach it, because `k`-rational translations only
ever move closed points to closed points while `Pic⁰` of a positive-genus curve has
non-closed points (its generic point). The mathematics that reduction was standing in for —
the `≤` half's uniform cotangent bound — therefore still needs a route that reaches
**non-closed** points: transport along a translation by a point valued in an extension of
`k`, or a generic-point argument, not an orbit of `k`-sections.

The rest of `GroupSchemeHomogeneity.lean` is unaffected: the cotangent-invariance theorems
(`finrank_cotangentSpace_eq_of_ringEquiv`, `finrank_cotangentSpace_stalk_eq_of_isIso`) are
about a single isomorphism and are exactly as useful as before. What is refuted is the *shape*
of the hypothesis those theorems were assembled behind.
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open Topology TopologicalSpace Order AlgebraicGeometry

namespace AlgebraicGeometry

/-! ### Step 1: a homeomorphism preserves closed points -/

/-- A homeomorphism carries a closed point to a closed point. -/
theorem isClosed_singleton_homeomorph {X : Type*} [TopologicalSpace X] (e : X ≃ₜ X) {z : X}
    (hz : IsClosed ({z} : Set X)) : IsClosed ({e z} : Set X) := by
  have hpre : ({e z} : Set X) = e.symm ⁻¹' {z} := by
    ext w
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => by rw [h]; simp, fun h => by rw [← h]; simp⟩
  rw [hpre]
  exact hz.preimage e.symm.continuous

/-- **The orbit condition forces `T1`.** If some point `z₀` of `X` is closed and every point of
`X` is the image of `z₀` under *some* homeomorphism of `X`, then every singleton of `X` is
closed. -/
theorem t1Space_of_orbit_of_isClosed {X : Type*} [TopologicalSpace X] (z₀ : X)
    (hz₀ : IsClosed ({z₀} : Set X)) (horb : ∀ z : X, ∃ e : X ≃ₜ X, e z₀ = z) :
    T1Space X := by
  refine ⟨fun z => ?_⟩
  obtain ⟨e, he⟩ := horb z
  rw [← he]
  exact isClosed_singleton_homeomorph e hz₀

/-! ### Step 3: sober + `T1` ⟹ dimension zero -/

/-- **A nonempty sober `T1` space has topological Krull dimension `0`.**

`topologicalKrullDim` is the `krullDim` of the poset of irreducible closeds, and in a sober
`T0` space that poset is order-isomorphic to the points under the specialization order
(`irreducibleSetEquivPoints`). Under `T1` the specialization order is discrete
(`Specializes.eq`), so every element is maximal and the `krullDim` is `0`.

Stated for a bare topological space: only `QuasiSober`, `T1Space` and `Nonempty` are used, so
this applies verbatim to any scheme (schemes are sober). -/
theorem topologicalKrullDim_eq_zero_of_t1Space (X : Type*) [TopologicalSpace X] [Nonempty X]
    [QuasiSober X] [T1Space X] : topologicalKrullDim X = 0 := by
  letI : Preorder X := specializationPreorder X
  letI : PartialOrder X := specializationOrder X
  have h0 : topologicalKrullDim X = krullDim X :=
    krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  rw [h0]
  refine le_antisymm ?_ krullDim_nonneg
  rw [krullDim_nonpos_iff_forall_isMax]
  intro x y hxy
  exact le_of_eq (Specializes.eq hxy)

/-! ### Step 2: a section over `Spec k` has closed image -/

/-- **The image of a section is a closed point.** If `p : Spec k ⟶ X` is a section of
`f : X ⟶ Spec k` then `p` is a closed immersion (`isClosedImmersion_of_comp_eq_id`, available
because `Spec k` has a single point), so its range — the singleton of the image of that
point — is closed. -/
theorem isClosed_singleton_of_section {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) (t : Spec (.of k)) :
    IsClosed ({p.base t} : Set X) := by
  haveI := isClosedImmersion_of_comp_eq_id _ _ hp
  have h := p.isClosedEmbedding.isClosed_range
  rwa [Set.range_eq_singleton (fun x => congrArg p.base (Subsingleton.elim _ _))] at h

/-! ### The collapse, at the project's own `Pic⁰` orbit hypothesis -/

namespace Scheme.Pic0

open CategoryTheory.GrpObj PicScheme

/-- **THE COLLAPSE.** The orbit condition of
`Pic0.topologicalKrullDim_eq_genus_of_homogeneous` forces
`topologicalKrullDim Pic⁰_{C/k} = 0`.

Composition of the three steps: the identity section's point is closed
(`isClosed_singleton_of_section`), every translation is a scheme isomorphism hence a
homeomorphism (`Scheme.homeoOfIso`), so `htrans` gives `T1`
(`t1Space_of_orbit_of_isClosed`), and a nonempty sober `T1` space has dimension `0`
(`topologicalKrullDim_eq_zero_of_t1Space`).

Note the hypotheses are *exactly* those of the theorem being refuted — nothing extra is
assumed about `k` or about `C`. -/
theorem topologicalKrullDim_eq_zero_of_homogeneous {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    [GrpObj (Pic0Scheme C)]
    (htrans : ∀ z : (Pic0Scheme C).left,
      ∃ x y : 𝟙_ (Over (Spec (.of k))) ⟶ Pic0Scheme C,
        (pointTranslationIso (Pic0Scheme C) x y).hom.base
          ((identitySection C).base default) = z) :
    topologicalKrullDim (Pic0Scheme C).left = 0 := by
  haveI : Nonempty (Pic0Scheme C).left :=
    ⟨(identitySection C).base default⟩
  haveI : T1Space (Pic0Scheme C).left := by
    refine t1Space_of_orbit_of_isClosed ((identitySection C).base default) ?_ ?_
    · exact isClosed_singleton_of_section (Pic0Scheme C).hom (identitySection C)
        (identitySection_isSection C) default
    · intro z
      obtain ⟨x, y, hxy⟩ := htrans z
      exact ⟨Scheme.homeoOfIso (pointTranslationIso (Pic0Scheme C) x y), hxy⟩
  exact topologicalKrullDim_eq_zero_of_t1Space _

/-- **Consequence: the orbit condition is inconsistent with positive genus.** Combining the
collapse with `topologicalKrullDim_eq_genus_of_homogeneous` (which concludes
`dim Pic⁰ = g(C)` from the same `htrans` plus `hid` and `hreg`) forces `g(C) = 0`.

So for a curve of genus `≥ 1` those hypotheses cannot all hold, and any statement proved
from them says nothing about the case the A.3 leg exists for. -/
theorem genus_eq_zero_of_homogeneous {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    [GrpObj (Pic0Scheme C)]
    (hid : Module.finrank
        (IsLocalRing.ResidueField ((Pic0Scheme C).left.presheaf.stalk
          ((identitySection C).base default)))
        (IsLocalRing.CotangentSpace ((Pic0Scheme C).left.presheaf.stalk
          ((identitySection C).base default)))
      = AlgebraicGeometry.genus C)
    (hreg : IsRegularLocalRing ((Pic0Scheme C).left.presheaf.stalk
      ((identitySection C).base default)))
    (htrans : ∀ z : (Pic0Scheme C).left,
      ∃ x y : 𝟙_ (Over (Spec (.of k))) ⟶ Pic0Scheme C,
        (pointTranslationIso (Pic0Scheme C) x y).hom.base
          ((identitySection C).base default) = z) :
    AlgebraicGeometry.genus C = 0 := by
  have h1 := topologicalKrullDim_eq_genus_of_homogeneous C hid hreg htrans
  have h2 := topologicalKrullDim_eq_zero_of_homogeneous C htrans
  rw [h2] at h1
  have : ((AlgebraicGeometry.genus C : ℕ) : WithBot ℕ∞) = ((0 : ℕ) : WithBot ℕ∞) := by
    rw [← h1]; norm_num
  exact_mod_cast this

end Scheme.Pic0

end AlgebraicGeometry
