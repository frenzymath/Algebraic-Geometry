/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.ProjectionUnits
import AlgebraicJacobian.Picard.RelPicAlgebra

/-!
# (C1) étale separatedness of the relative Picard functor — assembly file

This file is the future home of the **(C1) étale-separatedness** theorem — injectivity of
the unit of the étale plus construction,

```
theorem PicEtAff.unit_injective : Function.Injective (PicEtAff.unit C A)
```

for a curve `C` (proper, geometrically irreducible and geometrically reduced) over a field
`k` — which is the separatedness half of Kleiman, *The Picard Scheme*, Theorem 2.5(1): the
relative Picard presheaf is a separated presheaf for the étale topology, so its
sheafification (the one-step plus `PicEtAff`) has an injective unit. The assembly follows
the "Refined design" of `informal/c1-etale-separatedness-assembly.md` (the ζ-decomposition
of the scheme-side step ε3/ζ), consuming brick 3 (`Over.prPullback_injective`), the
projection-descent equivalence (ε1, `Picard/ProjectionUnits.lean`), the composite unit
descent (ε2, `Descent/UnitDescentComposite.lean`) and the dictionary naturality (γ,
`Picard/CechPicToPicNaturality.lean`).

## What is landed here (ζ1)

`AlgebraicGeometry.Over.cechPicMap_tensorInl_eq_tensorInr`, the **class-level coherence
seed**: if a Čech Picard class `L` on the curve-product `C ⊗ Spec A` restricts, over a test
algebra `A → B`, to something pulled back from the base — i.e. `p_B^* N = (C ◁ Spec f)^* L`
for `N : CechPic (Spec B)` and `f = ofId A B` — then the two base changes of `N` to
`Spec (B ⊗[A] B)` agree along the two coprojections `tensorInl, tensorInr : B →ₐ[k] B ⊗[A] B`.
Both sides pull back along `p_{B ⊗[A] B}` to the same restriction of `L`
(`Scheme.CechPic.map_comp` + `Over.snd_left_naturality` + `Over.overSpecMap_comp`), and
pullback along the curve projection is injective (brick 3), so they are equal. This is the
"one genuinely delicate step" reduced to its cocycle-free seed — the honest descent datum is
built downstream (ζ2).

## Remaining steps of the assembly (per the worksheet)

* **ζ2 (construct the composite descent unit)**: choose a basic (Zariski) cover `f : ι → B`
  trivializing `toPic N`, build `v ∈ ((∏ Sᵢ) ⊗[A] (∏ Sᵢ))ˣ` whose collapse is the cover
  cocycle of `N` and whose cross terms are ζ1's comparison descended through ε1, and prove
  `Module.IsDescentCocycle v` by checking the two conditions after `p`-pullback (ε1
  injectivity), where they are coboundary computations for one cocycle representative of `L`.
* **ζ3 (close)**: `M := cechPicEquivPic.symm (picClass v)` over `A`; establish `p_A^* M = L`
  by the `unitsRes`/`mk_eq_one_iff` calculus (the fppf `descend_coboundary` analogue), then
  unfold to `PicEtAff.unit_injective` through `injective_iff_map_eq_one` + `mk_eq_mk_iff` +
  `relPicMk` calculus.

## Main declarations (this file)

* `AlgebraicGeometry.tensorInl`, `AlgebraicGeometry.tensorInr` — the two `k`-algebra
  coprojections `B →ₐ[k] B ⊗[A] B` (mirroring `doubleInl`/`doubleInr` of
  `Picard/PicEtAff.lean` for a general test algebra `B`), with the diagonal-coherence lemma
  `AlgebraicGeometry.tensorInl_comp_ofId`.
* `AlgebraicGeometry.Over.cechPicMap_tensorInl_eq_tensorInr` — sub-brick ζ1.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

/-- On a commutative `k`-algebra `B` which is also an `A`-algebra compatibly (a scalar tower
`k → A → B`), the `A`- and `k`-scalar actions commute. Needed so that
`Algebra.TensorProduct.includeLeft` elaborates as a `k`-algebra map into `B ⊗[A] B` and so
that `B ⊗[A] B` carries its `k`-algebra structure. -/
instance smulCommClass_of_isScalarTower : SMulCommClass A k B :=
  ⟨fun a c b => by simp only [Algebra.smul_def]; ring⟩

/-- The first coprojection `B →ₐ[k] B ⊗[A] B`, `b ↦ b ⊗ₜ 1`, as a `k`-algebra map — the
general-`B` mirror of `doubleInl` (`Picard/PicEtAff.lean`); definitionally
`Algebra.TensorProduct.includeLeft`. -/
def tensorInl : B →ₐ[k] B ⊗[A] B :=
  Algebra.TensorProduct.includeLeft

/-- The second coprojection `B →ₐ[k] B ⊗[A] B`, `b ↦ 1 ⊗ₜ b`, as a `k`-algebra map — the
general-`B` mirror of `doubleInr`; definitionally
`(Algebra.TensorProduct.includeRight).restrictScalars k`. -/
def tensorInr : B →ₐ[k] B ⊗[A] B :=
  (Algebra.TensorProduct.includeRight).restrictScalars k

/-- **Diagonal coherence of the two coprojections.** Precomposed with the base inclusion
`A →ₐ[k] B`, the two coprojections `B → B ⊗[A] B` agree: both send `a` to the image of
`algebraMap A B a`, and over `A` we have `(algebraMap A B a) ⊗ₜ 1 = 1 ⊗ₜ (algebraMap A B a)`.
This is what collapses the two base changes of a class pulled back from the base. -/
lemma tensorInl_comp_ofId :
    (tensorInl (A := A) (B := B)).comp ((Algebra.ofId A B).restrictScalars k)
      = (tensorInr (A := A) (B := B)).comp ((Algebra.ofId A B).restrictScalars k) := by
  ext a
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.ofId_apply, tensorInl,
    tensorInr, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

namespace Over

variable (C : Over (Spec (.of k)))
  [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

/-- **ζ1: the class-level coherence seed** (sub-brick of the (C1) étale-separatedness
assembly; the projection step of Kleiman, *The Picard Scheme*, Theorem 2.5(1)). If a Čech
Picard class `L` on the curve-product `C ⊗ Spec A` restricts, over a test algebra `A → B`, to
`p_B^*` of a class `N` on `Spec B` pulled back from the base along `Spec (ofId A B)`, then the
two base changes of `N` to `Spec (B ⊗[A] B)` — along the coprojections `tensorInl, tensorInr`
— coincide.

Both sides pull back along the projection `p_{B ⊗[A] B} : (C ⊗ Spec (B ⊗[A] B)).left ⟶
Spec (B ⊗[A] B)` to the SAME restriction `(C ◁ Spec (tensorInⱼ ∘ ofId A B))^* L` of `L`
(`Scheme.CechPic.map_comp`, `Over.snd_left_naturality`, the hypothesis `h`, and
`tensorInl_comp_ofId`), so they agree by injectivity of curve-projection pullback (brick 3,
`Over.prPullback_injective`). -/
theorem cechPicMap_tensorInl_eq_tensorInr
    (L : ((C ⊗ overSpec k A).left).CechPic) (N : ((overSpec k B).left).CechPic)
    (h : Scheme.CechPic.map (snd C (overSpec k B)).left N
        = Scheme.CechPic.map
            (C ◁ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left L) :
    Scheme.CechPic.map (Over.overSpecMap (tensorInl (A := A) (B := B))).left N
      = Scheme.CechPic.map (Over.overSpecMap (tensorInr (A := A) (B := B))).left N := by
  -- For each coprojection `j`, computing the `p_{B ⊗[A] B}`-pullback of `map (Spec j) N`.
  have key : ∀ j : B →ₐ[k] B ⊗[A] B,
      Scheme.CechPic.map (snd C (overSpec k (B ⊗[A] B))).left
          (Scheme.CechPic.map (Over.overSpecMap j).left N)
        = Scheme.CechPic.map
            (C ◁ (Over.overSpecMap j
              ≫ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k))).left L := by
    intro j
    rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
      ← snd_left_naturality C (Over.overSpecMap j),
      Scheme.CechPic.map_comp, MonoidHom.comp_apply, h,
      ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, ← Over.comp_left,
      ← MonoidalCategory.whiskerLeft_comp]
  -- Both sides pull back to the same thing, and curve-projection pullback is injective.
  apply prPullback_injective C (overSpec k (B ⊗[A] B))
  rw [key tensorInl, key tensorInr,
    show Over.overSpecMap (tensorInl (A := A) (B := B))
          ≫ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)
        = Over.overSpecMap (tensorInr (A := A) (B := B))
          ≫ Over.overSpecMap ((Algebra.ofId A B).restrictScalars k) from by
      rw [← Over.overSpecMap_comp, ← Over.overSpecMap_comp, tensorInl_comp_ofId]]

end Over

end AlgebraicGeometry
