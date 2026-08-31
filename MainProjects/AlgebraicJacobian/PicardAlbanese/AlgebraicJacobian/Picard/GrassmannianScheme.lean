/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianGlue
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# The Grassmannian structure morphism over the base field (DD-3, stage 3a)

The structure morphism `Gr(d, r) → Spec k` and the chart plumbing of the glued
Grassmannian scheme (`informal/spec-dd-3.md` §2/§3).  Unlike the ℤ-model route map
(where `Spec ℤ` is terminal), the structure morphism is descended through the glued
scheme's own colimit universal property (`Multicoequalizer.desc`): the compatibility
triangle over each overlap reduces to the ring identity "the transitions lie over `k`",
which is automatic in the `→ₐ[k]` architecture.

* `AlgebraicGeometry.Grassmannian.grStructMap`: **the structure morphism**
  `Gr(d, r) ⟶ Spec k`, with the triangle `ι_grStructMap`.
* `AlgebraicGeometry.Grassmannian.grOver`: the Grassmannian as an object of
  `Over (Spec k)` — the shape every campaign consumer takes.
* `AlgebraicGeometry.Grassmannian.pullbackιIso` and its leg lemmas: the intersection
  `U^I ∩ U^J` inside the glued scheme is the chart overlap `Spec R^I[1/P^I_J]`.
* `AlgebraicGeometry.Grassmannian.quasiCompact_grStructMap`,
  `locallyOfFiniteType_grStructMap`: the DD-Q bundle rows delivered by the finite
  affine atlas.
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Grassmannian

/-- The overlap-to-chart composite `t_{I,J} ≫ ι_{J,I}` is the comorphism of the
pre-localisation transition hom `θ̃_{I,J}`: both reduce to
`θ̃_{I,J} = θ_{I,J} ∘ (R^J → R^J[1/P^J_I])`. -/
theorem chartTransition_comp_chartIncl (k : Type u) [Field k] (d r : ℕ)
    (I J : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) :
    chartTransition k d r I J hI hJ ≫ chartIncl k d r J I hJ hI
      = Spec.map (CommRingCat.ofHom (transitionPreMap k d r I J hI hJ).toRingHom) := by
  rw [chartTransition, chartIncl,
    show CommRingCat.ofHom (transitionPreMap k d r I J hI hJ).toRingHom
        = CommRingCat.ofHom (algebraMap (ChartRing k d r J)
            (Localization.Away (minorDet k d r J I hJ hI))) ≫
          CommRingCat.ofHom (transitionMap k d r I J hI hJ).toRingHom
      from by
        rw [← CommRingCat.ofHom_comp]
        exact congrArg CommRingCat.ofHom
          (transitionMap_comp_algebraMap k d r I J hI hJ).symm]
  exact (Spec.map_comp _ _).symm

/-- The compatibility triangle for the structure morphism: over each overlap
`V (I,J) = Spec R^I[1/P^I_J]`, the two routes to `Spec k` agree — the ring identity
"`θ̃_{I,J}` lies over `k`", automatic from the `→ₐ[k]` architecture. -/
theorem chartStructCompat (k : Type u) [Field k] (d r : ℕ)
    (I J : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) :
    chartIncl k d r I J hI hJ ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d r I)))
      = (chartTransition k d r I J hI hJ ≫ chartIncl k d r J I hJ hI) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d r J))) := by
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap (ChartRing k d r I)
        (Localization.Away (minorDet k d r I J hI hJ)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d r I)))
      = Spec.map (CommRingCat.ofHom
          (algebraMap k (Localization.Away (minorDet k d r I J hI hJ)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (algebraMap (ChartRing k d r I)
            (Localization.Away (minorDet k d r I J hI hJ))).comp
          (algebraMap k (ChartRing k d r I))
        = algebraMap k (Localization.Away (minorDet k d r I J hI hJ)) from
        (IsScalarTower.algebraMap_eq k (ChartRing k d r I)
          (Localization.Away (minorDet k d r I J hI hJ))).symm]
  have h2 : Spec.map (CommRingCat.ofHom (transitionPreMap k d r I J hI hJ).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d r J)))
      = Spec.map (CommRingCat.ofHom
          (algebraMap k (Localization.Away (minorDet k d r I J hI hJ)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (transitionPreMap k d r I J hI hJ).toRingHom.comp
          (algebraMap k (ChartRing k d r J))
        = algebraMap k (Localization.Away (minorDet k d r I J hI hJ)) from
        AlgHom.comp_algebraMap (transitionPreMap k d r I J hI hJ)]
  rw [chartTransition_comp_chartIncl]
  exact h1.trans h2.symm

/-- **The structure morphism** `Gr(d, r) ⟶ Spec k`: descended through the glued
scheme's colimit universal property from the affine chart structure maps
`Spec R^I → Spec k`; the compatibility over each overlap is `chartStructCompat`. -/
noncomputable def grStructMap (k : Type u) [Field k] (d r : ℕ) :
    grScheme k d r ⟶ Spec (CommRingCat.of k) :=
  Limits.Multicoequalizer.desc (glueData k d r).diagram (Spec (CommRingCat.of k))
    (fun I => Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d r I.down.1))))
    (fun p => chartStructCompat k d r p.1.down.1 p.2.down.1 p.1.down.2 p.2.down.2)

/-- The chart inclusion composed with the structure morphism is the affine structure
map `Spec R^I → Spec k`: the defining triangle of `grStructMap`. -/
theorem ι_grStructMap (k : Type u) [Field k] (d r : ℕ) (i : (glueData k d r).J) :
    (glueData k d r).ι i ≫ grStructMap k d r
      = Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d r i.down.1))) :=
  Limits.Multicoequalizer.π_desc (glueData k d r).diagram (Spec (CommRingCat.of k))
    (fun I => Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d r I.down.1))))
    (fun p => chartStructCompat k d r p.1.down.1 p.2.down.1 p.1.down.2 p.2.down.2) i

/-- **The Grassmannian as a test object**: `Gr(d, r)` with its structure morphism, as
an object of `Over (Spec k)` — the shape in which every campaign consumer (DD-4's
embedding, DD-R's carve) receives the Grassmannian. -/
noncomputable def grOver (k : Type u) [Field k] (d r : ℕ) : Over (Spec (CommRingCat.of k)) :=
  Over.mk (grStructMap k d r)

/-- The intersection pullback `U^I ∩ U^J = pullback (ι i) (ι j)` inside the glued
Grassmannian is the chart overlap `U^I_J = Spec R^I[1/P^I_J]`: from the glue-data
pullback cone `vPullbackConeIsLimit`.  The source identification of the
restricted-diagonal (separatedness) computation, and the frame-atlas overlap export. -/
noncomputable def pullbackιIso (k : Type u) [Field k] (d r : ℕ)
    (i j : (glueData k d r).J) :
    Limits.pullback ((glueData k d r).ι i) ((glueData k d r).ι j) ≅
      chartOverlap k d r i.down.1 j.down.1 i.down.2 j.down.2 :=
  (Limits.limit.isLimit _).conePointUniqueUpToIso
    ((glueData k d r).vPullbackConeIsLimit i j)

/-- First leg of `pullbackιIso`: `e⁻¹ ≫ pr₁ = chartIncl I J` (the `V (i,j) ⟶ U i` leg
of the glue-data pullback cone). -/
theorem pullbackιIso_inv_fst (k : Type u) [Field k] (d r : ℕ)
    (i j : (glueData k d r).J) :
    (pullbackιIso k d r i j).inv ≫
        Limits.pullback.fst ((glueData k d r).ι i) ((glueData k d r).ι j)
      = chartIncl k d r i.down.1 j.down.1 i.down.2 j.down.2 := by
  have := (Limits.limit.isLimit
      (Limits.cospan ((glueData k d r).ι i)
        ((glueData k d r).ι j))).conePointUniqueUpToIso_inv_comp
    ((glueData k d r).vPullbackConeIsLimit i j) Limits.WalkingCospan.left
  simp only [pullbackιIso, Limits.pullback.fst, Grassmannian.glueData] at this ⊢
  exact this

/-- Second leg of `pullbackιIso`: `e⁻¹ ≫ pr₂ = chartTransition I J ≫ chartIncl J I`
(the `V (i,j) ⟶ U j` leg of the glue-data pullback cone, which is `t ≫ f`). -/
theorem pullbackιIso_inv_snd (k : Type u) [Field k] (d r : ℕ)
    (i j : (glueData k d r).J) :
    (pullbackιIso k d r i j).inv ≫
        Limits.pullback.snd ((glueData k d r).ι i) ((glueData k d r).ι j)
      = chartTransition k d r i.down.1 j.down.1 i.down.2 j.down.2 ≫
          chartIncl k d r j.down.1 i.down.1 j.down.2 i.down.2 := by
  have := (Limits.limit.isLimit
      (Limits.cospan ((glueData k d r).ι i)
        ((glueData k d r).ι j))).conePointUniqueUpToIso_inv_comp
    ((glueData k d r).vPullbackConeIsLimit i j) Limits.WalkingCospan.right
  simp only [pullbackιIso, Limits.pullback.snd, Grassmannian.glueData] at this ⊢
  exact this

/-- The structure morphism `Gr(d, r) → Spec k` is **quasi-compact**: `Spec k` is affine
and the Grassmannian is a compact space (finitely many affine charts).  A DD-Q bundle
row. -/
theorem quasiCompact_grStructMap (k : Type u) [Field k] (d r : ℕ) :
    QuasiCompact (grStructMap k d r) := by
  have : CompactSpace (grScheme k d r) := compactSpace_grScheme k d r
  exact HasAffineProperty.iff_of_isAffine.mpr this

/-- The structure morphism `Gr(d, r) → Spec k` is **locally of finite type**: on each
chart the composite `U^I → Gr → Spec k` is `Spec.map` of the structure map of a
polynomial ring in finitely many variables.  A DD-Q bundle row. -/
theorem locallyOfFiniteType_grStructMap (k : Type u) [Field k] (d r : ℕ) :
    LocallyOfFiniteType (grStructMap k d r) := by
  apply IsZariskiLocalAtSource.of_openCover (glueData k d r).openCover
  intro i
  rw [show (glueData k d r).openCover.f i ≫ grStructMap k d r
      = Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d r i.down.1))) from
    ι_grStructMap k d r i]
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

end AlgebraicGeometry.Grassmannian
