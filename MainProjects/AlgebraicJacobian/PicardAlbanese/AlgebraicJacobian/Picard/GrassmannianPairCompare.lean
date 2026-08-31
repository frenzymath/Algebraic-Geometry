/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianChartCompare
import AlgebraicJacobian.Picard.DivCarveLocus

/-!
# Cross-chart comparison for the Grassmannian pair (G-5, W2)

The pair version of the W1 cross-chart converse (`informal/w4-g5-worksheet.md` §3.1
W2): two pair-chart maps — over possibly different pair charts — that pull the two
tautological pair points back to the same Grassmannian points present the same
morphism `Spec B ⟶ grPair`.

`grPair` is a `Limits.pullback`, so `pullback.hom_ext` reduces to the two projections;
`pairChartMap_fst`/`_snd` rewrite each composite into a chart-immersion composite, and
W1 (`specMap_ι_eq_of_map_chartTautologicalPoint_eq`) closes each leg.

* `AlgebraicGeometry.Grassmannian.specMap_pairChartMap_eq_of_map_includeLR_eq`: the
  core, with hypotheses in the `includeLeft`/`includeRight` composite form.
* `AlgebraicGeometry.specMap_pairChartMap_eq_of_map_pairTaut_eq`: **W2** in the
  `pairTautFst`/`pairTautSnd` spelling consumed by the G-5 stitch.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.Grassmannian

section PairCompare

open CategoryTheory Limits

variable (k : Type u) [Field k] (d₁ r₁ d₂ r₂ : ℕ)

/-- **W2, core form**: two pair-chart maps pulling both tautological chart points back
equally (in the `includeLeft`/`includeRight` composite spelling) present the same
morphism to the Grassmannian pair.  `pullback.hom_ext` + `pairChartMap_fst/snd` + W1
on each factor. -/
theorem specMap_pairChartMap_eq_of_map_includeLR_eq
    (i i' : (glueData k d₁ r₁).J) (j j' : (glueData k d₂ r₂).J)
    {B : Type u} [CommRing B] [Algebra k B]
    (w : PairChartRing k d₁ r₁ d₂ r₂ i j →ₐ[k] B)
    (w' : PairChartRing k d₁ r₁ d₂ r₂ i' j' →ₐ[k] B)
    (h₁ : Module.Grassmannian.map (w.comp (Algebra.TensorProduct.includeLeft (S := k)))
        (chartTautologicalPoint k d₁ r₁ i.down.1 i.down.2)
      = Module.Grassmannian.map (w'.comp (Algebra.TensorProduct.includeLeft (S := k)))
          (chartTautologicalPoint k d₁ r₁ i'.down.1 i'.down.2))
    (h₂ : Module.Grassmannian.map (w.comp Algebra.TensorProduct.includeRight)
        (chartTautologicalPoint k d₂ r₂ j.down.1 j.down.2)
      = Module.Grassmannian.map (w'.comp Algebra.TensorProduct.includeRight)
          (chartTautologicalPoint k d₂ r₂ j'.down.1 j'.down.2)) :
    Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k d₁ r₁ d₂ r₂ i j
      = Spec.map (CommRingCat.ofHom w'.toRingHom) ≫ pairChartMap k d₁ r₁ d₂ r₂ i' j' := by
  refine Limits.pullback.hom_ext ?_ ?_
  · -- first projection: W1 on the first Grassmannian
    have hW1 := specMap_ι_eq_of_map_chartTautologicalPoint_eq k d₁ r₁ i i'
      (w.comp (Algebra.TensorProduct.includeLeft (S := k)))
      (w'.comp (Algebra.TensorProduct.includeLeft (S := k))) h₁
    rw [show CommRingCat.ofHom
          (w.comp (Algebra.TensorProduct.includeLeft (S := k))).toRingHom
        = CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := k)) ≫
          CommRingCat.ofHom w.toRingHom from rfl,
      show CommRingCat.ofHom
          (w'.comp (Algebra.TensorProduct.includeLeft (S := k))).toRingHom
        = CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := k)) ≫
          CommRingCat.ofHom w'.toRingHom from rfl,
      Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc] at hW1
    change (Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k d₁ r₁ d₂ r₂ i j)
        ≫ grPairFst k d₁ r₁ d₂ r₂
      = (Spec.map (CommRingCat.ofHom w'.toRingHom) ≫ pairChartMap k d₁ r₁ d₂ r₂ i' j')
        ≫ grPairFst k d₁ r₁ d₂ r₂
    rw [Category.assoc, Category.assoc, pairChartMap_fst, pairChartMap_fst]
    exact hW1
  · -- second projection: W1 on the second Grassmannian
    have hW1 := specMap_ι_eq_of_map_chartTautologicalPoint_eq k d₂ r₂ j j'
      (w.comp Algebra.TensorProduct.includeRight)
      (w'.comp Algebra.TensorProduct.includeRight) h₂
    rw [show CommRingCat.ofHom
          (w.comp (Algebra.TensorProduct.includeRight (R := k)
            (A := ChartRing k d₁ r₁ i.down.1)
            (B := ChartRing k d₂ r₂ j.down.1))).toRingHom
        = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k)).toRingHom ≫
          CommRingCat.ofHom w.toRingHom from rfl,
      show CommRingCat.ofHom
          (w'.comp (Algebra.TensorProduct.includeRight (R := k)
            (A := ChartRing k d₁ r₁ i'.down.1)
            (B := ChartRing k d₂ r₂ j'.down.1))).toRingHom
        = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k)).toRingHom ≫
          CommRingCat.ofHom w'.toRingHom from rfl,
      Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc] at hW1
    change (Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k d₁ r₁ d₂ r₂ i j)
        ≫ grPairSnd k d₁ r₁ d₂ r₂
      = (Spec.map (CommRingCat.ofHom w'.toRingHom) ≫ pairChartMap k d₁ r₁ d₂ r₂ i' j')
        ≫ grPairSnd k d₁ r₁ d₂ r₂
    rw [Category.assoc, Category.assoc, pairChartMap_snd, pairChartMap_snd]
    exact hW1

end PairCompare

end AlgebraicGeometry.Grassmannian

namespace AlgebraicGeometry

section PairTaut

open CategoryTheory Grassmannian

variable (k : Type u) [Field k] (g r₁ r₂ : ℕ)

/-- **W2 — the pair cross-chart converse** (`informal/w4-g5-worksheet.md` §3.1), in the
`pairTautFst`/`pairTautSnd` spelling consumed by the G-5 overlap agreement: two
pair-chart maps pulling the tautological pair back to the same pair of Grassmannian
points present the same morphism `Spec B ⟶ grPair`. -/
theorem specMap_pairChartMap_eq_of_map_pairTaut_eq
    (i i' : (glueData k g r₁).J) (j j' : (glueData k g r₂).J)
    {B : Type u} [CommRing B] [Algebra k B]
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] B)
    (w' : PairChartRing k g r₁ g r₂ i' j' →ₐ[k] B)
    (h₁ : Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)
        = Module.Grassmannian.map w' (pairTautFst k g r₁ r₂ i' j'))
    (h₂ : Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)
        = Module.Grassmannian.map w' (pairTautSnd k g r₁ r₂ i' j')) :
    Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j
      = Spec.map (CommRingCat.ofHom w'.toRingHom) ≫ pairChartMap k g r₁ g r₂ i' j' := by
  refine specMap_pairChartMap_eq_of_map_includeLR_eq k g r₁ g r₂ i i' j j' w w' ?_ ?_
  · rw [pairTautFst, pairTautFst, ← Module.Grassmannian.map_comp,
      ← Module.Grassmannian.map_comp] at h₁
    exact h₁
  · rw [pairTautSnd, pairTautSnd, ← Module.Grassmannian.map_comp,
      ← Module.Grassmannian.map_comp] at h₂
    exact h₂

end PairTaut

end AlgebraicGeometry
