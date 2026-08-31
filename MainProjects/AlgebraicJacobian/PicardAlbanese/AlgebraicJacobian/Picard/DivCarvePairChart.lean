/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianTautologicalCocycle
import AlgebraicJacobian.Picard.GrassmannianChartFrame
import AlgebraicJacobian.Picard.GrassmannianScheme
import AlgebraicJacobian.Picard.GrassmannianPair

/-!
# The pair charts of the Grassmannian pair: compatibility and hom-ext (DDR-1 support + DDR-7)

The Grassmannian-side chart layer of the DD-R carve locus
(`informal/spec-dd-r.md` §2 verdict B, §3 items 1/6); the module-algebra substrate is
`Picard/DivCarveKit.lean`.

* **Chart compatibility** (`map_chartTautologicalPoint_eq_of_specMap_ι_eq`): two affine
  chart maps presenting the same morphism to the glued Grassmannian pull the tautological
  points back equally — the scheme-level form of the landed GL-cocycle
  (`map_transitionPreMap_chartTautologicalPoint`): the morphism factors through the chart
  overlap (`pullbackιIso`), with no new gluing.
* **The pair charts** (`PairChartRing`, `pairChartMap`, `pairChartMap_fst/snd`): the
  affine atlas `Spec (R^I ⊗[k] R^J) ⟶ grPair` of the Grassmannian pair, with its two
  chart projections, and the pair form of chart compatibility
  (`map_includeLeft/Right_chartTautologicalPoint_eq_of_specMap_pairChartMap_eq`).
* **DDR-7 hom-ext** (`algHom_ext_of_map_chartTautologicalPoint_eq`,
  `grPair_hom_ext_of_frame`): two chart maps (resp. two morphisms to `grPair` through a
  common pair chart) with equal pulled-back tautological frame data are equal —
  `MvPolynomial.algHom_ext` + `exists_isUnit_mul_of_matrixPoint_eq`.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.Grassmannian


/-! ## Chart compatibility of the tautological family in the glued scheme -/

section ChartCompat

open CategoryTheory Limits

variable (k : Type u) [Field k] (d r : ℕ)

/-- **Chart compatibility of the tautological family**: two affine chart maps presenting
the same morphism to the glued Grassmannian pull the tautological points back equally.
The scheme-level form of the landed GL-cocycle compatibility: the morphism factors
through the chart overlap (`pullbackιIso`), where the two pullbacks are matched by
`map_transitionPreMap_chartTautologicalPoint`. -/
theorem map_chartTautologicalPoint_eq_of_specMap_ι_eq
    (i i' : (glueData k d r).J) {B : Type u} [CommRing B] [Algebra k B]
    (a : ChartRing k d r i.down.1 →ₐ[k] B) (a' : ChartRing k d r i'.down.1 →ₐ[k] B)
    (h : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (glueData k d r).ι i
       = Spec.map (CommRingCat.ofHom a'.toRingHom) ≫ (glueData k d r).ι i') :
    Module.Grassmannian.map a (chartTautologicalPoint k d r i.down.1 i.down.2)
      = Module.Grassmannian.map a' (chartTautologicalPoint k d r i'.down.1 i'.down.2) := by
  set φ : Spec (CommRingCat.of B) ⟶ Limits.pullback ((glueData k d r).ι i)
      ((glueData k d r).ι i') := Limits.pullback.lift _ _ h
  have hfst : φ ≫ Limits.pullback.fst _ _ = Spec.map (CommRingCat.ofHom a.toRingHom) :=
    Limits.pullback.lift_fst _ _ _
  have hsnd : φ ≫ Limits.pullback.snd _ _ = Spec.map (CommRingCat.ofHom a'.toRingHom) :=
    Limits.pullback.lift_snd _ _ _
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (φ ≫ (pullbackιIso k d r i i').hom)
  have hchart1 : (pullbackιIso k d r i i').hom ≫
        chartIncl k d r i.down.1 i'.down.1 i.down.2 i'.down.2
      = Limits.pullback.fst ((glueData k d r).ι i) ((glueData k d r).ι i') :=
    (congrArg ((pullbackιIso k d r i i').hom ≫ ·)
      (pullbackιIso_inv_fst k d r i i').symm).trans
      (Iso.hom_inv_id_assoc (pullbackιIso k d r i i') _)
  have hchart2 : (pullbackιIso k d r i i').hom ≫
        (chartTransition k d r i.down.1 i'.down.1 i.down.2 i'.down.2 ≫
          chartIncl k d r i'.down.1 i.down.1 i'.down.2 i.down.2)
      = Limits.pullback.snd ((glueData k d r).ι i) ((glueData k d r).ι i') :=
    (congrArg ((pullbackιIso k d r i i').hom ≫ ·)
      (pullbackιIso_inv_snd k d r i i').symm).trans
      (Iso.hom_inv_id_assoc (pullbackιIso k d r i i') _)
  -- leg 1: `ψ` restricted along the localization is `a`
  have hleg1 : CommRingCat.ofHom (algebraMap (ChartRing k d r i.down.1)
      (Localization.Away (minorDet k d r i.down.1 i'.down.1 i.down.2 i'.down.2))) ≫ ψ
      = CommRingCat.ofHom a.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, Category.assoc]
    exact (congrArg (φ ≫ ·) hchart1).trans hfst
  -- leg 2: `ψ` composed with the transition pre-hom is `a'`
  have hleg2 : CommRingCat.ofHom
      (transitionPreMap k d r i.down.1 i'.down.1 i.down.2 i'.down.2).toRingHom ≫ ψ
      = CommRingCat.ofHom a'.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, Category.assoc]
    refine Eq.trans ?_ ((congrArg (φ ≫ ·) hchart2).trans hsnd)
    exact congrArg (φ ≫ (pullbackιIso k d r i i').hom ≫ ·)
      (chartTransition_comp_chartIncl k d r i.down.1 i'.down.1 i.down.2 i'.down.2).symm
  -- ring-level forms
  have hleg1r : ψ.hom.comp (algebraMap (ChartRing k d r i.down.1)
      (Localization.Away (minorDet k d r i.down.1 i'.down.1 i.down.2 i'.down.2)))
      = a.toRingHom := congrArg CommRingCat.Hom.hom hleg1
  have hleg2r : ψ.hom.comp
      (transitionPreMap k d r i.down.1 i'.down.1 i.down.2 i'.down.2).toRingHom
      = a'.toRingHom := congrArg CommRingCat.Hom.hom hleg2
  -- `ψ` is a `k`-algebra hom
  have hcommutes : ∀ c : k, ψ.hom (algebraMap k
      (Localization.Away (minorDet k d r i.down.1 i'.down.1 i.down.2 i'.down.2)) c)
      = algebraMap k B c := fun c => by
    rw [IsScalarTower.algebraMap_apply k (ChartRing k d r i.down.1)
      (Localization.Away (minorDet k d r i.down.1 i'.down.1 i.down.2 i'.down.2)),
      show ψ.hom ((algebraMap (ChartRing k d r i.down.1)
          (Localization.Away (minorDet k d r i.down.1 i'.down.1 i.down.2 i'.down.2)))
          (algebraMap k (ChartRing k d r i.down.1) c))
        = (ψ.hom.comp (algebraMap (ChartRing k d r i.down.1)
          (Localization.Away (minorDet k d r i.down.1 i'.down.1 i.down.2 i'.down.2))))
          (algebraMap k (ChartRing k d r i.down.1) c) from rfl,
      hleg1r]
    exact a.commutes c
  set ψa : Localization.Away (minorDet k d r i.down.1 i'.down.1 i.down.2 i'.down.2) →ₐ[k] B :=
    { toRingHom := ψ.hom, commutes' := hcommutes } with hψa
  have hψa1 : ψa.comp (Algebra.algHom k (ChartRing k d r i.down.1)
      (Localization.Away (minorDet k d r i.down.1 i'.down.1 i.down.2 i'.down.2))) = a :=
    AlgHom.coe_ringHom_injective hleg1r
  have hψa2 : ψa.comp (transitionPreMap k d r i.down.1 i'.down.1 i.down.2 i'.down.2) = a' :=
    AlgHom.coe_ringHom_injective hleg2r
  calc Module.Grassmannian.map a (chartTautologicalPoint k d r i.down.1 i.down.2)
      = Module.Grassmannian.map (ψa.comp (Algebra.algHom k (ChartRing k d r i.down.1)
          (Localization.Away (minorDet k d r i.down.1 i'.down.1 i.down.2 i'.down.2))))
          (chartTautologicalPoint k d r i.down.1 i.down.2) := by rw [hψa1]
    _ = Module.Grassmannian.map ψa (Module.Grassmannian.map
          (Algebra.algHom k (ChartRing k d r i.down.1)
            (Localization.Away (minorDet k d r i.down.1 i'.down.1 i.down.2 i'.down.2)))
          (chartTautologicalPoint k d r i.down.1 i.down.2)) := by
        rw [Module.Grassmannian.map_comp]
    _ = Module.Grassmannian.map ψa (Module.Grassmannian.map
          (transitionPreMap k d r i.down.1 i'.down.1 i.down.2 i'.down.2)
          (chartTautologicalPoint k d r i'.down.1 i'.down.2)) := by
        rw [map_transitionPreMap_chartTautologicalPoint]
    _ = Module.Grassmannian.map
          (ψa.comp (transitionPreMap k d r i.down.1 i'.down.1 i.down.2 i'.down.2))
          (chartTautologicalPoint k d r i'.down.1 i'.down.2) := by
        rw [Module.Grassmannian.map_comp]
    _ = Module.Grassmannian.map a' (chartTautologicalPoint k d r i'.down.1 i'.down.2) := by
        rw [hψa2]

end ChartCompat

/-! ## The pair charts of the Grassmannian pair -/

section PairChart

open CategoryTheory Limits

variable (k : Type u) [Field k] (d₁ r₁ d₂ r₂ : ℕ)

/-- The chart ring of the Grassmannian pair at a pair of chart indices:
`R_{I,J} = R^I ⊗[k] R^J`. -/
abbrev PairChartRing (i : (glueData k d₁ r₁).J) (j : (glueData k d₂ r₂).J) : Type u :=
  TensorProduct k (ChartRing k d₁ r₁ i.down.1) (ChartRing k d₂ r₂ j.down.1)

/-- The affine pair chart of the Grassmannian pair:
`Spec (R^I ⊗[k] R^J) ⟶ grPair`, the `grPairPatchIso`-twisted patch inclusion of the
product atlas `grPairCover`. -/
noncomputable def pairChartMap (i : (glueData k d₁ r₁).J) (j : (glueData k d₂ r₂).J) :
    Spec (CommRingCat.of (PairChartRing k d₁ r₁ d₂ r₂ i j)) ⟶ grPair k d₁ r₁ d₂ r₂ :=
  (grPairPatchIso k d₁ r₁ d₂ r₂ i j).inv ≫ (grPairCover k d₁ r₁ d₂ r₂).f (i, j)

instance isOpenImmersion_pairChartMap (i : (glueData k d₁ r₁).J) (j : (glueData k d₂ r₂).J) :
    IsOpenImmersion (pairChartMap k d₁ r₁ d₂ r₂ i j) := by
  haveI h1 := (grPairCover k d₁ r₁ d₂ r₂).map_prop (i, j)
  exact @IsOpenImmersion.comp _ _ _ (grPairPatchIso k d₁ r₁ d₂ r₂ i j).inv
    ((grPairCover k d₁ r₁ d₂ r₂).f (i, j)) inferInstance h1

/-- The first projection of a pair chart: through `grPairFst`, the pair chart maps to the
chart `U^I` of the first Grassmannian by the left inclusion `R^I → R^I ⊗ R^J`. -/
theorem pairChartMap_fst (i : (glueData k d₁ r₁).J) (j : (glueData k d₂ r₂).J) :
    pairChartMap k d₁ r₁ d₂ r₂ i j ≫ grPairFst k d₁ r₁ d₂ r₂
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := k)
            (A := ChartRing k d₁ r₁ i.down.1) (B := ChartRing k d₂ r₂ j.down.1)))
        ≫ (glueData k d₁ r₁).ι i := by
  have hcov : (grPairCover k d₁ r₁ d₂ r₂).f (i, j) ≫
        Limits.pullback.fst (grStructMap k d₁ r₁) (grStructMap k d₂ r₂)
      = Limits.pullback.fst ((glueData k d₁ r₁).openCover.f i ≫ grStructMap k d₁ r₁)
          ((glueData k d₂ r₂).openCover.f j ≫ grStructMap k d₂ r₂)
        ≫ (glueData k d₁ r₁).openCover.f i := by
    simp only [grPairCover, Scheme.Pullback.openCoverOfLeftRight]
    exact Limits.pullback.lift_fst _ _ _
  have hcongr : (Limits.pullback.congrHom (ι_grStructMap k d₁ r₁ i)
        (ι_grStructMap k d₂ r₂ j)).inv ≫
        Limits.pullback.fst ((glueData k d₁ r₁).openCover.f i ≫ grStructMap k d₁ r₁)
          ((glueData k d₂ r₂).openCover.f j ≫ grStructMap k d₂ r₂)
      = Limits.pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d₁ r₁ i.down.1))))
          (Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d₂ r₂ j.down.1)))) := by
    have h1 := Limits.pullback.congrHom_inv (ι_grStructMap k d₁ r₁ i) (ι_grStructMap k d₂ r₂ j)
    refine Eq.trans (congrArg (· ≫ Limits.pullback.fst _ _) h1) ?_
    refine Eq.trans (Limits.pullback.lift_fst _ _ _) (Category.comp_id _)
  have hpatch : (grPairPatchIso k d₁ r₁ d₂ r₂ i j).inv ≫
        Limits.pullback.fst ((glueData k d₁ r₁).openCover.f i ≫ grStructMap k d₁ r₁)
          ((glueData k d₂ r₂).openCover.f j ≫ grStructMap k d₂ r₂)
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := k)
          (A := ChartRing k d₁ r₁ i.down.1) (B := ChartRing k d₂ r₂ j.down.1))) := by
    exact (Category.assoc _ _ _).trans
      ((congrArg ((pullbackSpecIso k (ChartRing k d₁ r₁ i.down.1)
        (ChartRing k d₂ r₂ j.down.1)).inv ≫ ·) hcongr).trans
        (pullbackSpecIso_inv_fst k _ _))
  calc pairChartMap k d₁ r₁ d₂ r₂ i j ≫ grPairFst k d₁ r₁ d₂ r₂
      = (grPairPatchIso k d₁ r₁ d₂ r₂ i j).inv ≫
          ((grPairCover k d₁ r₁ d₂ r₂).f (i, j) ≫
            Limits.pullback.fst (grStructMap k d₁ r₁) (grStructMap k d₂ r₂)) :=
        Category.assoc _ _ _
    _ = (grPairPatchIso k d₁ r₁ d₂ r₂ i j).inv ≫
          (Limits.pullback.fst ((glueData k d₁ r₁).openCover.f i ≫ grStructMap k d₁ r₁)
            ((glueData k d₂ r₂).openCover.f j ≫ grStructMap k d₂ r₂)
          ≫ (glueData k d₁ r₁).openCover.f i) :=
        congrArg ((grPairPatchIso k d₁ r₁ d₂ r₂ i j).inv ≫ ·) hcov
    _ = ((grPairPatchIso k d₁ r₁ d₂ r₂ i j).inv ≫
          Limits.pullback.fst ((glueData k d₁ r₁).openCover.f i ≫ grStructMap k d₁ r₁)
            ((glueData k d₂ r₂).openCover.f j ≫ grStructMap k d₂ r₂))
          ≫ (glueData k d₁ r₁).openCover.f i :=
        (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := k)
            (A := ChartRing k d₁ r₁ i.down.1) (B := ChartRing k d₂ r₂ j.down.1)))
        ≫ (glueData k d₁ r₁).openCover.f i :=
        congrArg (· ≫ (glueData k d₁ r₁).openCover.f i) hpatch

/-- The second projection of a pair chart: through `grPairSnd`, the pair chart maps to
the chart `U^J` of the second Grassmannian by the right inclusion `R^J → R^I ⊗ R^J`. -/
theorem pairChartMap_snd (i : (glueData k d₁ r₁).J) (j : (glueData k d₂ r₂).J) :
    pairChartMap k d₁ r₁ d₂ r₂ i j ≫ grPairSnd k d₁ r₁ d₂ r₂
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := k)
            (A := ChartRing k d₁ r₁ i.down.1) (B := ChartRing k d₂ r₂ j.down.1)).toRingHom)
        ≫ (glueData k d₂ r₂).ι j := by
  have hcov : (grPairCover k d₁ r₁ d₂ r₂).f (i, j) ≫
        Limits.pullback.snd (grStructMap k d₁ r₁) (grStructMap k d₂ r₂)
      = Limits.pullback.snd ((glueData k d₁ r₁).openCover.f i ≫ grStructMap k d₁ r₁)
          ((glueData k d₂ r₂).openCover.f j ≫ grStructMap k d₂ r₂)
        ≫ (glueData k d₂ r₂).openCover.f j := by
    simp only [grPairCover, Scheme.Pullback.openCoverOfLeftRight]
    exact Limits.pullback.lift_snd _ _ _
  have hcongr : (Limits.pullback.congrHom (ι_grStructMap k d₁ r₁ i)
        (ι_grStructMap k d₂ r₂ j)).inv ≫
        Limits.pullback.snd ((glueData k d₁ r₁).openCover.f i ≫ grStructMap k d₁ r₁)
          ((glueData k d₂ r₂).openCover.f j ≫ grStructMap k d₂ r₂)
      = Limits.pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d₁ r₁ i.down.1))))
          (Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d₂ r₂ j.down.1)))) := by
    have h1 := Limits.pullback.congrHom_inv (ι_grStructMap k d₁ r₁ i) (ι_grStructMap k d₂ r₂ j)
    refine Eq.trans (congrArg (· ≫ Limits.pullback.snd _ _) h1) ?_
    refine Eq.trans (Limits.pullback.lift_snd _ _ _) (Category.comp_id _)
  have hpatch : (grPairPatchIso k d₁ r₁ d₂ r₂ i j).inv ≫
        Limits.pullback.snd ((glueData k d₁ r₁).openCover.f i ≫ grStructMap k d₁ r₁)
          ((glueData k d₂ r₂).openCover.f j ≫ grStructMap k d₂ r₂)
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k)
          (A := ChartRing k d₁ r₁ i.down.1) (B := ChartRing k d₂ r₂ j.down.1)).toRingHom) := by
    exact (Category.assoc _ _ _).trans
      ((congrArg ((pullbackSpecIso k (ChartRing k d₁ r₁ i.down.1)
        (ChartRing k d₂ r₂ j.down.1)).inv ≫ ·) hcongr).trans
        (pullbackSpecIso_inv_snd k _ _))
  calc pairChartMap k d₁ r₁ d₂ r₂ i j ≫ grPairSnd k d₁ r₁ d₂ r₂
      = (grPairPatchIso k d₁ r₁ d₂ r₂ i j).inv ≫
          ((grPairCover k d₁ r₁ d₂ r₂).f (i, j) ≫
            Limits.pullback.snd (grStructMap k d₁ r₁) (grStructMap k d₂ r₂)) :=
        Category.assoc _ _ _
    _ = (grPairPatchIso k d₁ r₁ d₂ r₂ i j).inv ≫
          (Limits.pullback.snd ((glueData k d₁ r₁).openCover.f i ≫ grStructMap k d₁ r₁)
            ((glueData k d₂ r₂).openCover.f j ≫ grStructMap k d₂ r₂)
          ≫ (glueData k d₂ r₂).openCover.f j) :=
        congrArg ((grPairPatchIso k d₁ r₁ d₂ r₂ i j).inv ≫ ·) hcov
    _ = ((grPairPatchIso k d₁ r₁ d₂ r₂ i j).inv ≫
          Limits.pullback.snd ((glueData k d₁ r₁).openCover.f i ≫ grStructMap k d₁ r₁)
            ((glueData k d₂ r₂).openCover.f j ≫ grStructMap k d₂ r₂))
          ≫ (glueData k d₂ r₂).openCover.f j :=
        (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := k)
            (A := ChartRing k d₁ r₁ i.down.1) (B := ChartRing k d₂ r₂ j.down.1)).toRingHom)
        ≫ (glueData k d₂ r₂).openCover.f j :=
        congrArg (· ≫ (glueData k d₂ r₂).openCover.f j) hpatch

/-- **Pair-chart compatibility, first factor**: two pair-chart maps presenting the same
morphism to `grPair` pull the first tautological point back equally. -/
theorem map_includeLeft_chartTautologicalPoint_eq_of_specMap_pairChartMap_eq
    {i i' : (glueData k d₁ r₁).J} {j j' : (glueData k d₂ r₂).J}
    {B : Type u} [CommRing B] [Algebra k B]
    (w : PairChartRing k d₁ r₁ d₂ r₂ i j →ₐ[k] B)
    (w' : PairChartRing k d₁ r₁ d₂ r₂ i' j' →ₐ[k] B)
    (h : Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k d₁ r₁ d₂ r₂ i j
       = Spec.map (CommRingCat.ofHom w'.toRingHom) ≫ pairChartMap k d₁ r₁ d₂ r₂ i' j') :
    Module.Grassmannian.map (w.comp (Algebra.TensorProduct.includeLeft (S := k)))
        (chartTautologicalPoint k d₁ r₁ i.down.1 i.down.2)
      = Module.Grassmannian.map (w'.comp (Algebra.TensorProduct.includeLeft (S := k)))
          (chartTautologicalPoint k d₁ r₁ i'.down.1 i'.down.2) := by
  apply map_chartTautologicalPoint_eq_of_specMap_ι_eq k d₁ r₁ i i'
  have h1 := congrArg (· ≫ grPairFst k d₁ r₁ d₂ r₂) h
  simp only [Category.assoc] at h1
  rw [pairChartMap_fst, pairChartMap_fst] at h1
  rw [show CommRingCat.ofHom (w.comp (Algebra.TensorProduct.includeLeft (S := k))).toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := k)) ≫
        CommRingCat.ofHom w.toRingHom from rfl,
    show CommRingCat.ofHom (w'.comp (Algebra.TensorProduct.includeLeft (S := k))).toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := k)) ≫
        CommRingCat.ofHom w'.toRingHom from rfl,
    Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
  exact h1

/-- **Pair-chart compatibility, second factor**: two pair-chart maps presenting the same
morphism to `grPair` pull the second tautological point back equally. -/
theorem map_includeRight_chartTautologicalPoint_eq_of_specMap_pairChartMap_eq
    {i i' : (glueData k d₁ r₁).J} {j j' : (glueData k d₂ r₂).J}
    {B : Type u} [CommRing B] [Algebra k B]
    (w : PairChartRing k d₁ r₁ d₂ r₂ i j →ₐ[k] B)
    (w' : PairChartRing k d₁ r₁ d₂ r₂ i' j' →ₐ[k] B)
    (h : Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k d₁ r₁ d₂ r₂ i j
       = Spec.map (CommRingCat.ofHom w'.toRingHom) ≫ pairChartMap k d₁ r₁ d₂ r₂ i' j') :
    Module.Grassmannian.map (w.comp Algebra.TensorProduct.includeRight)
        (chartTautologicalPoint k d₂ r₂ j.down.1 j.down.2)
      = Module.Grassmannian.map (w'.comp Algebra.TensorProduct.includeRight)
          (chartTautologicalPoint k d₂ r₂ j'.down.1 j'.down.2) := by
  apply map_chartTautologicalPoint_eq_of_specMap_ι_eq k d₂ r₂ j j'
  have h1 := congrArg (· ≫ grPairSnd k d₁ r₁ d₂ r₂) h
  simp only [Category.assoc] at h1
  rw [pairChartMap_snd, pairChartMap_snd] at h1
  rw [show CommRingCat.ofHom (w.comp (Algebra.TensorProduct.includeRight (R := k)
        (A := ChartRing k d₁ r₁ i.down.1) (B := ChartRing k d₂ r₂ j.down.1))).toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k)).toRingHom ≫
        CommRingCat.ofHom w.toRingHom from rfl,
    show CommRingCat.ofHom (w'.comp (Algebra.TensorProduct.includeRight (R := k)
        (A := ChartRing k d₁ r₁ i'.down.1) (B := ChartRing k d₂ r₂ j'.down.1))).toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k)).toRingHom ≫
        CommRingCat.ofHom w'.toRingHom from rfl,
    Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
  exact h1

end PairChart

/-! ## DDR-7: hom-ext from tautological frame data -/

section HomExt

variable (k : Type u) [Field k] (d r : ℕ)

/-- **Chart-map extensionality from the tautological pullback** (DDR-7): two chart maps
`R^I →ₐ[k] S` pulling the tautological point back equally are equal.  The two mapped
universal matrices present the same point, so they differ by a `GL_d` factor
(`exists_isUnit_mul_of_matrixPoint_eq`) which is the identity on the `I`-minor; the free
entries then pin the maps on the `MvPolynomial` generators. -/
theorem algHom_ext_of_map_chartTautologicalPoint_eq (I : Finset (Fin r)) (hI : I.card = d)
    {S : Type u} [CommRing S] [Algebra k S] (w w' : ChartRing k d r I →ₐ[k] S)
    (h : Module.Grassmannian.map w (chartTautologicalPoint k d r I hI)
       = Module.Grassmannian.map w' (chartTautologicalPoint k d r I hI)) : w = w' := by
  have hs : Function.Surjective (matrixProj k d r S ((universalMatrix k d r I hI).map w)) :=
    matrixProj_surjective_map k d r w (universalMatrix k d r I hI)
      (chartTautologicalProj_surjective k d r I hI)
  have hs' : Function.Surjective (matrixProj k d r S ((universalMatrix k d r I hI).map w')) :=
    matrixProj_surjective_map k d r w' (universalMatrix k d r I hI)
      (chartTautologicalProj_surjective k d r I hI)
  have h1 : matrixPoint k d r S ((universalMatrix k d r I hI).map w) hs
      = matrixPoint k d r S ((universalMatrix k d r I hI).map w') hs' := by
    rw [← map_matrixPoint k d r w (universalMatrix k d r I hI)
        (chartTautologicalProj_surjective k d r I hI) hs,
      ← map_matrixPoint k d r w' (universalMatrix k d r I hI)
        (chartTautologicalProj_surjective k d r I hI) hs',
      ← chartTautologicalPoint_eq_matrixPoint]
    exact h
  obtain ⟨U, hU, hUeq⟩ := exists_isUnit_mul_of_matrixPoint_eq k d r S _ _ hs hs' h1
  have hminor : frameMinor k d r S ((universalMatrix k d r I hI).map w) I hI = 1 := by
    rw [frameMinor, Matrix.submatrix_map, universalMatrix_submatrix_self,
      Matrix.map_one _ (map_zero w) (map_one w)]
  have hminor' : frameMinor k d r S ((universalMatrix k d r I hI).map w') I hI = 1 := by
    rw [frameMinor, Matrix.submatrix_map, universalMatrix_submatrix_self,
      Matrix.map_one _ (map_zero w') (map_one w')]
  have hU1 : U = 1 := by
    have h2 : frameMinor k d r S ((universalMatrix k d r I hI).map w) I hI
        = frameMinor k d r S (U * (universalMatrix k d r I hI).map w') I hI := by
      rw [← hUeq]
    rw [hminor, frameMinor, mul_submatrix_col] at h2
    rw [show (((universalMatrix k d r I hI).map w').submatrix id
        (fun j => (I.orderIsoOfFin hI j : Fin r)))
      = frameMinor k d r S ((universalMatrix k d r I hI).map w') I hI from rfl, hminor',
      Matrix.mul_one] at h2
    exact h2.symm
  have hXeq : (universalMatrix k d r I hI).map w = (universalMatrix k d r I hI).map w' := by
    rw [hUeq, hU1, Matrix.one_mul]
  apply MvPolynomial.algHom_ext
  intro e
  have h3 := congrFun (congrFun hXeq e.1) e.2.1
  rwa [Matrix.map_apply, Matrix.map_apply,
    show universalMatrix k d r I hI e.1 e.2.1 = MvPolynomial.X e from by
      rw [universalMatrix, dif_neg e.2.2]] at h3

end HomExt

section PairHomExt

variable (k : Type u) [Field k] (d₁ r₁ d₂ r₂ : ℕ)

/-- **The pair-chart hom-ext** (DDR-7, `grPair_hom_ext_of_frame`): two morphisms from an
affine test through a common pair chart of `grPair` agreeing on the pulled-back
tautological frame data are equal — indeed the two chart maps themselves agree. -/
theorem grPair_hom_ext_of_frame
    (i : (glueData k d₁ r₁).J) (j : (glueData k d₂ r₂).J)
    {S : Type u} [CommRing S] [Algebra k S]
    (w w' : PairChartRing k d₁ r₁ d₂ r₂ i j →ₐ[k] S)
    (h₁ : Module.Grassmannian.map (w.comp (Algebra.TensorProduct.includeLeft (S := k)))
        (chartTautologicalPoint k d₁ r₁ i.down.1 i.down.2)
      = Module.Grassmannian.map (w'.comp (Algebra.TensorProduct.includeLeft (S := k)))
          (chartTautologicalPoint k d₁ r₁ i.down.1 i.down.2))
    (h₂ : Module.Grassmannian.map (w.comp Algebra.TensorProduct.includeRight)
        (chartTautologicalPoint k d₂ r₂ j.down.1 j.down.2)
      = Module.Grassmannian.map (w'.comp Algebra.TensorProduct.includeRight)
          (chartTautologicalPoint k d₂ r₂ j.down.1 j.down.2)) :
    w = w' := by
  apply Algebra.TensorProduct.ext
  · exact algHom_ext_of_map_chartTautologicalPoint_eq k d₁ r₁ i.down.1 i.down.2 _ _ h₁
  · exact algHom_ext_of_map_chartTautologicalPoint_eq k d₂ r₂ j.down.1 j.down.2 _ _ h₂

end PairHomExt

end AlgebraicGeometry.Grassmannian
