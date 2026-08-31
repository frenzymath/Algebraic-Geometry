/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Projective.FiniteMapProjectiveGluing

/-!
# Local projective charts for a finite map to the projective line

The two distinguished homogeneous coordinates cut out target charts whose
inverse images are the two pulled-back standard charts of `P1`. On each chart,
the global relative coordinate morphism is the closed immersion supplied by
the algebra-generating coordinate family.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization
  TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.P1FiniteMap.FiniteMapGenerators

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))} {pi : C.left ⟶ P1 k}
variable (G : P1FiniteMap.FiniteMapGenerators pi)

noncomputable local instance : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

noncomputable local instance sourceOpenAlgebra (U : C.left.Opens) :
    Algebra k Γ(C.left, U) :=
  (C.left.overAlgebraMap k U).toAlgebra

/-- The coordinate normalized to one on the first source chart. -/
abbrev firstIndex : G.ProjectiveIndex :=
  Sum.inl ⟨0, Nat.zero_lt_succ G.d⟩

/-- The coordinate normalized to one on the second source chart. -/
abbrev secondIndex : G.ProjectiveIndex :=
  Sum.inl ⟨G.d, Nat.lt_succ_self G.d⟩

/-- The target chart selected by the first distinguished coordinate. -/
def targetOpen0 : (ℙ(G.ProjectiveIndex; Spec (.of k))).Opens :=
  ProjectiveSpace.toProjInt G.ProjectiveIndex (Spec (.of k)) ⁻¹ᵁ
    Proj.basicOpen
      (homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ)) (X G.firstIndex)

/-- The target chart selected by the second distinguished coordinate. -/
def targetOpen1 : (ℙ(G.ProjectiveIndex; Spec (.of k))).Opens :=
  ProjectiveSpace.toProjInt G.ProjectiveIndex (Spec (.of k)) ⁻¹ᵁ
    Proj.basicOpen
      (homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ)) (X G.secondIndex)

/-- The first target open is the corresponding relative affine chart. -/
def targetOpen0IsoAffineChartAt :
    G.targetOpen0.toScheme ≅
      ProjectiveSpace.affineChartAt G.ProjectiveIndex G.firstIndex (Spec (.of k)) := by
  apply IsOpenImmersion.isoOfRangeEq G.targetOpen0.ι
    (ProjectiveSpace.affineChartAt.incl
      G.ProjectiveIndex G.firstIndex (Spec (.of k)))
  rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange,
    ProjectiveSpace.affineChartAt.opensRange_incl, targetOpen0]

/-- The second target open is the corresponding relative affine chart. -/
def targetOpen1IsoAffineChartAt :
    G.targetOpen1.toScheme ≅
      ProjectiveSpace.affineChartAt G.ProjectiveIndex G.secondIndex (Spec (.of k)) := by
  apply IsOpenImmersion.isoOfRangeEq G.targetOpen1.ι
    (ProjectiveSpace.affineChartAt.incl
      G.ProjectiveIndex G.secondIndex (Spec (.of k)))
  rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange,
    ProjectiveSpace.affineChartAt.opensRange_incl, targetOpen1]

@[reassoc]
theorem targetOpen0IsoAffineChartAt_hom_incl :
    G.targetOpen0IsoAffineChartAt.hom ≫
        ProjectiveSpace.affineChartAt.incl
          G.ProjectiveIndex G.firstIndex (Spec (.of k)) =
      G.targetOpen0.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc]
theorem targetOpen1IsoAffineChartAt_hom_incl :
    G.targetOpen1IsoAffineChartAt.hom ≫
        ProjectiveSpace.affineChartAt.incl
          G.ProjectiveIndex G.secondIndex (Spec (.of k)) =
      G.targetOpen1.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Removing the normalized coordinate preserves generation on chart zero. -/
theorem adjoin_projectiveCoordinates0_ne
    (hpi : pi ≫ P1.structureMap k = C.hom) :
    Algebra.adjoin k
      (Set.range fun j : {j : G.ProjectiveIndex // j ≠ G.firstIndex} ↦
        G.projectiveCoordinates0 j.1) = ⊤ := by
  have hfull := G.adjoin_chart0 hpi
  apply top_unique
  rw [← hfull]
  apply Algebra.adjoin_le
  rintro z ⟨j, rfl⟩
  by_cases hj : j = G.firstIndex
  · subst j
    change G.projectiveCoordinates0 G.firstIndex ∈ _
    rw [G.projectiveCoordinates0_zero]
    exact Subalgebra.one_mem _
  · exact Algebra.subset_adjoin ⟨⟨j, hj⟩, rfl⟩

/-- Removing the normalized coordinate preserves generation on chart one. -/
theorem adjoin_projectiveCoordinates1_ne
    (hpi : pi ≫ P1.structureMap k = C.hom) :
    Algebra.adjoin k
      (Set.range fun j : {j : G.ProjectiveIndex // j ≠ G.secondIndex} ↦
        G.projectiveCoordinates1 j.1) = ⊤ := by
  have hfull := G.adjoin_chart1 hpi
  apply top_unique
  rw [← hfull]
  apply Algebra.adjoin_le
  rintro z ⟨j, rfl⟩
  by_cases hj : j = G.secondIndex
  · subst j
    change G.projectiveCoordinates1 G.secondIndex ∈ _
    rw [G.projectiveCoordinates1_last]
    exact Subalgebra.one_mem _
  · exact Algebra.subset_adjoin ⟨⟨j, hj⟩, rfl⟩

/-- Sections on an open and global sections of its open subscheme agree. -/
def openSectionsEquiv (U : C.left.Opens) :
    Γ(C.left, U) ≃+* Γ(U.toScheme, ⊤) :=
  (asIso (U.ι.appLE U ⊤ U.ι_preimage_self.ge)).commRingCatIsoToRingEquiv

/-- The open-sections equivalence respects the structural algebra map. -/
theorem openSectionsEquiv_algebraMap (U : C.left.Opens) (c : k) :
    openSectionsEquiv U (algebraMap k Γ(C.left, U) c) =
      (U.ι ≫ C.hom).appTop.hom
        ((Scheme.ΓSpecIso (.of k)).inv.hom c) := by
  change (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom
      (algebraMap k Γ(C.left, U) c) = _
  have hL : algebraMap k Γ(C.left, U) c =
      (C.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        (C.hom.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)) := rfl
  rw [hL]
  change (C.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
      U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom
        (C.hom.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)) = _
  rw [Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop]
  simp only [Scheme.Hom.appLE, Scheme.Hom.preimage_top, homOfLE_refl,
    op_id, CommRingCat.comp_apply]
  have hid := congrArg
    (fun q : Γ(U.toScheme, ⊤) ⟶ Γ(U.toScheme, ⊤) ↦ q.hom
      (U.ι.appTop.hom (C.hom.appTop.hom
        ((Scheme.ΓSpecIso (.of k)).inv.hom c))))
    (U.toScheme.presheaf.map_id (Opposite.op (⊤ : U.toScheme.Opens)))
  simpa using hid

theorem topIso_inv_eq_appLE (U : C.left.Opens) :
    U.topIso.inv = U.ι.appLE U ⊤ U.ι_preimage_self.ge := by
  rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
  rfl

/-- The spectrum structural map is the structural map of the open subscheme. -/
theorem toSpecΓ_specToBase (U : C.left.Opens) :
    U.toSpecΓ ≫
        ProjectiveSpace.Coordinates.specToBase
          (k := k) (B := Γ(C.left, U)) =
      U.ι ≫ C.hom := by
  apply ext_to_Spec
  ext c
  change (U.toSpecΓ ≫
      ProjectiveSpace.Coordinates.specToBase
        (k := k) (B := Γ(C.left, U))).appTop.hom
          ((Scheme.ΓSpecIso (.of k)).inv.hom c) =
    (U.ι ≫ C.hom).appTop.hom
      ((Scheme.ΓSpecIso (.of k)).inv.hom c)
  rw [Scheme.Hom.comp_appTop]
  change U.toSpecΓ.appTop.hom
      ((ProjectiveSpace.Coordinates.specToBase
        (k := k) (B := Γ(C.left, U))).appTop.hom
          ((Scheme.ΓSpecIso (.of k)).inv.hom c)) = _
  have hbase :
      (ProjectiveSpace.Coordinates.specToBase
        (k := k) (B := Γ(C.left, U))).appTop.hom
          ((Scheme.ΓSpecIso (.of k)).inv.hom c) =
        (Scheme.ΓSpecIso Γ(C.left, U)).inv.hom
          (algebraMap k Γ(C.left, U) c) := by
    rw [ProjectiveSpace.Coordinates.specToBase,
      ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply, ConcreteCategory.hom_ofHom]
    rw [Scheme.ΓSpecIso_inv, Scheme.ΓSpecIso_inv]
  rw [hbase, Scheme.Opens.toSpecΓ_appTop]
  rw [topIso_inv_eq_appLE U]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  change openSectionsEquiv U (algebraMap k Γ(C.left, U) c) = _
  exact openSectionsEquiv_algebraMap U c

/-- The global map factored through the first relative affine chart. -/
def chartFactor0 :
    (pi ⁻¹ᵁ P1.chartOpen k 0).toScheme ⟶
      ProjectiveSpace.affineChartAt
        G.ProjectiveIndex G.firstIndex (Spec (.of k)) :=
  (pi ⁻¹ᵁ P1.chartOpen k 0).toSpecΓ ≫
    ProjectiveSpace.Coordinates.toAffineChartAt G.firstIndex
      G.projectiveCoordinates0 G.projectiveCoordinates0_zero

/-- The global map factored through the second relative affine chart. -/
def chartFactor1 :
    (pi ⁻¹ᵁ P1.chartOpen k 1).toScheme ⟶
      ProjectiveSpace.affineChartAt
        G.ProjectiveIndex G.secondIndex (Spec (.of k)) :=
  (pi ⁻¹ᵁ P1.chartOpen k 1).toSpecΓ ≫
    ProjectiveSpace.Coordinates.toAffineChartAt G.secondIndex
      G.projectiveCoordinates1 G.projectiveCoordinates1_last

@[reassoc]
theorem chartFactor0_incl :
    G.chartFactor0 ≫
        ProjectiveSpace.affineChartAt.incl
          G.ProjectiveIndex G.firstIndex (Spec (.of k)) =
      (pi ⁻¹ᵁ P1.chartOpen k 0).ι ≫ G.toProjectiveSpace := by
  rw [chartFactor0, Category.assoc,
    ProjectiveSpace.Coordinates.toAffineChartAt_incl]
  apply pullback.hom_ext
  · change ((pi ⁻¹ᵁ P1.chartOpen k 0).toSpecΓ ≫
        ProjectiveSpace.Coordinates.relativeFromSpec G.firstIndex
          G.projectiveCoordinates0 G.projectiveCoordinates0_zero) ≫
        (ℙ(G.ProjectiveIndex; Spec (.of k)) ↘ Spec (.of k)) =
      ((pi ⁻¹ᵁ P1.chartOpen k 0).ι ≫ G.toProjectiveSpace) ≫
        (ℙ(G.ProjectiveIndex; Spec (.of k)) ↘ Spec (.of k))
    rw [Category.assoc, ProjectiveSpace.Coordinates.relativeFromSpec_over,
      toSpecΓ_specToBase (k := k) (C := C), Category.assoc,
      G.toProjectiveSpace_over]
  · change ((pi ⁻¹ᵁ P1.chartOpen k 0).toSpecΓ ≫
        ProjectiveSpace.Coordinates.relativeFromSpec G.firstIndex
          G.projectiveCoordinates0 G.projectiveCoordinates0_zero) ≫
        ProjectiveSpace.toProjInt G.ProjectiveIndex (Spec (.of k)) =
      ((pi ⁻¹ᵁ P1.chartOpen k 0).ι ≫ G.toProjectiveSpace) ≫
        ProjectiveSpace.toProjInt G.ProjectiveIndex (Spec (.of k))
    rw [Category.assoc,
      ProjectiveSpace.Coordinates.relativeFromSpec_toProjInt,
      Category.assoc, G.toProjectiveSpace_toProjInt, G.open0_toProjInt]
    rfl

@[reassoc]
theorem chartFactor1_incl :
    G.chartFactor1 ≫
        ProjectiveSpace.affineChartAt.incl
          G.ProjectiveIndex G.secondIndex (Spec (.of k)) =
      (pi ⁻¹ᵁ P1.chartOpen k 1).ι ≫ G.toProjectiveSpace := by
  rw [chartFactor1, Category.assoc,
    ProjectiveSpace.Coordinates.toAffineChartAt_incl]
  apply pullback.hom_ext
  · change ((pi ⁻¹ᵁ P1.chartOpen k 1).toSpecΓ ≫
        ProjectiveSpace.Coordinates.relativeFromSpec G.secondIndex
          G.projectiveCoordinates1 G.projectiveCoordinates1_last) ≫
        (ℙ(G.ProjectiveIndex; Spec (.of k)) ↘ Spec (.of k)) =
      ((pi ⁻¹ᵁ P1.chartOpen k 1).ι ≫ G.toProjectiveSpace) ≫
        (ℙ(G.ProjectiveIndex; Spec (.of k)) ↘ Spec (.of k))
    rw [Category.assoc, ProjectiveSpace.Coordinates.relativeFromSpec_over,
      toSpecΓ_specToBase (k := k) (C := C), Category.assoc,
      G.toProjectiveSpace_over]
  · change ((pi ⁻¹ᵁ P1.chartOpen k 1).toSpecΓ ≫
        ProjectiveSpace.Coordinates.relativeFromSpec G.secondIndex
          G.projectiveCoordinates1 G.projectiveCoordinates1_last) ≫
        ProjectiveSpace.toProjInt G.ProjectiveIndex (Spec (.of k)) =
      ((pi ⁻¹ᵁ P1.chartOpen k 1).ι ≫ G.toProjectiveSpace) ≫
        ProjectiveSpace.toProjInt G.ProjectiveIndex (Spec (.of k))
    rw [Category.assoc,
      ProjectiveSpace.Coordinates.relativeFromSpec_toProjInt,
      Category.assoc, G.toProjectiveSpace_toProjInt, G.open1_toProjInt]
    rfl

/-- The first local chart factor is a closed immersion. -/
theorem isClosedImmersion_chartFactor0
    (hpi : pi ≫ P1.structureMap k = C.hom) [IsFinite pi] :
    IsClosedImmersion G.chartFactor0 := by
  letI : IsAffine (pi ⁻¹ᵁ P1.chartOpen k 0).toScheme :=
    (P1.isAffineOpen_chartOpen k 0).preimage pi
  letI : IsIso (pi ⁻¹ᵁ P1.chartOpen k 0).toSpecΓ := by
    dsimp [Scheme.Opens.toSpecΓ]
    infer_instance
  apply MorphismProperty.comp_mem @IsClosedImmersion
  · infer_instance
  · exact ProjectiveSpace.Coordinates.isClosedImmersion_toAffineChartAt
      G.firstIndex G.projectiveCoordinates0
        G.projectiveCoordinates0_zero (G.adjoin_projectiveCoordinates0_ne hpi)

/-- The second local chart factor is a closed immersion. -/
theorem isClosedImmersion_chartFactor1
    (hpi : pi ≫ P1.structureMap k = C.hom) [IsFinite pi] :
    IsClosedImmersion G.chartFactor1 := by
  letI : IsAffine (pi ⁻¹ᵁ P1.chartOpen k 1).toScheme :=
    (P1.isAffineOpen_chartOpen k 1).preimage pi
  letI : IsIso (pi ⁻¹ᵁ P1.chartOpen k 1).toSpecΓ := by
    dsimp [Scheme.Opens.toSpecΓ]
    infer_instance
  apply MorphismProperty.comp_mem @IsClosedImmersion
  · infer_instance
  · exact ProjectiveSpace.Coordinates.isClosedImmersion_toAffineChartAt
      G.secondIndex G.projectiveCoordinates1
        G.projectiveCoordinates1_last (G.adjoin_projectiveCoordinates1_ne hpi)

/-- The inverse image of the first distinguished target chart is chart zero. -/
theorem preimage_targetOpen0 :
    G.toProjectiveSpace ⁻¹ᵁ G.targetOpen0 =
      pi ⁻¹ᵁ P1.chartOpen k 0 := by
  rw [targetOpen0, ← Scheme.Hom.comp_preimage,
    G.toProjectiveSpace_toProjInt]
  ext x
  constructor
  · intro hx
    have hcover : x ∈
        (pi ⁻¹ᵁ P1.chartOpen k 0) ⊔ (pi ⁻¹ᵁ P1.chartOpen k 1) := by
      rw [show (pi ⁻¹ᵁ P1.chartOpen k 0) ⊔ (pi ⁻¹ᵁ P1.chartOpen k 1) = ⊤ by
        change pi ⁻¹ᵁ (P1.chartOpen k 0 ⊔ P1.chartOpen k 1) = ⊤
        rw [P1.chartOpen_sup]
        rfl]
      trivial
    rw [TopologicalSpace.Opens.mem_sup] at hcover
    rcases hcover with hx0 | hx1
    · exact hx0
    · let x1 : (pi ⁻¹ᵁ P1.chartOpen k 1).toScheme := ⟨x, hx1⟩
      have hmap : G.toProjInt x = G.localProjectiveMap1 x1 := by
        change G.toProjInt ((pi ⁻¹ᵁ P1.chartOpen k 1).ι x1) =
          G.localProjectiveMap1 x1
        rw [← Scheme.Hom.comp_apply, G.open1_toProjInt]
      have hlocal : G.localProjectiveMap1 x1 ∈
          Proj.basicOpen
            (homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ))
              (X G.firstIndex) := by
        rwa [← hmap]
      change x1 ∈ G.localProjectiveMap1 ⁻¹ᵁ
        Proj.basicOpen
          (homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ))
            (X G.firstIndex) at hlocal
      have hbasic : x ∈ C.left.basicOpen ((pullbackCoord1 pi) ^ G.d) := by
        rw [show G.localProjectiveMap1 ⁻¹ᵁ
            Proj.basicOpen
              (homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ))
                (X G.firstIndex) =
            (pi ⁻¹ᵁ P1.chartOpen k 1).ι ⁻¹ᵁ
              C.left.basicOpen (G.projectiveCoordinates1 G.firstIndex) by
          exact ProjectiveSpace.Coordinates.fromOpen_preimage_basicOpen
            (pi ⁻¹ᵁ P1.chartOpen k 1) G.secondIndex G.firstIndex
              G.projectiveCoordinates1 G.projectiveCoordinates1_last] at hlocal
        change x ∈ C.left.basicOpen
          (G.projectiveCoordinates1 G.firstIndex) at hlocal
        simpa [projectiveCoordinates1, firstIndex,
          AlgebraicJacobian.TwoChart.TwistedCoordinates.chart1] using hlocal
      rw [C.left.basicOpen_pow (pullbackCoord1 pi) G.pos] at hbasic
      have hW1 : pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1) =
          C.left.basicOpen (pullbackCoord1 pi) := by
        have h := Scheme.preimage_basicOpen pi (coord1 (k := k))
        rw [basicOpen_coord1] at h
        exact h
      rw [← hW1] at hbasic
      exact hbasic.1
  · intro hx0
    let x0 : (pi ⁻¹ᵁ P1.chartOpen k 0).toScheme := ⟨x, hx0⟩
    have hmap : G.toProjInt x = G.localProjectiveMap0 x0 := by
      change G.toProjInt ((pi ⁻¹ᵁ P1.chartOpen k 0).ι x0) =
        G.localProjectiveMap0 x0
      rw [← Scheme.Hom.comp_apply, G.open0_toProjInt]
    change G.toProjInt x ∈
      Proj.basicOpen
        (homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ))
          (X G.firstIndex)
    rw [hmap]
    change x0 ∈ G.localProjectiveMap0 ⁻¹ᵁ
      Proj.basicOpen
        (homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ))
          (X G.firstIndex)
    simp [localProjectiveMap0,
      ProjectiveSpace.Coordinates.fromOpen_preimage_basicOpen]

/-- The inverse image of the second distinguished target chart is chart one. -/
theorem preimage_targetOpen1 :
    G.toProjectiveSpace ⁻¹ᵁ G.targetOpen1 =
      pi ⁻¹ᵁ P1.chartOpen k 1 := by
  rw [targetOpen1, ← Scheme.Hom.comp_preimage,
    G.toProjectiveSpace_toProjInt]
  ext x
  constructor
  · intro hx
    have hcover : x ∈
        (pi ⁻¹ᵁ P1.chartOpen k 0) ⊔ (pi ⁻¹ᵁ P1.chartOpen k 1) := by
      rw [show (pi ⁻¹ᵁ P1.chartOpen k 0) ⊔ (pi ⁻¹ᵁ P1.chartOpen k 1) = ⊤ by
        change pi ⁻¹ᵁ (P1.chartOpen k 0 ⊔ P1.chartOpen k 1) = ⊤
        rw [P1.chartOpen_sup]
        rfl]
      trivial
    rw [TopologicalSpace.Opens.mem_sup] at hcover
    rcases hcover with hx0 | hx1
    · let x0 : (pi ⁻¹ᵁ P1.chartOpen k 0).toScheme := ⟨x, hx0⟩
      have hmap : G.toProjInt x = G.localProjectiveMap0 x0 := by
        change G.toProjInt ((pi ⁻¹ᵁ P1.chartOpen k 0).ι x0) =
          G.localProjectiveMap0 x0
        rw [← Scheme.Hom.comp_apply, G.open0_toProjInt]
      have hlocal : G.localProjectiveMap0 x0 ∈
          Proj.basicOpen
            (homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ))
              (X G.secondIndex) := by
        rwa [← hmap]
      change x0 ∈ G.localProjectiveMap0 ⁻¹ᵁ
        Proj.basicOpen
          (homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ))
            (X G.secondIndex) at hlocal
      have hbasic : x ∈ C.left.basicOpen ((pullbackCoord0 pi) ^ G.d) := by
        rw [show G.localProjectiveMap0 ⁻¹ᵁ
            Proj.basicOpen
              (homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ))
                (X G.secondIndex) =
            (pi ⁻¹ᵁ P1.chartOpen k 0).ι ⁻¹ᵁ
              C.left.basicOpen (G.projectiveCoordinates0 G.secondIndex) by
          exact ProjectiveSpace.Coordinates.fromOpen_preimage_basicOpen
            (pi ⁻¹ᵁ P1.chartOpen k 0) G.firstIndex G.secondIndex
              G.projectiveCoordinates0 G.projectiveCoordinates0_zero] at hlocal
        change x ∈ C.left.basicOpen
          (G.projectiveCoordinates0 G.secondIndex) at hlocal
        simpa [projectiveCoordinates0, secondIndex,
          AlgebraicJacobian.TwoChart.TwistedCoordinates.chart0] using hlocal
      rw [C.left.basicOpen_pow (pullbackCoord0 pi) G.pos] at hbasic
      have hW0 : pi ⁻¹ᵁ (P1.chartOpen k 0 ⊓ P1.chartOpen k 1) =
          C.left.basicOpen (pullbackCoord0 pi) := by
        have h := Scheme.preimage_basicOpen pi (coord0 (k := k))
        rw [basicOpen_coord0] at h
        exact h
      rw [← hW0] at hbasic
      exact hbasic.2
    · exact hx1
  · intro hx1
    let x1 : (pi ⁻¹ᵁ P1.chartOpen k 1).toScheme := ⟨x, hx1⟩
    have hmap : G.toProjInt x = G.localProjectiveMap1 x1 := by
      change G.toProjInt ((pi ⁻¹ᵁ P1.chartOpen k 1).ι x1) =
        G.localProjectiveMap1 x1
      rw [← Scheme.Hom.comp_apply, G.open1_toProjInt]
    change G.toProjInt x ∈
      Proj.basicOpen
        (homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ))
          (X G.secondIndex)
    rw [hmap]
    change x1 ∈ G.localProjectiveMap1 ⁻¹ᵁ
      Proj.basicOpen
        (homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ))
          (X G.secondIndex)
    simp [localProjectiveMap1,
      ProjectiveSpace.Coordinates.fromOpen_preimage_basicOpen]

end AlgebraicGeometry.P1FiniteMap.FiniteMapGenerators
