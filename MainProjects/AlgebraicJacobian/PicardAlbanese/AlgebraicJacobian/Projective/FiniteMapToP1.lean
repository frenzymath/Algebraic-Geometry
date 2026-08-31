/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Projective.FiniteMapProjectiveImmersion

/-!
# Projectivity from a finite map to the projective line

The projective-coordinate morphism attached to a finite map to `P1` is an
immersion by target-locality on its two distinguished charts. A proper source
is therefore projective over the base field.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.P1FiniteMap.FiniteMapGenerators

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))} {pi : C.left ⟶ P1 k}
variable (G : P1FiniteMap.FiniteMapGenerators pi)

/-- The two distinguished target charts cover the image. -/
theorem range_subset_targetOpen_sup :
    Set.range G.toProjectiveSpace ⊆
      (G.targetOpen0 ⊔ G.targetOpen1 : _) := by
  rintro _ ⟨x, rfl⟩
  have hx : x ∈
      (pi ⁻¹ᵁ P1.chartOpen k 0) ⊔ (pi ⁻¹ᵁ P1.chartOpen k 1) := by
    rw [show (pi ⁻¹ᵁ P1.chartOpen k 0) ⊔ (pi ⁻¹ᵁ P1.chartOpen k 1) = ⊤ by
      change pi ⁻¹ᵁ (P1.chartOpen k 0 ⊔ P1.chartOpen k 1) = ⊤
      rw [P1.chartOpen_sup]
      rfl]
    trivial
  rw [TopologicalSpace.Opens.mem_sup] at hx
  change G.toProjectiveSpace x ∈ G.targetOpen0 ⊔ G.targetOpen1
  rw [TopologicalSpace.Opens.mem_sup]
  rcases hx with hx | hx
  · left
    change x ∈ G.toProjectiveSpace ⁻¹ᵁ G.targetOpen0
    rwa [G.preimage_targetOpen0]
  · right
    change x ∈ G.toProjectiveSpace ⁻¹ᵁ G.targetOpen1
    rwa [G.preimage_targetOpen1]

/-- Replace a canonical restriction by one to an equal source open. -/
def restrictionIsoResLE {X Z : Scheme.{u}} (f : X ⟶ Z)
    (U : Z.Opens) (V : X.Opens) (h : f ⁻¹ᵁ U = V) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk (f.resLE U V h.ge) :=
  Arrow.isoMk (X.isoOfEq h) (Iso.refl _) (by
    change (X.isoOfEq h).hom ≫ (X.homOfLE _ ≫ f ∣_ U) =
      (f ∣_ U) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc]
    rw [show X.homOfLE _ = (X.isoOfEq h).inv by
      rw [← cancel_mono (f ⁻¹ᵁ U).ι, Scheme.homOfLE_ι,
        Scheme.isoOfEq_inv_ι], Iso.hom_inv_id, Category.id_comp])

/-- Transport a restriction through an isomorphism of its target open. -/
def restrictionIsoChart {X Z A : Scheme.{u}} (f : X ⟶ Z)
    (U : Z.Opens) (V : X.Opens) (hpre : f ⁻¹ᵁ U = V)
    (e : U.toScheme ≅ A) (g : V.toScheme ⟶ A)
    (hfactor : f.resLE U V hpre.ge ≫ e.hom = g) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk g :=
  restrictionIsoResLE f U V hpre ≪≫
    Arrow.isoMk (Iso.refl V.toScheme) e (by
      change 𝟙 V.toScheme ≫ g = f.resLE U V _ ≫ e.hom
      rw [Category.id_comp]
      convert hfactor.symm)

/-- The first restricted map is the first chart factor. -/
theorem resLE_targetOpen0_iso_eq_chartFactor0 :
    G.toProjectiveSpace.resLE G.targetOpen0
          (pi ⁻¹ᵁ P1.chartOpen k 0) G.preimage_targetOpen0.ge ≫
        G.targetOpen0IsoAffineChartAt.hom =
      G.chartFactor0 := by
  rw [← cancel_mono
    (ProjectiveSpace.affineChartAt.incl
      G.ProjectiveIndex G.firstIndex (Spec (.of k)))]
  simp only [Category.assoc]
  rw [G.targetOpen0IsoAffineChartAt_hom_incl]
  rw [Scheme.Hom.resLE_comp_ι]
  rw [G.chartFactor0_incl]

/-- The second restricted map is the second chart factor. -/
theorem resLE_targetOpen1_iso_eq_chartFactor1 :
    G.toProjectiveSpace.resLE G.targetOpen1
          (pi ⁻¹ᵁ P1.chartOpen k 1) G.preimage_targetOpen1.ge ≫
        G.targetOpen1IsoAffineChartAt.hom =
      G.chartFactor1 := by
  rw [← cancel_mono
    (ProjectiveSpace.affineChartAt.incl
      G.ProjectiveIndex G.secondIndex (Spec (.of k)))]
  simp only [Category.assoc]
  rw [G.targetOpen1IsoAffineChartAt_hom_incl]
  rw [Scheme.Hom.resLE_comp_ι]
  rw [G.chartFactor1_incl]

/-- The restriction to the first target chart is a closed immersion. -/
theorem isClosedImmersion_restrict_targetOpen0
    (hpi : pi ≫ P1.structureMap k = C.hom) [IsFinite pi] :
    IsClosedImmersion (G.toProjectiveSpace ∣_ G.targetOpen0) := by
  rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
    (restrictionIsoChart G.toProjectiveSpace G.targetOpen0
      (pi ⁻¹ᵁ P1.chartOpen k 0) G.preimage_targetOpen0
        G.targetOpen0IsoAffineChartAt G.chartFactor0
          G.resLE_targetOpen0_iso_eq_chartFactor0)]
  exact G.isClosedImmersion_chartFactor0 hpi

/-- The restriction to the second target chart is a closed immersion. -/
theorem isClosedImmersion_restrict_targetOpen1
    (hpi : pi ≫ P1.structureMap k = C.hom) [IsFinite pi] :
    IsClosedImmersion (G.toProjectiveSpace ∣_ G.targetOpen1) := by
  rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
    (restrictionIsoChart G.toProjectiveSpace G.targetOpen1
      (pi ⁻¹ᵁ P1.chartOpen k 1) G.preimage_targetOpen1
        G.targetOpen1IsoAffineChartAt G.chartFactor1
          G.resLE_targetOpen1_iso_eq_chartFactor1)]
  exact G.isClosedImmersion_chartFactor1 hpi

/-- The global projective-coordinate morphism is an immersion. -/
theorem isImmersion_toProjectiveSpace
    (hpi : pi ≫ P1.structureMap k = C.hom) [IsFinite pi] :
    IsImmersion G.toProjectiveSpace := by
  letI : MorphismProperty.RespectsRight
      (@IsImmersion) (@IsOpenImmersion) := ⟨fun i hi f hf => by
    letI : IsOpenImmersion i := hi
    letI : IsImmersion f := hf
    infer_instance⟩
  apply IsZariskiLocalAtTarget.of_range_subset_iSup
    (P := @IsImmersion)
      (fun b : Bool => bif b then G.targetOpen0 else G.targetOpen1)
  · intro y hy
    have hy' := G.range_subset_targetOpen_sup hy
    change y ∈ G.targetOpen0 ⊔ G.targetOpen1 at hy'
    rw [TopologicalSpace.Opens.mem_sup] at hy'
    change y ∈
      (⨆ b : Bool, bif b then G.targetOpen0 else G.targetOpen1)
    rw [TopologicalSpace.Opens.mem_iSup]
    rcases hy' with hy' | hy'
    · exact ⟨true, by simpa⟩
    · exact ⟨false, by simpa⟩
  · intro b
    cases b
    · haveI : IsClosedImmersion
          (G.toProjectiveSpace ∣_ G.targetOpen1) :=
        G.isClosedImmersion_restrict_targetOpen1 hpi
      simpa using (inferInstance : IsImmersion
        (G.toProjectiveSpace ∣_ G.targetOpen1))
    · haveI : IsClosedImmersion
          (G.toProjectiveSpace ∣_ G.targetOpen0) :=
        G.isClosedImmersion_restrict_targetOpen0 hpi
      simpa using (inferInstance : IsImmersion
        (G.toProjectiveSpace ∣_ G.targetOpen0))

include G

set_option maxHeartbeats 800000 in
-- The target-local proof elaborates through two nested pullback presentations.
/-- A proper source with a finite map to `P1` is projective. -/
theorem isProjective (hpi : pi ≫ P1.structureMap k = C.hom)
    [IsFinite pi] [IsProper C.hom] : C.hom.IsProjective := by
  exact Scheme.Hom.IsProjective.of_isProper_of_immersion
    (pi := C.hom) (by infer_instance) G.toProjectiveSpace
      (G.isImmersion_toProjectiveSpace hpi) G.toProjectiveSpace_over

end AlgebraicGeometry.P1FiniteMap.FiniteMapGenerators

namespace AlgebraicGeometry

/-- A proper scheme finite over `P1` is projective over the base field. -/
theorem isProjective_of_isFinite_toP1
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom) [IsProper C.hom] :
    C.hom.IsProjective := by
  obtain ⟨G⟩ := P1FiniteMap.nonempty_finiteMapGenerators pi
  exact G.isProjective hpi

end AlgebraicGeometry
