/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivScheme
import AlgebraicJacobian.Cohomology.SectionsBaseChange

/-!
# `KeyChart`: the chart value of the carve ideal sheaf (DDR-9.F0)

The one DDR-1 gap of `Picard/DivScheme.lean` (`informal/w4-ddr9-worksheet.md` §3.2):

* `AlgebraicGeometry.Grassmannian.pairChartOpen`, `pairChartΓ`: the pair chart as an
  affine open of `grPair`, and the sections identification `Γ(grPair, U_{I,J}) ⟶ R_{I,J}`
  (an isomorphism); `pairChartMap_grPairStructMap` is the chart structure triangle.
* **KeyChart** (`carveIdealSheaf_ideal_pairChartOpen`; campaign form
  `ker_divSchemeι_ideal_pairChartOpen`):
  `(carveIdealSheaf μ).ideal U_{I,J} = (carveIdeal μ I J).comap pairChartΓ`.  The `≤` half
  is the self-term kernel computation; the `≥` half tests membership at every stalk of
  every chart locus through `Scheme.fromSpecStalk` and discharges it by the landed gluing
  compatibility (`carveIdeal_le_ker_of_specMap_pairChartMap_eq`) — no new gluing.
* **Over packaging** (`carveSchemeOver_triangle_of_chartCover`, `carveSchemeOverHomMk`,
  campaign `divSchemeOverHomMk`): a test morphism `v : Spec S ⟶ Z(♦)` presented over a
  spanning family through pair charts by `k`-algebra maps is automatically a morphism
  `overSpec k S ⟶ divSchemeOver` — the hom-set packaging of the worksheet §1.2.
-/

set_option autoImplicit false

universe u

open TensorProduct CategoryTheory

namespace AlgebraicGeometry

/-! ## A germ reading of `fromSpecStalk` -/

/-- The `appLE` of `Spec 𝒪_{X,z} ⟶ X` from a neighbourhood `V ∋ z` to the total space is
the germ at `z`, read through `ΓSpecIso`. -/
theorem Scheme.fromSpecStalk_appLE {X : Scheme.{u}} {V : X.Opens} {z : X} (hz : z ∈ V)
    (e : ⊤ ≤ X.fromSpecStalk z ⁻¹ᵁ V) :
    (X.fromSpecStalk z).appLE V ⊤ e
      = X.presheaf.germ V z hz ≫ (Scheme.ΓSpecIso (X.presheaf.stalk z)).inv := by
  change (X.fromSpecStalk z).app V
      ≫ (Spec (X.presheaf.stalk z)).presheaf.map (homOfLE e).op = _
  rw [Scheme.fromSpecStalk_app hz, Category.assoc, Category.assoc, ← Functor.map_comp,
    show (homOfLE (le_top (a := X.fromSpecStalk z ⁻¹ᵁ V))).op ≫ (homOfLE e).op
      = 𝟙 (Opposite.op (⊤ : (Spec (X.presheaf.stalk z)).Opens)) from rfl]
  exact congrArg (fun t => X.presheaf.germ V z hz
    ≫ (Scheme.ΓSpecIso (X.presheaf.stalk z)).inv ≫ t)
      (CategoryTheory.Functor.map_id _ _) |>.trans
    (congrArg (fun t => X.presheaf.germ V z hz ≫ t) (Category.comp_id _))

/-- A section whose pullback to `Spec 𝒪_{Z,z}` along a morphism `q : Z ⟶ Y` vanishes
(through `ΓSpecIso`) has vanishing germ at `z`: the `fromSpecStalk`-to-germ dictionary in
kill form. -/
theorem Scheme.germ_app_eq_zero_of_fromSpecStalk {Y Z : Scheme.{u}} (q : Z ⟶ Y)
    {U : Y.Opens} (s : Γ(Y, U)) {z : Z} (hz : z ∈ q ⁻¹ᵁ U)
    (e : ⊤ ≤ Z.fromSpecStalk z ⁻¹ᵁ (q ⁻¹ᵁ U))
    (h0 : (Scheme.ΓSpecIso (Z.presheaf.stalk z)).hom.hom
      (((Z.fromSpecStalk z ≫ q).appLE U ⊤ e).hom s) = 0) :
    (Z.presheaf.germ (q ⁻¹ᵁ U) z hz).hom ((q.app U).hom s) = 0 := by
  have hsplit : q.appLE U (q ⁻¹ᵁ U) le_rfl ≫ (Z.fromSpecStalk z).appLE (q ⁻¹ᵁ U) ⊤ e
      = (Z.fromSpecStalk z ≫ q).appLE U ⊤ e := Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h1 : ((Z.fromSpecStalk z ≫ q).appLE U ⊤ e).hom s
      = (Scheme.ΓSpecIso (Z.presheaf.stalk z)).inv.hom
          ((Z.presheaf.germ (q ⁻¹ᵁ U) z hz).hom ((q.app U).hom s)) :=
    calc ((Z.fromSpecStalk z ≫ q).appLE U ⊤ e).hom s
        = ((Z.fromSpecStalk z).appLE (q ⁻¹ᵁ U) ⊤ e).hom
            ((q.appLE U (q ⁻¹ᵁ U) le_rfl).hom s) :=
          (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hsplit) s).symm
      _ = ((Z.fromSpecStalk z).appLE (q ⁻¹ᵁ U) ⊤ e).hom ((q.app U).hom s) :=
          congrArg _ (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
            (Scheme.Hom.appLE_eq_app q)) s)
      _ = _ := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
            (Scheme.fromSpecStalk_appLE hz e)) _
  have h2 := (DFunLike.congr_arg
    (Scheme.ΓSpecIso (Z.presheaf.stalk z)).hom.hom h1).symm.trans h0
  exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso (Z.presheaf.stalk z)).inv_hom_id)
    ((Z.presheaf.germ (q ⁻¹ᵁ U) z hz).hom ((q.app U).hom s))).symm.trans h2

namespace Grassmannian

/-! ## The pair chart as an affine open, and its sections identification -/

section PairChartOpen

open Limits

variable (k : Type u) [Field k] (d₁ r₁ d₂ r₂ : ℕ)
variable (i : (glueData k d₁ r₁).J) (j : (glueData k d₂ r₂).J)

/-- **The pair-chart open** `U_{I,J} ⊆ grPair`: the range of the affine pair chart
`pairChartMap`, as an affine open of the Grassmannian pair. -/
noncomputable def pairChartOpen : (grPair k d₁ r₁ d₂ r₂).affineOpens :=
  ⟨(pairChartMap k d₁ r₁ d₂ r₂ i j).opensRange, isAffineOpen_opensRange _⟩

lemma top_le_preimage_pairChartOpen :
    ⊤ ≤ pairChartMap k d₁ r₁ d₂ r₂ i j ⁻¹ᵁ (pairChartOpen k d₁ r₁ d₂ r₂ i j).1 :=
  fun x _ => ⟨x, rfl⟩

/-- Any morphism factoring through the pair chart lands inside the pair-chart open. -/
lemma top_le_preimage_pairChartOpen_of_factor {B : CommRingCat.{u}}
    {u : Spec B ⟶ grPair k d₁ r₁ d₂ r₂}
    (φ : CommRingCat.of (PairChartRing k d₁ r₁ d₂ r₂ i j) ⟶ B)
    (hu : u = Spec.map φ ≫ pairChartMap k d₁ r₁ d₂ r₂ i j) :
    ⊤ ≤ u ⁻¹ᵁ (pairChartOpen k d₁ r₁ d₂ r₂ i j).1 := by
  subst hu
  exact fun x _ => ⟨(Spec.map φ) x, rfl⟩

/-- **The chart sections identification** `Γ(grPair, U_{I,J}) ⟶ R_{I,J}`: sections over
the pair-chart open, read back on the chart through the open immersion and `ΓSpecIso`.
An isomorphism (`isIso_pairChartΓ`); the `KeyChart` transport map. -/
noncomputable def pairChartΓ :
    Γ(grPair k d₁ r₁ d₂ r₂, (pairChartOpen k d₁ r₁ d₂ r₂ i j).1)
      ⟶ CommRingCat.of (PairChartRing k d₁ r₁ d₂ r₂ i j) :=
  (pairChartMap k d₁ r₁ d₂ r₂ i j).appLE (pairChartOpen k d₁ r₁ d₂ r₂ i j).1 ⊤
      (top_le_preimage_pairChartOpen k d₁ r₁ d₂ r₂ i j)
    ≫ (Scheme.ΓSpecIso (CommRingCat.of (PairChartRing k d₁ r₁ d₂ r₂ i j))).hom

instance isIso_pairChartΓ : IsIso (pairChartΓ k d₁ r₁ d₂ r₂ i j) := by
  rw [pairChartΓ, Scheme.Hom.appLE]
  haveI h1 : IsIso ((pairChartMap k d₁ r₁ d₂ r₂ i j).app
      (pairChartOpen k d₁ r₁ d₂ r₂ i j).1) :=
    Scheme.Hom.isIso_app _ _ le_rfl
  haveI h2 : IsIso ((Spec (CommRingCat.of (PairChartRing k d₁ r₁ d₂ r₂ i j))).presheaf.map
      (homOfLE (top_le_preimage_pairChartOpen k d₁ r₁ d₂ r₂ i j)).op) := by
    rw [show (homOfLE (top_le_preimage_pairChartOpen k d₁ r₁ d₂ r₂ i j)).op
        = eqToHom (congrArg Opposite.op
            ((top_le_preimage_pairChartOpen k d₁ r₁ d₂ r₂ i j).antisymm le_top).symm) from
      Subsingleton.elim _ _]
    infer_instance
  infer_instance

/-- **The chart structure triangle** (`pairChartMap_structMap` of I-0193): the pair chart
composed with the structure morphism of the Grassmannian pair is `Spec` of the structure
map of the pair-chart ring. -/
theorem pairChartMap_grPairStructMap :
    pairChartMap k d₁ r₁ d₂ r₂ i j ≫ grPairStructMap k d₁ r₁ d₂ r₂
      = Spec.map (CommRingCat.ofHom (algebraMap k (PairChartRing k d₁ r₁ d₂ r₂ i j))) :=
  have hring : CommRingCat.ofHom (algebraMap k (ChartRing k d₁ r₁ i.down.1))
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := k)
        (A := ChartRing k d₁ r₁ i.down.1) (B := ChartRing k d₂ r₂ j.down.1))
      = CommRingCat.ofHom (algebraMap k (PairChartRing k d₁ r₁ d₂ r₂ i j)) :=
    (CommRingCat.ofHom_comp _ _).symm.trans (congrArg CommRingCat.ofHom
      (AlgHom.comp_algebraMap (Algebra.TensorProduct.includeLeft (R := k) (S := k)
        (A := ChartRing k d₁ r₁ i.down.1) (B := ChartRing k d₂ r₂ j.down.1))))
  calc pairChartMap k d₁ r₁ d₂ r₂ i j ≫ grPairFst k d₁ r₁ d₂ r₂ ≫ grStructMap k d₁ r₁
      = (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := k)
            (A := ChartRing k d₁ r₁ i.down.1) (B := ChartRing k d₂ r₂ j.down.1)))
          ≫ (glueData k d₁ r₁).ι i) ≫ grStructMap k d₁ r₁ :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ grStructMap k d₁ r₁) (pairChartMap_fst k d₁ r₁ d₂ r₂ i j))
    _ = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := k)
            (A := ChartRing k d₁ r₁ i.down.1) (B := ChartRing k d₂ r₂ j.down.1)))
          ≫ Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k d₁ r₁ i.down.1))) :=
        (Category.assoc _ _ _).trans (congrArg (Spec.map _ ≫ ·) (ι_grStructMap k d₁ r₁ i))
    _ = Spec.map (CommRingCat.ofHom (algebraMap k (PairChartRing k d₁ r₁ d₂ r₂ i j))) :=
        (Spec.map_comp _ _).symm.trans (congrArg Spec.map hring)

/-- `Spec.map` naturality of `ΓSpecIso` in `appLE (⊤, ⊤)` form. -/
private lemma specMap_appLE_top_ΓSpecIso {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (e : ⊤ ≤ Spec.map φ ⁻¹ᵁ (⊤ : (Spec R).Opens)) :
    (Spec.map φ).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso S).hom
      = (Scheme.ΓSpecIso R).hom ≫ φ := by
  have h1 : (Spec.map φ).appLE ⊤ ⊤ e = (Spec.map φ).appTop := by
    change (Spec.map φ).app ⊤ ≫ (Spec S).presheaf.map (homOfLE e).op = (Spec.map φ).app ⊤
    rw [show (homOfLE e).op = 𝟙 (Opposite.op (⊤ : (Spec S).Opens)) from rfl]
    exact (congrArg ((Spec.map φ).app ⊤ ≫ ·)
      (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  rw [h1]
  exact Scheme.ΓSpecIso_naturality φ

/-- **The chart-sections workhorse**: a morphism `u : Spec B ⟶ grPair` presented through
the pair chart `(I, J)` by a ring map `φ : R_{I,J} ⟶ B` reads a section `s` of the chart
open as `φ` of its chart value `pairChartΓ s`. -/
theorem ΓSpecIso_hom_appLE_of_eq_specMap_pairChartMap {B : CommRingCat.{u}}
    (φ : CommRingCat.of (PairChartRing k d₁ r₁ d₂ r₂ i j) ⟶ B)
    {u : Spec B ⟶ grPair k d₁ r₁ d₂ r₂}
    (hu : u = Spec.map φ ≫ pairChartMap k d₁ r₁ d₂ r₂ i j)
    (e : ⊤ ≤ u ⁻¹ᵁ (pairChartOpen k d₁ r₁ d₂ r₂ i j).1)
    (s : Γ(grPair k d₁ r₁ d₂ r₂, (pairChartOpen k d₁ r₁ d₂ r₂ i j).1)) :
    (Scheme.ΓSpecIso B).hom
        ((u.appLE (pairChartOpen k d₁ r₁ d₂ r₂ i j).1 ⊤ e).hom s)
      = φ.hom ((pairChartΓ k d₁ r₁ d₂ r₂ i j).hom s) := by
  subst hu
  have hsplit : (pairChartMap k d₁ r₁ d₂ r₂ i j).appLE
        (pairChartOpen k d₁ r₁ d₂ r₂ i j).1 ⊤
        (top_le_preimage_pairChartOpen k d₁ r₁ d₂ r₂ i j)
        ≫ (Spec.map φ).appLE ⊤ ⊤ le_rfl
      = (Spec.map φ ≫ pairChartMap k d₁ r₁ d₂ r₂ i j).appLE
          (pairChartOpen k d₁ r₁ d₂ r₂ i j).1 ⊤ e :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h1 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hsplit.symm) s
  have h2 := DFunLike.congr_fun
    (congrArg CommRingCat.Hom.hom (specMap_appLE_top_ΓSpecIso φ le_rfl))
    (((pairChartMap k d₁ r₁ d₂ r₂ i j).appLE (pairChartOpen k d₁ r₁ d₂ r₂ i j).1 ⊤
      (top_le_preimage_pairChartOpen k d₁ r₁ d₂ r₂ i j)).hom s)
  exact (congrArg (Scheme.ΓSpecIso B).hom.hom h1).trans h2

end PairChartOpen

end Grassmannian

/-! ## KeyChart: the chart value of the carve ideal sheaf -/

section KeyChart

open Grassmannian

variable (k : Type u) [Field k] (g r₁ r₂ : ℕ)
variable {ι : Type u} (μ : ι → ((Fin r₁ → k) →ₗ[k] (Fin r₂ → k)))

/-- **Two chart presentations transport the carve kill** (a `CommRingCat` packaging of
`carveIdeal_le_ker_of_specMap_pairChartMap_eq`; the `k`-structure on `B` comes from the
presentations through the chart structure triangles). -/
theorem carveIdeal_le_ker_of_presentations
    {i i' : (glueData k g r₁).J} {j j' : (glueData k g r₂).J} {B : CommRingCat.{u}}
    {u : Spec B ⟶ grPair k g r₁ g r₂}
    (φ : CommRingCat.of (PairChartRing k g r₁ g r₂ i j) ⟶ B)
    (φ' : CommRingCat.of (PairChartRing k g r₁ g r₂ i' j') ⟶ B)
    (hφ : u = Spec.map φ ≫ pairChartMap k g r₁ g r₂ i j)
    (hφ' : u = Spec.map φ' ≫ pairChartMap k g r₁ g r₂ i' j')
    (hker : carveIdeal k g r₁ r₂ μ i' j' ≤ RingHom.ker φ'.hom) :
    carveIdeal k g r₁ r₂ μ i j ≤ RingHom.ker φ.hom := by
  letI : Algebra k ↑B :=
    (φ'.hom.comp (algebraMap k (PairChartRing k g r₁ g r₂ i' j'))).toAlgebra
  have hstruct : CommRingCat.ofHom (algebraMap k (PairChartRing k g r₁ g r₂ i j)) ≫ φ
      = CommRingCat.ofHom (algebraMap k (PairChartRing k g r₁ g r₂ i' j')) ≫ φ' := by
    apply Spec.map_injective
    calc Spec.map (CommRingCat.ofHom (algebraMap k (PairChartRing k g r₁ g r₂ i j)) ≫ φ)
        = Spec.map φ ≫ (pairChartMap k g r₁ g r₂ i j ≫ grPairStructMap k g r₁ g r₂) :=
          (Spec.map_comp _ _).trans (congrArg (Spec.map φ ≫ ·)
            (pairChartMap_grPairStructMap k g r₁ g r₂ i j).symm)
      _ = u ≫ grPairStructMap k g r₁ g r₂ :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ grPairStructMap k g r₁ g r₂) hφ.symm)
      _ = Spec.map φ' ≫ (pairChartMap k g r₁ g r₂ i' j' ≫ grPairStructMap k g r₁ g r₂) :=
          (congrArg (· ≫ grPairStructMap k g r₁ g r₂) hφ').trans (Category.assoc _ _ _)
      _ = Spec.map (CommRingCat.ofHom (algebraMap k (PairChartRing k g r₁ g r₂ i' j')) ≫ φ') :=
          (congrArg (Spec.map φ' ≫ ·)
            (pairChartMap_grPairStructMap k g r₁ g r₂ i' j')).trans (Spec.map_comp _ _).symm
  exact carveIdeal_le_ker_of_specMap_pairChartMap_eq k g r₁ r₂ μ
    (B := ↑B)
    (w := ⟨φ.hom, fun c =>
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hstruct) c⟩)
    (w' := ⟨φ'.hom, fun c => rfl⟩)
    (hφ.symm.trans hφ') hker

/-- **The `≥`-half germ vanish**: a section of the pair-chart open whose chart value lies
in the chart carve ideal is annihilated by every chart locus, germ by germ.  The test ring
at `z` is the stalk `𝒪_z`, presented through the `(I,J)`-chart by `IsOpenImmersion.lift`
of `fromSpecStalk` and through the `(I',J')`-chart by the quotient map into the stalk. -/
theorem germ_carveLocusToGrPair_app_pairChartOpen_eq_zero
    (i i' : (glueData k g r₁).J) (j j' : (glueData k g r₂).J)
    (s : Γ(grPair k g r₁ g r₂, (pairChartOpen k g r₁ g r₂ i j).1))
    (hs : (pairChartΓ k g r₁ g r₂ i j).hom s ∈ carveIdeal k g r₁ r₂ μ i j)
    (z : carveLocus k g r₁ r₂ μ i' j')
    (hz : z ∈ carveLocusToGrPair k g r₁ r₂ μ i' j' ⁻¹ᵁ (pairChartOpen k g r₁ g r₂ i j).1) :
    ((carveLocus k g r₁ r₂ μ i' j').presheaf.germ
        (carveLocusToGrPair k g r₁ r₂ μ i' j' ⁻¹ᵁ (pairChartOpen k g r₁ g r₂ i j).1) z hz).hom
      (((carveLocusToGrPair k g r₁ r₂ μ i' j').app (pairChartOpen k g r₁ g r₂ i j).1).hom s)
      = 0 := by
  -- every point of `Spec 𝒪_z` maps into the preimage of the chart open
  have hgen : ⊤ ≤ (carveLocus k g r₁ r₂ μ i' j').fromSpecStalk z
      ⁻¹ᵁ (carveLocusToGrPair k g r₁ r₂ μ i' j' ⁻¹ᵁ (pairChartOpen k g r₁ g r₂ i j).1) := by
    intro y _
    have h1 : ((carveLocus k g r₁ r₂ μ i' j').fromSpecStalk z) y ⤳ z := by
      have := Scheme.range_fromSpecStalk (X := carveLocus k g r₁ r₂ μ i' j') (x := z)
      exact this.le ⟨y, rfl⟩
    exact (h1.map (carveLocusToGrPair k g r₁ r₂ μ i' j').continuous).mem_open
      (pairChartOpen k g r₁ g r₂ i j).1.2 hz
  -- the range condition for the lift through the chart
  have hrange : Set.range ((carveLocus k g r₁ r₂ μ i' j').fromSpecStalk z
        ≫ carveLocusToGrPair k g r₁ r₂ μ i' j')
      ⊆ Set.range (pairChartMap k g r₁ g r₂ i j) := by
    rintro _ ⟨y, rfl⟩
    exact hgen (Set.mem_univ y)
  -- the two chart presentations of `Spec 𝒪_z ⟶ grPair`
  have hu : (carveLocus k g r₁ r₂ μ i' j').fromSpecStalk z
        ≫ carveLocusToGrPair k g r₁ r₂ μ i' j'
      = Spec.map (Spec.preimage (IsOpenImmersion.lift (pairChartMap k g r₁ g r₂ i j)
          ((carveLocus k g r₁ r₂ μ i' j').fromSpecStalk z
            ≫ carveLocusToGrPair k g r₁ r₂ μ i' j') hrange))
        ≫ pairChartMap k g r₁ g r₂ i j := by
    rw [Spec.map_preimage]
    exact (IsOpenImmersion.lift_fac _ _ hrange).symm
  have hu' : (carveLocus k g r₁ r₂ μ i' j').fromSpecStalk z
        ≫ carveLocusToGrPair k g r₁ r₂ μ i' j'
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i' j'))
          ≫ Spec.preimage ((carveLocus k g r₁ r₂ μ i' j').fromSpecStalk z))
        ≫ pairChartMap k g r₁ g r₂ i' j' := by
    rw [Spec.map_comp, Spec.map_preimage, Category.assoc]
    rfl
  -- the compatibility of the two presentations kills the chart value in the stalk
  have hkill : (Spec.preimage (IsOpenImmersion.lift (pairChartMap k g r₁ g r₂ i j)
      ((carveLocus k g r₁ r₂ μ i' j').fromSpecStalk z
        ≫ carveLocusToGrPair k g r₁ r₂ μ i' j') hrange)).hom
      ((pairChartΓ k g r₁ g r₂ i j).hom s) = 0 :=
    carveIdeal_le_ker_of_presentations k g r₁ r₂ μ _ _ hu hu'
      (fun x hx => RingHom.mem_ker.mpr (by
        change (Spec.preimage ((carveLocus k g r₁ r₂ μ i' j').fromSpecStalk z)).hom
          (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i' j') x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero])) hs
  -- read the section through the chart-sections workhorse, then take germs
  have hW := ΓSpecIso_hom_appLE_of_eq_specMap_pairChartMap k g r₁ g r₂ i j
    (Spec.preimage (IsOpenImmersion.lift (pairChartMap k g r₁ g r₂ i j)
      ((carveLocus k g r₁ r₂ μ i' j').fromSpecStalk z
        ≫ carveLocusToGrPair k g r₁ r₂ μ i' j') hrange)) hu hgen s
  rw [hkill] at hW
  exact Scheme.germ_app_eq_zero_of_fromSpecStalk
    (carveLocusToGrPair k g r₁ r₂ μ i' j') s hz hgen hW

/-- **KeyChart** (the "one DDR-1 gap" of I-0193, `informal/w4-ddr9-worksheet.md` §3.2):
the value of the carve ideal sheaf `I_♦` on the pair-chart open `U_{I,J}` is the chart
carve ideal, transported along the chart sections identification. -/
theorem carveIdealSheaf_ideal_pairChartOpen
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    (carveIdealSheaf k g r₁ r₂ μ).ideal (pairChartOpen k g r₁ g r₂ i j)
      = (carveIdeal k g r₁ r₂ μ i j).comap (pairChartΓ k g r₁ g r₂ i j).hom := by
  apply le_antisymm
  · -- `≤`: through the self term `ker ((carveLocusToGrPair i j).app U_{I,J})`
    intro s hsmem
    have h2 : (((carveLocusToGrPair k g r₁ r₂ μ i j).app
        (pairChartOpen k g r₁ g r₂ i j).1).hom) s = 0 := by
      rw [← RingHom.mem_ker, ← Scheme.Hom.ker_apply]
      exact carveIdealSheaf_le_ker_carveLocusToGrPair k g r₁ r₂ μ i j _ hsmem
    have hW := ΓSpecIso_hom_appLE_of_eq_specMap_pairChartMap k g r₁ g r₂ i j
      (CommRingCat.ofHom (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i j)))
      (u := carveLocusToGrPair k g r₁ r₂ μ i j) rfl
      (top_le_preimage_pairChartOpen_of_factor k g r₁ g r₂ i j
        (CommRingCat.ofHom (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i j))) rfl) s
    have h3 : ((carveLocusToGrPair k g r₁ r₂ μ i j).appLE
        (pairChartOpen k g r₁ g r₂ i j).1 ⊤
        (top_le_preimage_pairChartOpen_of_factor k g r₁ g r₂ i j
          (CommRingCat.ofHom (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i j))) rfl)).hom s
        = 0 := by
      change ((carveLocus k g r₁ r₂ μ i j).presheaf.map (homOfLE
          (top_le_preimage_pairChartOpen_of_factor k g r₁ g r₂ i j
            (CommRingCat.ofHom (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i j))) rfl)).op).hom
        (((carveLocusToGrPair k g r₁ r₂ μ i j).app
          (pairChartOpen k g r₁ g r₂ i j).1).hom s) = 0
      rw [h2]
      exact map_zero _
    have h4 := (DFunLike.congr_arg
      (Scheme.ΓSpecIso (CommRingCat.of
        (PairChartRing k g r₁ g r₂ i j ⧸ carveIdeal k g r₁ r₂ μ i j))).hom.hom
      h3).symm.trans hW
    exact Ideal.mem_comap.mpr
      (Ideal.Quotient.eq_zero_iff_mem.mp (((map_zero _).symm.trans h4).symm))
  · -- `≥`: kill every chart locus, section by section through the germs
    intro s hs
    have hval : (carveIdealSheaf k g r₁ r₂ μ).ideal (pairChartOpen k g r₁ g r₂ i j)
        = ⨅ c : (glueData k g r₁).J × (glueData k g r₂).J,
            RingHom.ker (((carveLocusToGrPair k g r₁ r₂ μ c.1 c.2).app
              (pairChartOpen k g r₁ g r₂ i j).1).hom) :=
      ((congrFun (Scheme.IdealSheafData.ideal_iInf
          fun c : (glueData k g r₁).J × (glueData k g r₂).J =>
            (carveLocusToGrPair k g r₁ r₂ μ c.1 c.2).ker)
        (pairChartOpen k g r₁ g r₂ i j)).trans iInf_apply).trans
        (iInf_congr fun c => Scheme.Hom.ker_apply _ _)
    rw [hval]
    refine Ideal.mem_iInf.mpr fun c => RingHom.mem_ker.mpr ?_
    refine TopCat.Presheaf.section_ext (carveLocus k g r₁ r₂ μ c.1 c.2).sheaf _ _ _
      (fun z hz => ?_)
    exact (germ_carveLocusToGrPair_app_pairChartOpen_eq_zero k g r₁ r₂ μ i c.1 j c.2 s
      (Ideal.mem_comap.mp hs) z hz).trans (map_zero _).symm

end KeyChart

/-! ## The Over-triangle packaging (`informal/w4-ddr9-worksheet.md` §1.2) -/

section OverPackaging

open Grassmannian

variable (k : Type u) [Field k] (g r₁ r₂ : ℕ)
variable {ι : Type u} (μ : ι → ((Fin r₁ → k) →ₗ[k] (Fin r₂ → k)))

/-- Per piece, the chart presentation reads off the structure triangle. -/
private theorem piece_triangle {S : Type u} [CommRing S] [Algebra k S]
    (v : Spec (CommRingCat.of S) ⟶ carveScheme k g r₁ r₂ μ) (x : S)
    (h : ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
        (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away x),
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
            ≫ v ≫ carveSchemeι k g r₁ r₂ μ
          = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j) :
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
        ≫ v ≫ carveSchemeι k g r₁ r₂ μ ≫ grPairStructMap k g r₁ g r₂
      = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)) := by
  obtain ⟨i, j, w, hw⟩ := h
  calc Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
        ≫ v ≫ carveSchemeι k g r₁ r₂ μ ≫ grPairStructMap k g r₁ g r₂
      = (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
          ≫ v ≫ carveSchemeι k g r₁ r₂ μ) ≫ grPairStructMap k g r₁ g r₂ :=
        (congrArg (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x))) ≫ ·)
          (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom w.toRingHom)
          ≫ (pairChartMap k g r₁ g r₂ i j ≫ grPairStructMap k g r₁ g r₂) :=
        (congrArg (· ≫ grPairStructMap k g r₁ g r₂) hw).trans (Category.assoc _ _ _)
    _ = Spec.map (CommRingCat.ofHom (algebraMap k (PairChartRing k g r₁ g r₂ i j))
          ≫ CommRingCat.ofHom w.toRingHom) :=
        (congrArg (Spec.map (CommRingCat.ofHom w.toRingHom) ≫ ·)
          (pairChartMap_grPairStructMap k g r₁ g r₂ i j)).trans (Spec.map_comp _ _).symm
    _ = Spec.map (CommRingCat.ofHom (algebraMap k S)
          ≫ CommRingCat.ofHom (algebraMap S (Localization.Away x))) :=
        congrArg Spec.map (((CommRingCat.ofHom_comp _ _).symm.trans
          (congrArg CommRingCat.ofHom (w.comp_algebraMap.trans
            (IsScalarTower.algebraMap_eq k S (Localization.Away x))))).trans
          (CommRingCat.ofHom_comp _ _))
    _ = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away x)))
          ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)) := Spec.map_comp _ _

/-- **The Over triangle from a chart cover**: a test morphism `v : Spec S ⟶ Z(♦)` whose
`carveSchemeι`-composite is presented, over a spanning family of localizations, through
pair charts by `k`-algebra maps, is a morphism over `Spec k`. -/
theorem carveSchemeOver_triangle_of_chartCover {S : Type u} [CommRing S] [Algebra k S]
    (v : Spec (CommRingCat.of S) ⟶ carveScheme k g r₁ r₂ μ)
    {m : ℕ} (f : Fin m → S) (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ t : Fin m, ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
        (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away (f t)),
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t))))
            ≫ v ≫ carveSchemeι k g r₁ r₂ μ
          = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j) :
    v ≫ (carveSchemeOver k g r₁ r₂ μ).hom = (overSpec k S).hom := by
  change v ≫ (carveSchemeι k g r₁ r₂ μ ≫ grPairStructMap k g r₁ g r₂)
      = Spec.map (CommRingCat.ofHom (algebraMap k S))
  apply Scheme.Cover.hom_ext
    ((Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) f hf).openCover)
  intro t
  exact piece_triangle k g r₁ r₂ μ v (f t) (h t)

/-- **The Over-hom packaging** of `informal/w4-ddr9-worksheet.md` §1.2: the morphism
`overSpec k S ⟶ carveSchemeOver` carried by a chart-covered test morphism. -/
noncomputable def carveSchemeOverHomMk {S : Type u} [CommRing S] [Algebra k S]
    (v : Spec (CommRingCat.of S) ⟶ carveScheme k g r₁ r₂ μ)
    {m : ℕ} (f : Fin m → S) (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ t : Fin m, ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
        (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away (f t)),
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t))))
            ≫ v ≫ carveSchemeι k g r₁ r₂ μ
          = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j) :
    overSpec k S ⟶ carveSchemeOver k g r₁ r₂ μ :=
  Over.homMk v (carveSchemeOver_triangle_of_chartCover k g r₁ r₂ μ v f hf h)

end OverPackaging

/-! ## The campaign spellings (the DAT-D windows) -/

section Curve

open Scheme Grassmannian

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable (A B : X.CurveDivisor) (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k ↥(divisorSections k B ⊤))
variable (b₂ : Module.Basis (Fin r₂) k ↥(divisorSections k (A + B) ⊤))

/-- **KeyChart at the campaign windows**: the kernel ideal sheaf of `divSchemeι` has chart
value the DD-R carve ideal `I_♦`, transported along the chart sections identification. -/
theorem ker_divSchemeι_ideal_pairChartOpen
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    (divSchemeι k A B g r₁ r₂ b₁ b₂).ker.ideal (pairChartOpen k g r₁ g r₂ i j)
      = (divCarveIdeal k A B g r₁ r₂ b₁ b₂ i j).comap (pairChartΓ k g r₁ g r₂ i j).hom :=
  (congrArg (fun (I : (grPair k g r₁ g r₂).IdealSheafData)
      => I.ideal (pairChartOpen k g r₁ g r₂ i j))
    (ker_carveSchemeι k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂))).trans
  (carveIdealSheaf_ideal_pairChartOpen k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂) i j)

/-- **The campaign Over-hom packaging** (`informal/w4-ddr9-worksheet.md` §1.2, §3.2): the
morphism `overSpec k S ⟶ divSchemeOver` carried by a chart-covered test morphism into
`DivScheme g`.  The Over triangle itself is `Over.w` of this hom (or
`carveSchemeOver_triangle_of_chartCover` at the campaign multiplier). -/
noncomputable def divSchemeOverHomMk {S : Type u} [CommRing S] [Algebra k S]
    (v : Spec (CommRingCat.of S) ⟶ DivScheme k A B g r₁ r₂ b₁ b₂)
    {m : ℕ} (f : Fin m → S) (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ t : Fin m, ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
        (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away (f t)),
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t))))
            ≫ v ≫ divSchemeι k A B g r₁ r₂ b₁ b₂
          = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j) :
    overSpec k S ⟶ divSchemeOver k A B g r₁ r₂ b₁ b₂ :=
  carveSchemeOverHomMk k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂) v f hf h

@[simp]
lemma divSchemeOverHomMk_left {S : Type u} [CommRing S] [Algebra k S]
    (v : Spec (CommRingCat.of S) ⟶ DivScheme k A B g r₁ r₂ b₁ b₂)
    {m : ℕ} (f : Fin m → S) (hf : Ideal.span (Set.range f) = ⊤) (h) :
    (divSchemeOverHomMk k A B g r₁ r₂ b₁ b₂ v f hf h).left = v :=
  rfl

end Curve

end AlgebraicGeometry
