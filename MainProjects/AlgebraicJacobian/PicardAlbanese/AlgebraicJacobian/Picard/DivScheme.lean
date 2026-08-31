/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivCarveLocus

/-!
# `DivScheme g = Z(♦)`: the carve locus as a closed subscheme of the Grassmannian pair (DDR-1)

The glued carve locus of the DAT-D design (`informal/spec-dd-r.md` §3 item 1): the
chart-wise loci `Z(♦) ⊆ Spec (R^I ⊗ R^J)` (`Picard/DivCarveLocus.lean`) assemble into a
closed subscheme of `grPair` through the mathlib ideal-sheaf machinery — `carveIdealSheaf`
is the kernel ideal sheaf of the disjoint family of chart loci (the largest ideal sheaf
vanishing on all of them, `⨅ over the pair atlas`), and `DivScheme` is its subscheme.

* `AlgebraicGeometry.carveIdealSheaf`: the ideal sheaf `I_♦` on `grPair`.
* `AlgebraicGeometry.carveScheme`, `carveSchemeι`, `carveSchemeOver`: the generic glued
  locus, its closed immersion (mathlib's `IdealSheafData.subschemeι` instance), and its
  `Over (Spec k)` form.
* `AlgebraicGeometry.carveScheme_exists_factor_of_le_ker` and
  `carveIdealSheaf_le_ker_of_factors`: the factoring criterion at chart tests — a test
  map through a pair chart killing the chart carve ideal factors (uniquely, by `Mono`)
  through `carveSchemeι`.
* `AlgebraicGeometry.carveScheme_hom_ext` (`divScheme_hom_ext`, DDR-7's tail): morphisms
  into the locus are determined by their composites with the closed immersion.
* **Campaign spellings**: `DivScheme`, `divSchemeι`, `divSchemeOver` at the DAT-D
  windows.

The chart-value identification (`carveIdealSheaf.ideal (pair chart) = I_♦`-chart, the
`KeyChart` of the DD-R roadmap) rests on the landed gluing compatibility
(`carveIdeal_le_ker_of_specMap_pairChartMap_eq`); its remaining half is the app-level
localization bookkeeping and is left to the successor lane (see the inbox memory).
-/

set_option autoImplicit false

universe u

open TensorProduct CategoryTheory

namespace AlgebraicGeometry

open Grassmannian

section Generic

variable (k : Type u) [Field k] (g r₁ r₂ : ℕ)
variable {ι : Type u} (μ : ι → ((Fin r₁ → k) →ₗ[k] (Fin r₂ → k)))

/-- **The carve ideal sheaf `I_♦`** on the Grassmannian pair: the largest ideal sheaf
vanishing on every chart-wise carve locus — the infimum of the kernels of the chart
loci mapped into `grPair`. -/
noncomputable def carveIdealSheaf : (grPair k g r₁ g r₂).IdealSheafData :=
  ⨅ c : (glueData k g r₁).J × (glueData k g r₂).J,
    (carveLocusToGrPair k g r₁ r₂ μ c.1 c.2).ker

/-- **The glued carve locus `Z(♦)`** as a scheme: the subscheme of the carve ideal
sheaf on the Grassmannian pair. -/
noncomputable def carveScheme : Scheme :=
  (carveIdealSheaf k g r₁ r₂ μ).subscheme

/-- **The closed immersion `Z(♦) ⟶ grPair`**. -/
noncomputable def carveSchemeι : carveScheme k g r₁ r₂ μ ⟶ grPair k g r₁ g r₂ :=
  (carveIdealSheaf k g r₁ r₂ μ).subschemeι

instance isClosedImmersion_carveSchemeι :
    IsClosedImmersion (carveSchemeι k g r₁ r₂ μ) :=
  inferInstanceAs (IsClosedImmersion (carveIdealSheaf k g r₁ r₂ μ).subschemeι)

/-- The kernel of the closed immersion is the carve ideal sheaf. -/
theorem ker_carveSchemeι :
    (carveSchemeι k g r₁ r₂ μ).ker = carveIdealSheaf k g r₁ r₂ μ :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- **`Z(♦)` as a test object of `Over (Spec k)`**. -/
noncomputable def carveSchemeOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (carveSchemeι k g r₁ r₂ μ ≫ grPairStructMap k g r₁ g r₂)

/-- Each chart-wise carve locus maps to the glued locus over `grPair`. -/
theorem carveIdealSheaf_le_ker_carveLocusToGrPair
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    carveIdealSheaf k g r₁ r₂ μ ≤ (carveLocusToGrPair k g r₁ r₂ μ i j).ker :=
  iInf_le _ (i, j)

/-- **The factoring criterion, existence half** (the chart-test universal property): a
test morphism through a pair chart whose chart map kills the chart carve ideal factors
through the closed immersion `carveSchemeι`. -/
theorem carveScheme_exists_factor_of_le_ker
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    {S : Type u} [CommRing S]
    (w : PairChartRing k g r₁ g r₂ i j →+* S)
    (hker : carveIdeal k g r₁ r₂ μ i j ≤ RingHom.ker w) :
    ∃ v : Spec (CommRingCat.of S) ⟶ carveScheme k g r₁ r₂ μ,
      v ≫ carveSchemeι k g r₁ r₂ μ
        = Spec.map (CommRingCat.ofHom w) ≫ pairChartMap k g r₁ g r₂ i j := by
  obtain ⟨φ, hφ, -⟩ := (ideal_le_ker_iff_factors _ w).mp hker
  have hfac : Spec.map (CommRingCat.ofHom w) ≫ pairChartMap k g r₁ g r₂ i j
      = Spec.map (CommRingCat.ofHom φ) ≫ carveLocusToGrPair k g r₁ r₂ μ i j := by
    rw [carveLocusToGrPair, carveLocusι]
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine congrArg (· ≫ pairChartMap k g r₁ g r₂ i j) ?_
    rw [← Spec.map_comp]
    exact (congrArg (fun ρ => Spec.map (CommRingCat.ofHom ρ)) hφ).symm
  refine ⟨IsClosedImmersion.lift (carveSchemeι k g r₁ r₂ μ)
    (Spec.map (CommRingCat.ofHom w) ≫ pairChartMap k g r₁ g r₂ i j) ?_,
    IsClosedImmersion.lift_fac _ _ _⟩
  rw [ker_carveSchemeι, hfac]
  exact le_trans (carveIdealSheaf_le_ker_carveLocusToGrPair k g r₁ r₂ μ i j)
    (Scheme.Hom.le_ker_comp _ _)

/-- **The factoring criterion, kernel half**: a test morphism factoring through the
closed immersion has the carve ideal sheaf in its kernel. -/
theorem carveIdealSheaf_le_ker_of_factors {T : Scheme.{u}} (u : T ⟶ grPair k g r₁ g r₂)
    (v : T ⟶ carveScheme k g r₁ r₂ μ) (hv : v ≫ carveSchemeι k g r₁ r₂ μ = u) :
    carveIdealSheaf k g r₁ r₂ μ ≤ u.ker := by
  rw [← hv, ← ker_carveSchemeι k g r₁ r₂ μ]
  exact Scheme.Hom.le_ker_comp _ _

/-- **Hom-ext into `Z(♦)`** (the `divScheme_hom_ext` tail of DDR-7): morphisms into the
glued carve locus are determined by their composites with the closed immersion — closed
immersions are monomorphisms. -/
theorem carveScheme_hom_ext {T : Scheme.{u}} (u v : T ⟶ carveScheme k g r₁ r₂ μ)
    (h : u ≫ carveSchemeι k g r₁ r₂ μ = v ≫ carveSchemeι k g r₁ r₂ μ) : u = v :=
  (cancel_mono (carveSchemeι k g r₁ r₂ μ)).mp h

end Generic

/-! ## The campaign spellings (the DAT-D windows) -/

section Curve

open Scheme

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable (A B : X.CurveDivisor) (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k ↥(divisorSections k B ⊤))
variable (b₂ : Module.Basis (Fin r₂) k ↥(divisorSections k (A + B) ⊤))

/-- **`DivScheme g = Z(♦)`** (`informal/spec-dd-r.md` §3 item 1): the glued carve locus
of the DAT-D two-window multiplication carve, a closed subscheme of the Grassmannian
pair `Gr(g, H_M) ×_k Gr(g, H_{M+s})` through `divSchemeι`. -/
noncomputable def DivScheme : Scheme :=
  carveScheme k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂)

/-- **The closed immersion `divSchemeι : DivScheme g ⟶ grPair`**. -/
noncomputable def divSchemeι : DivScheme k A B g r₁ r₂ b₁ b₂ ⟶ grPair k g r₁ g r₂ :=
  carveSchemeι k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂)

instance isClosedImmersion_divSchemeι :
    IsClosedImmersion (divSchemeι k A B g r₁ r₂ b₁ b₂) :=
  isClosedImmersion_carveSchemeι k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂)

/-- **`DivScheme g` as a test object of `Over (Spec k)`**. -/
noncomputable def divSchemeOver : Over (Spec (CommRingCat.of k)) :=
  carveSchemeOver k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂)

/-- The DDR-1 factoring criterion at the campaign windows: a chart test killing `I_♦`
factors through `divSchemeι`. -/
theorem divScheme_exists_factor_of_le_ker
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    {S : Type u} [CommRing S] (w : PairChartRing k g r₁ g r₂ i j →+* S)
    (hker : divCarveIdeal k A B g r₁ r₂ b₁ b₂ i j ≤ RingHom.ker w) :
    ∃ v : Spec (CommRingCat.of S) ⟶ DivScheme k A B g r₁ r₂ b₁ b₂,
      v ≫ divSchemeι k A B g r₁ r₂ b₁ b₂
        = Spec.map (CommRingCat.ofHom w) ≫ pairChartMap k g r₁ g r₂ i j :=
  carveScheme_exists_factor_of_le_ker k g r₁ r₂ _ i j w hker

/-- **`divScheme_hom_ext`** (DDR-7): morphisms into `DivScheme g` are determined by
their composites with `divSchemeι`. -/
theorem divScheme_hom_ext {T : Scheme.{u}} (u v : T ⟶ DivScheme k A B g r₁ r₂ b₁ b₂)
    (h : u ≫ divSchemeι k A B g r₁ r₂ b₁ b₂ = v ≫ divSchemeι k A B g r₁ r₂ b₁ b₂) :
    u = v :=
  carveScheme_hom_ext k g r₁ r₂ _ u v h

end Curve

end AlgebraicGeometry
