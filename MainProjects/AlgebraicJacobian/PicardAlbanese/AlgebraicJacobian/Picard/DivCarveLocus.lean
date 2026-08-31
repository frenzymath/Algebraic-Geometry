/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivCarveKit
import AlgebraicJacobian.Picard.DivCarvePairChart
import AlgebraicJacobian.RiemannRoch.SectionMul
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The DD-R carve locus `Z(♦)` over the pair charts (DDR-1)

The carve locus of the DAT-D design (`informal/spec-dd-r.md` §3 item 1;
`informal/dat-d-worksheet.md` §3.1): over each pair chart `Spec (R^I ⊗[k] R^J)` of the
Grassmannian pair, the tautological pair `(K_taut^I, K_taut^J)` is carved by the SINGLE
closed condition `(♦)` — for every multiplier the carve-pair arrow
`K_taut^I → (H₂ ⊗ R_{I,J}) ⧸ K_taut^J` vanishes — cut out by the carve ideal `I_♦`
(the span of the `entriesIdeal`s of the carve arrows).

Following the spec §3 preamble, the scheme side is developed for the coordinate ambients
`H = Fin r → k`; the abstract window spaces `H_M`, `H_{M+s}` enter through the DD-4
boundary bases (`Module.finBasis` at the consumer seam), which conjugate the section
multiplication `sectionMulBilin` into the coordinate multiplier family `divCarveMul`.
The generic layer (`carveIdeal`, `carveLocus`, keystones, the gluing compatibility) is
stated for an arbitrary multiplier family and instantiated by the campaign spellings
(`divCarveArrow`, `divCarveIdeal`, `divCarveLocus`).

* `AlgebraicGeometry.pairTautFst/Snd`: the tautological Grassmannian pair over a pair
  chart ring.
* `AlgebraicGeometry.carveIdeal`: the carve ideal `I_♦` of a multiplier family.
* **Keystones** (`carveIdeal_le_ker_iff`, `carveIdeal_le_ker_iff_carve_map`,
  `carveIdeal_le_ker_iff_factors`): a test map kills `I_♦` iff the base-changed carve
  arrows vanish (`(♦) ⊗ S` holds, via `carveArrow_baseChange_eq_zero_iff`'s
  `entriesIdeal` mechanism) iff the carve holds for the pulled-back Grassmannian pair
  (the carve transport L1) iff the map factors through the locus.
* `AlgebraicGeometry.carveLocus`, `carveLocusι`, `carveLocusToGrPair`: the chart-wise
  `Z(♦)` as a closed subscheme of the pair chart, mapped into `grPair`.
* **The gluing compatibility** (`carveIdeal_le_ker_of_specMap_pairChartMap_eq`): the
  carve ideals of two pair charts presenting a common test morphism to `grPair` have the
  same kill-sets — the mathematical content of "`Z(♦)` glues", via L1 + the GL-cocycle
  pair-chart compatibility.
* **Campaign spellings**: `divCarveMul`, `divCarveArrow`, `divCarveIdeal`,
  `divCarveLocus` at the windows `A = s·F`, `B = M·F` (through their `H⁰`-bases).
-/

set_option autoImplicit false

universe u

open TensorProduct CategoryTheory

namespace AlgebraicGeometry

open Grassmannian

section Generic

variable (k : Type u) [Field k] (g r₁ r₂ : ℕ)

/-! ## The tautological pair over a pair chart -/

/-- **The first tautological window** over the pair chart `R_{I,J} = R^I ⊗[k] R^J`:
the pullback of the chart-`I` tautological point along the left inclusion
`R^I → R^I ⊗ R^J`.  The `K_taut^I` of the carve. -/
noncomputable def pairTautFst (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    grFunctorAff k (Fin r₁ → k) g (PairChartRing k g r₁ g r₂ i j) :=
  Module.Grassmannian.map (Algebra.TensorProduct.includeLeft (S := k))
    (chartTautologicalPoint k g r₁ i.down.1 i.down.2)

/-- **The second tautological window** over the pair chart: the pullback of the
chart-`J` tautological point along the right inclusion `R^J → R^I ⊗ R^J`.
The `K_taut^J` of the carve. -/
noncomputable def pairTautSnd (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    grFunctorAff k (Fin r₂ → k) g (PairChartRing k g r₁ g r₂ i j) :=
  Module.Grassmannian.map (Algebra.TensorProduct.includeRight
    (R := k) (A := ChartRing k g r₁ i.down.1))
    (chartTautologicalPoint k g r₂ j.down.1 j.down.2)

instance finite_pairTautFst (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    Module.Finite (PairChartRing k g r₁ g r₂ i j)
      ↥(pairTautFst k g r₁ r₂ i j).toSubmodule :=
  finite_submodule_of_projective_quotient _

instance finite_pairTautSnd (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    Module.Finite (PairChartRing k g r₁ g r₂ i j)
      ↥(pairTautSnd k g r₁ r₂ i j).toSubmodule :=
  finite_submodule_of_projective_quotient _

/-! ## The carve ideal of a multiplier family and its keystones -/

variable {ι : Type u} (μ : ι → ((Fin r₁ → k) →ₗ[k] (Fin r₂ → k)))

/-- **The carve ideal `I_♦`** of a multiplier family over a pair chart: the span of the
entries ideals of the carve-pair arrows of the tautological pair, over all multipliers.
Its vanishing locus is the chart-wise `Z(♦)`. -/
noncomputable def carveIdeal (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    Ideal (PairChartRing k g r₁ g r₂ i j) :=
  ⨆ m : ι, entriesIdeal (carvePairArrow (μ m) (pairTautFst k g r₁ r₂ i j).toSubmodule
    (pairTautSnd k g r₁ r₂ i j).toSubmodule)

/-- **Keystone, base-change form**: a test algebra kills the carve ideal iff all the
base-changed carve arrows vanish — the `(♦) ⊗ S` condition, through the `entriesIdeal`
universal property (`carveArrow_baseChange_eq_zero_iff`'s mechanism). -/
theorem carveIdeal_le_ker_iff (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    (S : Type u) [CommRing S] [Algebra (PairChartRing k g r₁ g r₂ i j) S] :
    carveIdeal k g r₁ r₂ μ i j
        ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) S) ↔
      ∀ m, LinearMap.baseChange S (carvePairArrow (μ m)
        (pairTautFst k g r₁ r₂ i j).toSubmodule
        (pairTautSnd k g r₁ r₂ i j).toSubmodule) = 0 := by
  rw [carveIdeal, iSup_le_iff]
  exact forall_congr' fun m => (baseChange_eq_zero_iff _ S).symm

/-- **Keystone, pulled-back-pair form**: a test algebra kills the carve ideal iff the
carve holds for the pulled-back tautological pair over `S` (mathlib's
`Module.Grassmannian.map`, as `ker (baseChangeMkQ)`) — the carve transport L1. -/
theorem carveIdeal_le_ker_iff_carve_map (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    (S : Type u) [CommRing S] [Algebra k S]
    [Algebra (PairChartRing k g r₁ g r₂ i j) S]
    [IsScalarTower k (PairChartRing k g r₁ g r₂ i j) S] :
    carveIdeal k g r₁ r₂ μ i j
        ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) S) ↔
      ∀ m, carvePairArrow (μ m)
        (LinearMap.ker (Module.Grassmannian.baseChangeMkQ S
          (pairTautFst k g r₁ r₂ i j).toSubmodule))
        (LinearMap.ker (Module.Grassmannian.baseChangeMkQ S
          (pairTautSnd k g r₁ r₂ i j).toSubmodule)) = 0 := by
  rw [carveIdeal_le_ker_iff]
  exact forall_congr' fun m => baseChange_carvePairArrow_eq_zero_iff S (μ m) _ _

/-- **Keystone, factorisation form**: a test algebra kills the carve ideal iff it
factors (uniquely) through the chart-wise `Z(♦)`. -/
theorem carveIdeal_le_ker_iff_factors (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    {S : Type u} [CommRing S] (f : PairChartRing k g r₁ g r₂ i j →+* S) :
    carveIdeal k g r₁ r₂ μ i j ≤ RingHom.ker f ↔
      ∃! φ : PairChartRing k g r₁ g r₂ i j ⧸ carveIdeal k g r₁ r₂ μ i j →+* S,
        φ.comp (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i j)) = f :=
  ideal_le_ker_iff_factors _ f

/-! ## The chart-wise `Z(♦)` as a closed subscheme -/

/-- **The chart-wise carve locus `Z(♦)`**: the vanishing locus of the carve ideal in the
pair chart. -/
noncomputable def carveLocus (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    Scheme :=
  Spec (CommRingCat.of (PairChartRing k g r₁ g r₂ i j ⧸ carveIdeal k g r₁ r₂ μ i j))

/-- The closed immersion `Z(♦) ⟶ Spec (R^I ⊗ R^J)` of the chart-wise carve locus. -/
noncomputable def carveLocusι (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    carveLocus k g r₁ r₂ μ i j ⟶ Spec (CommRingCat.of (PairChartRing k g r₁ g r₂ i j)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (carveIdeal k g r₁ r₂ μ i j)))

instance isClosedImmersion_carveLocusι
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    IsClosedImmersion (carveLocusι k g r₁ r₂ μ i j) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The chart-wise carve locus mapped into the Grassmannian pair, through the pair
chart. -/
noncomputable def carveLocusToGrPair (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    carveLocus k g r₁ r₂ μ i j ⟶ grPair k g r₁ g r₂ :=
  carveLocusι k g r₁ r₂ μ i j ≫ pairChartMap k g r₁ g r₂ i j

/-! ## Noetherian instances (the DDR-3 licence) -/

instance isNoetherianRing_pairChartRing
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    IsNoetherianRing (PairChartRing k g r₁ g r₂ i j) :=
  isNoetherianRing_of_ringEquiv _
    (MvPolynomial.algebraTensorAlgEquiv (R := k) (A := ChartRing k g r₁ i.down.1)
      (σ := Fin g × {q : Fin r₂ // q ∉ j.down.1})).symm.toRingEquiv

instance quasiCompact_carveLocusToGrPair
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    QuasiCompact (carveLocusToGrPair k g r₁ r₂ μ i j) := by
  haveI : TopologicalSpace.NoetherianSpace (carveLocus k g r₁ r₂ μ i j) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (Spec (CommRingCat.of
      (PairChartRing k g r₁ g r₂ i j ⧸ carveIdeal k g r₁ r₂ μ i j))))
  infer_instance

/-! ## The gluing compatibility of the carve ideals -/

/-- **The carve ideals glue** (the `(♦)` overlap compatibility): for two pair charts
presenting a common morphism from an affine test to `grPair`, a test map killing the
carve ideal of one chart kills the carve ideal of the other.  Mechanism: the carve
transport (L1) on both sides, matched through the GL-cocycle pair-chart compatibility of
the tautological pair.  This is the entries-ideal transport of `informal/spec-dd-r.md`
§3 item 1, in kill-set form. -/
theorem carveIdeal_le_ker_of_specMap_pairChartMap_eq
    {i i' : (glueData k g r₁).J} {j j' : (glueData k g r₂).J}
    {B : Type u} [CommRing B] [Algebra k B]
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] B)
    (w' : PairChartRing k g r₁ g r₂ i' j' →ₐ[k] B)
    (h : Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j
       = Spec.map (CommRingCat.ofHom w'.toRingHom) ≫ pairChartMap k g r₁ g r₂ i' j')
    (hker : carveIdeal k g r₁ r₂ μ i' j' ≤ RingHom.ker w'.toRingHom) :
    carveIdeal k g r₁ r₂ μ i j ≤ RingHom.ker w.toRingHom := by
  letI : Algebra (PairChartRing k g r₁ g r₂ i j) B := w.toAlgebra
  letI : IsScalarTower k (PairChartRing k g r₁ g r₂ i j) B :=
    IsScalarTower.of_algebraMap_eq' w.comp_algebraMap.symm
  letI : Algebra (PairChartRing k g r₁ g r₂ i' j') B := w'.toAlgebra
  letI : IsScalarTower k (PairChartRing k g r₁ g r₂ i' j') B :=
    IsScalarTower.of_algebraMap_eq' w'.comp_algebraMap.symm
  -- the pulled-back tautological pairs agree (the GL-cocycle)
  have hFst : LinearMap.ker (Module.Grassmannian.baseChangeMkQ B
      (pairTautFst k g r₁ r₂ i j).toSubmodule)
      = LinearMap.ker (Module.Grassmannian.baseChangeMkQ B
        (pairTautFst k g r₁ r₂ i' j').toSubmodule) := by
    have e2 : Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)
        = Module.Grassmannian.map w' (pairTautFst k g r₁ r₂ i' j') := by
      rw [pairTautFst, pairTautFst, ← Module.Grassmannian.map_comp,
        ← Module.Grassmannian.map_comp]
      exact map_includeLeft_chartTautologicalPoint_eq_of_specMap_pairChartMap_eq
        k g r₁ g r₂ w w' h
    rw [← Module.Grassmannian.map_toSubmodule w, ← Module.Grassmannian.map_toSubmodule w',
      e2]
  have hSnd : LinearMap.ker (Module.Grassmannian.baseChangeMkQ B
      (pairTautSnd k g r₁ r₂ i j).toSubmodule)
      = LinearMap.ker (Module.Grassmannian.baseChangeMkQ B
        (pairTautSnd k g r₁ r₂ i' j').toSubmodule) := by
    have e2 : Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)
        = Module.Grassmannian.map w' (pairTautSnd k g r₁ r₂ i' j') := by
      rw [pairTautSnd, pairTautSnd, ← Module.Grassmannian.map_comp,
        ← Module.Grassmannian.map_comp]
      exact map_includeRight_chartTautologicalPoint_eq_of_specMap_pairChartMap_eq
        k g r₁ g r₂ w w' h
    rw [← Module.Grassmannian.map_toSubmodule w, ← Module.Grassmannian.map_toSubmodule w',
      e2]
  have hker' : carveIdeal k g r₁ r₂ μ i' j'
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i' j') B) := hker
  rw [carveIdeal_le_ker_iff_carve_map] at hker'
  have hgoal : carveIdeal k g r₁ r₂ μ i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) B) := by
    rw [carveIdeal_le_ker_iff_carve_map]
    intro m
    rw [hFst, hSnd]
    exact hker' m
  exact hgoal

end Generic

/-! ## The campaign spellings (the DAT-D windows) -/

section Curve

open Scheme

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable (A B : X.CurveDivisor) (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k ↥(divisorSections k B ⊤))
variable (b₂ : Module.Basis (Fin r₂) k ↥(divisorSections k (A + B) ⊤))

/-- The DAT-D carve arrow is the generic carve-pair arrow at the section multiplication:
`carveArrow` (SectionMul) and `carvePairArrow (sectionMulBilin …)` agree by
definition. -/
theorem carveArrow_eq_carvePairArrow (R : Type u) [CommRing R] [Algebra k R]
    (a : ↥(divisorSections k A ⊤))
    (Km : Submodule R (TensorProduct k R ↥(divisorSections k B ⊤)))
    (K' : Submodule R (TensorProduct k R ↥(divisorSections k (A + B) ⊤))) :
    carveArrow k R A B a Km K' = carvePairArrow (sectionMulBilin k A B a) Km K' :=
  rfl

/-- **The coordinate multiplier of the DAT-D carve**: the section multiplication
`μ_a = sectionMulBilin a` conjugated into the coordinate ambients through the DD-4
boundary bases of the two windows. -/
noncomputable def divCarveMul (a : ↥(divisorSections k A ⊤)) :
    (Fin r₁ → k) →ₗ[k] (Fin r₂ → k) :=
  b₂.equivFun.toLinearMap ∘ₗ sectionMulBilin k A B a ∘ₗ b₁.equivFun.symm.toLinearMap

/-- **The DD-R carve arrow** (`informal/spec-dd-r.md` §3 item 1) over a pair chart, at a
multiplier section `a ∈ H⁰(𝒪(A))`: the carve-pair arrow
`K_taut^I ⟶ (R_{I,J} ⊗ H₂) ⧸ K_taut^J` of the tautological pair at the coordinate
multiplier of `a`.  In the coordinate ambients of the scheme side (spec §3 preamble);
the section-space form is `carveArrow` through `carveArrow_eq_carvePairArrow` and the
boundary bases. -/
noncomputable def divCarveArrow (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    (a : ↥(divisorSections k A ⊤)) :
    ↥(pairTautFst k g r₁ r₂ i j).toSubmodule →ₗ[PairChartRing k g r₁ g r₂ i j]
      (TensorProduct k (PairChartRing k g r₁ g r₂ i j) (Fin r₂ → k)) ⧸
        (pairTautSnd k g r₁ r₂ i j).toSubmodule :=
  carvePairArrow (divCarveMul k A B r₁ r₂ b₁ b₂ a)
    (pairTautFst k g r₁ r₂ i j).toSubmodule (pairTautSnd k g r₁ r₂ i j).toSubmodule

/-- **The DD-R carve ideal `I_♦`** over a pair chart: the carve ideal of the coordinate
multiplier family of all sections of `H⁰(𝒪(A))`. -/
noncomputable def divCarveIdeal (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    Ideal (PairChartRing k g r₁ g r₂ i j) :=
  carveIdeal k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂) i j

/-- **The DDR-1 chart keystone** (`informal/spec-dd-r.md` §3 item 1): a `k`-algebra map
`R_{I,J} → S` kills the carve ideal `I_♦` iff the base change of every carve arrow
vanishes — the `(♦) ⊗ S` condition. -/
theorem divCarveIdeal_le_ker_iff (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    (S : Type u) [CommRing S] [Algebra (PairChartRing k g r₁ g r₂ i j) S] :
    divCarveIdeal k A B g r₁ r₂ b₁ b₂ i j
        ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) S) ↔
      ∀ a : ↥(divisorSections k A ⊤),
        LinearMap.baseChange S (divCarveArrow k A B g r₁ r₂ b₁ b₂ i j a) = 0 :=
  carveIdeal_le_ker_iff k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂) i j S

/-- **The DDR-1 chart keystone, locus form**: a map kills `I_♦` iff it factors uniquely
through the chart-wise `Z(♦)`. -/
theorem divCarveIdeal_le_ker_iff_factors
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    {S : Type u} [CommRing S] (f : PairChartRing k g r₁ g r₂ i j →+* S) :
    divCarveIdeal k A B g r₁ r₂ b₁ b₂ i j ≤ RingHom.ker f ↔
      ∃! φ : PairChartRing k g r₁ g r₂ i j ⧸ divCarveIdeal k A B g r₁ r₂ b₁ b₂ i j →+* S,
        φ.comp (Ideal.Quotient.mk (divCarveIdeal k A B g r₁ r₂ b₁ b₂ i j)) = f :=
  ideal_le_ker_iff_factors _ f

/-- **The chart-wise `Z(♦)` of the campaign**: the carve locus of the DAT-D windows over
a pair chart, a closed subscheme of `Spec (R^I ⊗ R^J)` through `carveLocusι`. -/
noncomputable def divCarveLocus (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    Scheme :=
  carveLocus k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂) i j

end Curve

end AlgebraicGeometry
