/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivCarveLocus

/-!
# DDR-3 anchor — the universal carve pair over the `Z(♦)`-chart rings

The input side of the relative local-generator construction
(`informal/spec-dd-r.md` §3 item 3; I-0193 "notes for DDR-3"): each chart of `DivScheme g`
is `Spec` of the **carve chart ring** `R_Z = R_{I,J} ⧸ I_♦`, and the tautological pair
pushes to a universal Grassmannian pair over it which satisfies the carve after *every*
base change — in particular in every residue-field fibre, which is exactly where P-fib
(`RiemannRoch/PFib.lean`) takes over.

* `AlgebraicGeometry.DivCarveChartRing` — the `Z(♦)`-chart ring, with its Noetherian
  instance (`isNoetherianRing_pairChartRing` + quotient), the DDR-3 licence;
* `AlgebraicGeometry.divCarveChartMk` — the quotient presentation, as a `k`-algebra map;
* `AlgebraicGeometry.divUniversalFst/Snd` — **the universal pair**: the tautological
  pair pushed to the chart ring along `divCarveChartMk` (`Module.Grassmannian.map`);
* `AlgebraicGeometry.divCarveIdeal_le_ker_of_tower` — the kill law: any algebra over the
  chart ring kills `I_♦`;
* `AlgebraicGeometry.divUniversal_carve` — **the universal carve law**: over any algebra
  `S` of the chart ring, the pulled-back tautological pair satisfies `(♦)` (through the
  DDR-1 keystone `carveIdeal_le_ker_iff_carve_map`); stated over instance arguments
  `[Algebra R_{I,J} S] [IsScalarTower …]` per the recorded `Grassmannian.map` seam
  discipline (I-0193 hazard 6) — consumers instantiate with `w.toAlgebra`;
* `AlgebraicGeometry.divUniversal_carve_residueField` — **the fibrewise carve** at every
  prime of the chart ring: the pair `(K_M ⊗ κ(p), K' ⊗ κ(p))` satisfies the carve over
  `κ(p)` — the hypothesis package P-fib's `existsUnique_effective_divisor_of_carve`
  consumes fibrewise (with the window/corank data supplied by the DD-4 transport seam).
-/

set_option autoImplicit false

universe u

open TensorProduct CategoryTheory

namespace AlgebraicGeometry

open Grassmannian Scheme

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable (A B : X.CurveDivisor) (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k ↥(divisorSections k B ⊤))
variable (b₂ : Module.Basis (Fin r₂) k ↥(divisorSections k (A + B) ⊤))

/-- **The `Z(♦)`-chart ring** `R_Z = R_{I,J} ⧸ I_♦`: the coordinate ring of the
chart-wise carve locus `divCarveLocus` (`Spec` of this ring is `carveLocus` at the
campaign multipliers). -/
abbrev DivCarveChartRing (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) : Type u :=
  PairChartRing k g r₁ g r₂ i j ⧸ divCarveIdeal k A B g r₁ r₂ b₁ b₂ i j

/-- **The DDR-3 Noetherian licence**: the `Z(♦)`-chart rings are Noetherian (finite type
over `k`: quotient of the Noetherian pair chart ring). -/
instance isNoetherianRing_divCarveChartRing
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    IsNoetherianRing (DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j) :=
  inferInstance

/-- The quotient presentation of the `Z(♦)`-chart ring, as a `k`-algebra map. -/
noncomputable def divCarveChartMk (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    PairChartRing k g r₁ g r₂ i j →ₐ[k] DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j :=
  Ideal.Quotient.mkₐ k (divCarveIdeal k A B g r₁ r₂ b₁ b₂ i j)

/-- **The universal first window** `K_M^{univ}` over a `Z(♦)`-chart ring: the
tautological chart-`I` window pushed to the quotient. -/
noncomputable def divUniversalFst (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    grFunctorAff k (Fin r₁ → k) g (DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j) :=
  Module.Grassmannian.map (divCarveChartMk k A B g r₁ r₂ b₁ b₂ i j)
    (pairTautFst k g r₁ r₂ i j)

/-- **The universal second window** `K'^{univ}` over a `Z(♦)`-chart ring: the
tautological chart-`J` window pushed to the quotient. -/
noncomputable def divUniversalSnd (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) :
    grFunctorAff k (Fin r₂ → k) g (DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j) :=
  Module.Grassmannian.map (divCarveChartMk k A B g r₁ r₂ b₁ b₂ i j)
    (pairTautSnd k g r₁ r₂ i j)

/-- **The kill law**: every algebra of the `Z(♦)`-chart ring kills the carve ideal (the
algebra map factors through the quotient by the scalar tower). -/
theorem divCarveIdeal_le_ker_of_tower
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) (S : Type u) [CommRing S]
    [Algebra (PairChartRing k g r₁ g r₂ i j) S]
    [Algebra (DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j) S]
    [IsScalarTower (PairChartRing k g r₁ g r₂ i j)
      (DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j) S] :
    divCarveIdeal k A B g r₁ r₂ b₁ b₂ i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) S) := by
  intro x hx
  rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply (PairChartRing k g r₁ g r₂ i j)
    (DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j) S, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- **The universal carve law** (`informal/spec-dd-r.md` §3 item 3, the input): over any
algebra `S` of the `Z(♦)`-chart ring, the pulled-back tautological pair satisfies the
carve `(♦)` — for every multiplier section `s ∈ H⁰(𝒪(A))` the carve-pair arrow of the
base-changed pair vanishes.  This is the DDR-1 keystone
`carveIdeal_le_ker_iff_carve_map` fed by the kill law; the instance-argument spelling is
the recorded `Grassmannian.map` seam discipline (consumers instantiate `[Algebra R_{I,J}
S]` with `w.toAlgebra` and the tower with `IsScalarTower.of_algebraMap_eq'`). -/
theorem divUniversal_carve
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J) (S : Type u) [CommRing S]
    [Algebra k S] [Algebra (PairChartRing k g r₁ g r₂ i j) S]
    [IsScalarTower k (PairChartRing k g r₁ g r₂ i j) S]
    [Algebra (DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j) S]
    [IsScalarTower (PairChartRing k g r₁ g r₂ i j)
      (DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j) S]
    (s : ↥(divisorSections k A ⊤)) :
    carvePairArrow (divCarveMul k A B r₁ r₂ b₁ b₂ s)
      (LinearMap.ker (Module.Grassmannian.baseChangeMkQ S
        (pairTautFst k g r₁ r₂ i j).toSubmodule))
      (LinearMap.ker (Module.Grassmannian.baseChangeMkQ S
        (pairTautSnd k g r₁ r₂ i j).toSubmodule)) = 0 :=
  (carveIdeal_le_ker_iff_carve_map k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂) i j S).mp
    (divCarveIdeal_le_ker_of_tower k A B g r₁ r₂ b₁ b₂ i j S) s

set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
-- the canonical residue-field tower `k → R_{I,J} → κ(q)` (localization + quotient
-- composites over the `MvPolynomial` tensor chart ring) exceeds the default search
-- budget and the project-default pending depth (the recorded in-file escape hatch)
/-- **The fibrewise carve** (the P-fib input, `informal/spec-dd-r.md` §3 item 3): at
every point of the chart-wise carve locus — a prime `q` of the pair chart ring
containing `I_♦` — the tautological pair pulled back to the residue field `κ(q)`
satisfies the carve.  (Points of the `Z(♦)`-chart correspond to such primes; this
spelling stays on the pair chart ring, where all `κ(q)`-instances are the cheap
canonical ones.)  This is the hypothesis package P-fib's
`existsUnique_effective_divisor_of_carve` consumes fibrewise, with the window/corank
data supplied by the DD-4 transport seam. -/
theorem divUniversal_carve_residueField
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    (q : PrimeSpectrum (PairChartRing k g r₁ g r₂ i j))
    (hq : divCarveIdeal k A B g r₁ r₂ b₁ b₂ i j ≤ q.asIdeal)
    (s : ↥(divisorSections k A ⊤)) :
    carvePairArrow (divCarveMul k A B r₁ r₂ b₁ b₂ s)
      (LinearMap.ker (Module.Grassmannian.baseChangeMkQ q.asIdeal.ResidueField
        (pairTautFst k g r₁ r₂ i j).toSubmodule))
      (LinearMap.ker (Module.Grassmannian.baseChangeMkQ q.asIdeal.ResidueField
        (pairTautSnd k g r₁ r₂ i j).toSubmodule)) = 0 :=
  (carveIdeal_le_ker_iff_carve_map k g r₁ r₂ (divCarveMul k A B r₁ r₂ b₁ b₂) i j
      q.asIdeal.ResidueField).mp
    (hq.trans (Ideal.ker_algebraMap_residueField (I := q.asIdeal)).symm.le) s

end AlgebraicGeometry
