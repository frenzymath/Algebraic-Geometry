/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafExtraction
import AlgebraicJacobian.Picard.DivSchemeEpsCarve
import AlgebraicJacobian.Picard.DivisorFamilyFieldDictionary
import AlgebraicJacobian.Picard.DivSchemeSeedUnivFibre

/-!
# G-4 — the reading multiplicativity and the `(M,s)`-coherence unit (worksheet §1.5)

The `K`-generic layer of the universal-seed assembly (`I-0241` gap 1, the hcarve
bridge): over any field extension `K/k`, the function-field reading of the theta
trivialization is **multiplicative across the ledger exponents** on window products,
and the resulting coherence defect between `Φ_s · Φ_M` and `Φ_{M+s}` is a single fixed
unit of `K(C_K)` whose divisor is exactly the transported-window discrepancy
`T(M+s) − (N + S)` — so multiplication by it translates the `Φ`-image of the shifted
window onto the fibre keystone's `N + S` side.

* `Scheme.MeromorphicPresentation.ofCocycle_elem_genericPoint` — the base-index
  trivializing element at `η` is `1` (cocycle diagonal);
* `thetaFieldRead_eq_germ_fst`/`_snd` — **the reading is a germ at `η`**: with the
  base-index normalization, `thetaFieldRead` is the germ at the generic point of the
  chart component containing `η`;
* `relThetaCocycle_add`/`thetaChartUnit_mul` — exponent additivity of the theta
  cocycle (`pow_add` of the theta unit pushed through the pullback);
* `thetaFieldDivisor_add` — **exponent additivity of the theta divisor** `N₀(a)`
  (elem-multiplicativity + `ordZ` is a monoid map);
* `thetaFieldRead_relThetaWindowEquiv_windowShiftMul` — **the read multiplicativity**
  (the I-0241 germ-at-`η` computation): the reading of the `(M+s)`-window image of a
  multiplied pure tensor is the product of the `s`- and `M`-readings, on the nose (no
  unit — the base-index elems at `η` are all `1`);
* `msCoherenceUnit` + `divOf_msCoherenceUnit` + `map_mulLinear_msCoherenceUnit` —
  **the coherence unit** `w = u_s·u_M·u_{M+s}⁻¹` of the three shift units, with
  `div w = T(M+s) − (N + S)` exactly (theta-divisor additivity kills the `N₀` terms);
* `divFamPhi_one_tmul_mul` — **the `Φ` product law**: `Φ_s(1 ⊗ a) · Φ_M(x)
  = w · Φ_{M+s}((windowShiftMul a) ⊗ x)` — the hcarve bridge of the κ(q) assembly
  (`AlgebraicJacobian.Picard.DivSchemeSeedUnivAssembleKappa`).
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

/-! ## The base-index trivializing element at the generic point -/

section OfCocycle

variable {X : Scheme.{u}} [IsIntegral X]

/-- The trivializing element of the base-index presentation, unfolded. -/
lemma Scheme.MeromorphicPresentation.ofCocycle_elem (𝒰 : X.PointedCover)
    (γ : X.unitsCocycle 𝒰) (x : X) :
    (Scheme.MeromorphicPresentation.ofCocycle 𝒰 γ).elem x
      = Scheme.germGenericUnits (𝒰.genericPoint_mem_inf x (genericPoint X))
          (Scheme.unitsEvInf γ x (genericPoint X)) :=
  rfl

/-- **The base-index normalization**: the trivializing element of the `ofCocycle`
presentation at the generic point itself is `1` — the diagonal value of a unit cocycle
is `1`. -/
lemma Scheme.MeromorphicPresentation.ofCocycle_elem_genericPoint (𝒰 : X.PointedCover)
    (γ : X.unitsCocycle 𝒰) :
    (Scheme.MeromorphicPresentation.ofCocycle 𝒰 γ).elem (genericPoint X) = 1 := by
  rw [Scheme.MeromorphicPresentation.ofCocycle_elem, Scheme.unitsEvInf_self, map_one]

end OfCocycle

/-! ## Exponent additivity of the theta cocycle and the chart units -/

section CocycleAdd

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (B : Type u) [CommRing B] [Algebra k B]
variable (π : C.left ⟶ P1 k) [IsFinite π]

/-- **Exponent additivity of the relative theta cocycle**: `t₀^{a+b} = t₀^a · t₀^b` —
`pow_add` of the field-level theta unit pushed through the (multiplicative) pullback to
the relative curve. -/
lemma relThetaCocycle_add (a b : ℕ) :
    relThetaCocycle C B π (a + b) = relThetaCocycle C B π a * relThetaCocycle C B π b := by
  rw [relThetaCocycle, relThetaCocycle, relThetaCocycle, relUnitCocycle, relUnitCocycle,
    relUnitCocycle, pow_add, map_mul]

/-- **Exponent additivity of the whole-chart theta units**, index pair by index pair:
`1` on the diagonal blocks, `pow_add` (through the restriction) on the cross blocks. -/
lemma thetaChartUnit_mul (a b : ℕ) (i j : (thetaChartCover C B π).index) :
    thetaChartUnit C B π (a + b) i j
      = thetaChartUnit C B π a i j * thetaChartUnit C B π b i j := by
  rcases i with i | i <;> rcases j with j | j
  · exact (one_mul 1).symm
  · change (relCurve C B).unitsRestrict _ (relThetaCocycle C B π (a + b))
      = (relCurve C B).unitsRestrict _ (relThetaCocycle C B π a)
        * (relCurve C B).unitsRestrict _ (relThetaCocycle C B π b)
    rw [relThetaCocycle_add, map_mul]
  · change (relCurve C B).unitsRestrict _ (relThetaCocycle C B π (a + b))⁻¹
      = (relCurve C B).unitsRestrict _ (relThetaCocycle C B π a)⁻¹
        * (relCurve C B).unitsRestrict _ (relThetaCocycle C B π b)⁻¹
    rw [relThetaCocycle_add, mul_inv, map_mul]
  · exact (one_mul 1).symm

end CocycleAdd

/-! ## The reading as a germ at `η`, and the theta-divisor additivity -/

section Reading

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]
variable (a : ℕ)
variable [IsIntegral (relCurve C K)]

/-- The trivializing element of the theta presentation at the generic point is `1`. -/
lemma thetaFieldPresentation_elem_genericPoint :
    (thetaFieldPresentation C K π a).elem (genericPoint (relCurve C K)) = 1 :=
  Scheme.MeromorphicPresentation.ofCocycle_elem_genericPoint _ _

/-- **Elem multiplicativity across exponents**: the trivializing elements of the theta
presentations multiply — the subordinated cocycle values are restrictions of the
whole-chart theta units, which multiply by `pow_add`. -/
lemma thetaFieldPresentation_elem_mul (b : ℕ) (z : relCurve C K) :
    (thetaFieldPresentation C K π (a + b)).elem z
      = (thetaFieldPresentation C K π a).elem z
        * (thetaFieldPresentation C K π b).elem z := by
  have hmem : genericPoint (relCurve C K)
      ∈ (thetaChartCover C K π).pieces (thetaFieldChartIndex C K π z)
        ⊓ (thetaChartCover C K π).pieces
            (thetaFieldChartIndex C K π (genericPoint (relCurve C K))) :=
    ⟨genericPoint_mem_of_nonempty ⟨z, mem_pieces_thetaFieldChartIndex C K π z⟩,
      genericPoint_mem_of_nonempty
        ⟨genericPoint (relCurve C K), mem_pieces_thetaFieldChartIndex C K π _⟩⟩
  have key : ∀ e : ℕ, (thetaFieldPresentation C K π e).elem z
      = Scheme.germGenericUnits hmem
          (thetaChartUnit C K π e (thetaFieldChartIndex C K π z)
            (thetaFieldChartIndex C K π (genericPoint (relCurve C K)))) := by
    intro e
    refine Eq.trans (congrArg (Scheme.germGenericUnits _)
      (gluedSubordCocycle_evInf (thetaChartDatum C K π e).isGluingCocycle
        (thetaFieldPointedCover C K π) (thetaFieldChartIndex C K π) (fun _ => le_rfl)
        z (genericPoint (relCurve C K)))) ?_
    exact Scheme.germGenericUnits_unitsRestrict _ _ _
  rw [key, key, key, thetaChartUnit_mul, map_mul]

variable [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **Exponent additivity of the theta divisor** `N₀(a+b) = N₀(a) + N₀(b)`: the
coefficients are orders of the trivializing elements, which multiply. -/
theorem thetaFieldDivisor_add (b : ℕ) :
    thetaFieldDivisor C K π (a + b)
      = thetaFieldDivisor C K π a + thetaFieldDivisor C K π b := by
  refine Scheme.CurveDivisor.ext_coeffAt fun z hz => ?_
  have hco : ∀ e : ℕ, coeffAt hz (thetaFieldDivisor C K π e)
      = Multiplicative.toAdd (Scheme.ordZ (relCurve C K ↘ Spec (CommRingCat.of K)) hz
          ((thetaFieldPresentation C K π e).elem z)) := fun e =>
    Scheme.coeffAt_presentationDivisor K (thetaFieldPresentation C K π e) hz
  rw [Scheme.CurveDivisor.coeffAt_add, hco, hco, hco,
    thetaFieldPresentation_elem_mul, map_mul, toAdd_mul]

/-- **The reading is a germ at `η`, chart-0 case**: when the generic point lies in the
first pinned chart, `thetaFieldRead` is the germ at `η` of the chart-0 component — the
base-index elem at `η` is `1`, and the glued component at `η` restricts the chart-0
component. -/
lemma thetaFieldRead_eq_germ_fst
    (hη : genericPoint (relCurve C K) ∈ (relCover C K (fiberTwoCover π)).V₀)
    (s : relThetaSections C K π a) :
    thetaFieldRead C K π a s
      = ((relCurve C K).presheaf.germ (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₀)
          (genericPoint (relCurve C K)) ⟨trivial, hη⟩).hom s.val.1 := by
  rw [thetaFieldRead_apply,
    Scheme.MeromorphicPresentation.gluedVal_eq_elem_inv_mul K
      (thetaFieldPresentation C K π a) (genericPoint (relCurve C K)) (W := ⊤) trivial
      (thetaFieldGluedEquiv C K π a s),
    thetaFieldPresentation_elem_genericPoint, inv_one, Units.val_one, one_mul]
  exact germ_thetaFieldGluedEquiv_fst C K π a s hη
    ⟨trivial, (thetaFieldPointedCover C K π).mem_opens _⟩ ⟨trivial, hη⟩

/-- **The reading is a germ at `η`, chart-1 case** (mirror). -/
lemma thetaFieldRead_eq_germ_snd
    (hη : genericPoint (relCurve C K) ∉ (relCover C K (fiberTwoCover π)).V₀)
    (s : relThetaSections C K π a) :
    thetaFieldRead C K π a s
      = ((relCurve C K).presheaf.germ (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₁)
          (genericPoint (relCurve C K))
          ⟨trivial, mem_V₁_of_notMem_V₀ C K π hη⟩).hom s.val.2 := by
  rw [thetaFieldRead_apply,
    Scheme.MeromorphicPresentation.gluedVal_eq_elem_inv_mul K
      (thetaFieldPresentation C K π a) (genericPoint (relCurve C K)) (W := ⊤) trivial
      (thetaFieldGluedEquiv C K π a s),
    thetaFieldPresentation_elem_genericPoint, inv_one, Units.val_one, one_mul]
  exact germ_thetaFieldGluedEquiv_snd C K π a s hη
    ⟨trivial, (thetaFieldPointedCover C K π).mem_opens _⟩
    ⟨trivial, mem_V₁_of_notMem_V₀ C K π hη⟩

end Reading

/-! ## The read multiplicativity across the ledger exponents -/

section ReadMul

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance instOverCleftAssemble : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- (Implementation) Germs commute with `resHom`. -/
private lemma germ_resHom_assemble {X : Scheme.{u}} {W V : X.Opens} (h : W ≤ V) (z : X)
    (hz : z ∈ W) (t : Γ(X, V)) :
    (X.presheaf.germ W z hz).hom (X.resHom h t)
      = (X.presheaf.germ V z (h hz)).hom t :=
  X.presheaf.germ_res_apply (homOfLE h) z hz t

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- The chart-0 multiplier section is the chart-0 component of the `s`-window image of
the pure tensor `1 ⊗ a` — the Kit's pure-tensor computation, read backwards. -/
lemma windowShiftTheta₀_eq
    (hH1S : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π (windowS_choice π hπ g))).H1)
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    windowShiftTheta₀ C π hπ g K a
      = (relCurve C K).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C K π (windowS_choice π hπ g) hH1S (1 ⊗ₜ a)).val.1) :=
  (resHom_relThetaWindowEquiv_one_tmul_fst C π K (windowS_choice π hπ g) hH1S a).symm

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- Mirror of `windowShiftTheta₀_eq` on the second chart. -/
lemma windowShiftTheta₁_eq
    (hH1S : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π (windowS_choice π hπ g))).H1)
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    windowShiftTheta₁ C π hπ g K a
      = (relCurve C K).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C K π (windowS_choice π hπ g) hH1S (1 ⊗ₜ a)).val.2) :=
  (resHom_relThetaWindowEquiv_one_tmul_snd C π K (windowS_choice π hπ g) hH1S a).symm

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
/-- **The read multiplicativity across the ledger exponents** (the I-0241 germ-at-`η`
computation, on the nose — the base-index elems at `η` are all `1`): the reading of the
`(M+s)`-window image of a `windowShiftMul`-multiplied element is the product of the
`s`-reading of the multiplier and the `M`-reading of the element. -/
theorem thetaFieldRead_relThetaWindowEquiv_windowShiftMul
    (hH1S : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π (windowS_choice π hπ g))).H1)
    (hH1M : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π (windowM_choice π hπ g))).H1)
    (hH1MS : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π (windowM_choice π hπ g + windowS_choice π hπ g))).H1)
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤))
    (x : K ⊗[k] ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    thetaFieldRead C K π (windowM_choice π hπ g + windowS_choice π hπ g)
        (relThetaWindowEquiv C K π (windowM_choice π hπ g + windowS_choice π hπ g)
          hH1MS (LinearMap.baseChange K (windowShiftMul hπ g a) x))
      = thetaFieldRead C K π (windowS_choice π hπ g)
          (relThetaWindowEquiv C K π (windowS_choice π hπ g) hH1S (1 ⊗ₜ a))
        * thetaFieldRead C K π (windowM_choice π hπ g)
            (relThetaWindowEquiv C K π (windowM_choice π hπ g) hH1M x) := by
  by_cases hη : genericPoint (relCurve C K) ∈ (relCover C K (fiberTwoCover π)).V₀
  · -- the germ-at-η computation on the first chart
    have hkey := congrArg
      ((relCurve C K).presheaf.germ ((relCover C K (fiberTwoCover π)).V₀)
        (genericPoint (relCurve C K)) hη).hom
      (relThetaWindowEquiv_sectionMul_fst C π hπ g K a hH1M hH1MS x)
    rw [map_mul, windowShiftTheta₀_eq C K π hπ g hH1S a,
      germ_resHom_assemble (le_inf le_top le_rfl), germ_resHom_assemble
        (le_inf le_top le_rfl), germ_resHom_assemble (le_inf le_top le_rfl)] at hkey
    rw [thetaFieldRead_eq_germ_fst C K π _ hη, thetaFieldRead_eq_germ_fst C K π _ hη,
      thetaFieldRead_eq_germ_fst C K π _ hη]
    exact hkey
  · -- mirror on the second chart
    have hkey := congrArg
      ((relCurve C K).presheaf.germ ((relCover C K (fiberTwoCover π)).V₁)
        (genericPoint (relCurve C K)) (mem_V₁_of_notMem_V₀ C K π hη)).hom
      (relThetaWindowEquiv_sectionMul_snd C π hπ g K a hH1M hH1MS x)
    rw [map_mul, windowShiftTheta₁_eq C K π hπ g hH1S a,
      germ_resHom_assemble (le_inf le_top le_rfl), germ_resHom_assemble
        (le_inf le_top le_rfl), germ_resHom_assemble (le_inf le_top le_rfl)] at hkey
    rw [thetaFieldRead_eq_germ_snd C K π _ hη, thetaFieldRead_eq_germ_snd C K π _ hη,
      thetaFieldRead_eq_germ_snd C K π _ hη]
    exact hkey

end ReadMul

/-! ## The `(M,s)`-coherence unit and the `Φ` product law -/

section Coherence

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftAssembleCoh : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **The `(M,s)`-coherence unit**: the product `u_s · u_M · u_{M+s}⁻¹` of the three
class-comparison shift units.  Its divisor is exactly the transported-window
discrepancy `T(M+s) − (N + S)` (`divOf_msCoherenceUnit`), and it realizes the `Φ`
product defect (`divFamPhi_one_tmul_mul`). -/
noncomputable def msCoherenceUnit : (relCurve C K).functionFieldˣ :=
  thetaFieldShiftUnit C K π (windowS_choice π hπ g)
    * thetaFieldShiftUnit C K π (windowM_choice π hπ g)
    * (thetaFieldShiftUnit C K π (windowM_choice π hπ g + windowS_choice π hπ g))⁻¹

/-- **The divisor of the coherence unit is the transported-window discrepancy**:
`div (u_s·u_M·u_{M+s}⁻¹) = T(M+s) − (N + S)` — the theta-divisor terms cancel by the
exponent additivity `thetaFieldDivisor_add`. -/
theorem divOf_msCoherenceUnit :
    windowTransportDivisor C K π (windowM_choice π hπ g + windowS_choice π hπ g)
        - (windowN C K hπ g + windowS C K hπ g)
      = Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
          (msCoherenceUnit C K hπ g) := by
  have hinv : Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
        (thetaFieldShiftUnit C K π (windowM_choice π hπ g + windowS_choice π hπ g))⁻¹
      = -Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
          (thetaFieldShiftUnit C K π
            (windowM_choice π hπ g + windowS_choice π hπ g)) := by
    have h0 := Scheme.divOf_mul (relCurve C K ↘ Spec (CommRingCat.of K))
      (thetaFieldShiftUnit C K π (windowM_choice π hπ g + windowS_choice π hπ g))
      (thetaFieldShiftUnit C K π (windowM_choice π hπ g + windowS_choice π hπ g))⁻¹
    rw [mul_inv_cancel, Scheme.divOf_one] at h0
    exact (neg_eq_of_add_eq_zero_right h0.symm).symm
  rw [msCoherenceUnit, Scheme.divOf_mul, Scheme.divOf_mul, hinv,
    ← divOf_thetaFieldShiftUnit C K π (windowS_choice π hπ g),
    ← divOf_thetaFieldShiftUnit C K π (windowM_choice π hπ g),
    ← divOf_thetaFieldShiftUnit C K π (windowM_choice π hπ g + windowS_choice π hπ g),
    thetaFieldDivisor_add C K π (windowM_choice π hπ g) (windowS_choice π hπ g),
    show windowN C K hπ g
      = windowTransportDivisor C K π (windowM_choice π hπ g) from rfl,
    show windowS C K hπ g
      = windowTransportDivisor C K π (windowS_choice π hπ g) from rfl]
  abel

/-- **The coherence-unit section translation**: multiplication by the coherence unit
carries `H⁰(𝒪(T(M+s) − D))` exactly onto `H⁰(𝒪(N + S − D))` for every divisor `D` —
the `K'`-side bridge between the `Φ`-image at exponent `M+s` and the fibre keystone's
`N + S`. -/
theorem map_mulLinear_msCoherenceUnit (D : (relCurve C K).CurveDivisor) :
    Submodule.map
        (Scheme.mulLinear K ((msCoherenceUnit C K hπ g :
          (relCurve C K).functionFieldˣ) : (relCurve C K).functionField))
        (Scheme.divisorSections K (windowTransportDivisor C K π
          (windowM_choice π hπ g + windowS_choice π hπ g) - D) ⊤)
      = Scheme.divisorSections K
          (windowN C K hπ g + windowS C K hπ g - D) ⊤ := by
  rw [map_mulLinear_divisorSections_top K
    (Units.ne_zero (msCoherenceUnit C K hπ g)) _]
  congr 1
  rw [show Units.mk0 _ (Units.ne_zero (msCoherenceUnit C K hπ g))
      = msCoherenceUnit C K hπ g from Units.ext rfl,
    ← divOf_msCoherenceUnit C K hπ g]
  abel

/-- The top-window instance of the coherence-unit translation:
`w · H⁰(𝒪(T(M+s))) = H⁰(𝒪(N + S))`. -/
theorem map_mulLinear_msCoherenceUnit_top :
    Submodule.map
        (Scheme.mulLinear K ((msCoherenceUnit C K hπ g :
          (relCurve C K).functionFieldˣ) : (relCurve C K).functionField))
        (Scheme.divisorSections K (windowTransportDivisor C K π
          (windowM_choice π hπ g + windowS_choice π hπ g)) ⊤)
      = Scheme.divisorSections K (windowN C K hπ g + windowS C K hπ g) ⊤ := by
  have h := map_mulLinear_msCoherenceUnit C K hπ g 0
  rwa [sub_zero, sub_zero] at h

set_option linter.unusedSectionVars false in
/-- **The `Φ` product law** (the hcarve bridge, worksheet §1.5): the product of a
multiplier value `Φ_s(1 ⊗ a)` with an `M`-window value `Φ_M(x)` is the coherence unit
times the `(M+s)`-window value of the `windowShiftMul`-multiplied element. -/
theorem divFamPhi_one_tmul_mul
    (hH1S : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π (windowS_choice π hπ g))).H1)
    (hH1M : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π (windowM_choice π hπ g))).H1)
    (hH1MS : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π (windowM_choice π hπ g + windowS_choice π hπ g))).H1)
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤))
    (x : K ⊗[k] ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    divFamPhi C K π (windowS_choice π hπ g) hH1S (1 ⊗ₜ a)
        * divFamPhi C K π (windowM_choice π hπ g) hH1M x
      = ((msCoherenceUnit C K hπ g : (relCurve C K).functionFieldˣ) :
            (relCurve C K).functionField)
        * divFamPhi C K π (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
            (LinearMap.baseChange K (windowShiftMul hπ g a) x) := by
  have hphi : ∀ (e : ℕ)
      (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π e)).H1)
      (y : K ⊗[k] ↥(divisorSections k (e • fiberWeilDivisor π) ⊤)),
      divFamPhi C K π e hH1 y
        = ((thetaFieldShiftUnit C K π e : (relCurve C K).functionFieldˣ) :
            (relCurve C K).functionField)
          * thetaFieldRead C K π e (relThetaWindowEquiv C K π e hH1 y) :=
    fun _ _ _ => rfl
  rw [hphi, hphi, hphi,
    thetaFieldRead_relThetaWindowEquiv_windowShiftMul C K π hπ g hH1S hH1M hH1MS a x,
    msCoherenceUnit, Units.val_mul, Units.val_mul]
  rw [Units.val_inv_eq_inv_val]
  have hne : ((thetaFieldShiftUnit C K π
      (windowM_choice π hπ g + windowS_choice π hπ g) :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) ≠ 0 :=
    Units.ne_zero _
  field_simp

end Coherence

end AlgebraicGeometry
