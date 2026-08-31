/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedUnivGen
import AlgebraicJacobian.Picard.DivSchemeSeedUnivFields
import AlgebraicJacobian.Picard.DivSchemeSeedUnivClose
import AlgebraicJacobian.Picard.SlicingFlat

/-!
# G-4 — the four cheap seed facts of the `seedUniv` close (I-0281)

The Lean-verified sound entry point
`ThetaGeneratorSeed.isGenerator_of_fibrewise_ker_span_of_field_vanishing`
(`Picard/DivSchemeSeedUnivClose.lean`) needs six route-independent fibre facts at
`seedUniv` (`R = R_Z`, `K = divUniversalSeedK`).  The two XL/L fibre-comparison facts
(`hspan`, `hfield`) are the carve's rank-`g` content (a sibling lane).  This file builds
the **four cheap ones**, each a committed keystone the assembly lane feeds individually:

* `seedUniv_hfib` — the fibre-nonvanishing clause, from `seedUniv_sec_h_windowCompare` +
  `relPinnedSectionsMap_relThetaResSide_windowEquiv_ne_zero` + the **no-leak**
  (`notMem_of_basicOpen_relPinnedSectionsMap_algebraMap_ne_bot`): a nonempty fibre of
  `D(relPinnedSectionsMap κ(p) (algebraMap f))` forces `f ∉ p`, via naturality of the
  sections-comparison map over `algebraMap` and the residue-field kernel.
* `seedUniv_hcolFlat` — each ambient colength `Γ(D(h z)) ⧸ (eqn z)` is `R_Z`-flat, from the
  slicing criterion `Module.Flat.quotient_span_singleton_of_forall_tmul_residueField` fed by
  the seed's fibre-regularity (`relPinned_tmul_one_mem_nonZeroDivisors`, i.e. `hfib`).
* `seedUniv_hreg` — the germ of `eqn z` is a stalk nonzerodivisor, the germ-regularity law
  from the seed's fibre-regularity (`germ_eqn_mem_nonZeroDivisors_of_fibre_regular`, without
  the circular `IsGenerator`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

/-! ## The germ-regularity law from fibre-regularity alone (no circular `IsGenerator`)

`ThetaGeneratorSeed.germ_eqn_mem_nonZeroDivisors` (`Picard/DivSchemeFamily.lean`) yields
`hreg` from `D.IsGenerator`, but the `hreg`/`hcolFin`/… facts are *inputs* to
`IsGenerator`, so that route is circular.  These two lemmas re-derive the germ law from the
`fibre_regular` predicate directly (the only part of `IsGenerator` that the germ closer
uses): the fibrewise slicing criterion gives section-level regularity on basic sub-opens,
and a zerodivisor relation at the stalk descends to such a sub-open. -/

section GermRegular

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}
variable {K : Submodule R (relThetaSections C R π a)}

namespace ThetaGeneratorSeed

variable (D : ThetaGeneratorSeed C R π a K)

/-- **Section-level regularity from the fibre-regularity predicate**: the restriction of
`eqn z` to any basic sub-open `D(f) ⊆ D(h z)` is a nonzerodivisor — the slicing criterion
over the Noetherian test ring, fed by the seed's `fibre_regular` predicate (supplied
externally, breaking the `IsGenerator` circularity). -/
theorem res_eqn_mem_nonZeroDivisors_of_fibre_regular [IsNoetherianRing R]
    (hfr : ∀ (z : relCurve C R) (p : PrimeSpectrum R) (f : Γ(relCurve C R, D.piece z)),
      ((relCurve C R).resHom ((relCurve C R).basicOpen_le f) (D.eqn z) ⊗ₜ[R]
          (1 : p.asIdeal.ResidueField)) ∈
        nonZeroDivisors (Γ(relCurve C R, (relCurve C R).basicOpen f) ⊗[R]
          p.asIdeal.ResidueField))
    (z : relCurve C R) (f : Γ(relCurve C R, D.piece z)) :
    (relCurve C R).resHom ((relCurve C R).basicOpen_le f) (D.eqn z)
      ∈ nonZeroDivisors Γ(relCurve C R, (relCurve C R).basicOpen f) := by
  haveI : Module.Flat R Γ(relCurve C R, (relCurve C R).basicOpen f) :=
    flat_sections_basicOpen R (D.isAffineOpen_piece z) (D.flat_sections_piece z) f
  exact Module.Flat.mem_nonZeroDivisors_of_forall_tmul_residueField (fun p => hfr z p f)

/-- **The germ-regularity law from fibre-regularity** (the `hreg` shape, without the
circular `IsGenerator`): every germ of `eqn z` on its piece is a nonzerodivisor.  A
zerodivisor relation at the stalk descends to a basic sub-open, where
`res_eqn_mem_nonZeroDivisors_of_fibre_regular` applies.  (Body mirrors
`ThetaGeneratorSeed.germ_eqn_mem_nonZeroDivisors`, with the `IsGenerator` input replaced by
the `fibre_regular` predicate.) -/
theorem germ_eqn_mem_nonZeroDivisors_of_fibre_regular [IsNoetherianRing R]
    (hfr : ∀ (z : relCurve C R) (p : PrimeSpectrum R) (f : Γ(relCurve C R, D.piece z)),
      ((relCurve C R).resHom ((relCurve C R).basicOpen_le f) (D.eqn z) ⊗ₜ[R]
          (1 : p.asIdeal.ResidueField)) ∈
        nonZeroDivisors (Γ(relCurve C R, (relCurve C R).basicOpen f) ⊗[R]
          p.asIdeal.ResidueField))
    (z : relCurve C R) {y : relCurve C R} (hy : y ∈ D.piece z) :
    ((relCurve C R).presheaf.germ (D.piece z) y hy).hom (D.eqn z)
      ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk y) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro τ hτ
  obtain ⟨V', hyV', t, ht⟩ := (relCurve C R).presheaf.exists_germ_eq τ
  have hyW₀ : y ∈ V' ⊓ D.piece z := ⟨hyV', hy⟩
  have hprod : ((relCurve C R).presheaf.germ (V' ⊓ D.piece z) y hyW₀).hom
      ((relCurve C R).resHom inf_le_left t
        * (relCurve C R).resHom inf_le_right (D.eqn z)) = 0 := by
    rw [map_mul]
    rw [show ((relCurve C R).presheaf.germ (V' ⊓ D.piece z) y hyW₀).hom
        ((relCurve C R).resHom inf_le_left t)
        = ((relCurve C R).presheaf.germ V' y hyV').hom t from
      TopCat.Presheaf.germ_res_apply _ _ _ _ _]
    rw [show ((relCurve C R).presheaf.germ (V' ⊓ D.piece z) y hyW₀).hom
        ((relCurve C R).resHom inf_le_right (D.eqn z))
        = ((relCurve C R).presheaf.germ (D.piece z) y hy).hom (D.eqn z) from
      TopCat.Presheaf.germ_res_apply _ _ _ _ _]
    rw [ht]
    exact hτ
  obtain ⟨W₁, hyW₁, i₁, i₂, heq⟩ := (relCurve C R).presheaf.germ_eq y hyW₀ hyW₀
    ((relCurve C R).resHom inf_le_left t
      * (relCurve C R).resHom inf_le_right (D.eqn z)) 0
    (by rw [hprod, map_zero])
  rw [map_zero] at heq
  obtain ⟨f, hfle, hyf⟩ := (D.isAffineOpen_piece z).exists_basicOpen_le
    (⟨y, hyW₁⟩ : W₁) hy
  have hres := congrArg ((relCurve C R).resHom hfle) heq
  rw [map_zero, show i₁ = homOfLE i₁.le from Subsingleton.elim _ _] at hres
  rw [show (relCurve C R).resHom hfle
      (((relCurve C R).presheaf.map (homOfLE i₁.le).op).hom
        ((relCurve C R).resHom inf_le_left t
          * (relCurve C R).resHom inf_le_right (D.eqn z)))
      = (relCurve C R).resHom (hfle.trans i₁.le)
        ((relCurve C R).resHom inf_le_left t
          * (relCurve C R).resHom inf_le_right (D.eqn z)) from
    Scheme.resHom_resHom _ _ _] at hres
  rw [map_mul, Scheme.resHom_resHom, Scheme.resHom_resHom] at hres
  have ht0 : (relCurve C R).resHom ((hfle.trans i₁.le).trans inf_le_left) t = 0 :=
    (mul_right_mem_nonZeroDivisors_eq_zero_iff
      (D.res_eqn_mem_nonZeroDivisors_of_fibre_regular hfr z f)).mp hres
  rw [← ht, show ((relCurve C R).presheaf.germ V' y hyV').hom t
      = ((relCurve C R).presheaf.germ ((relCurve C R).basicOpen f) y hyf).hom
        ((relCurve C R).resHom ((hfle.trans i₁.le).trans inf_le_left) t) from
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm, ht0, map_zero]

end ThetaGeneratorSeed

end GermRegular

section SeedFacts

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftSeedFacts : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(Scheme.divisorSections k ((windowS_choice π hπ g • fiberWeilDivisor π)
    + (windowM_choice π hπ g • fiberWeilDivisor π)) ⊤))
variable (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)

noncomputable local instance instIsIntegralRelCurveSeedFacts (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveSeedFacts (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveSeedFacts (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveSeedFacts (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveSeedFacts (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveSeedFacts (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

/-! ## The no-leak: a nonempty fibre of `D(algebraMap f)` forces `f ∉ p` -/

set_option maxHeartbeats 1600000 in
-- the side-cased `relSectionsMap`/`overAlgebraMap` naturality forces the `relPinnedChart` ↔
-- chart-preimage defeq through the product spelling, past the default budget
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option linter.unusedSectionVars false in
/-- **Naturality of the pinned sections-comparison map over `algebraMap`**: the compared
image of a pulled-back base element `algebraMap f` is the pullback of the residue image
`algebraMap R_Z κ(p) f`.  From `relSectionsMap_overAlgebraMap` (cased over the side). -/
private lemma relPinnedSectionsMap_algebraMap_eq (b : Bool)
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
    (f : DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) :
    relPinnedSectionsMap C
        (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
        p.asIdeal.ResidueField π b
        (algebraMap
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          Γ(relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
            relPinnedChart C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) π b) f)
      = algebraMap p.asIdeal.ResidueField
          Γ(relCurve C p.asIdeal.ResidueField,
            relPinnedChart C p.asIdeal.ResidueField π b)
          (algebraMap
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
            p.asIdeal.ResidueField f) := by
  rw [Scheme.algebraMap_overSectionsAlgebra, Scheme.algebraMap_overSectionsAlgebra]
  cases b with
  | false =>
    exact relSectionsMap_overAlgebraMap C
      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
      p.asIdeal.ResidueField (fiberChart₀ π) f
  | true =>
    exact relSectionsMap_overAlgebraMap C
      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
      p.asIdeal.ResidueField (fiberChart₁ π) f

set_option maxHeartbeats 1600000 in
-- the residue-field tower `k → R_Z → κ(p)` and the `relPinnedChart`/basic-open defeq drive
-- the naturality rewrite past the default budget
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
/-- **The no-leak** (I-0280 residual, I-0281 hfib input): if the pinned fibre basic open of
`algebraMap f` at `κ(p)` is nonempty, the base element `f` avoids the prime `p`.
Contrapositive: `f ∈ p` sends `f` to `0` in `κ(p)` (`Ideal.algebraMap_residueField_eq_zero`),
so — by the naturality `relPinnedSectionsMap_algebraMap_eq` — the compared section is `0`,
whose basic open is `⊥`. -/
private lemma notMem_of_basicOpen_relPinnedSectionsMap_algebraMap_ne_bot (b : Bool)
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
    (f : DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
    (hne : ((relCurve C p.asIdeal.ResidueField).basicOpen
        (relPinnedSectionsMap C
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          p.asIdeal.ResidueField π b
          (algebraMap
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
            Γ(relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
              relPinnedChart C
                (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                  (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) π b) f)) :
      (relCurve C p.asIdeal.ResidueField).Opens) ≠ ⊥) :
    f ∉ p.asIdeal := by
  intro hf
  apply hne
  rw [relPinnedSectionsMap_algebraMap_eq C hπ g r₁ r₂ b₁ b₂ i j b p f,
    (Ideal.algebraMap_residueField_eq_zero (I := p.asIdeal)).mpr hf, map_zero]
  exact (relCurve C p.asIdeal.ResidueField).toLocallyRingedSpace.basicOpen_zero _

/-! ## `hfib` — fibre nonvanishing of the seed section -/

set_option maxHeartbeats 2400000 in
-- the seed structure fields carry the huge `DivCarveChartRing`/window/`relThetaSections`
-- types; the field-dependency substitution and the `κ(p)` tower re-elaborate them (hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
include hO hχ in
/-- **`hfib` at `seedUniv`** (the fibre-nonvanishing clause of
`isGenerator_of_fibrewise_ker_span_of_field_vanishing`): wherever the seed piece meets the
fibre at `κ(p)`, the compared chart component of the seed section is nonzero.  Threads
`seedUniv_sec_h_windowCompare` (giving `sec z = relThetaWindowEquiv … x`,
`h z = algebraMap f`, and `windowCompare … x ≠ 0` off `V(f)`) through the no-leak (to see
`f ∉ p` from the nonempty fibre) and the reading bridge
`relPinnedSectionsMap_relThetaResSide_windowEquiv_ne_zero`. -/
theorem seedUniv_hfib :
    ∀ (z : relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
      (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)),
      ((relCurve C p.asIdeal.ResidueField).basicOpen
          (relPinnedSectionsMap C
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
            p.asIdeal.ResidueField π
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z)
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).h z)) :
        (relCurve C p.asIdeal.ResidueField).Opens) ≠ ⊥ →
      relPinnedSectionsMap C
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          p.asIdeal.ResidueField π
          ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z)
          (relThetaResSide (windowM_choice π hπ g)
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z) le_rfl
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z)) ≠ 0 := by
  intro z p hne
  obtain ⟨x, f, _hx_mem, hsec, hh, hsurv⟩ :=
    seedUniv_sec_h_windowCompare C hπ g r₁ r₂ b₁ b₂ i j hO hχ z
  have hfp : f ∉ p.asIdeal :=
    notMem_of_basicOpen_relPinnedSectionsMap_algebraMap_ne_bot C hπ g r₁ r₂ b₁ b₂ i j
      ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z) p f (hh ▸ hne)
  rw [hsec]
  exact relPinnedSectionsMap_relThetaResSide_windowEquiv_ne_zero C hπ g r₁ r₂ b₁ b₂ i j
    (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) p
    ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z) x (hsurv p hfp)
    (relPinnedSectionsMap C
      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
      p.asIdeal.ResidueField π
      ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z)
      ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).h z)) hne

/-! ## `hcolFlat` — the ambient colength is `R_Z`-flat -/

set_option maxHeartbeats 2400000 in
-- the seed structure fields carry the huge `DivCarveChartRing`/window/`relThetaSections`
-- types; the colength quotient over the `κ(p)` tower re-elaborates them (recorded hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
include hO hχ in
/-- **`hcolFlat` at `seedUniv`**: each ambient colength `Γ(D(h z)) ⧸ (eqn z)` is `R_Z`-flat.
The pinned-chart sections are flat (`flat_sections_piece`), and the equation is fibrewise
regular (`relPinned_tmul_one_mem_nonZeroDivisors` fed by `seedUniv_hfib`), so the slicing
criterion `Module.Flat.quotient_span_singleton_of_forall_tmul_residueField` applies. -/
theorem seedUniv_hcolFlat :
    ∀ z : relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
      Module.Flat
        (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
        (Γ(relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
            (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).piece z)
          ⧸ Ideal.span {(seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).eqn z}) := by
  intro z
  haveI : Module.Flat
      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
      Γ(relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
          (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).piece z) :=
    (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).flat_sections_piece z
  refine Module.Flat.quotient_span_singleton_of_forall_tmul_residueField (fun p => ?_)
  have hcollapse : (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).eqn z
      = (relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).resHom
          ((relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).basicOpen_le
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).h z))
          (relThetaResSide (windowM_choice π hπ g)
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z) le_rfl
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z)) := by
    rw [resHom_relThetaResSide]; rfl
  rw [hcollapse]
  exact relPinned_tmul_one_mem_nonZeroDivisors C
    (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
    π p.asIdeal.ResidueField ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z)
    ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).h z)
    (relThetaResSide (windowM_choice π hπ g)
      ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z) le_rfl
      ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z))
    (seedUniv_hfib C hπ g r₁ r₂ b₁ b₂ i j hO hχ z p)

/-! ## `hreg` — the germ of the equation is a stalk nonzerodivisor -/

set_option maxHeartbeats 2400000 in
-- the seed structure fields carry the huge `DivCarveChartRing`/window/`relThetaSections`
-- types; the fibrewise regularity over the `κ(p)` tower re-elaborates them (recorded hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
include hO hχ in
/-- **The `seedUniv` fibre-regularity predicate** (the `IsGenerator.fibre_regular` clause,
proved directly from `hfib` without `IsGenerator`): on every basic sub-open of the piece
the restricted equation is a fibrewise nonzerodivisor.  Body mirrors the `fibre_regular`
field of `isGenerator_of_fibre_ne_zero`, with `hfib := seedUniv_hfib`. -/
theorem seedUniv_fibre_regular :
    ∀ (z : relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
      (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
      (f : Γ(relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
        (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).piece z)),
      ((relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).resHom
          ((relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).basicOpen_le f)
          ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).eqn z) ⊗ₜ[
        DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j]
          (1 : p.asIdeal.ResidueField)) ∈
        nonZeroDivisors
          (Γ(relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
              (relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).basicOpen f)
            ⊗[DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j]
              p.asIdeal.ResidueField) := by
  intro z p f
  obtain ⟨u, hBO⟩ := (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).basicOpen_eq_basicOpen_mul z f
  refine tmul_one_mem_nonZeroDivisors_of_eq p.asIdeal.ResidueField hBO _ ?_
  have hcollapse : (relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).resHom hBO.ge
        ((relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).resHom
          ((relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).basicOpen_le f)
          ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).eqn z))
      = (relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).resHom
          ((relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).basicOpen_le
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).h z * u))
          (relThetaResSide (windowM_choice π hπ g)
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z) le_rfl
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z)) := by
    rw [Scheme.resHom_resHom,
      show (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).eqn z
        = relThetaResSide (windowM_choice π hπ g)
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z)
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).piece_le z)
            ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z) from rfl,
      resHom_relThetaResSide, resHom_relThetaResSide]
  rw [hcollapse]
  refine relPinned_tmul_one_mem_nonZeroDivisors C
    (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
    π p.asIdeal.ResidueField ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z)
    ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).h z * u)
    (relThetaResSide (windowM_choice π hπ g)
      ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).side z) le_rfl
      ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).sec z))
    (fun hne => seedUniv_hfib C hπ g r₁ r₂ b₁ b₂ i j hO hχ z p ?_)
  intro hbot
  exact hne (by
    rw [map_mul, (relCurve C p.asIdeal.ResidueField).basicOpen_mul, hbot, bot_inf_eq])

set_option maxHeartbeats 2400000 in
-- the stalk/germ descent over the huge `DivCarveChartRing`/`relThetaSections` piece types
-- re-elaborates the seed structure fields past the default budget (recorded hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
include hO hχ in
/-- **`hreg` at `seedUniv`**: the germ of `eqn z` is a nonzerodivisor in every stalk of the
piece.  The germ-regularity law `germ_eqn_mem_nonZeroDivisors_of_fibre_regular` fed by
`seedUniv_fibre_regular` (no circular `IsGenerator`). -/
theorem seedUniv_hreg :
    ∀ (z : relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
      (y : relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
      (hy : y ∈ (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).piece z),
      ((relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).presheaf.germ
          ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).piece z) y hy).hom
        ((seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).eqn z)
        ∈ nonZeroDivisors
          ((relCurve C (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)).presheaf.stalk y) :=
  fun z y hy =>
    (seedUniv C hπ g r₁ r₂ b₁ b₂ i j hO hχ).germ_eqn_mem_nonZeroDivisors_of_fibre_regular
      (seedUniv_fibre_regular C hπ g r₁ r₂ b₁ b₂ i j hO hχ) z hy

end SeedFacts

end AlgebraicGeometry
