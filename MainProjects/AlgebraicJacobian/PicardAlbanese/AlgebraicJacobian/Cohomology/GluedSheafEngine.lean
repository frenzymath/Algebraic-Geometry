/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafDatum
import AlgebraicJacobian.Cohomology.GluedSheafModule

/-!
# The rigid engine fired on the pinned cocycle datum (DAT-1, stage 1d-i, the engine)

The keystones of `informal/spec-dat-1.md` stage (1d-i): the abstract rigid engine of
`RigidEngine4Assembly`, fired on the glued sheaf of a pinned basic-open cocycle datum
`D : BasicOpenCocycleDatum C B π` (worksheet §3.2) through the pair data
`D.pairData` — the m-chart mirror of `RigidEngine4Engine`, with every hypothesis
discharged from the landed inputs:

* the `AEval'` chart finiteness through the stage-(1c) transitivity
  `moduleFinite_aeval'_glued` and the relative E-i
  (`moduleFinite_aeval'_mulSectionEnd_relFiberCoord₀/₁`) —
  `moduleFinite_aeval'_pair_t₀/t₁`;
* projectivity of the three section modules over `B` through the stage-(1c) transport
  `projective_glued_of_free` and the freeness of the relative chart rings
  (`free_relSections`) — `projective_sections₀/₁/Inf`; the datum's trivializing
  families serve the two pinned charts, and side-0's family restricted along
  `V₀ᴮ ⊓ V₁ᴮ ≤ V₀ᴮ` serves the overlap (the partition witness restricts:
  `BasicOpenCoverData.partitionInf`).

## Keystones

* `datumRigidEngine` — **Kleiman 3.10 (v)⟹(i)+(iii), curve-lite, on the datum**: under
  the complex-form fibrewise-vanishing hypothesis, `H¹(C_B, F_D) = 0` and
  `H⁰(C_B, F_D)` is a finite projective `B`-module.
* `datumRigidEngine_isOpen_vanishing` — the strata openness export (Noetherian-free).
* `datumH0TensorEquiv` — the module-coefficient clause (Kleiman `eq:Q`).
* `datumH0BaseChangeEquiv` — the ring-map clause, abstract kernel form (the
  on-the-nose threading onto `H⁰` of the base-changed sheaf is stage (1d-ii)).
* `datum_subsingleton_pairH1` — the fibre form ⟹ pair form wrapper.

**Staging note (worksheet §3.2, BINDING).** The fibre hypothesis `hfib` is consumed in
COMPLEX form (`Subsingleton (H¹(pair) ⊗ κ(p))`); its sheaf-level discharge gates on the
W6-full seam (DAT-3) and is deliberately NOT attempted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite Polynomial

open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k}

/-! ## The restricted partition witness of the overlap -/

namespace BasicOpenCoverData

variable [IsAffineHom π] (D : BasicOpenCoverData C B π)

/-- The chart-0 partition witness restricts to a partition witness on the overlap of
the pinned charts (the coefficient side of `coverInf`, exposed for span-⊤). -/
lemma partitionInf :
    ∑ j : D.J₀, (relCurve C B).resHom
        (inf_le_left : (relCover C B (fiberTwoCover π)).V₀ ⊓
          (relCover C B (fiberTwoCover π)).V₁ ≤ (relCover C B (fiberTwoCover π)).V₀)
        (D.a₀ j) * D.hInf j = 1 := by
  have hres := congrArg
    ((relCurve C B).resHom (inf_le_left : (relCover C B (fiberTwoCover π)).V₀ ⊓
      (relCover C B (fiberTwoCover π)).V₁ ≤ (relCover C B (fiberTwoCover π)).V₀))
    D.partition₀
  rw [map_sum, map_one] at hres
  rw [← hres]
  exact Finset.sum_congr rfl fun j _ => (map_mul _ _ _).symm

/-- The chart-0 generators span the unit ideal of the chart ring. -/
lemma span_range_h₀ : Ideal.span (Set.range D.h₀) = ⊤ :=
  Ideal.span_range_eq_top_of_sum_eq_one D.a₀ D.h₀ D.partition₀

/-- The chart-1 generators span the unit ideal of the chart ring. -/
lemma span_range_h₁ : Ideal.span (Set.range D.h₁) = ⊤ :=
  Ideal.span_range_eq_top_of_sum_eq_one D.a₁ D.h₁ D.partition₁

/-- The restricted chart-0 generators span the unit ideal of the overlap ring. -/
lemma span_range_hInf : Ideal.span (Set.range D.hInf) = ⊤ :=
  Ideal.span_range_eq_top_of_sum_eq_one
    (fun j => (relCurve C B).resHom inf_le_left (D.a₀ j)) D.hInf D.partitionInf

end BasicOpenCoverData

namespace BasicOpenCocycleDatum

variable [IsFinite π] (D : BasicOpenCocycleDatum C B π)

/-! ## The engine hypotheses, discharged -/

/-- **`AEval'` chart finiteness, chart 0**: the pinned finiteness of the datum pair's
chart-0 lattice, from the relative E-i through the stage-(1c) transitivity
`moduleFinite_aeval'_glued`. -/
theorem moduleFinite_aeval'_pair_t₀ (hπ : π ≫ P1.structureMap k = C.hom) :
    Module.Finite (Polynomial B) (Module.AEval'
      ((D.pairData.pair (relCover_isAffineOpen₀ C B (fiberTwoCover π))
        (relCover_isAffineOpen₁ C B (fiberTwoCover π))).t₀)) := by
  have hA := moduleFinite_aeval'_mulSectionEnd_relFiberCoord₀ C B π hπ
  exact moduleFinite_aeval'_glued B D.pieces D.unit
    (relCover_isAffineOpen₀ C B (fiberTwoCover π)) D.isGluingCocycle
    (fun _ _ _ => rfl) (σ := Sum.inl) (h := D.h₀) (fun _ => le_rfl)
    D.span_range_h₀ (relFiberCoord₀ C B π) hA
    ((D.pairData.pair (relCover_isAffineOpen₀ C B (fiberTwoCover π))
      (relCover_isAffineOpen₁ C B (fiberTwoCover π))).t₀) (fun _ => rfl)

/-- **`AEval'` chart finiteness, chart 1**. -/
theorem moduleFinite_aeval'_pair_t₁ (hπ : π ≫ P1.structureMap k = C.hom) :
    Module.Finite (Polynomial B) (Module.AEval'
      ((D.pairData.pair (relCover_isAffineOpen₀ C B (fiberTwoCover π))
        (relCover_isAffineOpen₁ C B (fiberTwoCover π))).t₁)) := by
  have hA := moduleFinite_aeval'_mulSectionEnd_relFiberCoord₁ C B π hπ
  exact moduleFinite_aeval'_glued B D.pieces D.unit
    (relCover_isAffineOpen₁ C B (fiberTwoCover π)) D.isGluingCocycle
    (fun _ _ _ => rfl) (σ := Sum.inr) (h := D.h₁) (fun _ => le_rfl)
    D.span_range_h₁ (relFiberCoord₁ C B π) hA
    ((D.pairData.pair (relCover_isAffineOpen₀ C B (fiberTwoCover π))
      (relCover_isAffineOpen₁ C B (fiberTwoCover π))).t₁) (fun _ => rfl)

/-- **Projectivity of the chart-0 glued sections over `B`**: the stage-(1c) transport
through the free relative chart ring. -/
theorem projective_sections₀ :
    Module.Projective B
      (D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₀)) := by
  haveI : Module.Free B Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₀) :=
    free_relSections C B (fiberChart₀ π)
      (isAffineOpen_preimage_chartOpen π 0).isCompact
      (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated
  exact projective_glued_of_free B D.pieces D.unit
    (relCover_isAffineOpen₀ C B (fiberTwoCover π)) D.isGluingCocycle
    (fun _ _ _ => rfl) (σ := Sum.inl) (h := D.h₀) (fun _ => le_rfl)
    D.span_range_h₀ ‹_›

/-- **Projectivity of the chart-1 glued sections over `B`**. -/
theorem projective_sections₁ :
    Module.Projective B
      (D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₁)) := by
  haveI : Module.Free B Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₁) :=
    free_relSections C B (fiberChart₁ π)
      (isAffineOpen_preimage_chartOpen π 1).isCompact
      (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated
  exact projective_glued_of_free B D.pieces D.unit
    (relCover_isAffineOpen₁ C B (fiberTwoCover π)) D.isGluingCocycle
    (fun _ _ _ => rfl) (σ := Sum.inr) (h := D.h₁) (fun _ => le_rfl)
    D.span_range_h₁ ‹_›

/-- **Projectivity of the overlap glued sections over `B`** (hence flatness — the
split/flat rigidity inputs of the engine): the overlap chart is served by side-0's
restricted trivializing family through the subordinate-pieces interface. -/
theorem projective_sectionsInf :
    Module.Projective B
      (D.sheaf.obj.obj (op ((relCover C B (fiberTwoCover π)).V₀ ⊓
        (relCover C B (fiberTwoCover π)).V₁))) := by
  haveI : Module.Free B Γ(relCurve C B,
      (relCover C B (fiberTwoCover π)).V₀ ⊓ (relCover C B (fiberTwoCover π)).V₁) :=
    free_relSections C B (fiberChart₀ π ⊓ fiberChart₁ π)
      (fiberTwoCover π).isAffineOpen_inf.isCompact
      (fiberTwoCover π).isAffineOpen_inf.isQuasiSeparated
  exact projective_glued_of_free B D.pieces D.unit
    (relCover C B (fiberTwoCover π)).isAffineOpen_inf D.isGluingCocycle
    (fun _ _ _ => rfl) (σ := fun j : D.J₀ => Sum.inl j) (h := D.hInf)
    (fun j => D.basicOpen_hInf_le j) D.span_range_hInf ‹_›

end BasicOpenCocycleDatum

/-! ## The keystones -/

section Keystones

variable [IsFinite π] (D : BasicOpenCocycleDatum C B π)
variable (hπ : π ≫ P1.structureMap k = C.hom)

/-- (Implementation) The two-lattice pair of the datum's glued sheaf. -/
noncomputable abbrev datumPair :=
  D.pairData.pair (relCover_isAffineOpen₀ C B (fiberTwoCover π))
    (relCover_isAffineOpen₁ C B (fiberTwoCover π))

include hπ in
/-- **The rigid engine on the pinned cocycle datum** (Kleiman 3.10 (v)⟹(i)+(iii),
curve-lite; spec (1d-i), all hypotheses discharged): if every residue-field fibre of
`H¹` of the two-lattice pair of the datum's glued sheaf vanishes (complex form — the
sheaf-level discharge is the W6-full seam), then

* `H¹(C_B, F_D) = 0`,
* `H⁰(C_B, F_D)` is a finite projective `B`-module. -/
theorem datumRigidEngine [IsNoetherianRing B]
    (hfib : ∀ p : PrimeSpectrum B,
      Subsingleton ((datumPair D).H1 ⊗[B] p.asIdeal.ResidueField)) :
    Subsingleton (Sheaf.HModule D.sheaf 1) ∧
      Module.Finite B (Sheaf.HModule D.sheaf 0) ∧
      Module.Projective B (Sheaf.HModule D.sheaf 0) := by
  haveI := D.moduleFinite_aeval'_pair_t₀ hπ
  haveI := D.moduleFinite_aeval'_pair_t₁ hπ
  haveI := D.projective_sections₀
  haveI := D.projective_sections₁
  haveI := D.projective_sectionsInf
  haveI : Module.Projective B
      ((D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₀)) ×
        (D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₁))) :=
    Module.Projective.prod
  exact D.pairData.rigidEngine
    (relCover_isAffineOpen₀ C B (fiberTwoCover π))
    (relCover_isAffineOpen₁ C B (fiberTwoCover π))
    (relCover_sup C B (fiberTwoCover π)) hfib

include hπ in
/-- **The openness export on the datum** (the strata gift): the fibrewise-vanishing
locus of `H¹` of the datum pair is open in `Spec B`. Noetherian-free (COH-1 + RE-2). -/
theorem datumRigidEngine_isOpen_vanishing :
    IsOpen {p : PrimeSpectrum B |
      Subsingleton ((datumPair D).H1 ⊗[B] p.asIdeal.ResidueField)} := by
  haveI := D.moduleFinite_aeval'_pair_t₀ hπ
  haveI := D.moduleFinite_aeval'_pair_t₁ hπ
  exact D.pairData.rigidEngine_isOpen_vanishing
    (relCover_isAffineOpen₀ C B (fiberTwoCover π))
    (relCover_isAffineOpen₁ C B (fiberTwoCover π))

/-- **The module-coefficient clause on the datum** (Kleiman `eq:Q`): on the vanishing
locus, formation of `H⁰(C_B, F_D)` commutes with `⊗_B P` for **every** `B`-module
`P`. -/
noncomputable def datumH0TensorEquiv (hH1 : Subsingleton (datumPair D).H1)
    (P : Type u) [AddCommGroup P] [Module B P] :
    (Sheaf.HModule D.sheaf 0) ⊗[B] P ≃ₗ[B]
      ↥(LinearMap.ker ((datumPair D).diff.rTensor P)) := by
  haveI := D.projective_sectionsInf
  exact D.pairData.h0TensorEquiv
    (relCover_isAffineOpen₀ C B (fiberTwoCover π))
    (relCover_isAffineOpen₁ C B (fiberTwoCover π))
    (relCover_sup C B (fiberTwoCover π)) hH1 P

/-- **The ring-map base-change clause on the datum, abstract half**: on the vanishing
locus, `B' ⊗[B] H⁰(C_B, F_D)` is `B'`-linearly the kernel of the base-changed Čech
differential, for **every** `B`-algebra `B'`. Threading onto `H⁰` of the base-changed
sheaf on the nose is stage (1d-ii) — the RE-5/DAT-3 transport interface. -/
noncomputable def datumH0BaseChangeEquiv (hH1 : Subsingleton (datumPair D).H1)
    (B' : Type u) [CommRing B'] [Algebra B B'] :
    B' ⊗[B] (Sheaf.HModule D.sheaf 0) ≃ₗ[B']
      ↥(LinearMap.ker ((datumPair D).diff.baseChange B')) := by
  haveI := D.projective_sectionsInf
  exact D.pairData.h0BaseChangeEquiv
    (relCover_isAffineOpen₀ C B (fiberTwoCover π))
    (relCover_isAffineOpen₁ C B (fiberTwoCover π))
    (relCover_sup C B (fiberTwoCover π)) hH1 B'

include hπ in
/-- **The vanishing hypothesis in pair form from the fibre form** — convenience
wrapper: COH-1 + Nakayama propagation for the datum pair (Noetherian-free). Consumers
holding the fibrewise hypothesis feed `datumH0TensorEquiv`/`datumH0BaseChangeEquiv`
through this. -/
theorem datum_subsingleton_pairH1
    (hfib : ∀ p : PrimeSpectrum B,
      Subsingleton ((datumPair D).H1 ⊗[B] p.asIdeal.ResidueField)) :
    Subsingleton (datumPair D).H1 := by
  haveI := D.moduleFinite_aeval'_pair_t₀ hπ
  haveI := D.moduleFinite_aeval'_pair_t₁ hπ
  haveI : Module.Finite B (datumPair D).H1 := (datumPair D).moduleFinite_h1
  exact AlgebraicJacobian.RigidEngine.subsingleton_of_forall_subsingleton_residueField_tensor
    hfib

end Keystones

end AlgebraicGeometry
