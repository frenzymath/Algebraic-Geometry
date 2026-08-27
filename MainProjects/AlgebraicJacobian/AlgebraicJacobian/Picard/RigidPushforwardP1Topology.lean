/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.FinitenessP1
import AlgebraicJacobian.Picard.RigidPushforward

/-!
# Integrality of `ℙ¹_k` from domain-ness of its two chart rings

This file supplies the *topological half* of the B3 leaf
`IsIntegral ((p1Over k).left)` consumed by
`p1RigidPushforwardStatement_of_leaves_of_isIntegral`
(`Picard/RigidPushforwardGate.lean`).

Everything here is **conditional** on the two chart-ring facts

* `IsDomain Γ(ℙ¹_k, V₀)` and `IsDomain Γ(ℙ¹_k, V₁)`,
* the two charts actually meet: `V₀ ⊓ V₁ ≠ ⊥`,

where `Vᵢ = p1Chart k i` is the standard chart of the concrete model
`ℙ¹_k = ℙ(ULift (Fin 2); Spec k)` (`RiemannRoch/Adelic/FinitenessP1.lean`).
The chart-ring computation `Γ(ℙ¹_k, Vᵢ) ≅ k[t]` — which supplies the
hypotheses — lives elsewhere; this file only turns them into
`IsIntegral (ℙ¹_k)`.

## Route

`IsIntegral X ↔ IrreducibleSpace X ∧ IsReduced X`
(`isIntegral_of_irreducibleSpace_of_isReduced`), and both halves are
assembled from the charts:

* each chart `Vᵢ` is affine (`isAffineOpen_p1Chart`), so `Vᵢ ≅ Spec Γ(X, Vᵢ)`
  and domain-ness of the chart ring makes the chart an integral scheme
  (`isIntegral_p1Chart`);
* the charts cover `X` (`p1Chart_sup_eq_top`), so reducedness is inherited
  from them via `IsReduced.of_openCover` (`isReduced_p1`);
* irreducibility is the two-chart gluing argument: the overlap `W = V₀ ⊓ V₁`
  is a nonempty open subset of the irreducible `V₀`, hence irreducible and
  dense in `V₀`; symmetrically dense in `V₁`; and `V₀ ∪ V₁ = X`, so `W` is a
  dense irreducible subset of `X` and `X = closure W` is irreducible
  (`irreducibleSpace_p1`).
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace Adelic

variable (k : Type u) [Field k]

/-! ## §1. The charts are integral schemes -/

/-- **Each standard chart of `ℙ¹_k` is an integral scheme** as soon as its
section ring is a domain: the chart is affine (`isAffineOpen_p1Chart`), so it
is isomorphic to `Spec Γ(ℙ¹_k, Vᵢ)`, and the spectrum of a domain is
integral. -/
theorem isIntegral_p1Chart (i : ULift.{u} (Fin 2))
    (h : IsDomain Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i)) :
    IsIntegral (p1Chart k i).toScheme := by
  haveI := h
  exact IsIntegral.of_isIso (isAffineOpen_p1Chart k i).isoSpec.inv

/-- The two standard charts form an open cover of `ℙ¹_k` in the sense of
`TopologicalSpace.IsOpenCover`. -/
theorem isOpenCover_p1Chart : IsOpenCover (p1Chart k) := by
  refine le_antisymm le_top ?_
  rw [← p1Chart_sup_eq_top k]
  exact sup_le (le_iSup (p1Chart k) ⟨0⟩) (le_iSup (p1Chart k) ⟨1⟩)

/-! ## §2. Reducedness -/

/-- **`ℙ¹_k` is reduced** when both chart rings are domains: the charts are
integral, hence reduced, and they cover. -/
theorem isReduced_p1
    (h₀ : IsDomain Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩))
    (h₁ : IsDomain Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩)) :
    IsReduced (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))) := by
  have key : ∀ i : ULift.{u} (Fin 2), IsReduced (p1Chart k i).toScheme := by
    rintro ⟨i⟩
    have h2 : (⟨i⟩ : ULift.{u} (Fin 2)) = ⟨0⟩ ∨ (⟨i⟩ : ULift.{u} (Fin 2)) = ⟨1⟩ := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases h2 with h2 | h2 <;> rw [h2]
    · haveI := isIntegral_p1Chart k ⟨0⟩ h₀; infer_instance
    · haveI := isIntegral_p1Chart k ⟨1⟩ h₁; infer_instance
  haveI : ∀ i, IsReduced
      ((Scheme.openCoverOfIsOpenCover _ (p1Chart k) (isOpenCover_p1Chart k)).X i) := key
  exact IsReduced.of_openCover _
    (Scheme.openCoverOfIsOpenCover _ (p1Chart k) (isOpenCover_p1Chart k))

/-! ## §3. Irreducibility -/

/-- **`ℙ¹_k` is an irreducible space** when both chart rings are domains and
the charts meet. -/
theorem irreducibleSpace_p1
    (h₀ : IsDomain Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩))
    (h₁ : IsDomain Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩))
    (hne : p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩ ≠ ⊥) :
    IrreducibleSpace (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))) := by
  haveI := isIntegral_p1Chart k ⟨0⟩ h₀
  haveI := isIntegral_p1Chart k ⟨1⟩ h₁
  set X : Scheme.{u} := ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) with hXdef
  -- The charts, as subsets of `ℙ¹`, are irreducible.
  have hs0 : IsIrreducible (p1Chart k ⟨0⟩ : Set X) := by
    rw [isIrreducible_iff_irreducibleSpace]
    exact inferInstanceAs (IrreducibleSpace (p1Chart k ⟨0⟩).toScheme)
  have hs1 : IsIrreducible (p1Chart k ⟨1⟩ : Set X) := by
    rw [isIrreducible_iff_irreducibleSpace]
    exact inferInstanceAs (IrreducibleSpace (p1Chart k ⟨1⟩).toScheme)
  -- The overlap is a nonempty open subset.
  have hWne : ((p1Chart k ⟨0⟩ : Set X) ∩ (p1Chart k ⟨1⟩ : Set X)).Nonempty := by
    rw [← TopologicalSpace.Opens.coe_inf]
    exact (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne
  have hWne' : ((p1Chart k ⟨1⟩ : Set X) ∩ (p1Chart k ⟨0⟩ : Set X)).Nonempty := by
    rwa [Set.inter_comm]
  -- A nonempty open subset of an irreducible subspace is dense in it.
  have hd0 : (p1Chart k ⟨0⟩ : Set X) ⊆
      closure ((p1Chart k ⟨0⟩ : Set X) ∩ (p1Chart k ⟨1⟩ : Set X)) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hs0.isPreirreducible
      (p1Chart k ⟨1⟩).isOpen hWne
  have hd1 : (p1Chart k ⟨1⟩ : Set X) ⊆
      closure ((p1Chart k ⟨0⟩ : Set X) ∩ (p1Chart k ⟨1⟩ : Set X)) := by
    have := subset_closure_inter_of_isPreirreducible_of_isOpen hs1.isPreirreducible
      (p1Chart k ⟨0⟩).isOpen hWne'
    rwa [Set.inter_comm] at this
  -- The overlap is itself irreducible: it is a nonempty open subset of `V₀`.
  have hWirr : IsIrreducible ((p1Chart k ⟨0⟩ : Set X) ∩ (p1Chart k ⟨1⟩ : Set X)) :=
    ⟨hWne, hs0.isPreirreducible.open_subset
      ((p1Chart k ⟨0⟩).isOpen.inter (p1Chart k ⟨1⟩).isOpen) Set.inter_subset_left⟩
  -- ... and dense in `ℙ¹`, because the two charts cover.
  have hcov : (p1Chart k ⟨0⟩ : Set X) ∪ (p1Chart k ⟨1⟩ : Set X) = Set.univ := by
    rw [← TopologicalSpace.Opens.coe_sup, p1Chart_sup_eq_top, TopologicalSpace.Opens.coe_top]
  have hcl : closure ((p1Chart k ⟨0⟩ : Set X) ∩ (p1Chart k ⟨1⟩ : Set X)) = Set.univ :=
    Set.eq_univ_of_univ_subset (hcov ▸ Set.union_subset hd0 hd1)
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hcl]
  exact isIrreducible_iff_closure.mpr hWirr

/-! ## §4. Integrality -/

/-- **`ℙ¹_k` is integral** when both chart rings are domains and the charts
meet. -/
theorem isIntegral_p1_of_isDomain_charts
    (h₀ : IsDomain Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩))
    (h₁ : IsDomain Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩))
    (hne : p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩ ≠ ⊥) :
    IsIntegral (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))) := by
  haveI := isReduced_p1 k h₀ h₁
  haveI := irreducibleSpace_p1 k h₀ h₁ hne
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- **The form the B3 gate consumes.**  `(p1Over k).left` is the projective
line `ℙ(ULift (Fin 2); Spec k)` on the nose, so this is
`isIntegral_p1_of_isDomain_charts` restated for
`p1RigidPushforwardStatement_of_leaves_of_isIntegral`
(`Picard/RigidPushforwardGate.lean`). -/
theorem isIntegral_p1Over_left_of_isDomain_charts
    (h₀ : IsDomain Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩))
    (h₁ : IsDomain Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩))
    (hne : p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩ ≠ ⊥) :
    IsIntegral ((p1Over k).left) :=
  isIntegral_p1_of_isDomain_charts k h₀ h₁ hne

end Adelic

end AlgebraicGeometry
