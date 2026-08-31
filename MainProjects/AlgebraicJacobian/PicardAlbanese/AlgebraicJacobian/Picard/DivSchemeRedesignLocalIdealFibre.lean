/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignRankOneFibre
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# DD-4 redesign: a one-point local-generator fibre lemma

This is the sharp local algebra input for the chart colength.  If, outside a prime `p`,
each element of a submodule is a scalar multiple of `s` after clearing one denominator,
then the residue-field fibre of any map that kills `s` has zero image fibre.

The proof makes the denominator explicit and inverts its nonzero residue in `κ(p)`.  It
does not use flatness, finite generation, or a statement about the whole base fibre.  In
the chart application, the local cofactor hypothesis is the algebraic form of germ
divisibility at the single total point; `RankOneFibre` then supplies the mapped-image
conclusion for `chartIdealColengthModule`.
-/

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

namespace LocalIdealFibre

/-- A local generator at one prime gives a span of the residue-field tensor fibre, and hence
the image of any map killing the generator has zero residue-field fibre.

The hypothesis is stated on the submodule itself: for `x : P`, some `r ∉ p` and `c : B`
satisfy `r • x = c • s` in the ambient module. -/
theorem subsingleton_map_tensor_residueField_of_local_generation
    {B M N : Type u} [CommRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (P : Submodule B M) (f : M →ₗ[B] N) (p : PrimeSpectrum B)
    (s : M) (hsP : s ∈ P)
    (hgen : ∀ x : P, ∃ r : B, r ∉ p.asIdeal ∧
      ∃ c : B, r • (x : M) = c • s)
    (hfs : f s = 0) :
    Subsingleton ((P.map f) ⊗[B] p.asIdeal.ResidueField) := by
  apply RankOneFibre.subsingleton_map_tensor_of_span_singleton P f s hsP
  · intro v
    induction v using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add v w hv hw =>
        obtain ⟨c, hc⟩ := hv
        obtain ⟨d, hd⟩ := hw
        exact ⟨c + d, by simpa only [add_smul] using congrArg₂ (fun x y => x + y) hc hd⟩
    | tmul a x =>
        obtain ⟨r, hr, c, hrc⟩ := hgen x
        have hrcP : r • x = c • (⟨s, hsP⟩ : P) := by
          apply Subtype.ext
          exact hrc
        have hbal :
            (algebraMap B p.asIdeal.ResidueField r) •
                ((1 : p.asIdeal.ResidueField) ⊗ₜ[B] x) =
              (algebraMap B p.asIdeal.ResidueField c) •
                ((1 : p.asIdeal.ResidueField) ⊗ₜ[B] (⟨s, hsP⟩ : P)) := by
          calc
            (algebraMap B p.asIdeal.ResidueField r) •
                ((1 : p.asIdeal.ResidueField) ⊗ₜ[B] x) =
                (1 : p.asIdeal.ResidueField) ⊗ₜ[B] (r • x) := by
                  simp [TensorProduct.tmul_smul]
            _ = (1 : p.asIdeal.ResidueField) ⊗ₜ[B]
                (c • (⟨s, hsP⟩ : P)) := by rw [hrcP]
            _ = (algebraMap B p.asIdeal.ResidueField c) •
                ((1 : p.asIdeal.ResidueField) ⊗ₜ[B] (⟨s, hsP⟩ : P)) := by
                  rw [TensorProduct.tmul_smul]
                  simp
        have hr0 : algebraMap B p.asIdeal.ResidueField r ≠ 0 := by
          intro hr0
          exact hr (Ideal.algebraMap_residueField_eq_zero.mp hr0)
        refine ⟨a * (algebraMap B p.asIdeal.ResidueField r)⁻¹ *
            (algebraMap B p.asIdeal.ResidueField c), ?_⟩
        have hx :
            (1 : p.asIdeal.ResidueField) ⊗ₜ[B] x =
              (algebraMap B p.asIdeal.ResidueField r)⁻¹ •
                ((algebraMap B p.asIdeal.ResidueField c) •
                  ((1 : p.asIdeal.ResidueField) ⊗ₜ[B] (⟨s, hsP⟩ : P))) := by
          calc
            (1 : p.asIdeal.ResidueField) ⊗ₜ[B] x =
                (1 : p.asIdeal.ResidueField) •
                  ((1 : p.asIdeal.ResidueField) ⊗ₜ[B] x) := by rw [one_smul]
            _ = (algebraMap B p.asIdeal.ResidueField r)⁻¹ •
                ((algebraMap B p.asIdeal.ResidueField r) •
                  ((1 : p.asIdeal.ResidueField) ⊗ₜ[B] x)) := by
              rw [smul_smul, inv_mul_cancel₀ hr0, one_smul]
            _ = (algebraMap B p.asIdeal.ResidueField r)⁻¹ •
                ((algebraMap B p.asIdeal.ResidueField c) •
                  ((1 : p.asIdeal.ResidueField) ⊗ₜ[B] (⟨s, hsP⟩ : P))) := by
              rw [hbal]
        symm
        calc
          a ⊗ₜ[B] x = a • ((1 : p.asIdeal.ResidueField) ⊗ₜ[B] x) :=
            TensorProduct.tmul_eq_smul_one_tmul a x
          _ = a • ((algebraMap B p.asIdeal.ResidueField r)⁻¹ •
                ((algebraMap B p.asIdeal.ResidueField c) •
                  ((1 : p.asIdeal.ResidueField) ⊗ₜ[B] (⟨s, hsP⟩ : P)))) := by rw [hx]
          _ = (a * (algebraMap B p.asIdeal.ResidueField r)⁻¹ *
                (algebraMap B p.asIdeal.ResidueField c)) •
                ((1 : p.asIdeal.ResidueField) ⊗ₜ[B] (⟨s, hsP⟩ : P)) := by
              simp only [smul_smul]
              rw [mul_assoc]
  · exact hfs

/-- Ideal-specialized form using the familiar membership statement
`r * x ∈ (e)`.  This is the shape produced by clearing denominators in a chart stalk. -/
theorem subsingleton_ideal_map_tensor_residueField_of_local_generation
    {B N : Type u} [CommRing B] [AddCommGroup N] [Module B N]
    (J : Ideal B) (f : B →ₗ[B] N) (p : PrimeSpectrum B)
    (e : B) (heJ : e ∈ J)
    (hgen : ∀ x : J, ∃ r : B, r ∉ p.asIdeal ∧
      r * (x : B) ∈ Ideal.span ({e} : Set B))
    (hfe : f e = 0) :
    Subsingleton ((Submodule.map f (J : Submodule B B)) ⊗[B] p.asIdeal.ResidueField) := by
  apply subsingleton_map_tensor_residueField_of_local_generation J f p e heJ
  · intro x
    obtain ⟨r, hr, hmem⟩ := hgen x
    obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton' (α := B)).mp hmem
    exact ⟨r, hr, c, by simpa [mul_comm] using hc.symm⟩
  · exact hfe

end LocalIdealFibre

end AlgebraicGeometry
