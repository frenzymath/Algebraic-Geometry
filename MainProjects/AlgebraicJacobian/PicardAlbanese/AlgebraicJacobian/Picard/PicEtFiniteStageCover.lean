/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicRepColimitResidual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-!
# Etale algebras descend to a finite subextension

An etale algebra over an algebraic field extension is defined over a finite intermediate
extension.  This is the algebraic finite-stage input for spreading an etale affine cover.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.DatG0

/-- An etale `K`-algebra over an algebraic extension `K/k` descends to an etale algebra over
some finite subextension of `K/k`. -/
theorem exists_finSubext_etale_model
    {k K B : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [CommRing B] [Algebra K B] [Algebra.Etale K B] :
    ∃ (L : FinSubext k K) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra L.1 B₀),
      Algebra.Etale L.1 B₀ ∧ Nonempty (B ≃ₐ[K] K ⊗[L.1] B₀) := by
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, hbase⟩ :=
    Algebra.Etale.exists_subalgebra_fg k K B
  letI : Algebra.IsAlgebraic k A₀ :=
    Algebra.IsAlgebraic.of_injective A₀.val Subtype.val_injective
  let L₀ : IntermediateField k K := Algebra.IsAlgebraic.toIntermediateField A₀
  letI : Algebra.FiniteType k L₀ := by
    change Algebra.FiniteType k A₀
    exact (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  letI : Module.Finite k L₀ := Algebra.finite_of_essFiniteType_of_isAlgebraic
  letI : Algebra L₀ B₀ := by
    change Algebra A₀ B₀
    infer_instance
  let L : FinSubext k K := ⟨L₀, inferInstance⟩
  exact ⟨L, B₀, inferInstance, inferInstance, hB₀, hbase⟩

/-- A presented etale cover of `Spec K` descends, as an etale cover, to a finite subextension
of an algebraic extension `K/k`.  The surjectivity conjunct is the input expected by
`Algebra.EtaleCover.of B₀`. -/
theorem exists_finSubext_etaleCover_model
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (E : Algebra.EtaleCover K) :
    ∃ (L : FinSubext k K) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra L.1 B₀),
      Algebra.Etale L.1 B₀ ∧
        Function.Surjective (PrimeSpectrum.comap (algebraMap L.1 B₀)) ∧
        Nonempty (E.Carrier ≃ₐ[K] K ⊗[L.1] B₀) := by
  obtain ⟨L, B₀, _, _, hB₀, ⟨e⟩⟩ :=
    exists_finSubext_etale_model (k := k) (K := K) (B := E.Carrier)
  haveI : Nontrivial E.Carrier := E.nontrivial_carrier
  haveI : Nontrivial B₀ := by
    by_contra h
    haveI : Subsingleton B₀ := not_nontrivial_iff_subsingleton.mp h
    haveI : Subsingleton (K ⊗[L.1] B₀) := inferInstance
    haveI : Subsingleton E.Carrier := e.toEquiv.subsingleton_congr.mpr inferInstance
    exact false_of_nontrivial_of_subsingleton E.Carrier
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap L.1 B₀)) := by
    intro p
    exact ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩
  exact ⟨L, B₀, inferInstance, inferInstance, hB₀, hsurj, ⟨e⟩⟩

end AlgebraicGeometry.DatG0
