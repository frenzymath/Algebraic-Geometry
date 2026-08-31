/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Rational points of a separably-closed fibre (the commutative-algebra core of DAT-P)

This file is the pure commutative-algebra heart of the density brick **DAT-P** (points over
separably closed fields, worksheet `informal/w4-datum-worksheet.md` §4 DAT-P, §5 risk 4).

The mathematical content: over a **separably closed** field `K`, a nonzero `K`-algebra `S`
which is **étale over the affine line** `K[X] = MvPolynomial (Fin 1) K` has a `K`-point, i.e.
a `K`-algebra homomorphism `S →ₐ[K] K`. This is the ring-theoretic form of "a smooth curve
chart over a separably closed field has a rational point": a standard-smooth chart of relative
dimension `1` is étale over `𝔸¹`
(`RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`), and this file produces
the rational point of the chart.

## The route (`AlgebraicGeometry.SeparablyClosed`)

* `AlgebraicGeometry.SeparablyClosed.instInfiniteOfIsSepClosed` — a separably closed field is
  infinite (`Xⁿ⁺¹ - 1` is separable, hence splits; the same argument mathlib uses for
  algebraically closed fields).
* `AlgebraicGeometry.SeparablyClosed.ratPt` — the rational point of `Spec (K[X])` at a value
  `x : Fin 1 → K` (the maximal ideal `ker (aeval x)`).
* `AlgebraicGeometry.SeparablyClosed.exists_ratPt_mem_range` — for `S ≠ 0` étale over `K[X]`
  and `K` infinite, the image of `Spec S → 𝔸¹` (open, since étale is flat + finitely presented,
  `isOpenMap_comap_of_hasGoingDown_of_finitePresentation`) contains a `K`-rational point of `𝔸¹`
  (a nonzero polynomial over an infinite field has a non-vanishing value,
  `MvPolynomial.funext_iff`).
* `AlgebraicGeometry.SeparablyClosed.exists_algHom_to_base` — a nonzero étale algebra over a
  separably closed field has a `K`-point: it splits as a product of copies of `K`
  (`Algebra.FormallyEtale.equivPiOfIsSepClosed`) and any factor projection is a `K`-point.
* `AlgebraicGeometry.SeparablyClosed.exists_algHom_of_etale_mvPoly` — **the core**: a nonzero
  `K`-algebra étale over `K[X]` has a `K`-point. Fire `exists_ratPt_mem_range`; the fibre over
  the rational base point is a nonzero étale `K`-algebra (base change of étale is étale,
  `Algebra.Etale.baseChange`; nonzero because the base point is in the image), so it has a
  `K`-point (`exists_algHom_to_base`), which pulls back along `includeRight` to a `K`-point of `S`.

The scheme-level density statement ("every nonempty open of the curve over a separably closed
field has a `K`-rational point") is built on top of this core in
`AlgebraicJacobian.Curve.SeparablyClosedPoints`.
-/

set_option autoImplicit false

universe u

open scoped TensorProduct
open MvPolynomial PrimeSpectrum

namespace AlgebraicGeometry.SeparablyClosed

/-- A separably closed field is infinite: `Xⁿ⁺¹ - 1` is separable, hence splits into `n + 1`
distinct roots, so the field has more than `n` elements for every `n`. This mirrors mathlib's
`Infinite` instance for algebraically closed fields, replacing the "splits" input by the
separable-splitting lemma `IsSepClosed.splits_domain`. -/
instance (priority := 500) instInfiniteOfIsSepClosed {K : Type u} [Field K] [IsSepClosed K] :
    Infinite K := by
  apply Infinite.of_not_fintype
  intro hfin
  set n := Fintype.card K with hn
  set f : Polynomial K := Polynomial.X ^ (n + 1) - Polynomial.C 1 with hf
  have hfsep : f.Separable := by
    rw [hf]; exact Polynomial.separable_X_pow_sub_C 1 (by simp [hn]) one_ne_zero
  apply Nat.not_succ_le_self (Fintype.card K)
  have hdeg : f.natDegree = n + 1 := by rw [hf, Polynomial.natDegree_X_pow_sub_C]
  have hroot : n.succ = Fintype.card (f.rootSet K) := by
    rw [Polynomial.card_rootSet_eq_natDegree hfsep (IsSepClosed.splits_domain _ hfsep), hdeg]
  rw [hroot]
  exact Fintype.card_le_of_injective _ Subtype.coe_injective

variable {K : Type u} [Field K]

/-- The `K`-rational point of `Spec (K[X]) = 𝔸¹` associated to a value `x : Fin 1 → K`:
the prime `ker (aeval x)`, i.e. the maximal ideal `(X - x₀)`. -/
noncomputable def ratPt (x : Fin 1 → K) : PrimeSpectrum (MvPolynomial (Fin 1) K) :=
  PrimeSpectrum.comap (aeval x).toRingHom ⊥

/-- Membership of the rational point `ratPt x` in a basic open `D(h)`: it holds iff `h` does not
vanish at `x`. -/
theorem mem_ratPt_basicOpen (x : Fin 1 → K) (h : MvPolynomial (Fin 1) K) :
    ratPt x ∈ basicOpen h ↔ aeval x h ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen]
  simp only [ratPt, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  rw [show ((⊥ : PrimeSpectrum K).asIdeal) = (⊥ : Ideal K) from rfl]
  simp

/-- For a nonzero `K`-algebra `S` étale over the affine line `K[X]` (with `K` infinite), the image
of `Spec S → 𝔸¹` contains a `K`-rational point. Indeed the image is open (étale is flat +
finitely presented, so `isOpenMap_comap_of_hasGoingDown_of_finitePresentation` applies) and
nonempty (`S ≠ 0`), hence contains a nonempty basic open `D(h)`; over the infinite field `K` the
nonzero polynomial `h` has a non-vanishing value `x`, and `ratPt x ∈ D(h)` lies in the image. -/
theorem exists_ratPt_mem_range [Infinite K] {S : Type u} [CommRing S]
    [Algebra (MvPolynomial (Fin 1) K) S] [Algebra.Etale (MvPolynomial (Fin 1) K) S]
    [Nontrivial S] :
    ∃ x : Fin 1 → K, ratPt x ∈ Set.range (comap (algebraMap (MvPolynomial (Fin 1) K) S)) := by
  have hopen : IsOpen (Set.range (comap (algebraMap (MvPolynomial (Fin 1) K) S))) :=
    (isOpenMap_comap_of_hasGoingDown_of_finitePresentation).isOpen_range
  obtain ⟨p, hp⟩ : (Set.range (comap (algebraMap (MvPolynomial (Fin 1) K) S))).Nonempty := by
    obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum S)); exact ⟨_, ⟨q, rfl⟩⟩
  obtain ⟨_, ⟨h, rfl⟩, hpB, hsub⟩ :=
    isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hopen
  have hh : h ≠ 0 := by
    rintro rfl
    simp only [PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot,
      Set.mem_empty_iff_false] at hpB
  obtain ⟨x, hx⟩ : ∃ x : Fin 1 → K, eval x h ≠ eval x 0 :=
    not_forall.mp fun H => hh (MvPolynomial.funext_iff.mpr H)
  refine ⟨x, hsub ?_⟩
  simp only [SetLike.mem_coe]
  rw [mem_ratPt_basicOpen, MvPolynomial.aeval_eq_eval]
  simpa using hx

/-- A nonzero étale algebra over a separably closed field has a `K`-point: it splits as a finite
product of copies of `K` (`Algebra.FormallyEtale.equivPiOfIsSepClosed`), and any factor projection
is a `K`-algebra homomorphism to `K`. -/
theorem exists_algHom_to_base [IsSepClosed K] {A : Type u} [CommRing A] [Algebra K A]
    [Algebra.Etale K A] [Nontrivial A] : Nonempty (A →ₐ[K] K) := by
  have e := Algebra.FormallyEtale.equivPiOfIsSepClosed K A
  obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum A))
  exact ⟨(Pi.evalAlgHom K (fun _ : PrimeSpectrum A => K) p).comp e.toAlgHom⟩

/-- **The commutative-algebra core of DAT-P.** A nonzero `K`-algebra `S` which is étale over the
affine line `K[X]`, with `K` separably closed, has a `K`-point `S →ₐ[K] K`.

Proof: pick a `K`-rational point `x` of `𝔸¹` in the image of `Spec S` (`exists_ratPt_mem_range`).
The fibre `K ⊗[K[X]] S` (base change along `aeval x`) is étale over `K` (`Algebra.Etale.baseChange`)
and nonzero: a prime `q` of `S` lying over `ratPt x` gives a `K[X]`-algebra map
`K ⊗[K[X]] S → S ⧸ q` (via `AlgHom.liftOfSurjective` on the surjection `K[X] ↠ K` and the residue
map `S ↠ S ⧸ q`), whose codomain is nontrivial. Being a nonzero étale `K`-algebra over a separably
closed field, the fibre has a `K`-point (`exists_algHom_to_base`), which composes with the
`K`-algebra map `S →ₐ[K] K ⊗[K[X]] S` (`includeRight`) to a `K`-point of `S`. -/
theorem exists_algHom_of_etale_mvPoly [IsSepClosed K] {S : Type u} [CommRing S] [Algebra K S]
    [Algebra (MvPolynomial (Fin 1) K) S] [IsScalarTower K (MvPolynomial (Fin 1) K) S]
    [Algebra.Etale (MvPolynomial (Fin 1) K) S] [Nontrivial S] :
    Nonempty (S →ₐ[K] K) := by
  obtain ⟨x, hx⟩ := exists_ratPt_mem_range (K := K) (S := S)
  letI algK : Algebra (MvPolynomial (Fin 1) K) K :=
    (aeval x : MvPolynomial (Fin 1) K →ₐ[K] K).toRingHom.toAlgebra
  have hAlg : (algebraMap (MvPolynomial (Fin 1) K) K) = (aeval x).toRingHom := rfl
  haveI : IsScalarTower K (MvPolynomial (Fin 1) K) K := by
    apply IsScalarTower.of_algebraMap_eq; intro a; rw [hAlg]; simp
  haveI hetale : Algebra.Etale K (K ⊗[MvPolynomial (Fin 1) K] S) :=
    Algebra.Etale.baseChange (MvPolynomial (Fin 1) K) S K
  -- the fibre `K ⊗[K[X]] S` is nonzero
  obtain ⟨q, hq⟩ := hx
  have hsurj : Function.Surjective (Algebra.ofId (MvPolynomial (Fin 1) K) K) := by
    intro a; exact ⟨C a, by rw [Algebra.ofId_apply, hAlg]; simp⟩
  have hkerEq : RingHom.ker (algebraMap (MvPolynomial (Fin 1) K) K) =
      RingHom.ker (algebraMap (MvPolynomial (Fin 1) K) (S ⧸ q.asIdeal)) := by
    rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin 1) K) S (S ⧸ q.asIdeal),
      ← RingHom.comap_ker, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, hAlg,
      RingHom.ker_eq_comap_bot]
    simpa [ratPt, PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hq).symm
  let f₁ : K →ₐ[MvPolynomial (Fin 1) K] (S ⧸ q.asIdeal) :=
    AlgHom.liftOfSurjective _ hsurj (Algebra.ofId _ _) (le_of_eq hkerEq)
  let f₂ : S →ₐ[MvPolynomial (Fin 1) K] (S ⧸ q.asIdeal) := IsScalarTower.toAlgHom _ S _
  let Φ := Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)
  haveI : q.asIdeal.IsPrime := q.2
  haveI hntq : Nontrivial (S ⧸ q.asIdeal) := inferInstance
  haveI hnt : Nontrivial (K ⊗[MvPolynomial (Fin 1) K] S) := RingHom.domain_nontrivial Φ.toRingHom
  -- split the fibre and pull the `K`-point back to `S`
  obtain ⟨φ⟩ := exists_algHom_to_base (K := K) (A := K ⊗[MvPolynomial (Fin 1) K] S)
  exact ⟨φ.comp (Algebra.TensorProduct.includeRight.restrictScalars K)⟩

end AlgebraicGeometry.SeparablyClosed
