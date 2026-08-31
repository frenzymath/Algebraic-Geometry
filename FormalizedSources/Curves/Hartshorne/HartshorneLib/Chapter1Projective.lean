/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Hartshorne I.2: projective points and homogeneous zero sets

This file gives a point-set presentation of projective space over a field and
the elementary closure properties of projective algebraic sets.  A homogeneous
polynomial is stored together with its degree.  Zero loci are defined using the
existence of a nonzero representative, so the definition is independent of a
choice of representative without requiring a separate scaling lemma.
-/

set_option autoImplicit false

universe u

open Set
open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace Hartshorne

noncomputable section

section ProjectiveSpace

variable (k : Type u) [Field k] (n : Nat)

/-- The `k`-valued points of projective `n`-space. -/
abbrev ProjectivePoint := Projectivization k (Fin (n + 1) -> k)

/-- The homogeneous coordinate polynomial ring of projective `n`-space. -/
abbrev ProjectivePolynomial := MvPolynomial (Fin (n + 1)) k

/-- A homogeneous polynomial together with the degree witnessing its grading. -/
structure HomogeneousPolynomial where
  degree : Nat
  polynomial : ProjectivePolynomial k n
  isHomogeneous : polynomial.IsHomogeneous degree

namespace HomogeneousPolynomial

instance : Coe (HomogeneousPolynomial k n) (ProjectivePolynomial k n) :=
  ⟨HomogeneousPolynomial.polynomial⟩

@[simp] theorem coe_polynomial (f : HomogeneousPolynomial k n) :
    (f : ProjectivePolynomial k n) = f.polynomial := rfl

/-- The zero homogeneous polynomial, placed in degree zero. -/
def zero : HomogeneousPolynomial k n :=
  ⟨0, 0, MvPolynomial.isHomogeneous_zero _ _ 0⟩

/-- The constant homogeneous polynomial `1`. -/
def one : HomogeneousPolynomial k n :=
  ⟨0, 1, MvPolynomial.isHomogeneous_one _ _⟩

@[simp] theorem zero_polynomial : (zero (k := k) (n := n)).polynomial = 0 := rfl

@[simp] theorem one_polynomial : (one (k := k) (n := n)).polynomial = 1 := rfl

/-- Product of homogeneous polynomials. -/
def mul (f g : HomogeneousPolynomial k n) : HomogeneousPolynomial k n :=
  ⟨f.degree + g.degree, f.polynomial * g.polynomial,
    f.isHomogeneous.mul g.isHomogeneous⟩

@[simp] theorem mul_polynomial (f g : HomogeneousPolynomial k n) :
    (HomogeneousPolynomial.mul k n f g).polynomial = f.polynomial * g.polynomial := rfl

end HomogeneousPolynomial

/-- The zero locus of one homogeneous polynomial in projective space. -/
def projectiveZeroSet (f : HomogeneousPolynomial k n) : Set (ProjectivePoint k n) :=
  {P | ∃ v : Fin (n + 1) -> k, ∃ hv : v ≠ 0,
      Projectivization.mk k v hv = P ∧ MvPolynomial.eval v f.polynomial = 0}

@[simp] theorem mem_projectiveZeroSet (f : HomogeneousPolynomial k n)
    (P : ProjectivePoint k n) :
    P ∈ projectiveZeroSet k n f ↔
      ∃ v : Fin (n + 1) -> k, ∃ hv : v ≠ 0,
        Projectivization.mk k v hv = P ∧ MvPolynomial.eval v f.polynomial = 0 := Iff.rfl

/-- The common projective zero locus of a family of homogeneous polynomials. -/
def commonProjectiveZeroSet (T : Set (HomogeneousPolynomial k n)) :
    Set (ProjectivePoint k n) :=
  {P | ∀ f, f ∈ T -> P ∈ projectiveZeroSet k n f}

@[simp] theorem mem_commonProjectiveZeroSet (T : Set (HomogeneousPolynomial k n))
    (P : ProjectivePoint k n) :
    P ∈ commonProjectiveZeroSet k n T ↔
      ∀ f, f ∈ T -> P ∈ projectiveZeroSet k n f := Iff.rfl

theorem commonProjectiveZeroSet_iUnion {ι : Type*}
    (T : ι -> Set (HomogeneousPolynomial k n)) :
    commonProjectiveZeroSet k n (⋃ i, T i) = ⋂ i, commonProjectiveZeroSet k n (T i) := by
  ext P
  simp only [commonProjectiveZeroSet, Set.mem_iInter]
  constructor
  · intro hP i f hf
    exact hP f (Set.mem_iUnion.mpr ⟨i, hf⟩)
  · intro hP f hf
    rcases Set.mem_iUnion.mp hf with ⟨i, hfi⟩
    exact hP i f hfi

def homogeneousPolynomialProducts (T U : Set (HomogeneousPolynomial k n)) :
    Set (HomogeneousPolynomial k n) :=
  {p | ∃ f ∈ T, ∃ g ∈ U, p = HomogeneousPolynomial.mul k n f g}

theorem commonProjectiveZeroSet_products
    (T U : Set (HomogeneousPolynomial k n)) :
    commonProjectiveZeroSet k n (homogeneousPolynomialProducts k n T U) =
      commonProjectiveZeroSet k n T ∪ commonProjectiveZeroSet k n U := by
  ext P
  simp only [commonProjectiveZeroSet, Set.mem_union]
  constructor
  · intro hP
    by_cases hT : P ∈ commonProjectiveZeroSet k n T
    · exact Or.inl hT
    · right
      intro g hg
      change ¬ (∀ f, f ∈ T -> P ∈ projectiveZeroSet k n f) at hT
      obtain ⟨f, hf⟩ := Classical.not_forall.mp hT
      obtain ⟨hfT, hfnot⟩ := Classical.not_imp.mp hf
      have hprod := hP (HomogeneousPolynomial.mul k n f g)
        ⟨f, hfT, g, hg, rfl⟩
      obtain ⟨v, hv, hPmk, hzero⟩ := hprod
      have hzero' : MvPolynomial.eval v f.polynomial *
          MvPolynomial.eval v g.polynomial = 0 := by
        simpa [HomogeneousPolynomial.mul_polynomial, MvPolynomial.eval_mul] using hzero
      rcases mul_eq_zero.mp hzero' with hfz | hgz
      · exact False.elim (hfnot ⟨v, hv, hPmk, hfz⟩)
      · exact ⟨v, hv, hPmk, hgz⟩
  · intro hP
    rcases hP with hT | hU
    · intro q hq
      rcases hq with ⟨f, hf, g, hg, rfl⟩
      obtain ⟨v, hv, hPm, hzero⟩ := hT f hf
      exact ⟨v, hv, hPm, by simp [HomogeneousPolynomial.mul_polynomial,
        MvPolynomial.eval_mul, hzero]⟩
    · intro q hq
      rcases hq with ⟨f, hf, g, hg, rfl⟩
      obtain ⟨v, hv, hPm, hzero⟩ := hU g hg
      exact ⟨v, hv, hPm, by simp [HomogeneousPolynomial.mul_polynomial,
        MvPolynomial.eval_mul, hzero]⟩

/-- A projective algebraic set is a common zero locus of homogeneous polynomials. -/
def IsProjectiveAlgebraicSet (Y : Set (ProjectivePoint k n)) : Prop :=
  ∃ T : Set (HomogeneousPolynomial k n), commonProjectiveZeroSet k n T = Y

theorem isProjectiveAlgebraicSet_zeroSet (f : HomogeneousPolynomial k n) :
    IsProjectiveAlgebraicSet k n (projectiveZeroSet k n f) := by
  refine ⟨{f}, ?_⟩
  ext P
  simp only [commonProjectiveZeroSet, Set.mem_singleton_iff]
  simp

theorem isProjectiveAlgebraicSet_empty :
    IsProjectiveAlgebraicSet k n (∅ : Set (ProjectivePoint k n)) := by
  refine ⟨{HomogeneousPolynomial.one (k := k) (n := n)}, ?_⟩
  ext P
  simp only [commonProjectiveZeroSet, Set.mem_singleton_iff]
  constructor
  · intro hP
    obtain ⟨v, hv, hPm, hzero⟩ := hP _ rfl
    change MvPolynomial.eval v (1 : ProjectivePolynomial k n) = 0 at hzero
    simp at hzero
  · intro hP
    change False at hP
    exact hP.elim

theorem isProjectiveAlgebraicSet_univ :
    IsProjectiveAlgebraicSet k n (Set.univ : Set (ProjectivePoint k n)) := by
  refine ⟨∅, ?_⟩
  ext P
  simp only [commonProjectiveZeroSet]
  simp

theorem isProjectiveAlgebraicSet_sInter {ι : Type*}
    (Y : ι -> Set (ProjectivePoint k n))
    (hY : ∀ i, IsProjectiveAlgebraicSet k n (Y i)) :
    IsProjectiveAlgebraicSet k n (⋂ i, Y i) := by
  choose T hT using hY
  refine ⟨⋃ i, T i, ?_⟩
  rw [commonProjectiveZeroSet_iUnion]
  congr 1
  funext i
  exact hT i

theorem isProjectiveAlgebraicSet_union {Y Z : Set (ProjectivePoint k n)}
    (hY : IsProjectiveAlgebraicSet k n Y)
    (hZ : IsProjectiveAlgebraicSet k n Z) :
    IsProjectiveAlgebraicSet k n (Y ∪ Z) := by
  rcases hY with ⟨T, hT⟩
  rcases hZ with ⟨U, hU⟩
  refine ⟨homogeneousPolynomialProducts k n T U, ?_⟩
  rw [commonProjectiveZeroSet_products, hT, hU]

end ProjectiveSpace

end
end Hartshorne
