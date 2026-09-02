/-
Copyright (c) 2026 The StacksPart01Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart01Lib Contributors
-/

import Mathlib.RingTheory.Spectrum.Prime.Polynomial

/-!
# StacksPart01Lib.Charpoly

The characteristic-polynomial criterion for nilpotence after passage to a
residue field (Stacks Project, Tag `00FC`).
-/

namespace StacksPart01

open TensorProduct

/-- A square matrix satisfies its characteristic polynomial
(Stacks, Tag 00DX). -/
theorem matrix_charpoly_aeval_eq_zero
    {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    Polynomial.aeval A A.charpoly = 0 := by
  exact Matrix.aeval_self_charpoly A

/-- For a finite free `R`-algebra, multiplication by `f` is nilpotent after
base change to the residue field at a prime ideal `I` exactly when every
non-leading coefficient of its characteristic polynomial lies in `I`
(Stacks, Tag `00FC`).

The finite-free hypothesis in the source statement is represented by
`Module.Free R A` together with `Module.Finite R A`.
-/
theorem characteristic_polynomial_prime
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A] (f : A) (I : Ideal R)
    [I.IsPrime] :
    IsNilpotent (algebraMap A (A ⊗[R] I.ResidueField) f) ↔
      ∀ i < Module.finrank R A,
        (Algebra.lmul R A f).charpoly.coeff i ∈ I := by
  exact _root_.isNilpotent_tensor_residueField_iff f I

end StacksPart01
