/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.TensorAway
import AlgebraicJacobian.Descent.UnitDescent

/-!
# Pi-decompositions of the tensor square and cube of a finite product of algebras

Let `A` be a commutative ring and `S : ι → Type u` a finite family of `A`-algebras, with
`P := ∀ i, S i`.  This file records the canonical `A`-algebra identifications

* `Algebra.TensorProduct.piDoubleEquivA : (P ⊗[A] P) ≃ₐ[A] ∀ p : ι × ι, S p.1 ⊗[A] S p.2`,
* `Algebra.TensorProduct.piTripleEquivA :
    (P ⊗[A] (P ⊗[A] P)) ≃ₐ[A] ∀ t : ι × ι × ι, S t.1 ⊗[A] (S t.2.1 ⊗[A] S t.2.2)`,

both obtained from `Algebra.TensorProduct.piPiAlgEquiv`, together with the images of the
simplicial ring maps of `AlgebraicJacobian.Descent.UnitDescent` (`Module.descentIncl₁/₂`,
`Module.descentFace₁₂/₁₃/₂₃`, `Algebra.TensorProduct.lmul'`) through them: each becomes an
index-wise inclusion/face/diagonal on the pairwise tensor products.

Unlike the localization-cover identifications of
`AlgebraicJacobian.Algebra.LocalizationCocycle` (where the tensor products are again `Away`
localizations *over `A`*), here the components `S p.1 ⊗[A] S p.2` need not be localizations
of `A`; consequently the transport lemmas are proved directly by pure-tensor computation
(`Algebra.TensorProduct.ext`, `piPiAlgEquiv_tmul`) rather than by the pi-extensionality
principle `AlgHom.ext_of_isLocalization_pi`.

Finally, for the tower `A → B → P` coming from a finite localization cover `f : ι → B`, the
faithful-flatness plumbing is packaged in `Module.FaithfullyFlat.pi_tower`.
-/

universe u

set_option autoImplicit false

open TensorProduct

namespace Algebra.TensorProduct

variable (A : Type u) [CommRing A] {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]

/-! ## The pi-double and pi-triple decompositions -/

/-- The `A`-algebra identification of `P ⊗[A] P`, `P := ∀ i, S i`, with the product of the
pairwise tensor products `S p.1 ⊗[A] S p.2`. 


 * Provenance: CUSTOM.
-/
noncomputable def piDoubleEquivA :
    ((∀ i, S i) ⊗[A] ∀ i, S i) ≃ₐ[A] ∀ p : ι × ι, S p.1 ⊗[A] S p.2 :=
  Algebra.TensorProduct.piPiAlgEquiv A S S

/-- Provenance: CUSTOM. -/
@[simp]
lemma piDoubleEquivA_tmul (s t : ∀ i, S i) :
    piDoubleEquivA A S (s ⊗ₜ[A] t) = fun p : ι × ι => s p.1 ⊗ₜ[A] t p.2 :=
  rfl

/-- The `A`-algebra identification of `P ⊗[A] (P ⊗[A] P)` with the product of the triple
tensor products `S t.1 ⊗[A] (S t.2.1 ⊗[A] S t.2.2)`. 


 * Provenance: CUSTOM.
-/
noncomputable def piTripleEquivA :
    ((∀ i, S i) ⊗[A] ((∀ i, S i) ⊗[A] ∀ i, S i)) ≃ₐ[A]
      ∀ t : ι × ι × ι, S t.1 ⊗[A] (S t.2.1 ⊗[A] S t.2.2) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (piDoubleEquivA A S)).trans
    (Algebra.TensorProduct.piPiAlgEquiv A S (fun p : ι × ι => S p.1 ⊗[A] S p.2))

/-- Provenance: CUSTOM. -/
lemma piTripleEquivA_tmul (s : ∀ i, S i) (v : (∀ i, S i) ⊗[A] ∀ i, S i) :
    piTripleEquivA A S (s ⊗ₜ[A] v)
      = fun t : ι × ι × ι => s t.1 ⊗ₜ[A] piDoubleEquivA A S v t.2 :=
  rfl

/-! ## The index-wise inclusions, faces and diagonal on the components -/

/-- Index-wise inclusion of the first factor: `S i →ₐ[A] S i ⊗[A] S j`. 


 * Provenance: CUSTOM.
-/
noncomputable def inclLeftA (i j : ι) : S i →ₐ[A] S i ⊗[A] S j :=
  Algebra.TensorProduct.includeLeft

/-- Index-wise inclusion of the second factor: `S j →ₐ[A] S i ⊗[A] S j`. 


 * Provenance: CUSTOM.
-/
noncomputable def inclRightA (i j : ι) : S j →ₐ[A] S i ⊗[A] S j :=
  Algebra.TensorProduct.includeRight

/-- Index-wise face hitting tensor positions `1, 2`. 


 * Provenance: CUSTOM.
-/
noncomputable def faceA₁₂ (i j k : ι) : (S i ⊗[A] S j) →ₐ[A] S i ⊗[A] (S j ⊗[A] S k) :=
  Algebra.TensorProduct.map (AlgHom.id A (S i)) Algebra.TensorProduct.includeLeft

/-- Index-wise face hitting tensor positions `1, 3`. 


 * Provenance: CUSTOM.
-/
noncomputable def faceA₁₃ (i j k : ι) : (S i ⊗[A] S k) →ₐ[A] S i ⊗[A] (S j ⊗[A] S k) :=
  Algebra.TensorProduct.map (AlgHom.id A (S i)) Algebra.TensorProduct.includeRight

/-- Index-wise face hitting tensor positions `2, 3`. 


 * Provenance: CUSTOM.
-/
noncomputable def faceA₂₃ (i j k : ι) : (S j ⊗[A] S k) →ₐ[A] S i ⊗[A] (S j ⊗[A] S k) :=
  Algebra.TensorProduct.includeRight

/-- Index-wise diagonal (multiplication) `S i ⊗[A] S i →ₐ[A] S i`. 
Algebra.TensorProduct.faceA₁₂.



 * Provenance: CUSTOM.
-/
noncomputable def diagA (i : ι) : (S i ⊗[A] S i) →ₐ[A] S i :=
  Algebra.TensorProduct.lmul' A

/-! ## Transport of the simplicial maps -/

variable {A S}

/-- The inclusion `descentIncl₁ : P → P ⊗[A] P` becomes the index-wise left inclusion. 


 * Provenance: CUSTOM.
-/
lemma piDoubleEquivA_descentIncl₁ (s : ∀ i, S i) :
    piDoubleEquivA A S (Module.descentIncl₁ A (∀ i, S i) s)
      = fun p : ι × ι => inclLeftA A S p.1 p.2 (s p.1) := by
  funext p
  simp only [piDoubleEquivA, Module.descentIncl₁_apply, inclLeftA,
    Algebra.TensorProduct.piPiAlgEquiv_tmul, Pi.one_apply,
    Algebra.TensorProduct.includeLeft_apply]

/-- The inclusion `descentIncl₂ : P → P ⊗[A] P` becomes the index-wise right inclusion. 


 * Provenance: CUSTOM.
-/
lemma piDoubleEquivA_descentIncl₂ (s : ∀ i, S i) :
    piDoubleEquivA A S (Module.descentIncl₂ A (∀ i, S i) s)
      = fun p : ι × ι => inclRightA A S p.1 p.2 (s p.2) := by
  funext p
  simp only [piDoubleEquivA, Module.descentIncl₂_apply, inclRightA,
    Algebra.TensorProduct.piPiAlgEquiv_tmul, Pi.one_apply,
    Algebra.TensorProduct.includeRight_apply]

/-- The face `descentFace₂₃` becomes the index-wise `2,3`-face. 


 * Provenance: CUSTOM.
-/
lemma piTripleEquivA_descentFace₂₃ (w : ∀ p : ι × ι, S p.1 ⊗[A] S p.2) :
    piTripleEquivA A S (Module.descentFace₂₃ A (∀ i, S i) ((piDoubleEquivA A S).symm w))
      = fun t : ι × ι × ι => faceA₂₃ A S t.1 t.2.1 t.2.2 (w (t.2.1, t.2.2)) := by
  funext t
  rw [Module.descentFace₂₃_apply, piTripleEquivA_tmul, AlgEquiv.apply_symm_apply]
  simp only [faceA₂₃, Pi.one_apply, Algebra.TensorProduct.includeRight_apply]

/-- The face `descentFace₁₂` becomes the index-wise `1,2`-face. 


 * Provenance: CUSTOM.
-/
lemma piTripleEquivA_descentFace₁₂ (w : ∀ p : ι × ι, S p.1 ⊗[A] S p.2) :
    piTripleEquivA A S (Module.descentFace₁₂ A (∀ i, S i) ((piDoubleEquivA A S).symm w))
      = fun t : ι × ι × ι => faceA₁₂ A S t.1 t.2.1 t.2.2 (w (t.1, t.2.1)) := by
  have key : (piTripleEquivA A S).toAlgHom.comp (Module.descentFace₁₂ A (∀ i, S i))
      = (Pi.algHom A _ fun t : ι × ι × ι =>
          (faceA₁₂ A S t.1 t.2.1 t.2.2).comp (Pi.evalAlgHom A _ (t.1, t.2.1))).comp
            (piDoubleEquivA A S).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro x y
    funext t
    simp [piTripleEquivA_tmul, piDoubleEquivA_tmul, faceA₁₂]
  have h := DFunLike.congr_fun key ((piDoubleEquivA A S).symm w)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply] at h
  exact h

/-- The face `descentFace₁₃` becomes the index-wise `1,3`-face. 


 * Provenance: CUSTOM.
-/
lemma piTripleEquivA_descentFace₁₃ (w : ∀ p : ι × ι, S p.1 ⊗[A] S p.2) :
    piTripleEquivA A S (Module.descentFace₁₃ A (∀ i, S i) ((piDoubleEquivA A S).symm w))
      = fun t : ι × ι × ι => faceA₁₃ A S t.1 t.2.1 t.2.2 (w (t.1, t.2.2)) := by
  have key : (piTripleEquivA A S).toAlgHom.comp (Module.descentFace₁₃ A (∀ i, S i))
      = (Pi.algHom A _ fun t : ι × ι × ι =>
          (faceA₁₃ A S t.1 t.2.1 t.2.2).comp (Pi.evalAlgHom A _ (t.1, t.2.2))).comp
            (piDoubleEquivA A S).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro x y
    funext t
    simp [piTripleEquivA_tmul, piDoubleEquivA_tmul, faceA₁₃]
  have h := DFunLike.congr_fun key ((piDoubleEquivA A S).symm w)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply] at h
  exact h

/-- Multiplication `P ⊗[A] P → P` becomes the index-wise diagonal. 


 * Provenance: CUSTOM.
-/
lemma lmul'_piDoubleEquivA_symm (w : ∀ p : ι × ι, S p.1 ⊗[A] S p.2) :
    Algebra.TensorProduct.lmul' A (S := ∀ i, S i) ((piDoubleEquivA A S).symm w)
      = fun i => diagA A S i (w (i, i)) := by
  have key : Algebra.TensorProduct.lmul' A (S := ∀ i, S i)
      = (Pi.algHom A _ fun i => (diagA A S i).comp (Pi.evalAlgHom A _ (i, i))).comp
          (piDoubleEquivA A S).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro x y
    funext i
    simp [piDoubleEquivA_tmul, diagA]
  have h := DFunLike.congr_fun key ((piDoubleEquivA A S).symm w)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply] at h
  exact h

end Algebra.TensorProduct

/-! ## Faithful flatness of the composite cover tower `A → B → P` -/

namespace Module.FaithfullyFlat

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {ι : Type u} [Fintype ι] (f : ι → B)
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)]
variable [∀ i, Algebra A (S i)] [∀ i, IsScalarTower A B (S i)]
variable [∀ i, IsLocalization.Away (f i) (S i)]

/-- **Faithful flatness of the composite cover tower `A → B → P`.**  If `A → B` is faithfully
flat and `f : ι → B` is a covering family (`span (range f) = ⊤`), then `P := ∀ i, S i` is a
faithfully flat `A`-algebra.  This is the tower over which staged descent (`ε2`) is run. 


 * Provenance: CUSTOM.
-/
theorem pi_tower [Module.FaithfullyFlat A B] (hspan : Ideal.span (Set.range f) = ⊤) :
    Module.FaithfullyFlat A (∀ i, S i) :=
  haveI : Module.FaithfullyFlat B (∀ i, S i) :=
    Module.FaithfullyFlat.pi_of_span_eq_top f hspan
  Module.FaithfullyFlat.trans A B (∀ i, S i)

end Module.FaithfullyFlat
