/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.TensorAwayPi
import AlgebraicJacobian.Algebra.LocalizationCocycle
import AlgebraicJacobian.Descent.UnitDescentComposite

/-!
# Assembling componentwise units into a composite descent cocycle (ζ2·ii, G4 + G6)

Let `A` be a commutative ring and `S : ι → Type u` a finite family of `A`-algebras, with
`P := ∀ i, S i`.  A family of units `w i j : (S i ⊗[A] S j)ˣ` assembles, through the
pi-decomposition `Algebra.TensorProduct.piDoubleEquivA`, into a single unit

* `Algebra.TensorProduct.piAssemblyUnit w : (P ⊗[A] P)ˣ`,

the **composite descent unit** of the family.  This file proves the two halves of the
ζ2·ii deliverable at the pure-algebra level, with the component-level identities taken as
hypotheses (they are discharged by the scheme side in
`AlgebraicJacobian.Picard.WitnessAssembly`):

* (G4) `Algebra.TensorProduct.isDescentCocycle_piAssemblyUnit`: if the components are `1`
  on the diagonal (via the index-wise multiplication `diagA`) and satisfy the index-wise
  cocycle identity on triple components (via the faces `faceA₁₂/₁₃/₂₃` of
  `AlgebraicJacobian.Algebra.TensorAwayPi`), the assembled unit is a descent 1-cocycle
  for `A → P`.  This mirrors `IsLocalization.AwayCover.isDescentCocycle_cocycleUnit`, with
  the pi-ext transport lemmas replaced by the pure-tensor transports of `TensorAwayPi`.

* (G6) `IsLocalization.AwayCover.tensorCollapse_piAssemblyUnit`: for a tower `A → B` and a
  finite localization cover `f : ι → B` with models `S i` (`Away (f i)` over `B`) and
  overlap models `T i j` (`Away (f i * f j)` over `B`), the collapse
  `Module.tensorCollapse A B P` of the assembled unit is the descent unit
  `IsLocalization.AwayCover.cocycleUnit` of any cover cocycle `c` matching the components
  under the index-wise collapse `componentCollapse : S i ⊗[A] S j →ₐ[A] T i j`.
  In particular (`diagA_eq_one_of_componentCollapse`) the diagonal hypothesis of (G4) is
  automatic when the components collapse onto a cover cocycle.

The index-wise collapse is the unique `B ⊗[A] B → B`-semilinear comparison between the
two-base localization `S i ⊗[A] S j` (`AlgebraicJacobian.Algebra.TensorAway`) and the
one-base overlap localization `T i j`; on pure tensors it is
`x ⊗ₜ y ↦ inclLeft x * inclRight y` (`componentCollapse_tmul`), and its comparison with
mathlib's `tensorEquiv'` (`tensorEquiv'_tmul`) is an instance of the uniqueness of
`B`-algebra maps out of localizations of `B`.
-/

universe u

set_option autoImplicit false

open TensorProduct

namespace Algebra.TensorProduct

variable (A : Type u) [CommRing A] {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]

/-! ## The assembled unit -/

/-- The **composite descent unit** assembled from a family of componentwise units
`w i j : (S i ⊗[A] S j)ˣ`: the unit of `P ⊗[A] P`, `P := ∀ i, S i`, corresponding to `w`
under the pi-decomposition `piDoubleEquivA`. 


 * Provenance: CUSTOM.
-/
noncomputable def piAssemblyUnit (w : ∀ i j, (S i ⊗[A] S j)ˣ) :
    ((∀ i, S i) ⊗[A] ∀ i, S i)ˣ :=
  Units.map ((piDoubleEquivA A S).symm :
      (∀ p : ι × ι, S p.1 ⊗[A] S p.2) ≃ₐ[A] _).toAlgHom.toRingHom.toMonoidHom
    (Pi.unitOf _ fun p => w p.1 p.2)

lemma piAssemblyUnit_val (w : ∀ i j, (S i ⊗[A] S j)ˣ) :
    (piAssemblyUnit A S w).val
      = (piDoubleEquivA A S).symm (fun p : ι × ι => (w p.1 p.2).val) :=
  rfl

@[simp]
lemma piDoubleEquivA_piAssemblyUnit_val (w : ∀ i j, (S i ⊗[A] S j)ˣ) :
    piDoubleEquivA A S (piAssemblyUnit A S w).val
      = fun p : ι × ι => (w p.1 p.2).val := by
  rw [piAssemblyUnit_val, AlgEquiv.apply_symm_apply]

/-! ## (G4) The descent-cocycle property -/

/-- **The assembled unit of a coherent family of componentwise units is a descent
1-cocycle** (ζ2·ii, G4).  The diagonal condition is the index-wise normalization through
`diagA`; the cocycle condition is the index-wise identity on the triple components,
transported through `piTripleEquivA` by the pure-tensor face lemmas of
`AlgebraicJacobian.Algebra.TensorAwayPi`. 


 * Provenance: CUSTOM.
-/
theorem isDescentCocycle_piAssemblyUnit {w : ∀ i j, (S i ⊗[A] S j)ˣ}
    (hdiag : ∀ i, diagA A S i (w i i).val = 1)
    (hcoc : ∀ i j k,
      faceA₂₃ A S i j k (w j k).val * faceA₁₂ A S i j k (w i j).val
        = faceA₁₃ A S i j k (w i k).val) :
    Module.IsDescentCocycle (piAssemblyUnit A S w) where
  lmul'_eq_one := by
    rw [piAssemblyUnit_val, lmul'_piDoubleEquivA_symm]
    funext i
    exact hdiag i
  cocycle := by
    apply (piTripleEquivA A S).injective
    rw [map_mul, piAssemblyUnit_val, piTripleEquivA_descentFace₂₃,
      piTripleEquivA_descentFace₁₂, piTripleEquivA_descentFace₁₃]
    funext t
    exact hcoc t.1 t.2.1 t.2.2

end Algebra.TensorProduct

namespace IsLocalization.AwayCover

variable {A : Type u} [CommRing A] {ι : Type u}
variable (B : Type u) [CommRing B] [Algebra A B]
variable (f : ι → B)
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
variable [∀ i, Algebra B (S i)] [∀ i, IsScalarTower A B (S i)]
variable [∀ i, IsLocalization.Away (f i) (S i)]
variable (T : ι → ι → Type u) [∀ i j, CommRing (T i j)] [∀ i j, Algebra B (T i j)]
variable [∀ i j, Algebra A (T i j)] [∀ i j, IsScalarTower A B (T i j)]
variable [∀ i j, IsLocalization.Away (f i * f j) (T i j)]

/-! ## (G6) The index-wise collapse and the comparison with the cover cocycle -/

/-- The index-wise collapse `S i ⊗[A] S j →ₐ[A] T i j` from the two-base tensor
localization onto the one-base overlap localization: on pure tensors,
`x ⊗ₜ y ↦ inclLeft x * inclRight y`. 


 * Provenance: CUSTOM.
-/
noncomputable def componentCollapse (i j : ι) : S i ⊗[A] S j →ₐ[A] T i j :=
  Algebra.TensorProduct.lift
    ((inclLeft f S T i j).restrictScalars A)
    ((inclRight f S T i j).restrictScalars A)
    fun _ _ => Commute.all _ _

@[simp]
lemma componentCollapse_tmul (i j : ι) (x : S i) (y : S j) :
    componentCollapse B f S T i j (x ⊗ₜ[A] y)
      = inclLeft f S T i j x * inclRight f S T i j y := by
  simp [componentCollapse]

/-- Mathlib's one-base tensor comparison `tensorEquiv'` computes on pure tensors as
`inclLeft * inclRight` — an instance of the uniqueness of `B`-algebra maps out of a
localization of `B`. -/
lemma tensorEquiv'_tmul (i j : ι) (x : S i) (y : S j) :
    IsLocalization.Away.tensorEquiv' (f i) (f j) (S i) (S j) (T i j) (x ⊗ₜ[B] y)
      = inclLeft f S T i j x * inclRight f S T i j y := by
  haveI := IsLocalization.Away.tensor' (f i) (f j) (S i) (S j)
  have key : (IsLocalization.Away.tensorEquiv' (f i) (f j) (S i) (S j) (T i j)).toAlgHom
      = Algebra.TensorProduct.lift (inclLeft f S T i j) (inclRight f S T i j)
          (fun _ _ => Commute.all _ _) :=
    (IsLocalization.algHom_subsingleton (Submonoid.powers (f i * f j))).elim _ _
  have h := congrArg (fun φ => φ (x ⊗ₜ[B] y)) key
  simpa using h

/-- The collapse `Module.tensorCollapse A B P` computes componentwise through the two
pi-decompositions: it becomes the index-wise `componentCollapse`. 


 * Provenance: CUSTOM.
-/
lemma piDoubleEquiv_tensorCollapse [Fintype ι] [DecidableEq ι]
    (v : (∀ i, S i) ⊗[A] ∀ i, S i) :
    piDoubleEquiv f S T (Module.tensorCollapse A B (∀ i, S i) v)
      = fun p : ι × ι =>
          componentCollapse B f S T p.1 p.2 (Algebra.TensorProduct.piDoubleEquivA A S v p) := by
  induction v with
  | zero => simp only [map_zero]; funext p; simp
  | tmul s t =>
      rw [Module.tensorCollapse_tmul, piDoubleEquiv_tmul,
        Algebra.TensorProduct.piDoubleEquivA_tmul]
      funext p
      rw [tensorEquiv'_tmul B f S T p.1 p.2, componentCollapse_tmul]
  | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      rw [hx, hy]
      funext p
      simp

/-- **The collapse of the assembled unit is the descent unit of the cover cocycle**
(ζ2·ii, G6): if the componentwise units `w i j` collapse onto the values of a family
`c i j : (T i j)ˣ` on the overlap models, then `Module.tensorCollapse` carries
`piAssemblyUnit w` to `cocycleUnit c`. 


 * Provenance: CUSTOM.
-/
theorem tensorCollapse_piAssemblyUnit [Fintype ι] [DecidableEq ι]
    {w : ∀ i j, (S i ⊗[A] S j)ˣ} {c : ∀ i j, (T i j)ˣ}
    (hcol : ∀ i j, componentCollapse B f S T i j (w i j).val = (c i j).val) :
    Units.map (Module.tensorCollapse A B (∀ i, S i)).toRingHom.toMonoidHom
        (Algebra.TensorProduct.piAssemblyUnit A S w)
      = cocycleUnit f S T c := by
  apply Units.ext
  apply (piDoubleEquiv f S T).injective
  rw [piDoubleEquiv_cocycleUnit_val]
  change piDoubleEquiv f S T
      (Module.tensorCollapse A B (∀ i, S i) (Algebra.TensorProduct.piAssemblyUnit A S w).val)
    = fun p : ι × ι => (c p.1 p.2).val
  rw [piDoubleEquiv_tensorCollapse]
  funext p
  rw [Algebra.TensorProduct.piDoubleEquivA_piAssemblyUnit_val]
  exact hcol p.1 p.2

/-- If the components collapse onto a family that is `1` on the diagonal (e.g. a cover
cocycle), the diagonal hypothesis of `isDescentCocycle_piAssemblyUnit` is automatic. 


 * Provenance: CUSTOM.
-/
theorem diagA_eq_one_of_componentCollapse {w : ∀ i j, (S i ⊗[A] S j)ˣ} {c : ∀ i j, (T i j)ˣ}
    (hcol : ∀ i j, componentCollapse B f S T i j (w i j).val = (c i j).val)
    (hdiagc : ∀ i, diag f S T i (c i i).val = 1) (i : ι) :
    Algebra.TensorProduct.diagA A S i (w i i).val = 1 := by
  have hkey : ∀ x : S i ⊗[A] S i,
      diag f S T i (componentCollapse B f S T i i x)
        = Algebra.TensorProduct.diagA A S i x := by
    intro x
    induction x with
    | zero => simp
    | tmul x y =>
        rw [componentCollapse_tmul, map_mul]
        have hL : (diag f S T i).comp (inclLeft f S T i i) = AlgHom.id B (S i) :=
          (IsLocalization.algHom_subsingleton (Submonoid.powers (f i))).elim _ _
        have hR : (diag f S T i).comp (inclRight f S T i i) = AlgHom.id B (S i) :=
          (IsLocalization.algHom_subsingleton (Submonoid.powers (f i))).elim _ _
        rw [show diag f S T i (inclLeft f S T i i x) = x from
            congrArg (fun φ => φ x) hL,
          show diag f S T i (inclRight f S T i i y) = y from
            congrArg (fun φ => φ y) hR]
        rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [← hkey, hcol]
  exact hdiagc i

/-! ## Compatibility of the index-wise faces with the two-base structure maps

The lemmas below compute the composites of the faces `faceA₁₂/₁₃/₂₃` and of
`componentCollapse` with the canonical structure maps
`tensorMap : B ⊗[A] B →ₐ[A] S i ⊗[A] S j` of `AlgebraicJacobian.Algebra.TensorAway`.
They are the pure-tensor halves of the `IsLocalization.ringHom_ext` comparisons run by
the scheme-side bridge (`AlgebraicJacobian.Picard.WitnessAssembly`). -/

open IsLocalization.Away in
/-- The face `faceA₂₃` intertwines the double and triple structure maps over the
simplicial coface `descentFace₂₃`. 


 * Provenance: CUSTOM.
-/
lemma faceA₂₃_comp_tensorMap (i j k : ι) :
    letI := tensorAwayAlgebra A B B (S j) (S k)
    haveI := tensorAwayScalarTower A B B (S j) (S k)
    (Algebra.TensorProduct.faceA₂₃ A S i j k).comp (tensorMap A B B (S j) (S k))
      = (tensorMap A B (B ⊗[A] B) (S i) (S j ⊗[A] S k)).comp (Module.descentFace₂₃ A B) := by
  letI := tensorAwayAlgebra A B B (S j) (S k)
  haveI := tensorAwayScalarTower A B B (S j) (S k)
  apply Algebra.TensorProduct.ext'
  intro x y
  change (1 : S i) ⊗ₜ[A] (algebraMap B (S j) x ⊗ₜ[A] algebraMap B (S k) y)
      = algebraMap B (S i) 1 ⊗ₜ[A] (algebraMap B (S j) x ⊗ₜ[A] algebraMap B (S k) y)
  rw [map_one]

open IsLocalization.Away in
/-- The face `faceA₁₂` intertwines the double and triple structure maps over the
simplicial coface `descentFace₁₂`. 


 * Provenance: CUSTOM.
-/
lemma faceA₁₂_comp_tensorMap (i j k : ι) :
    letI := tensorAwayAlgebra A B B (S j) (S k)
    haveI := tensorAwayScalarTower A B B (S j) (S k)
    (Algebra.TensorProduct.faceA₁₂ A S i j k).comp (tensorMap A B B (S i) (S j))
      = (tensorMap A B (B ⊗[A] B) (S i) (S j ⊗[A] S k)).comp (Module.descentFace₁₂ A B) := by
  letI := tensorAwayAlgebra A B B (S j) (S k)
  haveI := tensorAwayScalarTower A B B (S j) (S k)
  apply Algebra.TensorProduct.ext'
  intro x y
  change algebraMap B (S i) x ⊗ₜ[A] (algebraMap B (S j) y ⊗ₜ[A] (1 : S k))
      = algebraMap B (S i) x ⊗ₜ[A] (algebraMap B (S j) y ⊗ₜ[A] algebraMap B (S k) 1)
  rw [map_one]

open IsLocalization.Away in
/-- The face `faceA₁₃` intertwines the double and triple structure maps over the
simplicial coface `descentFace₁₃`. 


 * Provenance: CUSTOM.
-/
lemma faceA₁₃_comp_tensorMap (i j k : ι) :
    letI := tensorAwayAlgebra A B B (S j) (S k)
    haveI := tensorAwayScalarTower A B B (S j) (S k)
    (Algebra.TensorProduct.faceA₁₃ A S i j k).comp (tensorMap A B B (S i) (S k))
      = (tensorMap A B (B ⊗[A] B) (S i) (S j ⊗[A] S k)).comp (Module.descentFace₁₃ A B) := by
  letI := tensorAwayAlgebra A B B (S j) (S k)
  haveI := tensorAwayScalarTower A B B (S j) (S k)
  apply Algebra.TensorProduct.ext'
  intro x y
  change algebraMap B (S i) x ⊗ₜ[A] ((1 : S j) ⊗ₜ[A] algebraMap B (S k) y)
      = algebraMap B (S i) x ⊗ₜ[A] (algebraMap B (S j) 1 ⊗ₜ[A] algebraMap B (S k) y)
  rw [map_one]

open IsLocalization.Away in
/-- The index-wise collapse intertwines the double structure map with the multiplication
`lmul' : B ⊗[A] B →ₐ[A] B`. 


 * Provenance: CUSTOM.
-/
lemma componentCollapse_comp_tensorMap (i j : ι) :
    (componentCollapse B f S T i j).comp (tensorMap A B B (S i) (S j))
      = (IsScalarTower.toAlgHom A B (T i j)).comp (Algebra.TensorProduct.lmul' A) := by
  apply Algebra.TensorProduct.ext'
  intro x y
  rw [AlgHom.comp_apply, tensorMap_tmul, componentCollapse_tmul,
    (inclLeft f S T i j).commutes, (inclRight f S T i j).commutes,
    ← map_mul, AlgHom.comp_apply, Algebra.TensorProduct.lmul'_apply_tmul]
  rfl

end IsLocalization.AwayCover
