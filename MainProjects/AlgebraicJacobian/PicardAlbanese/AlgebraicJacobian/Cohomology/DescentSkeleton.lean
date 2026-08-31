/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RelativeSectionsLinear

/-!
# The descent skeleton: finite tensor data descend to a finitely generated stage (RE-5, stage i)

The pure-algebra half of RE-5 (worksheet §3.2 mechanism; rigid worksheet §2.4): over a
field `k`, the tensor functor `− ⊗[k] M` commutes with the filtered union
`B = ⋃ B₀` over finitely generated `k`-subalgebras, in the two forms the datum descent
consumes:

* **elements descend** — every element of `B ⊗[k] M` comes from `B₀ ⊗[k] M` for every
  subalgebra `B₀` containing a finite set of tensor components
  (`AlgebraicJacobian.Descent.exists_finset_forall_mem_range_rTensor`);
* **equalities descend for free** — the stage inclusion `B₀ ⊗[k] M → B ⊗[k] M` is
  *injective* (`rTensor_val_injective`; `M` is flat, `k` being a field), so any equality
  of descended elements already holds at the stage.

The geometric face, through the landed free base change
`relSectionsBaseChange : R ⊗[k] Γ(C.left, V) ≃ₗ[R] Γ(C_R, V_R)`
(`RelativeSectionsLinear.lean`):

* `AlgebraicGeometry.relSectionsMap_relSectionsBaseChange` — the comparison square: the
  sections comparison map `Γ(C_R, V_R) → Γ(C_{R'}, V_{R'})` corresponds under the
  base-change equivalences to `rTensor` of the algebra map `R → R'`;
* `AlgebraicGeometry.relSectionsMap_injective` — for an injective `R → R'` (e.g. a
  subalgebra inclusion), the sections comparison map is injective on every qcqs open;
* `AlgebraicGeometry.exists_finset_forall_mem_range_relSectionsMap` — every relative
  section over `B` descends to `Γ(C_{B₀}, V_{B₀})` for every subalgebra `B₀` containing
  a finite set of tensor components.

The quantifier shape "`∃ s : Finset B, ∀ B₀ ⊇ s`" (rather than "`∃ B₀`") lets the datum
descent (`DatumDescent.lean`) collect the finite sets of ALL its finitely many elements
and adjoin them in one stage, with no directed-colimit bookkeeping.
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicJacobian

namespace Descent

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]
variable {M : Type u} [AddCommGroup M] [Module k M]

/-- **Equalities descend for free** (stage-(i) skeleton, injectivity half): the stage
inclusion `B₀ ⊗[k] M → B ⊗[k] M` induced by a `k`-subalgebra `B₀ ⊆ B` is injective —
`M` is flat over the field `k`. Any equality between descended tensor data therefore
already holds at the stage. -/
theorem rTensor_val_injective (B₀ : Subalgebra k B) :
    Function.Injective (LinearMap.rTensor M B₀.val.toLinearMap) :=
  Module.Flat.rTensor_preserves_injective_linearMap
    (M := M) B₀.val.toLinearMap Subtype.val_injective

/-- **Elements descend** (stage-(i) skeleton, existence half): an element of `B ⊗[k] M`
lies in the image of `B₀ ⊗[k] M` for every `k`-subalgebra `B₀` containing a suitable
finite set of tensor components. Together with `Subalgebra.fg_adjoin_finset` this puts
every finite family of tensors inside one finitely generated stage. -/
theorem exists_finset_forall_mem_range_rTensor (x : B ⊗[k] M) :
    ∃ s : Finset B, ∀ B₀ : Subalgebra k B, (s : Set B) ⊆ (B₀ : Set B) →
      x ∈ LinearMap.range (LinearMap.rTensor M B₀.val.toLinearMap) := by
  classical
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  refine ⟨S.image Prod.fst, fun B₀ hs => ?_⟩
  refine ⟨∑ p ∈ S.attach,
    (⟨p.1.1, hs (Finset.mem_image_of_mem Prod.fst p.2)⟩ : B₀) ⊗ₜ[k] p.1.2, ?_⟩
  rw [map_sum, ← Finset.sum_attach S fun p => p.1 ⊗ₜ[k] p.2]
  exact Finset.sum_congr rfl fun p _ => rfl

end Descent

end AlgebraicJacobian

namespace AlgebraicGeometry

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open TopologicalSpace

attribute [local instance] Scheme.overModule Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']

section Square

variable {V : C.left.Opens}

/-- **The comparison square** (stage-(i) bridge): the sections comparison map
`relSectionsMap` over the test-ring change `R → R'` corresponds, under the free base
change `relSectionsBaseChange`, to `rTensor` of the algebra map on the tensor factor. -/
theorem relSectionsMap_relSectionsBaseChange
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (x : R ⊗[k] Γ(C.left, V)) :
    relSectionsMap C R R' V (relSectionsBaseChange C R hV hV' x) =
      relSectionsBaseChange C R' hV hV'
        (LinearMap.rTensor Γ(C.left, V)
          (IsScalarTower.toAlgHom k R R').toLinearMap x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a s =>
    rw [relSectionsBaseChange_tmul, map_mul, relSectionsMap_overAlgebraMap,
      relSectionsMap_pullback, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom', relSectionsBaseChange_tmul]

/-- **Equalities of relative sections descend for free**: over an injective test-ring
change `R → R'` (e.g. a subalgebra inclusion `B₀ ⊆ B`), the sections comparison map is
injective on every qcqs open. -/
theorem relSectionsMap_injective (hinj : Function.Injective (algebraMap R R'))
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left)) :
    Function.Injective (relSectionsMap C R R' V) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (relSectionsBaseChange C R hV hV').surjective x
  obtain ⟨b, rfl⟩ := (relSectionsBaseChange C R hV hV').surjective y
  rw [relSectionsMap_relSectionsBaseChange, relSectionsMap_relSectionsBaseChange] at hxy
  refine congrArg _ (Module.Flat.rTensor_preserves_injective_linearMap
    (M := Γ(C.left, V)) (IsScalarTower.toAlgHom k R R').toLinearMap hinj ?_)
  exact (relSectionsBaseChange C R' hV hV').injective hxy

end Square

section Descent

variable {C}
variable {B : Type u} [CommRing B] [Algebra k B]

/-- **Relative sections descend to a finite stage**: a section of the relative curve
`C_B` over a base-changed qcqs open `V_B` lies in the image of `Γ(C_{B₀}, V_{B₀})` for
every `k`-subalgebra `B₀ ⊆ B` containing a suitable finite set of tensor components
(one finite set per section; the datum descent adjoins the union). -/
theorem exists_finset_forall_mem_range_relSectionsMap {V : C.left.Opens}
    (hV : IsCompact (V : Set C.left)) (hV' : IsQuasiSeparated (V : Set C.left))
    (x : Γ(relCurve C B, (fst C (overSpec k B)).left ⁻¹ᵁ V)) :
    ∃ s : Finset B, ∀ B₀ : Subalgebra k B, (s : Set B) ⊆ (B₀ : Set B) →
      ∃ x₀ : Γ(relCurve C ↥B₀, (fst C (overSpec k ↥B₀)).left ⁻¹ᵁ V),
        relSectionsMap C ↥B₀ B V x₀ = x := by
  obtain ⟨s, hs⟩ := AlgebraicJacobian.Descent.exists_finset_forall_mem_range_rTensor
    (M := Γ(C.left, V)) ((relSectionsBaseChange C B hV hV').symm x)
  refine ⟨s, fun B₀ hB₀ => ?_⟩
  obtain ⟨y, hy⟩ := hs B₀ hB₀
  refine ⟨relSectionsBaseChange C ↥B₀ hV hV' y, ?_⟩
  rw [relSectionsMap_relSectionsBaseChange]
  have hval : (IsScalarTower.toAlgHom k ↥B₀ B).toLinearMap = B₀.val.toLinearMap := by
    ext b; rfl
  rw [hval, hy, LinearEquiv.apply_symm_apply]

end Descent

end AlgebraicGeometry
