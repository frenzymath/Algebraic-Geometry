/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.QuotSupportBaseChange

/-!
# The support of a finite module commutes with base change

`AJC.picrep.divzero`, carrier bridge (a).

This file proves the **carrier identity** the divisor-side reduction of
`Picard/DivSupportQuasiFinite.lean` was missing: for a finite `A`-module `M` and
an `A`-algebra `B`, the support of the base change `B ⊗[A] M` is the contraction
preimage of the support of `M`,

```
Supp_B (B ⊗[A] M) = (Spec B → Spec A)⁻¹ (Supp_A M).
```

The pointwise form `support_baseChange_finite` is the workhorse; the set equality
`support_baseChange_finite_eq` and the emptiness corollaries package it for the
two consuming directions.

## Why this is the bridge, and not a re-spelling

`Picard/QuotSupportBaseChange.lean` already proves the *forward* ideal-sheaf
inclusion `annihilator F ≤ (annihilator (g'^* F)).map g'`, which yields
`supp (g'^* F) ⊆ g'⁻¹ (supp F)` — properness of the *larger* support and nothing
more. The identification of the two carriers appearing in
`Scheme.DivFamily.isFinite_support_of_fibers` (the **support of the fibre**
`schematicSupport (fiberModule …)` versus the **fibre of the support**) needs the
*reverse* inclusion `g'⁻¹ (supp F) ⊆ supp (g'^* F)`, which is exactly what the
reverse direction of `support_baseChange_finite` supplies. It is a genuine
theorem, not a vocabulary rotation on the annihilator: it changes the containing
set from `supp F` to `supp (g'^* F)`, which `rfl` does not identify.

## Proof

At a prime `q : Spec B` with contraction `p = comap q`, membership in the support
of a finite module is nontriviality of the residue-field fibre
(`Module.mem_support_iff_nontrivial_residueField_tensorProduct`). Three canonical
identifications close it:

1. `κ(q) ⊗[B] (B ⊗[A] M) ≃ₗ[κ(q)] κ(q) ⊗[A] M` — base-change cancellation
   (`TensorProduct.AlgebraTensorModule.cancelBaseChange`).
2. `κ(q) ⊗[A] M ≃ₗ[κ(q)] κ(q) ⊗[κ(p)] (κ(p) ⊗[A] M)` — the same cancellation
   through the residue-field extension `κ(p) → κ(q)`
   (`Ideal.ResidueField.map`, which exists because `p = q.comap (algebraMap A B)`),
   with the scalar tower `A → κ(p) → κ(q)` supplied by
   `Ideal.ResidueField.map_algebraMap`.
3. `Nontrivial (κ(q) ⊗[κ(p)] N) ↔ Nontrivial N` — a field extension is faithfully
   flat (`Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right`).

No noetherian, flatness, or finite-presentation hypothesis on `M` beyond
`Module.Finite` (needed only so that support is a closed set of primes and the
residue-field criterion applies).

## References

* [Stacks, Tag 056J] (support and base change); [Stacks, Tag 05DR].
* Mathlib: `Mathlib/RingTheory/LocalRing/Module.lean`
  (`Module.mem_support_iff_nontrivial_residueField_tensorProduct`),
  `Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean`.
-/

set_option autoImplicit false

open CategoryTheory TensorProduct

namespace AlgebraicGeometry

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **Support commutes with base change** (finite module, pointwise form). For a
finite `A`-module `M` and an `A`-algebra `B`, a prime `q` of `B` lies in the
support of the base change `B ⊗[A] M` if and only if its contraction
`comap q` lies in the support of `M`.

The reverse implication `comap q ∈ Supp M → q ∈ Supp (B ⊗ M)` is the inclusion
`g'⁻¹ (supp F) ⊆ supp (g'^* F)` that `Picard/QuotSupportBaseChange.lean`'s
forward annihilator inclusion does not provide, and is the carrier bridge (a)
of `Scheme.DivFamily.isFinite_support_of_fibers`. No flatness hypothesis. -/
theorem support_baseChange_finite (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (q : PrimeSpectrum B) :
    q ∈ Module.support B (B ⊗[A] M) ↔
      PrimeSpectrum.comap (algebraMap A B) q ∈ Module.support A M := by
  set p := PrimeSpectrum.comap (algebraMap A B) q with hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  -- the residue-field extension `κ(p) → κ(q)`, from `p = q.comap (algebraMap A B)`
  have hcom : p.asIdeal = q.asIdeal.comap (algebraMap A B) := rfl
  letI φ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap A B) hcom
  letI algφ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := φ.toAlgebra
  haveI htower : IsScalarTower A p.asIdeal.ResidueField q.asIdeal.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change (algebraMap A q.asIdeal.ResidueField) a = φ _
    rw [Ideal.ResidueField.map_algebraMap,
        IsScalarTower.algebraMap_apply A B q.asIdeal.ResidueField]
  -- 1. cancel the `B`-base change: `κ(q) ⊗[B] (B ⊗[A] M) ≃ κ(q) ⊗[A] M`
  have e1 : Nontrivial (q.asIdeal.ResidueField ⊗[B] (B ⊗[A] M))
      ↔ Nontrivial (q.asIdeal.ResidueField ⊗[A] M) :=
    (AlgebraTensorModule.cancelBaseChange A B q.asIdeal.ResidueField
      q.asIdeal.ResidueField M).toEquiv.nontrivial_congr
  -- 2. re-expand through `κ(p)`: `κ(q) ⊗[A] M ≃ κ(q) ⊗[κ(p)] (κ(p) ⊗[A] M)`
  have e2 : Nontrivial (q.asIdeal.ResidueField ⊗[A] M)
      ↔ Nontrivial (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField]
          (p.asIdeal.ResidueField ⊗[A] M)) :=
    ((AlgebraTensorModule.cancelBaseChange A p.asIdeal.ResidueField
      q.asIdeal.ResidueField q.asIdeal.ResidueField M).toEquiv.nontrivial_congr).symm
  -- 3. `κ(q)` is faithfully flat over the field `κ(p)`
  have e3 : Nontrivial (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField]
        (p.asIdeal.ResidueField ⊗[A] M))
      ↔ Nontrivial (p.asIdeal.ResidueField ⊗[A] M) :=
    Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right
      p.asIdeal.ResidueField q.asIdeal.ResidueField
  rw [e1, e2, e3]

/-- **Support commutes with base change** (finite module, set-equality form): the
support of `B ⊗[A] M` is the contraction preimage of the support of `M`. -/
theorem support_baseChange_finite_eq (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    Module.support B (B ⊗[A] M)
      = PrimeSpectrum.comap (algebraMap A B) ⁻¹' Module.support A M := by
  ext q
  simpa using support_baseChange_finite M q

/-- The base change `B ⊗[A] M` of a finite module has **empty support exactly on the
primes lying over the support of `M`**; in particular if `Supp_A M = ∅` then
`Supp_B (B ⊗[A] M) = ∅`. The direction actually consumed by the divisor-side
reduction: emptiness of every fibre-of-support is emptiness of every
support-of-fibre. -/
theorem support_baseChange_finite_eq_empty_of_isEmpty (M : Type u) [AddCommGroup M]
    [Module A M] [Module.Finite A M] (h : Module.support A M = ∅) :
    Module.support B (B ⊗[A] M) = ∅ := by
  rw [support_baseChange_finite_eq, h, Set.preimage_empty]

private lemma mem_zeroLocus_iff_primeIdealOf_mem
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) (I : Ideal Γ(X, U)) :
    x ∈ X.zeroLocus (U := U) I ↔
      hU.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.zeroLocus I := by
  rw [← hU.fromSpec_preimage_zeroLocus]
  change x ∈ X.zeroLocus (U := U) I ↔
    hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.zeroLocus (U := U) I
  rw [hU.fromSpec_primeIdealOf]

namespace Scheme.Modules

/-- The support of a finitely presented sheaf commutes with pullback, expressed
as equality with the support of the comapped annihilator ideal sheaf. This is
the reverse carrier inclusion missing from the one-sided annihilator map. -/
theorem annihilator_pullback_support_eq_comap
    {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules) [F.IsFinitePresentation] :
    (annihilator ((Scheme.Modules.pullback g).obj F)).support =
      ((annihilator F).comap g).support := by
  haveI hGfp : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation :=
    pullback_isFinitePresentation g F ‹_›
  haveI hFqc : F.IsQuasicoherent := inferInstance
  haveI hGqc : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent := inferInstance
  rw [IdealSheafData.support_comap]
  ext y
  change y ∈ (annihilator ((Scheme.Modules.pullback g).obj F)).support ↔
    g.base y ∈ (annihilator F).support
  obtain ⟨V, hV, hgyV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := g.base y) (U := ⊤) trivial
  have hyV : y ∈ g ⁻¹ᵁ V := hgyV
  obtain ⟨U, hU, hyU, hUle⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y) (U := g ⁻¹ᵁ V) hyV
  letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U hUle).hom.toAlgebra
  letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj F, U) :=
    Module.compHom _ (g.appLE V U hUle).hom
  letI hfinF : Module.Finite Γ(X, V) Γ(F, V) :=
    module_finite_sections_of_isFinitePresentation F ⟨V, hV⟩
  letI hfinG : Module.Finite Γ(Y, U) Γ((Scheme.Modules.pullback g).obj F, U) :=
    module_finite_sections_of_isFinitePresentation
      ((Scheme.Modules.pullback g).obj F) ⟨U, hU⟩
  obtain ⟨⟨e, -⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv g F hU hV hUle
  rw [IdealSheafData.mem_support_iff_of_mem
        (I := annihilator ((Scheme.Modules.pullback g).obj F))
        (U := ⟨U, hU⟩) hyU,
    IdealSheafData.mem_support_iff_of_mem
      (I := annihilator F) (U := ⟨V, hV⟩) hgyV,
    annihilator_ideal ((Scheme.Modules.pullback g).obj F)
      (fun W => module_finite_sections_of_isFinitePresentation _ W) ⟨U, hU⟩,
    annihilator_ideal F
      (fun W => module_finite_sections_of_isFinitePresentation _ W) ⟨V, hV⟩,
    mem_zeroLocus_iff_primeIdealOf_mem hU hyU,
    mem_zeroLocus_iff_primeIdealOf_mem hV hgyV,
    ← Module.support_eq_zeroLocus, ← Module.support_eq_zeroLocus,
    ← e.support_eq, support_baseChange_finite Γ(F, V)]
  have hcom := IsAffineOpen.comap_primeIdealOf_appLE (f := g)
    V hV U hU hUle hyU
  rw [show algebraMap Γ(X, V) Γ(Y, U) = (g.appLE V U hUle).hom from rfl,
    hcom]

/-- Set-theoretic form of `annihilator_pullback_support_eq_comap`: the
schematic-support carrier of a pullback is the inverse image of the original
schematic-support carrier. -/
theorem annihilator_pullback_support_eq_preimage
    {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules) [F.IsFinitePresentation] :
    (annihilator ((Scheme.Modules.pullback g).obj F)).support =
      (annihilator F).support.preimage g.continuous := by
  rw [annihilator_pullback_support_eq_comap, IdealSheafData.support_comap]

end Scheme.Modules

end AlgebraicGeometry
