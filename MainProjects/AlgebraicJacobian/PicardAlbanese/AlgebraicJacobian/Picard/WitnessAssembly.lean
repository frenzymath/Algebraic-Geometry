/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.WitnessTransport
import AlgebraicJacobian.Algebra.PiAssembly
import AlgebraicJacobian.Picard.AffineTwoCover

/-!
# The composite descent unit of the ζ2·ii pi-assembly (G4–G6 keystones)

This file assembles the glued witness components of
`AlgebraicJacobian.Picard.WitnessComponents` into the composite `A`-descent unit of the
(C1) étale-separatedness campaign: for an Amitsur-coherent Čech witness
`θ' : CoherentCechWitness k A B 𝒩 γ` and a finite basic refinement `P` of `𝒩`, with
section-ring models `S i := Γ(Spec B, D(P.r i))` and `Pi := ∀ i, S i`,

* `AlgebraicGeometry.Over.witnessComponent θ' P i j : (S i ⊗[A] S j)ˣ` — the glued
  witness component transported through the two-base localization identification
  `S i ⊗[A] S j ≃ₐ Γ(Spec (B ⊗[A] B), D(pairSection P i j))`;
* `AlgebraicGeometry.Over.assemblyUnit θ' P : (Pi ⊗[A] Pi)ˣ` (G4) with
  `Over.isDescentCocycle_assemblyUnit` (G4/G5): the assembled unit is an `A`-descent
  1-cocycle — the cocycle identity is the Amitsur identity of the glued components
  (`witnessBasicSection_amitsur`), transported through the triple-tensor identification;
* `AlgebraicGeometry.Over.tensorCollapse_assemblyUnit` (G6): the collapse of the
  assembled unit along `A → Γ(Spec B, ⊤) → Pi` is the descent unit
  `cocycleUnit (P.coverCocycle γ)` of the Zariski cover cocycle — the diagonal collapse
  of the glued components (`witnessBasicSection_collapse`), transported componentwise;
* `AlgebraicGeometry.Over.mapAlgebra_picClass_assemblyUnit` (the ε2 corollary): for
  faithfully flat `A → B`, `CommRing.Pic.mapAlgebra` carries the Picard class of the
  assembled unit to `P.pic γ` — the class equation handed to ζ3.

## The `ΓSpecIso` crossing (design decision, fixed once here)

All section rings of `Spec R` (`R` any of `B`, `B ⊗[A] B`, `B ⊗[A] (B ⊗[A] B)`) carry
mathlib's canonical `Algebra R Γ(Spec R, U)` instance, whose structure map is
**definitionally** `ΓSpecIso.inv` followed by restriction; since
`(overSpec k R).left = Spec (.of R)` holds by `rfl`, these instances apply on the nose.
The bridge between the scheme-side base rings `Γ(Spec R, ⊤)` and the algebra-side rings
`R` is therefore crossed exactly twice, abstractly:

* `isLocalization_away_sections`: the section ring on `D(g)` is the `Away` localization
  of `R` **at the element `ΓSpecIso.hom g : R`** (transport of the canonical
  `Γ(Spec R, ⊤)`-localization along `ΓSpecIso` via `IsLocalization.of_ringEquiv_left`);
* `ΓSpecIso_hom_appTop`: `ΓSpecIso.hom` intertwines `appTop` of `Spec.map f` with `f`
  (mathlib's `ΓSpecIso_naturality`, elementwise); consequently the localization elements
  `ΓSpecIso.hom (pairSection/tripleSection)` are the tensor elements
  `(bᵢ ⊗ 1)(1 ⊗ bⱼ)` for `b i := ΓSpecIso.hom (P.r i) : B`.

The `A`-algebra structures on the section rings (needed for the `⊗[A]`-tensor products)
are the composites through the canonical `R`-structures; they are `local instance`s of
this file, so no global instance is added.  The intermediate ring of the collapse tower
`A → Γ(Spec B, ⊤) → Pi` is the scheme-side base ring `Γ(Spec B, ⊤)` itself (NOT `B`), so
that G6 and the ε2 corollary land verbatim in the vocabulary of
`Scheme.PointedCover.BasicRefinement.pic` and the Čech–Picard dictionary.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

set_option quotPrecheck false in
local notation "XB" => (overSpec k B).left
set_option quotPrecheck false in
local notation "Sq" => (overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "Scb" => (overSpec k (B ⊗[A] (B ⊗[A] B))).left
set_option quotPrecheck false in
local notation "q₁" => (Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "q₂" => (Over.overSpecMap (tensorInr (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "f₁₂" => (Over.overSpecMap (tensorFace₁₂ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "f₁₃" => (Over.overSpecMap (tensorFace₁₃ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "f₂₃" => (Over.overSpecMap (tensorFace₂₃ (k := k) (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "Δs" => (Over.overSpecMap (tensorMul (k := k) (A := A) (B := B))).left


-- Reactivate the section-ring algebra structures of
-- `AlgebraicJacobian.Picard.WitnessAway` (they are `local instance`s there).
attribute [local instance] specSectionsAlgebra overSpecSectionsAlgebra
  overSpecSectionsAlgebraSq overSpecSectionsAlgebraScb algebraA_sections
  isScalarTower_sections isScalarTower_sections_basicOpen

namespace Over

variable {𝒩 : ((overSpec k B).left).PointedCover}
variable {γ : ((overSpec k B).left).unitsCocycle 𝒩}
variable (P : 𝒩.BasicRefinement)

/-! ## The keystones: the composite descent unit and its properties (G4–G6) -/

variable (θ' : CoherentCechWitness k A B 𝒩 γ)

/-- **The witness component** (ζ2·ii, G5): the glued corrected witness unit on the
double basic open, transported into the tensor product of the section rings. -/
noncomputable def witnessComponent (i j : P.ι) :
    (Γ(XB, (XB).basicOpen (P.r i)) ⊗[A] Γ(XB, (XB).basicOpen (P.r j)))ˣ :=
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r i))
    Γ(XB, (XB).basicOpen (P.r j))
  Units.map ((pairAwayEquiv P i j).symm.toAlgHom.toRingHom.toMonoidHom)
    (witnessBasicSection P θ' i j)

lemma pairAwayEquiv_witnessComponent_val (i j : P.ι) :
    pairAwayEquiv P i j (witnessComponent P θ' i j).val
      = (witnessBasicSection P θ' i j).val := by
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r i))
    Γ(XB, (XB).basicOpen (P.r j))
  change pairAwayEquiv P i j
      ((pairAwayEquiv P i j).symm (witnessBasicSection P θ' i j).val) = _
  exact AlgEquiv.apply_symm_apply _ _

/-- **The composite descent unit of the pi-assembly** (ζ2·ii, G4): the witness
components assembled into a unit of `Pi ⊗[A] Pi`, `Pi := ∀ i, Γ(Spec B, D(P.r i))`. -/
noncomputable def assemblyUnit :
    ((∀ i, Γ(XB, (XB).basicOpen (P.r i))) ⊗[A] ∀ i, Γ(XB, (XB).basicOpen (P.r i)))ˣ :=
  Algebra.TensorProduct.piAssemblyUnit A (fun i => Γ(XB, (XB).basicOpen (P.r i)))
    (witnessComponent P θ')

/-- **The witness components collapse onto the Zariski cover cocycle** (the G6 component
identity, transported). -/
theorem componentCollapse_witnessComponent (i j : P.ι) :
    IsLocalization.AwayCover.componentCollapse Γ(XB, ⊤) P.r
        (fun i' => Γ(XB, (XB).basicOpen (P.r i')))
        (fun i' j' => Γ(XB, (XB).basicOpen (P.r i' * P.r j'))) i j
        (witnessComponent P θ' i j).val
      = (P.coverCocycle γ i j).val := by
  rw [← pairAwayEquiv_appLE_diag P i j (witnessComponent P θ' i j).val,
    pairAwayEquiv_witnessComponent_val P θ' i j]
  exact congrArg Units.val (witnessBasicSection_collapse P θ' i j)

/-- **The witness components satisfy the index-wise cocycle identity** (the Amitsur
identity of the glued components, transported). -/
theorem faceA_cocycle_witnessComponent (i j l : P.ι) :
    Algebra.TensorProduct.faceA₂₃ A (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l
        (witnessComponent P θ' j l).val
      * Algebra.TensorProduct.faceA₁₂ A (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l
          (witnessComponent P θ' i j).val
    = Algebra.TensorProduct.faceA₁₃ A (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i j l
        (witnessComponent P θ' i l).val := by
  letI := IsLocalization.Away.tensorAwayAlgebra A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  haveI := IsLocalization.Away.tensorAwayScalarTower A B B Γ(XB, (XB).basicOpen (P.r j))
    Γ(XB, (XB).basicOpen (P.r l))
  letI := IsLocalization.Away.tensorAwayAlgebra A B (B ⊗[A] B)
    Γ(XB, (XB).basicOpen (P.r i))
    (Γ(XB, (XB).basicOpen (P.r j)) ⊗[A] Γ(XB, (XB).basicOpen (P.r l)))
  apply (tripleAwayEquiv (A := A) P i j l).injective
  rw [map_mul, tripleAwayEquiv_faceA₂₃ P i j l, tripleAwayEquiv_faceA₁₂ P i j l,
    tripleAwayEquiv_faceA₁₃ P i j l, pairAwayEquiv_witnessComponent_val P θ' j l,
    pairAwayEquiv_witnessComponent_val P θ' i j, pairAwayEquiv_witnessComponent_val P θ' i l]
  have h := congrArg Units.val (witnessBasicSection_amitsur P θ' i j l)
  rw [Units.val_mul] at h
  exact h

/-- **G4/G5: the assembled witness unit is an `A`-descent 1-cocycle.** -/
theorem isDescentCocycle_assemblyUnit :
    Module.IsDescentCocycle (assemblyUnit P θ') := by
  have hdiag : ∀ i, Algebra.TensorProduct.diagA A
      (fun i' => Γ(XB, (XB).basicOpen (P.r i'))) i (witnessComponent P θ' i i).val = 1 :=
    fun i => IsLocalization.AwayCover.diagA_eq_one_of_componentCollapse Γ(XB, ⊤) P.r
      (fun i' => Γ(XB, (XB).basicOpen (P.r i')))
      (fun i' j' => Γ(XB, (XB).basicOpen (P.r i' * P.r j')))
      (componentCollapse_witnessComponent P θ')
      (fun i' => (P.isCoverCocycle γ).diag_eq_one i') i
  exact Algebra.TensorProduct.isDescentCocycle_piAssemblyUnit A
    (fun i => Γ(XB, (XB).basicOpen (P.r i)))
    hdiag (faceA_cocycle_witnessComponent P θ')

/-- **G6: the collapse of the assembled witness unit along
`A → Γ(Spec B, ⊤) → ∀ i, Γ(Spec B, D(P.r i))` is the descent unit of the Zariski cover
cocycle** — the ε2 hand-off to ζ3. -/
theorem tensorCollapse_assemblyUnit :
    Units.map (Module.tensorCollapse A Γ(XB, ⊤)
        (∀ i, Γ(XB, (XB).basicOpen (P.r i)))).toRingHom.toMonoidHom
        (assemblyUnit P θ')
      = IsLocalization.AwayCover.cocycleUnit P.r
          (fun i' => Γ(XB, (XB).basicOpen (P.r i')))
          (fun i' j' => Γ(XB, (XB).basicOpen (P.r i' * P.r j')))
          (P.coverCocycle γ) :=
  IsLocalization.AwayCover.tensorCollapse_piAssemblyUnit Γ(XB, ⊤) P.r
    (fun i' => Γ(XB, (XB).basicOpen (P.r i')))
    (fun i' j' => Γ(XB, (XB).basicOpen (P.r i' * P.r j')))
    (componentCollapse_witnessComponent P θ')

/-! ## The ε2 corollary: the class equation handed to ζ3 -/

/-- Elementwise round-trip of `ΓSpecIso`, other direction. -/
private lemma ΓSpecIso_hom_inv (R : CommRingCat.{u}) (x : R) :
    (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom x) = x := by
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

/-- Restriction along `⊤ ≤ ⊤` is the identity. -/
private lemma res_top_top (z : Γ(XB, ⊤)) :
    ((XB).presheaf.map (homOfLE (le_top : (⊤ : (XB).Opens) ≤ ⊤)).op).hom z = z := by
  rw [show (homOfLE (le_top : (⊤ : (XB).Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : (XB).Opens))
      from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- `ΓSpecIso` as an equivalence of `A`-algebras, for the composed `A`-structure on the
global sections of `Spec B`. -/
noncomputable def sectionsTopAlgEquiv : Γ(XB, ⊤) ≃ₐ[A] B :=
  AlgEquiv.ofRingEquiv
    (f := (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv)
    (fun a => by
      refine (congrArg ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom)
        (res_top_top (k := k) (B := B)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)))).trans ?_
      exact ΓSpecIso_hom_inv (CommRingCat.of B) (algebraMap A B a))

set_option linter.unusedSectionVars false in
/-- For faithfully flat `A → B`, the composed `A`-structure on the global sections of
`Spec B` is faithfully flat — the `ΓSpecIso`-transport of the hypothesis. -/
theorem faithfullyFlat_sectionsTop [Module.FaithfullyFlat A B] :
    Module.FaithfullyFlat A Γ(XB, ⊤) :=
  Module.FaithfullyFlat.of_linearEquiv _ _
    (sectionsTopAlgEquiv (k := k) (A := A) (B := B)).toLinearEquiv

/-- **The ε2 corollary (the class equation for ζ3):** for faithfully flat `A → B`, the
Picard class of the composite descent unit maps under `CommRing.Pic.mapAlgebra` to the
Picard class `P.pic γ` of the Zariski cover cocycle — which is `CommRing.Pic.mk N` when
`γ` is the trivializing cocycle of an invertible module `N`
(`Scheme.TrivializingFamily.pic_cocycle`). -/
theorem mapAlgebra_picClass_assemblyUnit [Module.FaithfullyFlat A B] :
    haveI := faithfullyFlat_sectionsTop (k := k) (A := A) (B := B)
    haveI := P.faithfullyFlat
    haveI := Module.FaithfullyFlat.trans A Γ(XB, ⊤)
      (∀ i, Γ(XB, (XB).basicOpen (P.r i)))
    CommRing.Pic.mapAlgebra A Γ(XB, ⊤)
        ((isDescentCocycle_assemblyUnit P θ').picClass)
      = P.pic γ := by
  haveI := faithfullyFlat_sectionsTop (k := k) (A := A) (B := B)
  haveI := P.faithfullyFlat
  haveI := Module.FaithfullyFlat.trans A Γ(XB, ⊤)
    (∀ i, Γ(XB, (XB).basicOpen (P.r i)))
  rw [← Module.IsDescentCocycle.picClass_collapse (isDescentCocycle_assemblyUnit P θ'),
    P.pic_eq_picClass γ]
  exact Module.IsDescentCocycle.picClass_congr _ _ (tensorCollapse_assemblyUnit P θ')


end Over

end AlgebraicGeometry
