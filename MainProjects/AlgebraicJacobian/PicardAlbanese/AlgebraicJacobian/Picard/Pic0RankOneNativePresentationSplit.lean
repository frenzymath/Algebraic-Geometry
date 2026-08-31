/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.Pic0RankOneFamilyCertificatesActualDatum
import AlgebraicJacobian.Picard.Pic0RankOneNativeBaseChangeCartesian
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentationField
import AlgebraicJacobian.Picard.Pic0VanishingAffineReduction

/-!
# Native presentations for split field classes

A residue-field H¹ witness for the lambda-tied cocycle datum supplies its arbitrary-ring
cohomology and rank certificates.  The native all-cartesian base-change theorem then completes
the corresponding `PicRankOneNativePresentation` without a separate pushforward hypothesis.

A split genus-degree class over a field stays split after every affine coefficient extension,
so it supplies those witnesses for each pullback datum.

The final theorem is the direct public consumer: a split field class belongs to
`PicRankOneOpen`, because every affine pullback receives the presentation constructed here.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
  CartesianMonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-- Every morphism between affine tests over `Spec k` is induced by a `k`-algebra map.

Unlike `exists_algHom_eq_of_overSpec_hom`, neither coefficient ring is required to be a
field.  This is the form needed when the target of a field-valued Picard point is tested by an
arbitrary affine scheme. -/
theorem exists_algHom_eq_of_overSpec_hom_of_commRing
    (R S : Type u) [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (t : overSpec k S ⟶ overSpec k R) :
    ∃ e : R →ₐ[k] S, t = Over.overSpecMap e := by
  have hw : t.left ≫ (overSpec k R).hom = (overSpec k S).hom := Over.w t
  let psi : CommRingCat.of R ⟶ CommRingCat.of S := Spec.preimage t.left
  have hmap : Spec.map psi = t.left := Spec.map_preimage t.left
  have htower : CommRingCat.ofHom (algebraMap k R) ≫ psi =
      CommRingCat.ofHom (algebraMap k S) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hmap]
    exact hw
  let e : R →ₐ[k] S :=
    { __ := psi.hom
      commutes' := fun r ↦
        congrArg (fun f => f r) (congrArg CommRingCat.Hom.hom htower) }
  refine ⟨e, ?_⟩
  ext : 1
  exact hmap.symm

/-- Complete the native presentation attached to an actual lambda-tied datum.

The input is exactly the remaining family-level H¹ obligation.  The degree law follows from the
two class equalities stored in `P`; finiteness, projectivity, and rank one follow from the
arbitrary-ring certificate theorem; and native pushforward base change is the canonical
all-cartesian theorem.  Thus every field concerns the same cocycle datum. -/
noncomputable def PicRankOneNativeDatum.toNativePresentation_of_residueH1Witness
    {A : Type u} [CommRing A] [Algebra k A]
    {pi : C.left ⟶ P1 k} [IsFinite pi]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (P : PicRankOneNativeDatum pi lam)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hres : ∀ p : PrimeSpectrum P.cover.Carrier,
      P.datum.HasWitnessH1Vanishing p.asIdeal.ResidueField) :
    PicRankOneNativePresentation pi lam :=
  PicRankOneNativePresentation.ofCertificatesWithNativeBaseChange
    P.cover P.representative P.represents P.datum P.datum_class
      (RankOneFamilyCertificates.ofActualDatum P.datum hpi hres
        (fun L ↦ P.classDeg_baseChange L))

/-- The arbitrary-affine pullback of a split field class has a complete native presentation.

The datum is the representative extracted from the displayed pullback `lam`.  Its residue-field
H¹ witnesses come from `hsplit`, while its degree law comes from the equality with `lam`.
Consequently all four cohomology/rank fields and the native base-change field concern the same
cocycle datum. -/
theorem PicRankOneNativePresentation.nonempty_of_fieldPullback
    {K A : Type u} [Field K] [Algebra k K] [CommRing A] [Algebra k A]
    {pi : C.left ⟶ P1 k} [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (e : K →ₐ[k] A) (nu : picEt C (overSpec k K))
    (hlam : lam.1 = picEtMap C (Over.overSpecMap e) nu)
    (hsplit : IsSplitWitness C nu) :
    Nonempty (PicRankOneNativePresentation pi lam) := by
  obtain ⟨P⟩ := PicRankOneNativeDatum.nonempty (C := C) pi lam
  exact ⟨P.toNativePresentation_of_residueH1Witness hpi
    (P.residueH1Witness_of_fieldPullback e nu hlam hsplit)⟩

/-- A split genus-degree class over a field belongs to the public rank-one Picard locus.

Every affine test morphism into `Spec K` is induced by a `k`-algebra map `K → A`; the
preceding producer therefore supplies the exact native presentation required on that pullback.
-/
theorem mem_picRankOneOpen_of_isSplitWitness
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {K : Type u} [Field K] [Algebra k K]
    (lam : picDegLayer C (genus C : ℤ) (overSpec k K))
    (hsplit : IsSplitWitness C lam.1) :
    lam ∈ (PicRankOneOpen pi).obj (op (overSpec k K)) := by
  apply mem_picRankOneOpen_of_nativePresentations pi
  intro A _ _ t
  obtain ⟨e, ht⟩ := exists_algHom_eq_of_overSpec_hom_of_commRing (k := k) K A t
  rw [ht]
  exact PicRankOneNativePresentation.nonempty_of_fieldPullback
    (C := C) hpi e lam.1 rfl hsplit

end

end AlgebraicGeometry
