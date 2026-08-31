/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneUniquenessDischarge
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorCarrierWitness

/-!
# The canonical rank-one divisor, Noetherian-free

`existsUnique_abel_divFamZarAff_of_mem` removes the Noetherian hypothesis from the canonical
rank-one divisor: over any affine test `A` whose plus class lies in the rank-one locus there
is a unique widened locally certified divisor class of degree `genus C` with Abel value the
input class — with no Noetherian hypothesis on any presentation carrier.  The price is the
structural hypothesis `hpi : pi ≫ P1.structureMap k = C.hom` tying the finite chart to the
curve, which feeds the finite-stage rigid engine.

Membership tested at the identity yields a presentation `P` of the input class on an étale
carrier `B := P.cover.Carrier`, arbitrary and in general not Noetherian.  The Noetherian
input of the glued-divisor keystone is manufactured by descent:

* the presented datum descends to a finitely generated — hence Noetherian — stage `A₀` with
  pair-`H¹` vanishing at the stage itself (`exists_fg_subalgebra_baseChange_eq` +
  `exists_fg_pairH1_vanishing_stage`);
* stage `H⁰` is finite projective (`datumRigidEngine`), so its `rankAtStalk` is locally
  constant; the rank-one level set of the stage is clopen, contains the image of
  `Spec B → Spec A₀` (rank one over `B` by the presentation), and that image is dense
  because `A₀ ⊆ B` is injective — hence the stage rank is one at every prime;
* rank one at a stage prime gives `h⁰ = 1` on the residue fibre, and the χ-formula
  `h⁰ = deg + (1 − genus)` (`h0_gluedSheaf_eq_classDeg_add_chi`), solved backwards, pins
  the fibre degree of the stage class at `genus C`; the degree law extends to every field
  point of the stage through the kernel-prime residue embedding
  (`Ideal.ResidueField.liftₐ` + `classDeg_cechPicMap_baseFieldTransition`);
* the keystone `exists_glued_divFamZarAff_of_admissible_fibre` now fires at the Noetherian
  stage; the resulting family pushes up to `B`, its Abel value is the restricted input
  class, and `existsUnique_abel_divFamZarAff_of_etale_witness` with the discharged
  uniqueness interface descends it uniquely to `A`.

The unique class is extracted as `canonicalRankOneDivisorOfMem`, with its Abel equation
and uniqueness accessors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

noncomputable local instance freeCanonicalOverCleft :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

/-! ## The Noetherian-free canonical divisor -/

/-- **The unique Abel-correct divisor of a rank-one class, Noetherian-free**: over any
affine test whose plus class lies in the rank-one locus there is a unique widened locally
certified divisor class of degree `genus C` whose Abel value is the input class.  No
Noetherian hypothesis is imposed on any carrier; the finite-chart normalization `hpi`
replaces it, feeding the finite-stage descent of the presented datum. -/
theorem existsUnique_abel_divFamZarAff_of_mem
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A))) :
    ∃! F : DivFamZarAff C A (genus C),
      abelDivAffPlus C A F = picEtAffineEquiv C A lam.1 := by
  classical
  -- membership tested at the identity yields a presentation of the input class
  obtain ⟨P⟩ := (mem_picRankOneOpen_iff pi lam).mp hlam A (𝟙 (overSpec k A))
  have e : ((picDegLayerFunctor C (genus C : ℤ)).map
      (𝟙 (overSpec k A)).op lam).1 = lam.1 :=
    picEtMap_id C lam.1
  obtain ⟨F, habel⟩ := P.exists_carrier_divFamZarAff_abel hpi
  have habel' : abelDivAffPlus C P.cover.Carrier F =
      PicEtAff.mapAlg C ((Algebra.ofId A P.cover.Carrier).restrictScalars k)
        (picEtAffineEquiv C A lam.1) :=
    habel.trans (congrArg
      (PicEtAff.mapAlg C ((Algebra.ofId A P.cover.Carrier).restrictScalars k))
      (congrArg (picEtAffineEquiv C A) e))
  -- Descend along the etale carrier via the discharged uniqueness interface.
  exact existsUnique_abel_divFamZarAff_of_etale_witness pi
    (rankOneDivisorUniqueness pi) lam hlam P.cover F habel'

/-! ## Extraction: the canonical divisor and its accessors -/

/-- **The canonical rank-one divisor of a membership certificate**: the unique widened
divisor class over the test algebra whose Abel value is the rank-one plus class, chosen
from `existsUnique_abel_divFamZarAff_of_mem`.  No Noetherian hypothesis. -/
noncomputable def canonicalRankOneDivisorOfMem
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A))) :
    DivFamZarAff C A (genus C) :=
  (existsUnique_abel_divFamZarAff_of_mem pi hpi hlam).choose

/-- The canonical rank-one divisor satisfies the Abel equation: its widened Abel value is
the input rank-one plus class. -/
theorem canonicalRankOneDivisorOfMem_abel
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A))) :
    abelDivAffPlus C A (canonicalRankOneDivisorOfMem pi hpi hlam)
      = picEtAffineEquiv C A lam.1 :=
  (existsUnique_abel_divFamZarAff_of_mem pi hpi hlam).choose_spec.1

/-- Any Abel-correct widened divisor class equals the canonical rank-one divisor. -/
theorem canonicalRankOneDivisorOfMem_unique
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A)))
    (F : DivFamZarAff C A (genus C))
    (hF : abelDivAffPlus C A F = picEtAffineEquiv C A lam.1) :
    F = canonicalRankOneDivisorOfMem pi hpi hlam :=
  (existsUnique_abel_divFamZarAff_of_mem pi hpi hlam).choose_spec.2 F hF

end AlgebraicGeometry
