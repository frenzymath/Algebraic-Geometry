/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneFibrePresentedProducerFiniteGlue
import AlgebraicJacobian.Picard.Pic0RankOneLocus
import AlgebraicJacobian.Picard.DivRepAffFaithfullyFlatDescent
import AlgebraicJacobian.Picard.PicEtAffEtaleSeparated

/-!
# Descent of the canonical rank-one divisor from an étale witness

Assuming the rank-one divisor **uniqueness interface** (`RankOneDivisorUniqueness`): over any
affine test whose plus class lies in the rank-one locus, at most one widened divisor class has
that Abel value — the missing-item interface to be discharged by a later session.

Under this hypothesis, a widened divisor over the carrier of an étale cover of the test whose
Abel value is the restricted input class **descends uniquely** to the test algebra
(`existsUnique_abel_divFamZarAff_of_etale_witness`): uniqueness at the tensor square of the
carrier manufactures the two-coprojection agreement demanded by the faithfully-flat descent
theorem `DivFamZarAff.exists_descent_of_tensor_eq`, and the Abel value of the descended class
is pinned by étale separatedness of `PicEtAff`.

The first consumer is the finite glue on a Noetherian presentation carrier
(`existsUnique_abel_divFamZarAff_of_localPresentation`), whose Abel conjunct is exactly the
étale witness above.  The unique class is then extracted as the **canonical rank-one divisor**
of a presentation (`canonicalRankOneDivisorOfPresentation`), with its Abel equation and
uniqueness accessors.

This file does not construct `PicRankOneOpen.FibrePresented`, does not prove independence of
the chosen presentation beyond what uniqueness already gives, and does not discharge the
uniqueness interface itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

/-- **The rank-one divisor uniqueness interface**: over every affine test whose plus class
lies in the rank-one locus, at most one widened locally certified divisor class of degree
`genus C` has Abel value the input class.

This is the sanctioned missing-item interface of the canonical-divisor route: producers prove
existence (the finite glue and its descent below), while injectivity of the widened Abel map
on the rank-one locus is to be discharged by a later session.  Stated as a named `Prop` so
consumers can take it as a single hypothesis. -/
def RankOneDivisorUniqueness : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra k S]
    (lam : picDegLayer C (genus C : ℤ) (overSpec k S)),
    lam ∈ (PicRankOneOpen pi).obj (op (overSpec k S)) →
    ∀ F G : DivFamZarAff C S (genus C),
      abelDivAffPlus C S F = picEtAffineEquiv C S lam.1 →
      abelDivAffPlus C S G = picEtAffineEquiv C S lam.1 → F = G

/-- **Descent of an Abel-correct divisor witness along an étale cover**: a widened divisor
class over the carrier of an étale cover of `A` whose Abel value is the restriction of the
input rank-one plus class descends to a unique Abel-correct widened divisor class over `A`.

The tensor-square cocycle condition of `DivFamZarAff.exists_descent_of_tensor_eq` is not
assumed: it is manufactured from the uniqueness interface, applied over the tensor square of
the carrier to the two coprojection pullbacks of the witness — both have Abel value the
restriction of the input class along the (single) structure map `A → E.Carrier ⊗[A] E.Carrier`,
because the two coprojections agree after the structure map of the cover.  The Abel value of
the descended class is recovered by étale separatedness of `PicEtAff`
(`PicEtAff.map_injective_of_etaleCover`). -/
theorem existsUnique_abel_divFamZarAff_of_etale_witness
    (hu : RankOneDivisorUniqueness pi)
    {A : Type u} [CommRing A] [Algebra k A]
    (lam : picDegLayer C (genus C : ℤ) (overSpec k A))
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A)))
    (E : Algebra.EtaleCover A) (F' : DivFamZarAff C E.Carrier (genus C))
    (habel : abelDivAffPlus C E.Carrier F' =
      PicEtAff.mapAlg C ((Algebra.ofId A E.Carrier).restrictScalars k)
        (picEtAffineEquiv C A lam.1)) :
    ∃! F : DivFamZarAff C A (genus C),
      abelDivAffPlus C A F = picEtAffineEquiv C A lam.1 := by
  classical
  set φ0 : A →ₐ[k] E.Carrier := (Algebra.ofId A E.Carrier).restrictScalars k with hφ0
  set φL : E.Carrier →ₐ[k] E.Carrier ⊗[A] E.Carrier :=
    (Algebra.TensorProduct.includeLeft :
      E.Carrier →ₐ[A] E.Carrier ⊗[A] E.Carrier).restrictScalars k with hφL
  set φR : E.Carrier →ₐ[k] E.Carrier ⊗[A] E.Carrier :=
    (Algebra.TensorProduct.includeRight :
      E.Carrier →ₐ[A] E.Carrier ⊗[A] E.Carrier).restrictScalars k with hφR
  set ψ : A →ₐ[k] E.Carrier ⊗[A] E.Carrier := φL.comp φ0 with hψ
  -- both coprojections restrict to the structure map of the tensor square
  have hψR : φR.comp φ0 = ψ := by
    rw [hψ]
    exact AlgHom.ext fun a =>
      ((Algebra.TensorProduct.includeRight :
        E.Carrier →ₐ[A] E.Carrier ⊗[A] E.Carrier).commutes a).trans
        ((Algebra.TensorProduct.includeLeft :
          E.Carrier →ₐ[A] E.Carrier ⊗[A] E.Carrier).commutes a).symm
  -- the input class restricted to the tensor square stays in the rank-one locus
  set lam_sq : picDegLayer C (genus C : ℤ)
      (overSpec k (E.Carrier ⊗[A] E.Carrier)) :=
    (picDegLayerFunctor C (genus C : ℤ)).map (Over.overSpecMap ψ).op lam with hlam_sq_def
  have hlam_sq : lam_sq ∈ (PicRankOneOpen pi).obj
      (op (overSpec k (E.Carrier ⊗[A] E.Carrier))) :=
    picRankOneOpen_map_mem pi (Over.overSpecMap ψ).op hlam
  have hsq : picEtAffineEquiv C (E.Carrier ⊗[A] E.Carrier) lam_sq.1
      = PicEtAff.mapAlg C ψ (picEtAffineEquiv C A lam.1) :=
    picEtAffineEquiv_naturality C ψ lam.1
  -- both coprojection pullbacks of the witness have the restricted Abel value
  have habelL : abelDivAffPlus C (E.Carrier ⊗[A] E.Carrier)
        (DivFamZarAff.mapAlgHom φL F')
      = picEtAffineEquiv C (E.Carrier ⊗[A] E.Carrier) lam_sq.1 := by
    rw [hsq, ← abelDivAffPlus_mapAlgHom φL F', habel, ← PicEtAff.mapAlg_comp, ← hψ]
  have habelR : abelDivAffPlus C (E.Carrier ⊗[A] E.Carrier)
        (DivFamZarAff.mapAlgHom φR F')
      = picEtAffineEquiv C (E.Carrier ⊗[A] E.Carrier) lam_sq.1 := by
    rw [hsq, ← abelDivAffPlus_mapAlgHom φR F', habel, ← PicEtAff.mapAlg_comp, hψR]
  -- uniqueness over the tensor square manufactures the descent cocycle
  have htensor : DivFamZarAff.mapAlgHom φL F' = DivFamZarAff.mapAlgHom φR F' :=
    hu (E.Carrier ⊗[A] E.Carrier) lam_sq hlam_sq _ _ habelL habelR
  obtain ⟨F, hF, -⟩ := DivFamZarAff.exists_descent_of_tensor_eq E F' htensor
  rw [← hφ0] at hF
  -- the Abel value of the descended class, by étale separatedness of `PicEtAff`
  have hmapF : PicEtAff.mapAlg C φ0 (abelDivAffPlus C A F)
      = PicEtAff.mapAlg C φ0 (picEtAffineEquiv C A lam.1) := by
    rw [abelDivAffPlus_mapAlgHom φ0 F, hF, habel]
  have habelF : abelDivAffPlus C A F = picEtAffineEquiv C A lam.1 := by
    apply PicEtAff.map_injective_of_etaleCover C E
    rw [PicEtAff.mapAlg_eq_map_of_toRingHom_eq_algebraMap C φ0 rfl,
      PicEtAff.mapAlg_eq_map_of_toRingHom_eq_algebraMap C φ0 rfl] at hmapF
    exact hmapF
  exact ⟨F, habelF, fun G hG => hu A lam hlam G F hG habelF⟩

/-- **The unique Abel-correct divisor of a rank-one local presentation**: over a rank-one
plus class with a tied local presentation on a Noetherian étale carrier, there is a unique
widened divisor class over the test algebra whose Abel value is the input class.

Existence: the finite glue
`PicRankOneLocalPresentation.exists_glued_rankOne_away_divisor_with_abel_evaluation`
produces an Abel-correct witness over the presentation carrier, which descends by
`existsUnique_abel_divFamZarAff_of_etale_witness`.  Uniqueness is the interface `hu`. -/
theorem existsUnique_abel_divFamZarAff_of_localPresentation
    (hu : RankOneDivisorUniqueness pi)
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A)))
    (P : PicRankOneLocalPresentation pi lam) [IsNoetherianRing P.cover.Carrier] :
    ∃! F : DivFamZarAff C A (genus C),
      abelDivAffPlus C A F = picEtAffineEquiv C A lam.1 := by
  obtain ⟨-, -, -, -, F0, -, -, habel, -, -, -⟩ :=
    P.exists_glued_rankOne_away_divisor_with_abel_evaluation
  exact existsUnique_abel_divFamZarAff_of_etale_witness pi hu lam hlam P.cover F0 habel

/-- **The canonical rank-one divisor of a presentation**: the unique widened divisor class
over the test algebra whose Abel value is the presented rank-one plus class, chosen from
`existsUnique_abel_divFamZarAff_of_localPresentation`.  By uniqueness, the choice does not
depend on the internal data of the glue — only on the class, the membership certificate,
and the presentation carrier's Noetherianity. -/
noncomputable def canonicalRankOneDivisorOfPresentation
    (hu : RankOneDivisorUniqueness pi)
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A)))
    (P : PicRankOneLocalPresentation pi lam) [IsNoetherianRing P.cover.Carrier] :
    DivFamZarAff C A (genus C) :=
  (existsUnique_abel_divFamZarAff_of_localPresentation pi hu hlam P).choose

/-- The canonical rank-one divisor satisfies the Abel equation: its widened Abel value is
the presented rank-one plus class. -/
theorem canonicalRankOneDivisorOfPresentation_abel
    (hu : RankOneDivisorUniqueness pi)
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A)))
    (P : PicRankOneLocalPresentation pi lam) [IsNoetherianRing P.cover.Carrier] :
    abelDivAffPlus C A (canonicalRankOneDivisorOfPresentation pi hu hlam P)
      = picEtAffineEquiv C A lam.1 :=
  (existsUnique_abel_divFamZarAff_of_localPresentation pi hu hlam P).choose_spec.1

/-- Any Abel-correct widened divisor class equals the canonical rank-one divisor. -/
theorem canonicalRankOneDivisorOfPresentation_unique
    (hu : RankOneDivisorUniqueness pi)
    {A : Type u} [CommRing A] [Algebra k A]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (hlam : lam ∈ (PicRankOneOpen pi).obj (op (overSpec k A)))
    (P : PicRankOneLocalPresentation pi lam) [IsNoetherianRing P.cover.Carrier]
    (F : DivFamZarAff C A (genus C))
    (hF : abelDivAffPlus C A F = picEtAffineEquiv C A lam.1) :
    F = canonicalRankOneDivisorOfPresentation pi hu hlam P :=
  (existsUnique_abel_divFamZarAff_of_localPresentation pi hu hlam P).choose_spec.2 F hF

end AlgebraicGeometry
