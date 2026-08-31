/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyBackward
import AlgebraicJacobian.Picard.DivisorFamilyFieldEquiv
import AlgebraicJacobian.Picard.DivisorFamilyFieldCRT
import AlgebraicJacobian.Picard.DivRepClassifyZar

/-!
# DAT-B B-3 — the `hsurj` completion and the field DivScheme-point

The field-dictionary completion of the DAT-B worksheet
(`informal/w4-datb-worksheet.md` §1.7, COV-4): over a field `K`, every effective
degree-`n` Weil divisor on the relative curve is the divisor of a certified divisor
family (`exists_divFam_divFamDivisor_eq`, the `hsurj` slot of
`divFamFieldEquivOfDegOfSurj`), so the field dictionary closes unconditionally
(`divFamFieldEquiv`), and — through the landed F4 layer (`divRepClassifyZar`,
I-0243) — every effective degree-`g` divisor yields a `DivScheme`-point
`overSpec k K ⟶ divSchemeOver!` (`effectiveDivisorClassifyZar`), the worksheet §3.3
effectivity export DAT-J's quasi-compactness image argument consumes.

## Route, and the recorded deviation from the worksheet pin

* The anchor equations come from the landed backward realization
  `exists_localEquations_presentationDivisor_eq` (`Picard/DivisorFamilyBackward.lean`):
  a product of tracked point-uniformizer equations cutting exactly `D`.
* **Deviation (worksheet §1.7 / risk 5, superseded by I-0230):** the worksheet routes
  the certificate through a *support-separated* adaptation and
  `deg_divFamDivisor_of_separated`.  The landed CRT layer
  (`DivisorAdaptation.deg_presentationDivisor`, `Picard/DivisorFamilyFieldCRT.lean`,
  I-0230) computes `deg K (div d) = finrank K W(d)` for **every** adaptation with no
  separation hypothesis — and full support-separation is in fact unachievable when a
  support point lies in the overlap of the two pinned charts (each chart's partition
  forces its pieces to cover the whole chart, so such a point lies in one piece of
  *each* chart).  The certificate is therefore discharged on the plain extraction
  adaptation (`exists_divisorAdaptation`, `Picard/DivisorFamilyExtraction.lean`):
  over the field every module is free — (c1)-projective, (c3), (c4) are instances —
  (c1)-finiteness is the chart colength reading
  (`moduleFinite_quotient_span_section`, empty pieces are subsingleton), and the
  (c2) rank is the CRT degree identity against `deg K D = n`
  (`DivisorAdaptation.isCertified_of_deg`).
* The DivScheme-point corollary consumes `DivFam.toZar` (`Picard/DivisorFamilyZar.lean`)
  and the landed `divRepClassifyZar` (`Picard/DivRepClassifyZar.lean`) verbatim.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C K, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k K).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open Module (finrank)

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## The field certificate of an arbitrary adaptation -/

section Certificate

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {K : Type u} [Field K] [Algebra k K]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

namespace DivisorAdaptation

variable {d : (relCurve C K).LocalEquations} (A : DivisorAdaptation C K π d)

omit [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **(c1)-finiteness over a field, for an arbitrary adaptation**: each chart-local
colength module `Γ(D(h_j)) ⧸ (f_j)` is a finite `K`-module — the chart colength
reading (`moduleFinite_quotient_span_section`) on a nonempty piece, and the zero ring
on an empty piece. -/
theorem moduleFinite_colength (j : A.index) : Module.Finite K (A.colength j) := by
  by_cases hη : genericPoint (relCurve C K) ∈ A.pieces j
  · exact moduleFinite_quotient_span_section K (A.isAffineOpen_pieces j) hη
      (A.eqn_ne_zero j hη)
  · have hbot : A.pieces j ≤ ⊥ :=
      fun x hx => hη (Scheme.genericPoint_mem_of_nonempty ⟨x, hx⟩)
    haveI : Subsingleton Γ(relCurve C K, A.pieces j) :=
      (relCurve C K).subsingleton_sections_of_le_bot hbot
    haveI : Subsingleton (A.colength j) :=
      (Ideal.Quotient.mk_surjective (I := Ideal.span {A.eqn j})).subsingleton
    haveI : Finite (A.colength j) := Finite.of_subsingleton
    exact Module.Finite.of_finite

/-- **The field certificate of an arbitrary adaptation** (the B-3 deviation of record,
superseding the worksheet's support-separated route): over the field `K`, an adaptation
of a system whose divisor has degree `n` is certified in degree `n`.  Every module over
`K` is free, so (c1)-projectivity and the flat-cokernel clauses (c3)/(c4) are instances;
(c1)-finiteness is `moduleFinite_colength`; and the (c2) rank is the unconditional CRT
colength↔degree identity (`DivisorAdaptation.deg_presentationDivisor`, I-0230) read
against the degree hypothesis. -/
theorem isCertified_of_deg {n : ℕ}
    (hdeg : Scheme.CurveDivisor.deg K
      (Scheme.presentationDivisor K d.presentation) = (n : ℤ)) :
    A.IsCertified n := by
  haveI hfin : ∀ j, Module.Finite K (A.colength j) := A.moduleFinite_colength
  haveI : Module.Finite K A.chartProd := Module.Finite.pi
  haveI : Module.Finite K A.Glued := inferInstance
  haveI : Module.Free K A.Glued := Module.Free.of_divisionRing _ _
  have hfr : finrank K A.Glued = n := by
    have hZ := A.deg_presentationDivisor
    rw [hdeg] at hZ
    exact_mod_cast hZ.symm
  refine
    { finite_colength := hfin
      projective_colength := fun j =>
        haveI : Module.Free K (A.colength j) := Module.Free.of_divisionRing _ _
        inferInstance
      finite_glued := inferInstance
      projective_glued := inferInstance
      rankAtStalk_glued := fun p => ?_
      flat_coker_incl :=
        haveI : Module.Free K (A.chartProd ⧸ A.gluedSubmodule) :=
          Module.Free.of_divisionRing _ _
        inferInstance
      flat_coker_diff :=
        haveI : Module.Free K
            (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight)) :=
          Module.Free.of_divisionRing _ _
        inferInstance }
  simp [hfr]

end DivisorAdaptation

/-! ## The `hsurj` completion and the unconditional field dictionary -/

variable {n : ℕ}

/-- **COV-4, the `hsurj` completion** (★ B-3 keystone, worksheet §1.7): over the field
`K`, every effective Weil divisor `D` of degree `n` on the relative curve is the divisor
of a certified divisor family.  The anchor equations are the point-uniformizer product
of the landed backward realization (`exists_localEquations_presentationDivisor_eq`);
any extraction adaptation (`exists_divisorAdaptation`) carries the field certificate
(`DivisorAdaptation.isCertified_of_deg`, via the unconditional CRT degree identity). -/
theorem exists_divFam_divFamDivisor_eq (D : (relCurve C K).CurveDivisor)
    (hD : 0 ≤ D) (hdeg : Scheme.CurveDivisor.deg K D = (n : ℤ)) :
    ∃ F : DivFam C K π n, divFamDivisor F = D := by
  obtain ⟨E, hE⟩ :=
    Scheme.LocalEquations.exists_localEquations_presentationDivisor_eq K D hD
  obtain ⟨A⟩ := exists_divisorAdaptation C K π E
  refine ⟨DivFam.mk ⟨E, A, A.isCertified_of_deg (by rw [hE]; exact hdeg)⟩, ?_⟩
  rw [divFamDivisor_mk]
  exact hE

/-- **The field dictionary, unconditional** (the frozen `divFamFieldEquiv` of
`informal/spec-dd-1.md` §3 (f), both named gaps discharged): certified divisor families
of degree `n` over the field `K` are exactly the effective degree-`n` Weil divisors.
`hdeg` is the landed CRT identity (`deg_divFamDivisor`, I-0230); `hsurj` is the B-3
keystone above. -/
noncomputable def divFamFieldEquiv :
    DivFam C K π n ≃
      {D : (relCurve C K).CurveDivisor //
        0 ≤ D ∧ Scheme.CurveDivisor.deg K D = (n : ℤ)} :=
  divFamFieldEquivOfDegOfSurj (fun F => deg_divFamDivisor F)
    (fun D hD hdeg => exists_divFam_divFamDivisor_eq D hD hdeg)

@[simp]
lemma divFamFieldEquiv_apply (F : DivFam C K π n) :
    (divFamFieldEquiv F : (relCurve C K).CurveDivisor) = divFamDivisor F :=
  rfl

end Certificate

/-! ## The field DivScheme-point of an effective degree-`g` divisor -/

section DivSchemePoint

open Scheme

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftFieldSurj :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g : ℕ)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
variable (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
variable (r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(divisorSections k
    ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤))
variable {K : Type u} [Field K] [Algebra k K]
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **The `DivScheme`-point of an effective degree-`g` divisor** (worksheet §1.7
corollary = the §3.3 effectivity-export vehicle): the backward classification
(`divRepClassifyZar`, the landed F4 keystone, I-0243) of the certified family
presenting `D` (the B-3 keystone), an `Over`-morphism `overSpec k K ⟶ divSchemeOver!`.
Characterized by `effectiveDivisorClassifyZar_spec`. -/
noncomputable def effectiveDivisorClassifyZar (D : (relCurve C K).CurveDivisor)
    (hD : 0 ≤ D) (hdeg : Scheme.CurveDivisor.deg K D = (g : ℤ)) :
    overSpec k K ⟶
      divSchemeOver k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm) :=
  divRepClassifyZar hπ g hO hχ r₁ r₂ b₁ b₂ K
    ((exists_divFam_divFamDivisor_eq D hD hdeg).choose.toZar)

/-- **The characterizing property of the field `DivScheme`-point**: it is the backward
classification of a certified divisor family presenting exactly `D`.  DAT-J composes
this with the Abel morphism and `compactSpace_divScheme` for the quasi-compactness
image argument (worksheet §3.3); B-6 upgrades it to the chart-shifted class clause
through CHART-U(c). -/
theorem effectiveDivisorClassifyZar_spec (D : (relCurve C K).CurveDivisor)
    (hD : 0 ≤ D) (hdeg : Scheme.CurveDivisor.deg K D = (g : ℤ)) :
    ∃ F : DivFam C K π g, divFamDivisor F = D ∧
      effectiveDivisorClassifyZar hπ g hO hχ r₁ r₂ b₁ b₂ D hD hdeg =
        divRepClassifyZar hπ g hO hχ r₁ r₂ b₁ b₂ K F.toZar :=
  ⟨(exists_divFam_divFamDivisor_eq D hD hdeg).choose,
    (exists_divFam_divFamDivisor_eq D hD hdeg).choose_spec, rfl⟩

end DivSchemePoint

end AlgebraicGeometry
