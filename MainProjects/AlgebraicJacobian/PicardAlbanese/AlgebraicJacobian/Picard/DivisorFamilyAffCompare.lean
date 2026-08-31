/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffZar

/-!
# The chart-typed → widened comparison (R2, human decision I-0492)

The widened lane (`DivisorFamilyAff*.lean`) is worth nothing to the DD-R chain until every
certificate the chart-typed design already produced instantiates it.  That is this file: the
migration of a `DivisorAdaptation` (over a `FinCoverData`, i.e. basic opens of the two pinned
`P¹` charts) to an `AffAdaptation` over the widened cover `FinCoverData.toAffCoverData`,
CERTIFICATE INCLUDED, and the induced map `DivFamZar → DivFamZarAff`.

## Why it is nearly free, and where the one real step is

`toAffCoverData.pieces j` is *definitionally* `D.pieces (finSumFinEquiv.symm j)`, so the
section rings, the equations, the colength modules, the overlap ideals and both overlap arrows
are the ORIGINAL ones read at a relabelled index — every comparison below that looks like it
needs a transport is `rfl`.  Clauses (c1) therefore transport pointwise.

The one real step is the glued clauses (c2)/(c3)/(c4): `gluedSubmodule` is a kernel inside
`∀ j : index, colength j`, so it must be carried along the index equivalence.  The transport
is `LinearEquiv.piCongrLeft`, used in the `symm` direction because that direction evaluates
CAST-FREE (`(piCongrLeft φ e).symm g j = g (e j)`), which is what keeps the intertwining
proofs from drowning in `Eq.mpr`s.

## Main declarations

* `AlgebraicGeometry.DivisorAdaptation.toAff` — the widened adaptation of a chart-typed one.
* `DivisorAdaptation.gluedCongr` — the glued modules agree, along `piCongrLeft.symm`.
* `DivisorAdaptation.isCertified_toAff` — the certificate migrates, all seven clauses.
* `AlgebraicGeometry.CertifiedDivisorFamily.toAff` — the certified family migrates.
* `AlgebraicGeometry.isLocallyCertifiedAff_of_isLocallyCertified` — the chart-typed pin
  implies the widened one.
* `AlgebraicGeometry.DivFamZar.toAff` — the induced map of functor values, compatible with
  `picClass`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d)

/-- **The widened adaptation of a chart-typed one.**  No transport: the pieces of
`toAffCoverData` are definitionally the old pieces at the relabelled index, so the equation
and the refinement clause carry over by `rfl`. -/
noncomputable def toAff : AffAdaptation A.toFinCoverData.toAffCoverData d where
  eqn := fun j => A.eqn (finSumFinEquiv.symm j)
  eqn_rel := fun j y => A.eqn_rel (finSumFinEquiv.symm j) y

@[simp]
lemma toAff_eqn (j : Fin (A.m₀ + A.m₁)) : A.toAff.eqn j = A.eqn (finSumFinEquiv.symm j) := rfl

/-- The relabelling equivalence: the widened index `Fin (m₀ + m₁)` against the chart-typed
`Fin m₀ ⊕ Fin m₁`. -/
abbrev reindexEquiv : Fin (A.m₀ + A.m₁) ≃ A.index := finSumFinEquiv.symm

lemma colength_toAff (j : Fin (A.m₀ + A.m₁)) :
    A.toAff.colength j = A.colength (A.reindexEquiv j) := rfl

lemma ovlColength_toAff (i j : Fin (A.m₀ + A.m₁)) :
    A.toAff.ovlColength i j = A.ovlColength (A.reindexEquiv i) (A.reindexEquiv j) := rfl

lemma toOvlLeft_toAff (i j : Fin (A.m₀ + A.m₁)) :
    A.toAff.toOvlLeft i j = A.toOvlLeft (A.reindexEquiv i) (A.reindexEquiv j) := rfl

lemma toOvlRight_toAff (i j : Fin (A.m₀ + A.m₁)) :
    A.toAff.toOvlRight i j = A.toOvlRight (A.reindexEquiv i) (A.reindexEquiv j) := rfl

/-! ### The product transports

Both use `piCongrLeft` in the `symm` direction, where evaluation is cast-free. -/

/-- The chart-product identification. -/
noncomputable def chartProdCongr : A.chartProd ≃ₗ[R] A.toAff.chartProd :=
  (LinearEquiv.piCongrLeft R A.colength A.reindexEquiv).symm

@[simp]
lemma chartProdCongr_apply (s : A.chartProd) (j : Fin (A.m₀ + A.m₁)) :
    A.chartProdCongr s j = s (A.reindexEquiv j) := rfl

/-- The overlap-product identification, along the diagonal action on the pair index. -/
noncomputable def ovlProdCongr : A.ovlProd ≃ₗ[R] A.toAff.ovlProd :=
  (LinearEquiv.piCongrLeft R (fun p : A.index × A.index => A.ovlColength p.1 p.2)
    (A.reindexEquiv.prodCongr A.reindexEquiv)).symm

@[simp]
lemma ovlProdCongr_apply (t : A.ovlProd) (p : Fin (A.m₀ + A.m₁) × Fin (A.m₀ + A.m₁)) :
    A.ovlProdCongr t p = t (A.reindexEquiv p.1, A.reindexEquiv p.2) := rfl

/-! ### The equalizer intertwines

Reindexing acts DIAGONALLY on the pair index, so the arrow at `(i, j)` of the widened
adaptation is the original arrow at `(e i, e j)` — the two squares commute componentwise. -/

/-- The left arrow intertwines with the product identifications. -/
lemma deltaLeft_chartProdCongr (s : A.chartProd) :
    A.toAff.deltaLeft (A.chartProdCongr s) = A.ovlProdCongr (A.deltaLeft s) := by
  funext p
  simp only [AffAdaptation.deltaLeft, deltaLeft, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply,
    chartProdCongr_apply, ovlProdCongr_apply]
  rw [toOvlLeft_toAff]
  rfl

/-- The right arrow intertwines with the product identifications. -/
lemma deltaRight_chartProdCongr (s : A.chartProd) :
    A.toAff.deltaRight (A.chartProdCongr s) = A.ovlProdCongr (A.deltaRight s) := by
  funext p
  simp only [AffAdaptation.deltaRight, deltaRight, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply,
    chartProdCongr_apply, ovlProdCongr_apply]
  rw [toOvlRight_toAff]
  rfl

/-- **Membership in the glued module transports.**  Both sides unfold to the same family of
overlap identities: the widened index runs over `Fin (m₀ + m₁)`, the original over
`Fin m₀ ⊕ Fin m₁`, and the relabelling is a bijection on pairs. -/
lemma mem_gluedSubmodule_chartProdCongr_iff (s : A.chartProd) :
    A.chartProdCongr s ∈ A.toAff.gluedSubmodule ↔ s ∈ A.gluedSubmodule := by
  simp only [AffAdaptation.gluedSubmodule, gluedSubmodule, LinearMap.mem_ker,
    LinearMap.sub_apply, sub_eq_zero, A.deltaLeft_chartProdCongr s,
    A.deltaRight_chartProdCongr s]
  exact ⟨fun h => A.ovlProdCongr.injective h, fun h => congrArg A.ovlProdCongr h⟩

/-- **The glued submodule is the image of the original one.**  This is the form the three
glued clauses need: `Submodule.map` of an equivalence, so `Module.Finite`, `Projective`,
`rankAtStalk` and the two cokernel flatnesses all transport. -/
lemma gluedSubmodule_toAff :
    A.toAff.gluedSubmodule = Submodule.map (A.chartProdCongr : A.chartProd →ₗ[R] _)
      A.gluedSubmodule := by
  refine le_antisymm (fun t ht => ?_) ?_
  · refine ⟨A.chartProdCongr.symm t, ?_, by simp⟩
    exact (A.mem_gluedSubmodule_chartProdCongr_iff _).mp
      (by simpa only [LinearEquiv.apply_symm_apply] using ht)
  · rintro t ⟨s, hs, rfl⟩
    exact (A.mem_gluedSubmodule_chartProdCongr_iff s).mpr hs

/-- **The glued modules are equivalent** — the map along which (c2)/(c3)/(c4) transport. -/
noncomputable def gluedCongr : A.Glued ≃ₗ[R] A.toAff.Glued :=
  (A.chartProdCongr.submoduleMap A.gluedSubmodule).trans
    (LinearEquiv.ofEq _ _ A.gluedSubmodule_toAff.symm)

/-- **(c3) transports**: the inclusion cokernels are equivalent, `chartProdCongr` carrying
`gluedSubmodule` onto `gluedSubmodule`. -/
noncomputable def cokerInclCongr :
    (A.chartProd ⧸ A.gluedSubmodule) ≃ₗ[R] (A.toAff.chartProd ⧸ A.toAff.gluedSubmodule) :=
  Submodule.Quotient.equiv _ _ A.chartProdCongr A.gluedSubmodule_toAff.symm

/-- **(c4) transports**: the difference-arrow ranges correspond under `ovlProdCongr`. -/
lemma difference_square :
    (A.toAff.deltaLeft - A.toAff.deltaRight) ∘ₗ (A.chartProdCongr : A.chartProd →ₗ[R] _)
      = (A.ovlProdCongr : A.ovlProd →ₗ[R] _) ∘ₗ (A.deltaLeft - A.deltaRight) := by
  refine LinearMap.ext fun s => ?_
  have hL := (A.ovlProdCongr : A.ovlProd →ₗ[R] A.toAff.ovlProd).map_sub
    (A.deltaLeft s) (A.deltaRight s)
  change A.toAff.deltaLeft (A.chartProdCongr s) - A.toAff.deltaRight (A.chartProdCongr s)
      = (A.ovlProdCongr : A.ovlProd →ₗ[R] A.toAff.ovlProd) ((A.deltaLeft - A.deltaRight) s)
  rw [LinearMap.sub_apply, hL, A.deltaLeft_chartProdCongr, A.deltaRight_chartProdCongr]
  rfl

lemma range_sub_toAff :
    LinearMap.range (A.toAff.deltaLeft - A.toAff.deltaRight)
      = Submodule.map (A.ovlProdCongr : A.ovlProd →ₗ[R] _)
          (LinearMap.range (A.deltaLeft - A.deltaRight)) := by
  have h1 : LinearMap.range ((A.toAff.deltaLeft - A.toAff.deltaRight)
        ∘ₗ (A.chartProdCongr : A.chartProd →ₗ[R] A.toAff.chartProd))
      = LinearMap.range (A.toAff.deltaLeft - A.toAff.deltaRight) :=
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr A.chartProdCongr.surjective)
  rw [← h1, A.difference_square, LinearMap.range_comp]

/-- The difference cokernels are equivalent. -/
noncomputable def cokerDiffCongr :
    (A.ovlProd ⧸ LinearMap.range (A.deltaLeft - A.deltaRight)) ≃ₗ[R]
      (A.toAff.ovlProd ⧸ LinearMap.range (A.toAff.deltaLeft - A.toAff.deltaRight)) :=
  Submodule.Quotient.equiv _ _ A.ovlProdCongr A.range_sub_toAff.symm

/-- **The certificate migrates, all seven clauses.**  Clauses (c1) are `rfl` at the
relabelled index; (c2)/(c3)/(c4) transport along `gluedCongr`, `cokerInclCongr` and
`cokerDiffCongr`.  Nothing is weakened and nothing is re-proved — this is what makes
"consumers port by reindexing alone" a theorem rather than a hope. -/
theorem isCertified_toAff {n : ℕ} (hA : A.IsCertified n) : A.toAff.IsCertified n where
  finite_colength := fun j => hA.finite_colength (A.reindexEquiv j)
  projective_colength := fun j => hA.projective_colength (A.reindexEquiv j)
  finite_glued :=
    haveI := hA.finite_glued
    Module.Finite.equiv A.gluedCongr
  projective_glued :=
    haveI := hA.projective_glued
    Module.Projective.of_equiv A.gluedCongr
  rankAtStalk_glued := fun p => by
    rw [← Module.rankAtStalk_eq_of_equiv A.gluedCongr]
    exact hA.rankAtStalk_glued p
  flat_coker_incl :=
    haveI := hA.flat_coker_incl
    Module.Flat.of_linearEquiv A.cokerInclCongr.symm
  flat_coker_diff :=
    haveI := hA.flat_coker_diff
    Module.Flat.of_linearEquiv A.cokerDiffCongr.symm

end DivisorAdaptation

/-! ## The family, the predicate and the functor value -/

namespace CertifiedDivisorFamily

variable {n : ℕ}

/-- **A chart-typed certified family is a widened one**, with the SAME local-equation
system — so every `DivEq` statement about it is unchanged. -/
noncomputable def toAff (F : CertifiedDivisorFamily C R π n) :
    CertifiedDivisorFamilyAff C R n where
  eqns := F.eqns
  cover := F.adaptation.toFinCoverData.toAffCoverData
  adaptation := F.adaptation.toAff
  certified := F.adaptation.isCertified_toAff F.certified

@[simp]
lemma toAff_eqns (F : CertifiedDivisorFamily C R π n) : F.toAff.eqns = F.eqns := rfl

end CertifiedDivisorFamily

/-- **The chart-typed pin implies the widened one.**  The base-side data `(m, g)` is reused
verbatim; only the curve-side certificate is migrated, and the divisor equality is literally
the same statement because `toAff` does not touch `eqns`.

The converse is FALSE, and that failure is the content of R2: a divisor straddling both pinned
vertical fibres has no chart-typed certificate (`informal/spec-dd-r.md` ADDENDUM 4 §4.3) but
does admit an affine-open one. -/
theorem isLocallyCertifiedAff_of_isLocallyCertified {n : ℕ}
    {d : (relCurve C R).LocalEquations} (hd : IsLocallyCertified C R π n d) :
    IsLocallyCertifiedAff n d := by
  obtain ⟨m, g, hg, hG⟩ := hd
  refine ⟨m, g, hg, fun i => ?_⟩
  haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (g i))) :=
    isOpenImmersion_relCurveMap_away C R (Localization.Away (g i)) (g i)
  obtain ⟨G, hGdiv⟩ := hG i
  exact ⟨G.toAff, hGdiv⟩

/-- **The induced map of functor values** `DivFamZar → DivFamZarAff`: the widened value
receives every chart-typed class.  Well defined because the two setoids are the same
`DivEq` relation on the same underlying systems. -/
noncomputable def DivFamZar.toAff {n : ℕ} (F : DivFamZar C R π n) : DivFamZarAff C R n :=
  Quotient.liftOn F
    (fun dp => DivFamZarAff.mk dp.1 (isLocallyCertifiedAff_of_isLocallyCertified dp.2))
    (fun _ _ h => DivFamZarAff.mk_eq_mk_iff.mpr h)

@[simp]
lemma DivFamZar.toAff_mk {n : ℕ} (d : (relCurve C R).LocalEquations)
    (hd : IsLocallyCertified C R π n d) :
    (DivFamZar.mk d hd).toAff
      = DivFamZarAff.mk d (isLocallyCertifiedAff_of_isLocallyCertified hd) :=
  rfl

/-- The old-to-widened comparison is injective. Both quotients identify local-equation
systems by the same `DivEq` relation; widening changes only which representatives are
admissible. -/
theorem DivFamZar.toAff_injective {n : ℕ} : Function.Injective
    (fun F : DivFamZar C R π n => F.toAff) := by
  intro F G h
  induction F using Quotient.inductionOn with
  | h dF =>
    induction G using Quotient.inductionOn with
    | h dG =>
      apply DivFamZar.mk_eq_mk_iff.mpr
      exact DivFamZarAff.mk_eq_mk_iff.mp h

/-- **The Picard class is unchanged by the widening** — the Abel hook DAT-C consumes the
same class whichever value it reads it from. -/
@[simp]
lemma DivFamZarAff.picClass_toAff {n : ℕ} (F : DivFamZar C R π n) :
    F.toAff.picClass = F.picClass := by
  induction F using Quotient.inductionOn with
  | h dp => rfl

end AlgebraicGeometry
