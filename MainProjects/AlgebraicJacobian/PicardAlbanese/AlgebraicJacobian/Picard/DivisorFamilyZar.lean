/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZarKit
import AlgebraicJacobian.Picard.DivisorFamilyZariskiSep
import AlgebraicJacobian.Picard.DivisorFamilyZariskiGlueKit

/-!
# Locally certified divisor families: the `DivFamZar` carrier (DD-2 stage S5b)

The Addendum-2 repair of the divisor-functor carrier (`informal/spec-dd-2.md`,
Addendum 2): the globally-certified `DivFam` is not a Zariski sheaf — the diagonal
divisor over `Γ(C \ pt)` is certifiable on a basic-open cover of the base but carries
no global certificate — so the faithful functor value is the **locally certified**
quotient `DivFamZar`. The generic germ-regularity engines live in
`AlgebraicJacobian.Picard.DivisorFamilyZarKit`.

* `AlgebraicGeometry.IsLocallyCertified` — the Addendum-2 frozen pin: a span-⊤ family
  `g : Fin m → R` with certified divisor families over `Localization.Away (g i)`
  divisor-equal to the pulled system; `hreg` is discharged by the Kit's open-immersion
  lemma, with the S4 instance provided by `haveI`.
* `IsLocallyCertified.of_divEq` — the pin respects divisor equality.
* `CertifiedDivisorFamily.isLocallyCertified` — a global certificate is a local one
  (trivial cover `g = ![1]`; the certified part is `mapAlg` to `Localization.Away 1`,
  whose equations ARE the pulled system on the nose).
* `IsLocallyCertified.germ_pullbackEqn_mem_nonZeroDivisors` — **the mapAlg-hreg
  engine**: a locally certified system has regular pulled equations along the
  comparison of an ARBITRARY test tower `R → R'` — regularity is germ-local, each germ
  sits over a chart `Localization.Away (algebraMap R R' (g i))` of `R'`, where the
  local certificate's regularity transports through its `DivEq` and the landed
  certificate-based pullback regularity.
* `AlgebraicGeometry.DivFamZar` — the quotient of locally certified systems by
  `DivEq`, with `mk`, `mk_eq_mk_iff`, `picClass`, and `DivFam.toZar`.

Total `DivFamZar.mapAlg` and the Zariski keystones are
`AlgebraicJacobian.Picard.DivisorFamilyZarMapAlg` / `…ZarGlue`.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## The locally certified pin -/

variable {k : Type u} [Field k]
variable (C : Over (Spec (.of k))) (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k) [IsAffineHom π]

/-- **The Addendum-2 frozen pin** (`informal/spec-dd-2.md`, Addendum 2): a
local-equation system on the relative curve is *locally certified* in degree `n` if
some span-⊤ family `g : Fin m → R` carries certified divisor families over the
localizations `Localization.Away (g i)` that are divisor-equal to the pulled system.
The pullback's regularity hypothesis is discharged once and for all by the Kit's
open-immersion lemma — the comparison of an away localization is an open immersion
(the S4 instance, provided by `haveI`). -/
def IsLocallyCertified (n : ℕ) (d : (relCurve C R).LocalEquations) : Prop :=
  ∃ (m : ℕ) (g : Fin m → R), Ideal.span (Set.range g) = ⊤ ∧
    ∀ i : Fin m,
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (g i))) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away (g i)) (g i)
      ∃ G : CertifiedDivisorFamily C (Localization.Away (g i)) π n,
        Scheme.LocalEquations.DivEq G.eqns
          (d.pullback (relCurveMap C R (Localization.Away (g i)))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away (g i))) d))

variable {C R π}

/-- **The locally certified pin respects divisor equality**: the local `DivEq`s
transport through `divEq_pullback` (regularity along the chart immersions is free). -/
theorem IsLocallyCertified.of_divEq {n : ℕ} {d d' : (relCurve C R).LocalEquations}
    (hd : IsLocallyCertified C R π n d) (h : Scheme.LocalEquations.DivEq d d') :
    IsLocallyCertified C R π n d' := by
  obtain ⟨m, g, hg, hG⟩ := hd
  refine ⟨m, g, hg, fun i => ?_⟩
  haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (g i))) :=
    isOpenImmersion_relCurveMap_away C R (Localization.Away (g i)) (g i)
  obtain ⟨G, hGdiv⟩ := hG i
  exact ⟨G, hGdiv.trans
    (Scheme.LocalEquations.divEq_pullback (relCurveMap C R (Localization.Away (g i)))
      h _ _)⟩

/-- **A global certificate is a local one** (the trivial cover `g = ![1]`): the
certified part over `Localization.Away (1 : R)` is `mapAlg` of the family, whose
equations are the pulled system on the nose (`pulledEquations` IS the pullback along
the comparison; the regularity proofs are proof-irrelevant). -/
theorem CertifiedDivisorFamily.isLocallyCertified {n : ℕ}
    (F : CertifiedDivisorFamily C R π n) : IsLocallyCertified C R π n F.eqns := by
  refine ⟨1, fun _ => (1 : R), ?_, fun i => ?_⟩
  · have hrange : Set.range (fun _ : Fin 1 => (1 : R)) = {1} := Set.range_const
    rw [hrange, Ideal.span_singleton_one]
  · haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (1 : R))) :=
      isOpenImmersion_relCurveMap_away C R (Localization.Away (1 : R)) 1
    exact ⟨F.mapAlg (Localization.Away (1 : R)) n,
      Scheme.LocalEquations.divEq_refl _⟩

/-! ## The mapAlg-hreg engine -/

section MapAlgHreg

variable {n : ℕ} {d : (relCurve C R).LocalEquations}
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']

/-- **The mapAlg-hreg engine** (S5b): a locally certified system has regular pulled
equations along the comparison of an ARBITRARY test tower `R → R'`. Regularity is
germ-local on the curve: the charts `Localization.Away (algebraMap R R' (g i))` cover
`relCurve C R'` by open immersions; over each, the composite comparison factors
through the certified chart `Localization.Away (g i)`, where the certificate's
pullback regularity (`DivisorAdaptation.germ_pullbackEqn_mem_nonZeroDivisors`)
transports through the recorded `DivEq`. -/
theorem IsLocallyCertified.germ_pullbackEqn_mem_nonZeroDivisors
    (hloc : IsLocallyCertified C R π n d)
    (y z : relCurve C R') (hz : z ∈ (d.cover.pullback (relCurveMap C R R')).opens y) :
    ((relCurve C R').presheaf.germ ((d.cover.pullback (relCurveMap C R R')).opens y)
        z hz).hom (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d y)
      ∈ nonZeroDivisors ((relCurve C R').presheaf.stalk z) := by
  classical
  obtain ⟨m, g, hg, hG⟩ := hloc
  -- the away charts of `R'` at the pushed cover, and their immersions
  haveI himm : ∀ i : ULift.{u} (Fin m),
      IsOpenImmersion (relCurveMap C R'
        (Localization.Away (algebraMap R R' (g i.down)))) := fun i =>
    isOpenImmersion_relCurveMap_away C R'
      (Localization.Away (algebraMap R R' (g i.down))) (algebraMap R R' (g i.down))
  -- the pushed family spans the unit ideal of `R'`
  have hspan' : Ideal.span (Set.range
      (fun i : ULift.{u} (Fin m) => algebraMap R R' (g i.down))) = ⊤ := by
    have hrange : Set.range (fun i : ULift.{u} (Fin m) => algebraMap R R' (g i.down))
        = algebraMap R R' '' Set.range g := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨g i.down, ⟨i.down, rfl⟩, rfl⟩
      · rintro ⟨-, ⟨j, rfl⟩, rfl⟩
        exact ⟨⟨j⟩, rfl⟩
    rw [hrange, ← Ideal.map_span, hg, Ideal.map_top]
  refine Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_immersion_cover
    (fun i : ULift.{u} (Fin m) => relCurveMap C R'
      (Localization.Away (algebraMap R R' (g i.down))))
    (fun y' => exists_relCurveMap_base_eq C R'
      (fun i : ULift.{u} (Fin m) => algebraMap R R' (g i.down))
      (fun i => Localization.Away (algebraMap R R' (g i.down))) hspan' y')
    (relCurveMap C R R') d (fun i ζ => ?_) y z hz
  -- over the chart at `g i`: factor the composite through the certified localization
  obtain ⟨G, hGdiv⟩ := hG i.down
  haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (g i.down))) :=
    isOpenImmersion_relCurveMap_away C R (Localization.Away (g i.down)) (g i.down)
  -- the away map `Localization.Away (g i) → Localization.Away (φ (g i))` as an
  -- algebra tower
  letI : Algebra (Localization.Away (g i.down))
      (Localization.Away (algebraMap R R' (g i.down))) :=
    (IsLocalization.map (M := Submonoid.powers (g i.down))
      (T := Submonoid.powers (algebraMap R R' (g i.down)))
      (Localization.Away (algebraMap R R' (g i.down))) (algebraMap R R')
      (by
        rintro x ⟨e, rfl⟩
        use e
        simp)).toAlgebra
  haveI : IsScalarTower R (Localization.Away (g i.down))
      (Localization.Away (algebraMap R R' (g i.down))) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp,
        ← IsScalarTower.algebraMap_eq])
  haveI : IsScalarTower k (Localization.Away (g i.down))
      (Localization.Away (algebraMap R R' (g i.down))) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq k R (Localization.Away (g i.down)),
        ← RingHom.comp_assoc,
        ← IsScalarTower.algebraMap_eq R (Localization.Away (g i.down))
          (Localization.Away (algebraMap R R' (g i.down))),
        ← IsScalarTower.algebraMap_eq k R
          (Localization.Away (algebraMap R R' (g i.down)))])
  -- the comparison triangle through the two factorizations of `C_{T i} → C_R`
  have hcomp₁ : relCurveMap C (Localization.Away (g i.down))
        (Localization.Away (algebraMap R R' (g i.down)))
      ≫ relCurveMap C R (Localization.Away (g i.down))
      = relCurveMap C R (Localization.Away (algebraMap R R' (g i.down))) :=
    relCurveMap_comp (R' := Localization.Away (g i.down))
      (R'' := Localization.Away (algebraMap R R' (g i.down)))
  have hcomp₂ : relCurveMap C R' (Localization.Away (algebraMap R R' (g i.down)))
      ≫ relCurveMap C R R'
      = relCurveMap C R (Localization.Away (algebraMap R R' (g i.down))) :=
    relCurveMap_comp (R' := R')
      (R'' := Localization.Away (algebraMap R R' (g i.down)))
  have step1 := Scheme.LocalEquations.germ_pullbackEqn_congr hcomp₂ d ζ
  have step2 := Scheme.LocalEquations.germ_pullbackEqn_comp hcomp₁ d
    (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
      (relCurveMap C R (Localization.Away (g i.down))) d) ζ
  have hfinal := Scheme.LocalEquations.germ_self_pullbackEqn_mem_nonZeroDivisors_of_divEq
    (relCurveMap C (Localization.Away (g i.down))
      (Localization.Away (algebraMap R R' (g i.down)))) hGdiv ζ
    (G.adaptation.germ_pullbackEqn_mem_nonZeroDivisors
      (Localization.Away (algebraMap R R' (g i.down)))
      G.certified.projective_colength ζ ζ
      ((G.eqns.cover.pullback (relCurveMap C (Localization.Away (g i.down))
        (Localization.Away (algebraMap R R' (g i.down))))).mem_opens ζ))
  exact ((step1.trans step2).symm ▸ hfinal)

end MapAlgHreg

/-! ## The locally certified divisor-functor value -/

variable (C R π)
variable (n : ℕ)

/-- The divisor-equality setoid on locally certified systems (Addendum 2's mirror of
`divFamSetoid`): the underlying local-equation systems cut the same divisor; the local
certificates are per-representative data and do not enter the relation. -/
def divFamZarSetoid : Setoid {d : (relCurve C R).LocalEquations //
    IsLocallyCertified C R π n d} where
  r d₁ d₂ := Scheme.LocalEquations.DivEq d₁.1 d₂.1
  iseqv :=
    ⟨fun d => Scheme.LocalEquations.divEq_refl d.1,
     fun h => h.symm, fun h h' => h.trans h'⟩

/-- **The locally certified divisor-functor value on the affine test `R`**
(`informal/spec-dd-2.md`, Addendum 2): locally certified local-equation systems of
degree `n` up to divisor equality. This is the carrier on which the divisor functor is
a Zariski sheaf — the globally certified `DivFam` remains the building block. -/
def DivFamZar : Type u := Quotient (divFamZarSetoid C R π n)

namespace DivFamZar

variable {C R π n}

/-- The class of a locally certified system. -/
def mk (d : (relCurve C R).LocalEquations) (hd : IsLocallyCertified C R π n d) :
    DivFamZar C R π n :=
  Quotient.mk (divFamZarSetoid C R π n) ⟨d, hd⟩

lemma mk_eq_mk_iff {d₁ d₂ : (relCurve C R).LocalEquations}
    {h₁ : IsLocallyCertified C R π n d₁} {h₂ : IsLocallyCertified C R π n d₂} :
    mk d₁ h₁ = mk d₂ h₂ ↔ Scheme.LocalEquations.DivEq d₁ d₂ :=
  Quotient.eq (r := divFamZarSetoid C R π n)

/-- **The Picard class of a locally certified divisor class** `𝒪(D)`: well defined on
the quotient by `picClass_eq_of_divEq`. -/
noncomputable def picClass (F : DivFamZar C R π n) : (relCurve C R).CechPic :=
  Quotient.lift
    (fun d : {d : (relCurve C R).LocalEquations // IsLocallyCertified C R π n d} =>
      d.1.picClass)
    (fun _ _ h => Scheme.LocalEquations.picClass_eq_of_divEq h) F

@[simp]
lemma picClass_mk (d : (relCurve C R).LocalEquations)
    (hd : IsLocallyCertified C R π n d) : picClass (mk d hd) = d.picClass :=
  rfl

end DivFamZar

variable {C R π n}

/-- **The comparison from the globally certified value**: a certified family is
locally certified (trivial cover), and divisor equality is the relation on both
sides. Over a field the two notions agree; over a general base `toZar` is the
sheafification-of-value comparison. -/
def DivFam.toZar : DivFam C R π n → DivFamZar C R π n :=
  Quotient.lift
    (fun F : CertifiedDivisorFamily C R π n =>
      DivFamZar.mk F.eqns F.isLocallyCertified)
    (fun _ _ h => DivFamZar.mk_eq_mk_iff.mpr h)

@[simp]
lemma DivFam.toZar_mk (F : CertifiedDivisorFamily C R π n) :
    (DivFam.mk F).toZar = DivFamZar.mk F.eqns F.isLocallyCertified :=
  rfl

/-- The Picard class factors through `toZar`. -/
@[simp]
lemma DivFamZar.picClass_toZar (F : DivFam C R π n) :
    F.toZar.picClass = F.picClass := by
  induction F using Quotient.inductionOn with
  | h F => rfl

end AlgebraicGeometry
