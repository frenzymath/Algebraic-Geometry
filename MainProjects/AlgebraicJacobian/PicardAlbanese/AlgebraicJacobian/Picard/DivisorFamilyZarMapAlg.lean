/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZar

/-!
# Total base change of locally certified divisor classes (DD-2 stage S5b)

`DivFamZar.mapAlg` along an ARBITRARY test change `R → R'` and the S5b separation
keystone (`informal/spec-dd-2.md`, Addendum 2). The pulled representative exists by
the mapAlg-hreg engine (`IsLocallyCertified.germ_pullbackEqn_mem_nonZeroDivisors`);
the local certificates transport chart by chart: the pushed cover
`algebraMap R R' ∘ g` spans `⊤`, and over `Localization.Away (algebraMap R R' (g i))`
the certified part is `mapAlg` of the local certified family along the induced away
map, coherent with the pulled system by the S2 pullback calculus.

* `AlgebraicGeometry.CertifiedDivisorFamily.divEq_mapAlg_pullback` — **witness
  transport along a tower** `R → A → B`: a certified family over `A` divisor-equal to
  the pulled system stays divisor-equal after `mapAlg` to `B`
  (`divEq_pullback` + `divEq_pullback_pullback` at `relCurveMap_comp`).
* `AlgebraicGeometry.IsLocallyCertified.pullback` — **certificate transport**: local
  certification is stable under arbitrary base change (the away map
  `Localization.Away (g i) → Localization.Away (algebraMap R R' (g i))` is
  `IsLocalization.map` of the powers submonoid, installed as a local tower).
* `AlgebraicGeometry.DivFamZar.mapAlg` — the total divisor-functor map on locally
  certified classes, with `mapAlg_mk`, the Abel-hook law `picClass_mapAlg`, the
  functor laws `mapAlg_id` / `mapAlg_comp`, and the comparison coherence
  `DivFam.toZar_mapAlg`.
* `AlgebraicGeometry.DivFamZar.eq_of_away_eq` — **Zariski separation at the Zar
  level**: certificates play no role in equality; the statement reduces verbatim to
  the S4 `DivEq`-level engine `divEq_of_divEq_pullback`.
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

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

/-! ## Witness transport along a tower -/

/-- **Witness transport along a tower `R → A → B`**: if a certified family `E` over
`A` is divisor-equal to the pullback of `d` along the comparison of `A`, then its
`mapAlg` to `B` is divisor-equal to the pullback of `d` along the comparison of `B`.
Chain: `divEq_pullback` along `relCurveMap C A B` (certificate regularity on the
`E`-side, `DivEq`-transported regularity on the `d`-side), then the composite
collapse `divEq_pullback_pullback` at `relCurveMap_comp`. -/
theorem CertifiedDivisorFamily.divEq_mapAlg_pullback {n : ℕ}
    {A : Type u} [CommRing A] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
    (B : Type u) [CommRing B] [Algebra k B] [Algebra R B] [Algebra A B]
    [IsScalarTower k R B] [IsScalarTower k A B] [IsScalarTower R A B]
    (E : CertifiedDivisorFamily C A π n) {d : (relCurve C R).LocalEquations}
    {hregA} (hregB)
    (hdiv : Scheme.LocalEquations.DivEq E.eqns (d.pullback (relCurveMap C R A) hregA)) :
    Scheme.LocalEquations.DivEq (E.mapAlg B n).eqns
      (d.pullback (relCurveMap C R B) hregB) := by
  have hcomp : relCurveMap C A B ≫ relCurveMap C R A = relCurveMap C R B :=
    relCurveMap_comp (R' := A) (R'' := B)
  have hregMid := Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_divEq
    (relCurveMap C A B) hdiv
    (E.adaptation.germ_pullbackEqn_mem_nonZeroDivisors B E.certified.projective_colength)
  exact Scheme.LocalEquations.DivEq.trans
    (Scheme.LocalEquations.divEq_pullback (relCurveMap C A B) hdiv
      (E.adaptation.germ_pullbackEqn_mem_nonZeroDivisors B
        E.certified.projective_colength) hregMid)
    (Scheme.LocalEquations.divEq_pullback_pullback hcomp d hregA hregMid hregB)

/-! ## Certificate transport -/

section Transport

variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable {n : ℕ}

private lemma span_range_algebraMap_eq_top {m : ℕ} {g : Fin m → R}
    (hg : Ideal.span (Set.range g) = ⊤) :
    Ideal.span (Set.range fun i : Fin m => algebraMap R R' (g i)) = ⊤ := by
  have hrange : (Set.range fun i : Fin m => algebraMap R R' (g i))
      = algebraMap R R' '' Set.range g := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨g i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨-, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  rw [hrange, ← Ideal.map_span, hg, Ideal.map_top]

/-- **Certificate transport** (S5b): local certification is stable under an ARBITRARY
test change `R → R'` — the pushed cover `algebraMap R R' ∘ g` spans `⊤`, and over each
`Localization.Away (algebraMap R R' (g i))` the certified part is `mapAlg` of the
local certified family along the induced away map, divisor-equal to the pulled system
by witness transport plus the composite collapse through the two factorizations of
the chart comparison. -/
theorem IsLocallyCertified.pullback {d : (relCurve C R).LocalEquations}
    (hloc : IsLocallyCertified C R π n d) (hreg) :
    IsLocallyCertified C R' π n (d.pullback (relCurveMap C R R') hreg) := by
  classical
  obtain ⟨m, g, hg, hG⟩ := hloc
  have hloc' : IsLocallyCertified C R π n d := ⟨m, g, hg, hG⟩
  refine ⟨m, fun i => algebraMap R R' (g i), span_range_algebraMap_eq_top R' hg,
    fun i => ?_⟩
  obtain ⟨G, hGdiv⟩ := hG i
  haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (g i))) :=
    isOpenImmersion_relCurveMap_away C R (Localization.Away (g i)) (g i)
  haveI : IsOpenImmersion (relCurveMap C R'
      (Localization.Away (algebraMap R R' (g i)))) :=
    isOpenImmersion_relCurveMap_away C R'
      (Localization.Away (algebraMap R R' (g i))) (algebraMap R R' (g i))
  -- the induced away map as a local algebra tower
  letI : Algebra (Localization.Away (g i))
      (Localization.Away (algebraMap R R' (g i))) :=
    (IsLocalization.map (M := Submonoid.powers (g i))
      (T := Submonoid.powers (algebraMap R R' (g i)))
      (Localization.Away (algebraMap R R' (g i))) (algebraMap R R')
      (by
        rintro x ⟨e, rfl⟩
        use e
        simp)).toAlgebra
  haveI : IsScalarTower R (Localization.Away (g i))
      (Localization.Away (algebraMap R R' (g i))) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp,
        ← IsScalarTower.algebraMap_eq])
  haveI : IsScalarTower k (Localization.Away (g i))
      (Localization.Away (algebraMap R R' (g i))) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq k R (Localization.Away (g i)),
        ← RingHom.comp_assoc,
        ← IsScalarTower.algebraMap_eq R (Localization.Away (g i))
          (Localization.Away (algebraMap R R' (g i))),
        ← IsScalarTower.algebraMap_eq k R
          (Localization.Away (algebraMap R R' (g i)))])
  -- witness transport along `R → Localization.Away (g i) → the pushed chart`
  have hW := G.divEq_mapAlg_pullback (Localization.Away (algebraMap R R' (g i)))
    (hloc'.germ_pullbackEqn_mem_nonZeroDivisors
      (Localization.Away (algebraMap R R' (g i)))) hGdiv
  -- the composite collapse through the `R'`-side factorization
  have hcomp₂ : relCurveMap C R' (Localization.Away (algebraMap R R' (g i)))
      ≫ relCurveMap C R R'
      = relCurveMap C R (Localization.Away (algebraMap R R' (g i))) :=
    relCurveMap_comp (R' := R') (R'' := Localization.Away (algebraMap R R' (g i)))
  have hstep := Scheme.LocalEquations.divEq_pullback_pullback hcomp₂ d hreg
    (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
      (relCurveMap C R' (Localization.Away (algebraMap R R' (g i))))
      (d.pullback (relCurveMap C R R') hreg))
    (hloc'.germ_pullbackEqn_mem_nonZeroDivisors
      (Localization.Away (algebraMap R R' (g i))))
  exact ⟨G.mapAlg (Localization.Away (algebraMap R R' (g i))) n, hW.trans hstep.symm⟩

/-! ## The total divisor-functor map on locally certified classes -/

variable (n : ℕ)

/-- **The total divisor-functor map on locally certified classes** along an ARBITRARY
test change (`informal/spec-dd-2.md`, Addendum 2): pull back the representative (the
mapAlg-hreg engine discharges regularity) and transport the local certificates. Well
defined by `divEq_pullback`. -/
noncomputable def DivFamZar.mapAlg : DivFamZar C R π n → DivFamZar C R' π n :=
  Quotient.lift
    (fun dp : {d : (relCurve C R).LocalEquations // IsLocallyCertified C R π n d} =>
      DivFamZar.mk (dp.1.pullback (relCurveMap C R R')
          (dp.2.germ_pullbackEqn_mem_nonZeroDivisors R'))
        (dp.2.pullback R' _))
    (fun _ _ h => DivFamZar.mk_eq_mk_iff.mpr
      (Scheme.LocalEquations.divEq_pullback (relCurveMap C R R') h _ _))

@[simp]
lemma DivFamZar.mapAlg_mk (d : (relCurve C R).LocalEquations)
    (hd : IsLocallyCertified C R π n d) :
    DivFamZar.mapAlg R' n (DivFamZar.mk d hd)
      = DivFamZar.mk (d.pullback (relCurveMap C R R')
          (hd.germ_pullbackEqn_mem_nonZeroDivisors R'))
        (hd.pullback R' _) :=
  rfl

/-- **The Abel-hook class law at the Zar level**: the divisor-functor map intertwines
the Picard classes with the Čech-Picard pullback, `𝒪(f*D) = f*𝒪(D)`. -/
lemma DivFamZar.picClass_mapAlg (F : DivFamZar C R π n) :
    (DivFamZar.mapAlg R' n F).picClass =
      Scheme.CechPic.map (relCurveMap C R R') F.picClass := by
  induction F using Quotient.inductionOn with
  | h d => exact Scheme.LocalEquations.picClass_pullback (relCurveMap C R R') d.1 _

/-- **`toZar` intertwines the two total maps**: base change of a globally certified
class agrees with base change of its locally certified image — both representatives
are the pulled system (with proof-irrelevant regularity witnesses). -/
lemma DivFam.toZar_mapAlg (F : DivFam C R π n) :
    (DivFam.mapAlg R' n F).toZar = DivFamZar.mapAlg R' n F.toZar := by
  induction F using Quotient.inductionOn with
  | h F => exact DivFamZar.mk_eq_mk_iff.mpr (Scheme.LocalEquations.divEq_refl _)

/-- **The identity functor law** at the Zar level: base change along the identity
tower is the identity (`divEq_pullback_id` at `relCurveMap_id`). -/
lemma DivFamZar.mapAlg_id (F : DivFamZar C R π n) : DivFamZar.mapAlg R n F = F := by
  induction F using Quotient.inductionOn with
  | h d =>
      exact DivFamZar.mk_eq_mk_iff.mpr
        (Scheme.LocalEquations.divEq_pullback_id relCurveMap_id d.1 _)

variable (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
variable [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R'']

/-- **The composition functor law** at the Zar level: base change composes over a
tower `R → R' → R''` (`divEq_pullback_pullback` at `relCurveMap_comp`). -/
lemma DivFamZar.mapAlg_comp (F : DivFamZar C R π n) :
    DivFamZar.mapAlg R'' n (DivFamZar.mapAlg R' n F) = DivFamZar.mapAlg R'' n F := by
  induction F using Quotient.inductionOn with
  | h d =>
      exact DivFamZar.mk_eq_mk_iff.mpr
        (Scheme.LocalEquations.divEq_pullback_pullback
          (relCurveMap_comp (R' := R') (R'' := R'')) d.1 _ _ _)

end Transport

/-! ## Zariski separation at the Zar level -/

/-- **Zariski separation of the locally certified divisor functor**
(`informal/spec-dd-2.md`, Addendum 2 — the S5b separation keystone): two locally
certified divisor classes over `R` agreeing under `DivFamZar.mapAlg` on every member
of a finite covering family of localizations agree. Certificates play no role in
equality: the statement reduces verbatim to the S4 `DivEq`-level engine
`divEq_of_divEq_pullback`, with regularity along the chart immersions free (Kit). -/
theorem DivFamZar.eq_of_away_eq {n : ℕ} {ι : Type u} [Finite ι] (g : ι → R)
    (S : ι → Type u)
    [∀ i, CommRing (S i)] [∀ i, Algebra k (S i)] [∀ i, Algebra R (S i)]
    [∀ i, IsScalarTower k R (S i)] [∀ i, IsLocalization.Away (g i) (S i)]
    (hg : Ideal.span (Set.range g) = ⊤) {F G : DivFamZar C R π n}
    (h : ∀ i, DivFamZar.mapAlg (S i) n F = DivFamZar.mapAlg (S i) n G) :
    F = G := by
  haveI : ∀ i, IsOpenImmersion (relCurveMap C R (S i)) := fun i =>
    isOpenImmersion_relCurveMap_away C R (S i) (g i)
  revert h
  refine Quotient.inductionOn₂ F G fun d₁ d₂ h => ?_
  refine DivFamZar.mk_eq_mk_iff.mpr ?_
  refine Scheme.LocalEquations.divEq_of_divEq_pullback
    (fun i => relCurveMap C R (S i))
    (fun y => exists_relCurveMap_base_eq C R g S hg y)
    (fun i => d₁.2.germ_pullbackEqn_mem_nonZeroDivisors (S i))
    (fun i => d₂.2.germ_pullbackEqn_mem_nonZeroDivisors (S i))
    (fun i => ?_)
  exact DivFamZar.mk_eq_mk_iff.mp (h i)

end AlgebraicGeometry
