/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffCert
import AlgebraicJacobian.Picard.DivisorFamilyAffZar
import AlgebraicJacobian.Picard.DivisorFamilyAffCompare
import AlgebraicJacobian.Picard.DivisorFamilyZarMapAlg

/-!
# The widened divisor-functor map (R2, human decision I-0492)

`DivFamZarAff.mapAlg` along an arbitrary test change `R → R'`, with the functor laws, the Abel
hook, and the Zariski separation keystone.  This is what makes the widened value a functor
VALUE rather than a bare type: before this file nothing could base-change a widened class.

## Where the widening does and does not show

Almost nowhere.  `IsLocallyCertifiedAff` widens where the pieces live on the CURVE and changes
nothing about the Zariski cover of the BASE, so the base-side machinery of
`DivisorFamilyZarMapAlg.lean` — the `Localization.Away` towers, `IsLocalization.map`,
`span_range_algebraMap_eq_top` — applies verbatim; the cover datum only appears inside the
opaque `mapAlg` of the local certified family.  Likewise
`Scheme.LocalEquations.divEq_pullback`, `divEq_pullback_id` and `divEq_pullback_pullback` are
stated for ARBITRARY scheme morphisms and know nothing about covers, so the functor laws are
the same three lines as in the chart-typed case.

## The one honest cost of the widening: overlap affineness

`AffCoverData` demands affineness of the pieces only (that is the R2 shape), so the certificate
transport takes an explicit `hinf` — the overlaps are affine.  A `CertifiedDivisorFamilyAff`
therefore cannot be base-changed without it, and rather than weaken the structure this file
carries `hinf` as a hypothesis on `mapAlg` at the family level.  It is not a hidden
assumption: it is visible in every signature below, as I-0492 clause 4 requires.  For a
relative curve over a proper `C` it is discharged by separatedness (`IsAffineOpen.inf`).

## Main declarations

* `CertifiedDivisorFamilyAff.mapAlg` — base change of a widened certified family.
* `IsLocallyCertifiedAff.pullback` — certificate transport along an arbitrary test change.
* `DivFamZarAff.mapAlg`, with `mapAlg_mk`, `picClass_mapAlg`, `mapAlg_id`, `mapAlg_comp`.
* `DivFamZarAff.eq_of_away_eq` — Zariski separation at the widened Zar level.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]

/-- **Overlap affineness of a widened cover** — the one datum the certificate transport needs
beyond `AffCoverData`'s own fields.  Named so that it can be threaded explicitly and read off
any signature; for a relative curve over a proper `C` it follows from separatedness. -/
def AffCoverData.HasAffineOverlaps (D : AffCoverData C R) : Prop :=
  ∀ i j : D.index, IsAffineOpen (D.pieces i ⊓ D.pieces j)

variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable (n : ℕ)

/-- **Base change of a widened certified family**: pulled equations, base-changed cover and
adaptation, transported certificate. -/
noncomputable def CertifiedDivisorFamilyAff.mapAlg (F : CertifiedDivisorFamilyAff C R n)
    (hinf : F.cover.HasAffineOverlaps) : CertifiedDivisorFamilyAff C R' n where
  eqns := F.adaptation.pulledEquations R' F.certified.projective_colength
  cover := F.cover.baseChange R'
  adaptation := F.adaptation.pullback R' F.certified.projective_colength
  certified := F.adaptation.isCertified_pullback R' hinf F.certified

@[simp]
lemma CertifiedDivisorFamilyAff.mapAlg_cover (F : CertifiedDivisorFamilyAff C R n)
    (hinf : F.cover.HasAffineOverlaps) :
    (F.mapAlg R' n hinf).cover = F.cover.baseChange R' := rfl

/-- **The base-changed cover again has affine overlaps**: overlaps of base-changed pieces are
preimages of overlaps, and preimages of affine opens under `relCurveMap` are affine.  So the
`hinf` obligation propagates along a tower rather than accumulating. -/
theorem AffCoverData.hasAffineOverlaps_baseChange {D : AffCoverData C R}
    (hinf : D.HasAffineOverlaps) : (D.baseChange R').HasAffineOverlaps := fun i j => by
  rw [show (D.baseChange R').pieces i ⊓ (D.baseChange R').pieces j
      = relCurveMap C R R' ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) from rfl]
  exact isAffineOpen_relCurveMap_preimage C R' (hinf i j)

/-- **`HasAffineOverlaps` is FREE for a proper `C`** — which is the only case the DD-R lane
ever uses.  The relative curve over a proper `C` is a separated scheme, so its affine opens are
closed under intersection (`Over.isAffineOpen_inf`, via the affine diagonal).

So the `hinf` threading below is bookkeeping, not a standing assumption: it is dischargeable
wherever `C` is proper, and it is stated rather than assumed so that a reader can see the cost
of `AffCoverData` demanding affineness of the pieces only. -/
theorem AffCoverData.hasAffineOverlaps_of_isProper [IsProper C.hom] (D : AffCoverData C R) :
    D.HasAffineOverlaps := fun i j =>
  Over.isAffineOpen_inf (A := R) C (D.isAffineOpen i) (D.isAffineOpen j)

/-! ## Witness transport along a tower -/

/-- **Witness transport along a tower `R → A → B`**, widened: a certified family over `A`
divisor-equal to the pulled system stays divisor-equal after `mapAlg` to `B`.  Verbatim the
chart-typed `CertifiedDivisorFamily.divEq_mapAlg_pullback` — `divEq_pullback` along
`relCurveMap C A B`, then the composite collapse `divEq_pullback_pullback` at
`relCurveMap_comp`; both are statements about arbitrary scheme morphisms. -/
theorem CertifiedDivisorFamilyAff.divEq_mapAlg_pullback
    {A : Type u} [CommRing A] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
    (B : Type u) [CommRing B] [Algebra k B] [Algebra R B] [Algebra A B]
    [IsScalarTower k R B] [IsScalarTower k A B] [IsScalarTower R A B]
    (E : CertifiedDivisorFamilyAff C A n) (hinf : E.cover.HasAffineOverlaps)
    {d : (relCurve C R).LocalEquations} {hregA} (hregB)
    (hdiv : Scheme.LocalEquations.DivEq E.eqns (d.pullback (relCurveMap C R A) hregA)) :
    Scheme.LocalEquations.DivEq (E.mapAlg B n hinf).eqns
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

/-! ## The mapAlg-hreg engine, widened

The widened analogue of `IsLocallyCertified.germ_pullbackEqn_mem_nonZeroDivisors`: a widened
locally certified system has regular pulled equations along an arbitrary test tower.
Regularity is germ-local on the curve, and the covering argument is on the BASE, so the proof
is the chart-typed one with `CertifiedDivisorFamily` replaced by
`CertifiedDivisorFamilyAff`. -/

theorem IsLocallyCertifiedAff.germ_pullbackEqn_mem_nonZeroDivisors
    {d : (relCurve C R).LocalEquations}
    (hloc : IsLocallyCertifiedAff (C := C) (R := R) n d)
    (y z : relCurve C R') (hz : z ∈ (d.cover.pullback (relCurveMap C R R')).opens y) :
    ((relCurve C R').presheaf.germ ((d.cover.pullback (relCurveMap C R R')).opens y)
        z hz).hom (Scheme.LocalEquations.pullbackEqn (relCurveMap C R R') d y)
      ∈ nonZeroDivisors ((relCurve C R').presheaf.stalk z) := by
  classical
  obtain ⟨m, g, hg, hG⟩ := hloc
  haveI himm : ∀ i : ULift.{u} (Fin m),
      IsOpenImmersion (relCurveMap C R'
        (Localization.Away (algebraMap R R' (g i.down)))) := fun i =>
    isOpenImmersion_relCurveMap_away C R'
      (Localization.Away (algebraMap R R' (g i.down))) (algebraMap R R' (g i.down))
  have hspan' : Ideal.span (Set.range
      (fun i : ULift.{u} (Fin m) => algebraMap R R' (g i.down))) = ⊤ := by
    have hrange : Set.range (fun i : ULift.{u} (Fin m) => algebraMap R R' (g i.down))
        = algebraMap R R' '' Set.range g := by
      ext x
      exact ⟨by rintro ⟨i, rfl⟩; exact ⟨g i.down, ⟨i.down, rfl⟩, rfl⟩,
        by rintro ⟨-, ⟨j, rfl⟩, rfl⟩; exact ⟨⟨j⟩, rfl⟩⟩
    rw [hrange, ← Ideal.map_span, hg, Ideal.map_top]
  refine Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_immersion_cover
    (fun i : ULift.{u} (Fin m) => relCurveMap C R'
      (Localization.Away (algebraMap R R' (g i.down))))
    (fun y' => exists_relCurveMap_base_eq C R'
      (fun i : ULift.{u} (Fin m) => algebraMap R R' (g i.down))
      (fun i => Localization.Away (algebraMap R R' (g i.down))) hspan' y')
    (relCurveMap C R R') d (fun i ζ => ?_) y z hz
  obtain ⟨G, hGdiv⟩ := hG i.down
  haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (g i.down))) :=
    isOpenImmersion_relCurveMap_away C R (Localization.Away (g i.down)) (g i.down)
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

/-! ## Certificate transport along an arbitrary test change

`IsProper C.hom` from here on: it is what makes `HasAffineOverlaps` free
(`hasAffineOverlaps_of_isProper`), so no `hinf` appears in any statement below.  The DD-R lane
has this hypothesis everywhere — the challenge curve is proper over `k`. -/

section Transport

variable [IsProper C.hom]

/-- **Certificate transport, widened** (the S5b keystone at `DivFamZarAff`): the widened
locally-certified predicate is stable under an ARBITRARY test change `R → R'`.

The base-side argument is untouched by the widening — the pushed cover `algebraMap R R' ∘ g`
spans `⊤` and the certified part over each `Localization.Away (algebraMap R R' (g i))` is
`mapAlg` of the local family — because R2 widens where the pieces live on the CURVE and changes
nothing about the Zariski cover of the BASE.  Compare
`IsLocallyCertified.pullback` (`DivisorFamilyZarMapAlg.lean`): the proof is the same, with the
cover datum appearing only inside the opaque `mapAlg`. -/
theorem IsLocallyCertifiedAff.pullback {d : (relCurve C R).LocalEquations}
    (hloc : IsLocallyCertifiedAff n d) (hreg) :
    IsLocallyCertifiedAff (C := C) (R := R') n
      (d.pullback (relCurveMap C R R') hreg) := by
  classical
  obtain ⟨m, g, hg, hG⟩ := hloc
  have hloc' : IsLocallyCertifiedAff (C := C) (R := R) n d := ⟨m, g, hg, hG⟩
  refine ⟨m, fun i => algebraMap R R' (g i), ?_, fun i => ?_⟩
  · have hrange : (Set.range fun i : Fin m => algebraMap R R' (g i))
        = algebraMap R R' '' Set.range g := by
      ext x
      exact ⟨by rintro ⟨i, rfl⟩; exact ⟨g i, ⟨i, rfl⟩, rfl⟩,
        by rintro ⟨-, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩⟩
    rw [hrange, ← Ideal.map_span, hg, Ideal.map_top]
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
  have hW := G.divEq_mapAlg_pullback n (Localization.Away (algebraMap R R' (g i)))
    (G.cover.hasAffineOverlaps_of_isProper)
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
  exact ⟨G.mapAlg (Localization.Away (algebraMap R R' (g i))) n
    (G.cover.hasAffineOverlaps_of_isProper), hW.trans hstep.symm⟩

/-! ## The widened divisor-functor map -/

/-- **The widened divisor-functor map on locally certified classes** along an ARBITRARY test
change: pull back the representative (the widened mapAlg-hreg engine discharges regularity) and
transport the certificates.  Well defined by `divEq_pullback`.

With this, `DivFamZarAff` is a functor value: the field-uniform carrier of R2 base-changes
exactly as the chart-typed one did. -/
noncomputable def DivFamZarAff.mapAlg :
    DivFamZarAff C R n → DivFamZarAff C R' n :=
  Quotient.lift
    (fun dp : {d : (relCurve C R).LocalEquations // IsLocallyCertifiedAff n d} =>
      DivFamZarAff.mk (dp.1.pullback (relCurveMap C R R')
          (dp.2.germ_pullbackEqn_mem_nonZeroDivisors R' n))
        (dp.2.pullback R' n _))
    (fun _ _ h => DivFamZarAff.mk_eq_mk_iff.mpr
      (Scheme.LocalEquations.divEq_pullback (relCurveMap C R R') h _ _))

@[simp]
lemma DivFamZarAff.mapAlg_mk (d : (relCurve C R).LocalEquations)
    (hd : IsLocallyCertifiedAff n d) :
    DivFamZarAff.mapAlg R' n (DivFamZarAff.mk d hd)
      = DivFamZarAff.mk (d.pullback (relCurveMap C R R')
          (hd.germ_pullbackEqn_mem_nonZeroDivisors R' n))
        (hd.pullback R' n _) :=
  rfl

/-- **The Abel-hook class law at the widened Zar level**: the divisor-functor map intertwines
the Picard classes with the Čech-Picard pullback, `𝒪(f*D) = f*𝒪(D)`.  Identical to the
chart-typed `DivFamZar.picClass_mapAlg` — the class never saw the cover. -/
lemma DivFamZarAff.picClass_mapAlg (F : DivFamZarAff C R n) :
    (DivFamZarAff.mapAlg R' n F).picClass =
      Scheme.CechPic.map (relCurveMap C R R') F.picClass := by
  induction F using Quotient.inductionOn with
  | h d => exact Scheme.LocalEquations.picClass_pullback (relCurveMap C R R') d.1 _

/-- **The identity functor law** at the widened Zar level. -/
lemma DivFamZarAff.mapAlg_id (F : DivFamZarAff C R n) :
    DivFamZarAff.mapAlg R n F = F := by
  induction F using Quotient.inductionOn with
  | h d =>
      exact DivFamZarAff.mk_eq_mk_iff.mpr
        (Scheme.LocalEquations.divEq_pullback_id relCurveMap_id d.1 _)

end Transport

section Comp

variable [IsProper C.hom]
variable (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
variable [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R'']

/-- **The composition functor law** at the widened Zar level, over a tower `R → R' → R''`. -/
lemma DivFamZarAff.mapAlg_comp (F : DivFamZarAff C R n) :
    DivFamZarAff.mapAlg R'' n (DivFamZarAff.mapAlg R' n F)
      = DivFamZarAff.mapAlg R'' n F := by
  induction F using Quotient.inductionOn with
  | h d =>
      exact DivFamZarAff.mk_eq_mk_iff.mpr
        (Scheme.LocalEquations.divEq_pullback_pullback
          (relCurveMap_comp (R' := R') (R'' := R'')) d.1 _ _ _)

end Comp

/-! ## Zariski separation at the widened Zar level -/

/-- **Zariski separation of the widened divisor functor**: two widened classes agreeing under
`mapAlg` on every member of a finite covering family of localizations agree.

Certificates play no role in equality, so — exactly as for `DivFamZar.eq_of_away_eq` — this
reduces verbatim to the `DivEq`-level engine `divEq_of_divEq_pullback`, and the widening is
invisible.  Note this needs `[IsProper C.hom]` only because `mapAlg` does. -/
theorem DivFamZarAff.eq_of_away_eq [IsProper C.hom] {ι : Type u} [Finite ι] (g : ι → R)
    (S : ι → Type u)
    [∀ i, CommRing (S i)] [∀ i, Algebra k (S i)] [∀ i, Algebra R (S i)]
    [∀ i, IsScalarTower k R (S i)] [∀ i, IsLocalization.Away (g i) (S i)]
    (hg : Ideal.span (Set.range g) = ⊤) {F G : DivFamZarAff C R n}
    (h : ∀ i, DivFamZarAff.mapAlg (S i) n F = DivFamZarAff.mapAlg (S i) n G) :
    F = G := by
  haveI : ∀ i, IsOpenImmersion (relCurveMap C R (S i)) := fun i =>
    isOpenImmersion_relCurveMap_away C R (S i) (g i)
  revert h
  refine Quotient.inductionOn₂ F G fun d₁ d₂ h => ?_
  refine DivFamZarAff.mk_eq_mk_iff.mpr ?_
  refine Scheme.LocalEquations.divEq_of_divEq_pullback
    (fun i => relCurveMap C R (S i))
    (fun y => exists_relCurveMap_base_eq C R g S hg y)
    (fun i => d₁.2.germ_pullbackEqn_mem_nonZeroDivisors (S i) n)
    (fun i => d₂.2.germ_pullbackEqn_mem_nonZeroDivisors (S i) n)
    (fun i => ?_)
  exact DivFamZarAff.mk_eq_mk_iff.mp (h i)

/-! ## Obligation I-0492 4(i) read on the FIBRE CURVE

The widened assembler's fibrewise-regularity input (`hfib` of
`AffAdaptation.isCertified_of_swallowedBy`, `DivisorFamilyAffAssemble.lean`) is stated as a
tensor condition: `eqn j ⊗ 1` is a nonzerodivisor in `Γ(pieces j) ⊗[R] κ(p)`.  Protection
I-0492 clause 4(i) says that datum must come from the seed's own degree data, and a tensor
product is not the shape any geometric argument produces.

The section base change of this file's upstream turns it into the shape that IS produced:
`Γ(pieces j) ⊗[R] κ(p) ≅ Γ(relCurve C κ(p), relCurveMap ⁻¹ᵁ pieces j)`, so `hfib` at `p` says
exactly that the **pulled equation is regular on the fibre curve over `κ(p)`** — a statement
about a section of a sheaf on a curve over a field, checkable germ by germ.

This is a restatement, not a discharge: the obligation stays an obligation, as clause 4(i)
requires.  What changes is that it is now stated in the vocabulary the seed layer speaks.  -/

section Fibre

variable {n}

/-- **The fibrewise-regularity obligation, read on the fibre curve.**  `eqn j ⊗ 1` is a
nonzerodivisor in `Γ(pieces j) ⊗[R] κ(p)` **iff** the compared equation is a nonzerodivisor in
the sections of the fibre curve over `κ(p)` on the preimage of the piece.

Both directions are the same ring isomorphism, so this is an honest translation with no
hypothesis beyond affineness of the piece — which is a field of `AffCoverData`. -/
theorem AffAdaptation.eqn_tmul_one_mem_nonZeroDivisors_iff {D : AffCoverData C R}
    {d : (relCurve C R).LocalEquations} (A : AffAdaptation D d) (j : D.index)
    (p : PrimeSpectrum R) :
    (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
        Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
      nonZeroDivisors (Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField)
    ↔ relAffSectionsMap C p.asIdeal.ResidueField (D.pieces j) (A.eqn j) ∈
        nonZeroDivisors
          Γ(relCurve C p.asIdeal.ResidueField,
            relCurveMap C R p.asIdeal.ResidueField ⁻¹ᵁ D.pieces j) := by
  let e : Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField ≃+*
      Γ(relCurve C p.asIdeal.ResidueField,
        relCurveMap C R p.asIdeal.ResidueField ⁻¹ᵁ D.pieces j) :=
    (Algebra.TensorProduct.comm R Γ(relCurve C R, D.pieces j)
        p.asIdeal.ResidueField).toRingEquiv.trans
      (relSectionsBaseChangeAff C p.asIdeal.ResidueField (D.isAffineOpen j)).toRingEquiv
  have hval : e (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField))
      = relAffSectionsMap C p.asIdeal.ResidueField (D.pieces j) (A.eqn j) := by
    change (relSectionsBaseChangeAff C p.asIdeal.ResidueField (D.isAffineOpen j))
        (Algebra.TensorProduct.comm R Γ(relCurve C R, D.pieces j)
          p.asIdeal.ResidueField (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField))) = _
    rw [Algebra.TensorProduct.comm_tmul,
      relSectionsBaseChangeAff_one_tmul C p.asIdeal.ResidueField (D.isAffineOpen j)]
  refine ⟨fun h => hval ▸ map_mem_nonZeroDivisors' e h, fun h => ?_⟩
  have hback := map_mem_nonZeroDivisors' e.symm (hval ▸ h)
  rwa [e.symm_apply_apply] at hback

end Fibre

/-! ## `toAff` is a map of FUNCTORS, not just of values

`DivisorFamilyAffCompare.lean` gave `DivFamZar.toAff` on values.  With `mapAlg` in place the
comparison can be checked to be natural, which is what a consumer needs in order to move
between the two values at will: both sides pull back the SAME representative system, and the
two `mk`s are equal because the setoids are the same `DivEq` relation. -/

/-- **`toAff` commutes with base change.**  So a consumer may transport a chart-typed class and
then widen, or widen and then transport, and get the same widened class. -/
lemma DivFamZar.toAff_mapAlg [IsProper C.hom] {π : C.left ⟶ P1 k} [IsAffineHom π]
    (F : DivFamZar C R π n) :
    (DivFamZar.mapAlg R' n F).toAff = DivFamZarAff.mapAlg R' n F.toAff := by
  induction F using Quotient.inductionOn with
  | h d => exact DivFamZarAff.mk_eq_mk_iff.mpr (Scheme.LocalEquations.divEq_refl _)

end AlgebraicGeometry
