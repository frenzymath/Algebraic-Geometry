/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFace
import AlgebraicJacobian.Picard.DivisorFamilyZarGlueKit

/-!
# The Zariski divisor assembly, freed of the certificate carrier (R2 keystone kit)

The S5 divisor assembly of `DivisorFamilyZariskiGlue.lean` — `awayGluedEquations` and its
chart restriction — is stated at `CertifiedDivisorFamily`, the CHART-TYPED certified family.
Its proof never touches the certificate: it consumes `(E i).eqns` and nothing else.  So the
statement is stronger than the proof needs, and that mismatch is exactly what blocks the R2
port: a widened class over `S i` has no chart-typed certificate at all (that failure IS the
content of R2), so the chart-typed assembly cannot be instantiated at widened input, however
carrier-free its proof happens to be.

This file removes the mismatch by restating the assembly at bare local-equation systems
`E : ∀ i, (relCurve C (S i)).LocalEquations`, with the pullback regularity that the certificate
used to supply carried as an explicit hypothesis (`Scheme.LocalEquations.PullRegular`).  Nothing
in the mathematics changes — the pointwise cross unit still goes through the overlap curve, the
glued system is still the immersion transport of the chosen chart's equation, and the chart
restriction is still the immersion round trip.  What changes is that the input is now the datum
the widened carrier actually has.

## The evidence for the claim above, since it is the whole reason this file exists

Measured over the entire body of `awayGluedEquations`: the only projections of its input `E`
that occur are `.eqns` (eight times) and `.cover` — which is `eqns.cover` — seven.  `.adaptation`
and `.certified` never appear, the result is a bare `(relCurve C R).LocalEquations`, and `π`
occurs zero times.  Its declared input is nonetheless
`E : ∀ i, CertifiedDivisorFamily C (S i) π n`.  The same holds of the certified-input core
`DivFamZar.exists_glue_of_certified_away_compat`, whose signature names no cover or adaptation
type and whose only two occurrences of "chart" are comments about the *base* localization
restriction.

## Main declarations — WHAT THIS FILE ACTUALLY CONTAINS

* `Scheme.LocalEquations.PullRegular` — the `hreg` side-condition of
  `Scheme.LocalEquations.pullback`, named so a *family* of them can be quantified over.  The
  naming is necessary rather than cosmetic: the overlap compatibility below has to quantify over
  one `hreg` per index, and the anonymous `∀ y z hz, …` spelling cannot be so quantified.
  `pullback` does not depend on *which* proof is supplied (`regular` is a `Prop`), so naming the
  predicate costs nothing.
* `Scheme.LocalEquations.pullRegular_of_isOpenImmersion` — the discharge in the case every away
  localization is in.
* `AwayCompatPullDivEq` — overlap compatibility at bare systems: over each overlap carrier the two
  pulled systems are divisor-equal.  The regularity witnesses are **existentially** bound; see the
  declaration's docstring for why the `∀` spelling would be a vacuous obligation.
* `germ_awayTransportLoc_mem_nonZeroDivisors` — germ regularity of the immersion transport of a
  chart equation.
* `exists_res_awayTransportLoc_eq_unit_mul` — the pointwise cross unit, through the overlap curve.
* `awayGluedEquationsLoc` — **the glued system** at bare input.
* `divEq_pullback_awayGluedEquationsLoc` — **chart restriction**: the pullback of the glue along
  `relCurveMap C R (S i)` is divisor-equal to the `i`-th system.
* `CertifiedDivisorFamilyAff.isLocallyCertifiedAff`, `CertifiedDivisorFamilyAff.toZarAff` — a
  widened global certificate is a widened local one, so a widened certified family names a class.
* `DivFamZarAff.exists_glue_of_certified_away_compat` — **the widened certified-input gluing
  core**: compatible WIDENED certified families over a finite away cover of `R` glue to a widened
  locally certified class restricting to them.

The pinned widened keystone `DivFamZarAff.exists_glue_of_away_compat` is
`AlgebraicJacobian.Picard.DivisorFamilyAffGlueZar`.
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

/-- Restriction of a section along `W ≤ V ≤ U` composes to restriction along `W ≤ U`. -/
private lemma res_res {X : Scheme.{u}} {W V U : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s)
      = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- `appLE` at (propositionally) equal morphisms (the inclusion witness is proof-irrelevant). -/
private lemma appLE_hom_congr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f')
    {U : Y.Opens} {W : X.Opens} (e : W ≤ f ⁻¹ᵁ U) :
    f.appLE U W e = f'.appLE U W (h ▸ e) := by
  subst h; rfl

/-! ## The pullback regularity side-condition, named -/

namespace Scheme.LocalEquations

/-- **The `hreg` side-condition of `Scheme.LocalEquations.pullback`**, named.

Naming it is what makes the widened overlap compatibility *statable at all*: that hypothesis
must quantify over one `hreg` per index of the away cover, and the anonymous `∀ y z hz, …`
spelling cannot be so quantified.  `pullback` does not depend on WHICH proof is supplied (the
`regular` field is a `Prop`), so introducing the abbreviation costs nothing and changes no
existing statement.

The compatibility that consumes it is `AwayCompatPullDivEq` below. -/
def PullRegular {X Y : Scheme.{u}} (f : Y ⟶ X) (d : X.LocalEquations) : Prop :=
  ∀ (y z : Y) (hz : z ∈ (d.cover.pullback f).opens y),
    (Y.presheaf.germ ((d.cover.pullback f).opens y) z hz).hom (pullbackEqn f d y)
      ∈ nonZeroDivisors (Y.presheaf.stalk z)

/-- Along an open immersion the side-condition is free (the Kit's stalk-isomorphism
discharge). -/
theorem pullRegular_of_isOpenImmersion {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (d : X.LocalEquations) : PullRegular f d :=
  germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion f d

end Scheme.LocalEquations

/-! ## The glued system at bare input -/

section Glued

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))} {R : Type u} [CommRing R] [Algebra k R]
variable {ι : Type u} (g : ι → R) (S : ι → Type u) [∀ i, CommRing (S i)]
  [∀ i, Algebra k (S i)] [∀ i, Algebra R (S i)] [∀ i, IsScalarTower k R (S i)]
  [∀ i, IsLocalization.Away (g i) (S i)]
variable [∀ i, IsOpenImmersion (relCurveMap C R (S i))]
variable (E : ∀ i, (relCurve C (S i)).LocalEquations)

/-- Germ regularity of the immersion transport of a chart equation, at bare input: the germs of
the transported equation are nonzerodivisors at every point of the image member.  Verbatim
`germ_awayTransport_mem_nonZeroDivisors` with `(E i).eqns` replaced by `E i` — its proof only ever
read the `regular` field. -/
lemma germ_awayTransportLoc_mem_nonZeroDivisors (i : ι) (x' : relCurve C (S i))
    (z : relCurve C R) (hz : z ∈ relCurveMap C R (S i) ''ᵁ (E i).cover.opens x') :
    ((relCurve C R).presheaf.germ
        (relCurveMap C R (S i) ''ᵁ (E i).cover.opens x') z hz).hom
        (((relCurveMap C R (S i)).appIso ((E i).cover.opens x')).inv.hom ((E i).eqn x'))
      ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk z) :=
  Scheme.Hom.germ_appIso_inv_mem_nonZeroDivisors (relCurveMap C R (S i))
    (fun z' hz' => (E i).regular x' z' hz') z hz

section Overlap

variable (T : ι → ι → Type u) [∀ i j, CommRing (T i j)] [∀ i j, Algebra k (T i j)]
  [∀ i j, Algebra R (T i j)] [∀ i j, IsScalarTower k R (T i j)]
  [∀ i j, Algebra (S i) (T i j)] [∀ i j, Algebra (S j) (T i j)]
  [∀ i j, IsScalarTower k (S i) (T i j)] [∀ i j, IsScalarTower k (S j) (T i j)]
  [∀ i j, IsScalarTower R (S i) (T i j)] [∀ i j, IsScalarTower R (S j) (T i j)]
  [∀ i j, IsLocalization.Away (g i * g j) (T i j)]

/-- **The representative-level overlap compatibility at bare systems**: over each overlap carrier
`T i j` the two pulled systems are divisor-equal.  The chart-typed `AwayCompatDivEq` spells the
pulled systems as `adaptation.pulledEquations`, i.e. as `pullback` at the regularity the
CERTIFICATE supplies; a bare system carries no certificate, so the regularity witnesses travel
with the hypothesis.

They are **existentially** bound.  A predecessor draft of this docstring justified that by
claiming the `∀ hi hj, DivEq …` spelling "would be vacuous the moment one of the two
`PullRegular`s happened to be uninhabited".  **That justification is false and was refuted by
elaboration** (reviewer pass, run 0070 s0010; inbox `I-0643`).  The two spellings are equivalent
wherever this file is instantiated:

* `∃ ⟹ ∀` holds unconditionally, because `regular` is a `Prop` field and so
  `d.pullback f h₁ = d.pullback f h₂` by `rfl`;
* `∀ ⟹ ∃` holds whenever both legs are open immersions, by
  `pullRegular_of_isOpenImmersion` above — and every instantiation in this tree puts the overlap
  carrier at an away localization, where both legs *are* open immersions
  (`isOpenImmersion_relCurveMap_away`).

So the vacuity scenario cannot arise here, and a vacuity argument of that shape is
**carrier-relative**: it must be checked where the side condition is actually instantiated, not
in the abstract (inbox `I-0644`).

The real reasons to keep the `∃` form, which are the ones to quote: the *producer* has the
certificate's own regularity witnesses in hand and should not have to prove the general
statement, and the *caller* need not know its legs are immersions in order to state the
hypothesis.  It is also the stronger form, so nothing is lost. -/
def AwayCompatPullDivEq : Prop :=
  ∀ i j, ∃ (hi : Scheme.LocalEquations.PullRegular (relCurveMap C (S i) (T i j)) (E i))
    (hj : Scheme.LocalEquations.PullRegular (relCurveMap C (S j) (T i j)) (E j)),
    Scheme.LocalEquations.DivEq
      ((E i).pullback (relCurveMap C (S i) (T i j)) hi)
      ((E j).pullback (relCurveMap C (S j) (T i j)) hj)

include g in
/-- **The pointwise cross unit at bare systems** (`informal/spec-dd-2.md` §5): near any point `z`
of an open `O` inside the overlap of two transported members — from charts `i` and `j` at points
`x'`, `y'` — the two transported equations differ by a unit.

Route, unchanged from `exists_res_awayTransport_eq_unit_mul`: `z` lifts to the overlap curve
`C_{T i j}` (the pairwise point lift); upstairs the compatibility `DivEq` provides a unit between
the two pulled equations at the lift, conjugated into the transported equations by the transition
units of the two systems; the open immersion `relCurveMap C R (T i j)` descends the relation.  No
step reads a certificate, which is why bare systems suffice. -/
theorem exists_res_awayTransportLoc_eq_unit_mul (hcompat : AwayCompatPullDivEq S E T)
    {i j : ι} {x' : relCurve C (S i)} {y' : relCurve C (S j)}
    {O : (relCurve C R).Opens}
    (hOx : O ≤ relCurveMap C R (S i) ''ᵁ (E i).cover.opens x')
    (hOy : O ≤ relCurveMap C R (S j) ''ᵁ (E j).cover.opens y')
    (z : relCurve C R) (hz : z ∈ O) :
    ∃ (W : (relCurve C R).Opens) (hWO : W ≤ O) (_ : z ∈ W) (u : Γ(relCurve C R, W)ˣ),
      ((relCurve C R).presheaf.map (homOfLE (hWO.trans hOx)).op).hom
          (((relCurveMap C R (S i)).appIso ((E i).cover.opens x')).inv.hom ((E i).eqn x'))
        = (u : Γ(relCurve C R, W))
          * ((relCurve C R).presheaf.map (homOfLE (hWO.trans hOy)).op).hom
            (((relCurveMap C R (S j)).appIso ((E j).cover.opens y')).inv.hom
              ((E j).eqn y')) := by
  classical
  haveI hOIT : IsOpenImmersion (relCurveMap C R (T i j)) :=
    isOpenImmersion_relCurveMap_away C R (T i j) (g i * g j)
  -- the preimages of `z` on the two charts
  obtain ⟨zi, hziV, hziz⟩ := hOx hz
  obtain ⟨zj, hzjV, hzjz⟩ := hOy hz
  -- the lift of `z` to the overlap curve
  obtain ⟨w, hw⟩ := exists_relCurveMap_base_eq_pair C R (g i) (g j) (S i) (S j) (T i j)
    hziz hzjz
  -- the comparison triangle through the overlap curve
  have hcompi : relCurveMap C (S i) (T i j) ≫ relCurveMap C R (S i)
      = relCurveMap C R (T i j) := relCurveMap_comp (R' := S i) (R'' := T i j)
  have hcompj : relCurveMap C (S j) (T i j) ≫ relCurveMap C R (S j)
      = relCurveMap C R (T i j) := relCurveMap_comp (R' := S j) (R'' := T i j)
  -- the base points of the lift on the two charts, inside the two members
  have hxwz : (relCurveMap C R (S i)).base
      ((relCurveMap C (S i) (T i j)).base w) = z := by
    rw [← Scheme.Hom.comp_apply, hcompi, hw]
  have hywz : (relCurveMap C R (S j)).base
      ((relCurveMap C (S j) (T i j)).base w) = z := by
    rw [← Scheme.Hom.comp_apply, hcompj, hw]
  have hxwV : (relCurveMap C (S i) (T i j)).base w ∈ (E i).cover.opens x' := by
    have hmem := hOx hz
    rw [← hxwz] at hmem
    exact (Scheme.Hom.apply_mem_image_iff (relCurveMap C R (S i))).mp hmem
  have hywV : (relCurveMap C (S j) (T i j)).base w ∈ (E j).cover.opens y' := by
    have hmem := hOy hz
    rw [← hywz] at hmem
    exact (Scheme.Hom.apply_mem_image_iff (relCurveMap C R (S j))).mp hmem
  -- the compatibility unit at the lift
  obtain ⟨hregi, hregj, 𝒲, h₁, h₂, H⟩ := hcompat i j
  obtain ⟨v, hv⟩ := H w
  -- the upstairs working open
  set Vi := (E i).cover.opens x'
    ⊓ (E i).cover.opens ((relCurveMap C (S i) (T i j)).base w) with hVi
  set Vj := (E j).cover.opens y'
    ⊓ (E j).cover.opens ((relCurveMap C (S j) (T i j)).base w) with hVj
  set V'' := 𝒲.opens w ⊓ relCurveMap C (S i) (T i j) ⁻¹ᵁ Vi
    ⊓ relCurveMap C (S j) (T i j) ⁻¹ᵁ Vj
    ⊓ relCurveMap C R (T i j) ⁻¹ᵁ O with hV''
  have hwV'' : w ∈ V'' := by
    refine ⟨⟨⟨𝒲.mem_opens w, ⟨hxwV, (E i).cover.mem_opens _⟩⟩,
      ⟨hywV, (E j).cover.mem_opens _⟩⟩, ?_⟩
    change (relCurveMap C R (T i j)).base w ∈ O
    rw [hw]
    exact hz
  -- projections out of the working open
  have hle𝒲 : V'' ≤ 𝒲.opens w :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hlei : V'' ≤ relCurveMap C (S i) (T i j) ⁻¹ᵁ Vi :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hlej : V'' ≤ relCurveMap C (S j) (T i j) ⁻¹ᵁ Vj :=
    inf_le_left.trans inf_le_right
  have hleO : V'' ≤ relCurveMap C R (T i j) ⁻¹ᵁ O := inf_le_right
  have eV₁ : V'' ≤ relCurveMap C R (T i j) ⁻¹ᵁ
      (relCurveMap C R (S i) ''ᵁ (E i).cover.opens x') :=
    hleO.trans ((relCurveMap C R (T i j)).preimage_mono hOx)
  have eV₂ : V'' ≤ relCurveMap C R (T i j) ⁻¹ᵁ
      (relCurveMap C R (S j) ''ᵁ (E j).cover.opens y') :=
    hleO.trans ((relCurveMap C R (T i j)).preimage_mono hOy)
  -- the `i`-side collapse: the pulled transported equation is the pulled ratio unit times the
  -- pullback of the chart equation at the lift's anchor
  have hi : ((relCurveMap C R (T i j)).appLE
        (relCurveMap C R (S i) ''ᵁ (E i).cover.opens x') V'' eV₁).hom
        (((relCurveMap C R (S i)).appIso ((E i).cover.opens x')).inv.hom ((E i).eqn x'))
      = (((relCurveMap C (S i) (T i j)).unitsAppLE Vi V'' hlei
            ((E i).ratioUnit x' ((relCurveMap C (S i) (T i j)).base w)))
          : Γ(relCurve C (T i j), V''))
        * ((relCurveMap C (S i) (T i j)).appLE
            ((E i).cover.opens ((relCurveMap C (S i) (T i j)).base w)) V''
            (hlei.trans (Scheme.Hom.preimage_mono _ inf_le_right))).hom
          ((E i).eqn ((relCurveMap C (S i) (T i j)).base w)) := by
    have hmid : Vi ≤ relCurveMap C R (S i) ⁻¹ᵁ
        (relCurveMap C R (S i) ''ᵁ (E i).cover.opens x') :=
      inf_le_left.trans ((relCurveMap C R (S i)).preimage_image_eq _).ge
    have hsplit := Scheme.Hom.appLE_comp_appLE
      (relCurveMap C (S i) (T i j)) (relCurveMap C R (S i))
      (relCurveMap C R (S i) ''ᵁ (E i).cover.opens x') Vi V'' hmid hlei
    have hcongr := appLE_hom_congr hcompi
      (U := relCurveMap C R (S i) ''ᵁ (E i).cover.opens x') (W := V'')
      (hlei.trans ((relCurveMap C (S i) (T i j)).preimage_mono hmid))
    have h0 : ((relCurveMap C R (T i j)).appLE
        (relCurveMap C R (S i) ''ᵁ (E i).cover.opens x') V'' eV₁).hom
        (((relCurveMap C R (S i)).appIso ((E i).cover.opens x')).inv.hom ((E i).eqn x'))
        = ((relCurveMap C (S i) (T i j)).appLE Vi V'' hlei).hom
          (((relCurveMap C R (S i)).appLE
              (relCurveMap C R (S i) ''ᵁ (E i).cover.opens x') Vi hmid).hom
            (((relCurveMap C R (S i)).appIso ((E i).cover.opens x')).inv.hom
              ((E i).eqn x'))) := by
      rw [← hcongr, ← hsplit, CommRingCat.comp_apply]
    rw [h0, Scheme.Hom.appIso_inv_appLE_apply]
    -- the transition unit between the two chart anchors
    have hratio := congrArg ((relCurveMap C (S i) (T i j)).appLE Vi V'' hlei).hom
      ((E i).eqn_restrict_eq x' ((relCurveMap C (S i) (T i j)).base w))
    rw [map_mul] at hratio
    rw [show ((relCurve C (S i)).presheaf.map (homOfLE (by
        rwa [(relCurveMap C R (S i)).preimage_image_eq] at hmid)).op).hom ((E i).eqn x')
        = ((relCurve C (S i)).presheaf.map (homOfLE (inf_le_left : Vi ≤ _)).op).hom
          ((E i).eqn x') from rfl, hratio]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  -- the `j`-side collapse
  have hj : ((relCurveMap C R (T i j)).appLE
        (relCurveMap C R (S j) ''ᵁ (E j).cover.opens y') V'' eV₂).hom
        (((relCurveMap C R (S j)).appIso ((E j).cover.opens y')).inv.hom ((E j).eqn y'))
      = (((relCurveMap C (S j) (T i j)).unitsAppLE Vj V'' hlej
            ((E j).ratioUnit y' ((relCurveMap C (S j) (T i j)).base w)))
          : Γ(relCurve C (T i j), V''))
        * ((relCurveMap C (S j) (T i j)).appLE
            ((E j).cover.opens ((relCurveMap C (S j) (T i j)).base w)) V''
            (hlej.trans (Scheme.Hom.preimage_mono _ inf_le_right))).hom
          ((E j).eqn ((relCurveMap C (S j) (T i j)).base w)) := by
    have hmid : Vj ≤ relCurveMap C R (S j) ⁻¹ᵁ
        (relCurveMap C R (S j) ''ᵁ (E j).cover.opens y') :=
      inf_le_left.trans ((relCurveMap C R (S j)).preimage_image_eq _).ge
    have hsplit := Scheme.Hom.appLE_comp_appLE
      (relCurveMap C (S j) (T i j)) (relCurveMap C R (S j))
      (relCurveMap C R (S j) ''ᵁ (E j).cover.opens y') Vj V'' hmid hlej
    have hcongr := appLE_hom_congr hcompj
      (U := relCurveMap C R (S j) ''ᵁ (E j).cover.opens y') (W := V'')
      (hlej.trans ((relCurveMap C (S j) (T i j)).preimage_mono hmid))
    have h0 : ((relCurveMap C R (T i j)).appLE
        (relCurveMap C R (S j) ''ᵁ (E j).cover.opens y') V'' eV₂).hom
        (((relCurveMap C R (S j)).appIso ((E j).cover.opens y')).inv.hom ((E j).eqn y'))
        = ((relCurveMap C (S j) (T i j)).appLE Vj V'' hlej).hom
          (((relCurveMap C R (S j)).appLE
              (relCurveMap C R (S j) ''ᵁ (E j).cover.opens y') Vj hmid).hom
            (((relCurveMap C R (S j)).appIso ((E j).cover.opens y')).inv.hom
              ((E j).eqn y'))) := by
      rw [← hcongr, ← hsplit, CommRingCat.comp_apply]
    rw [h0, Scheme.Hom.appIso_inv_appLE_apply]
    have hratio := congrArg ((relCurveMap C (S j) (T i j)).appLE Vj V'' hlej).hom
      ((E j).eqn_restrict_eq y' ((relCurveMap C (S j) (T i j)).base w))
    rw [map_mul] at hratio
    rw [show ((relCurve C (S j)).presheaf.map (homOfLE (by
        rwa [(relCurveMap C R (S j)).preimage_image_eq] at hmid)).op).hom ((E j).eqn y')
        = ((relCurve C (S j)).presheaf.map (homOfLE (inf_le_left : Vj ≤ _)).op).hom
          ((E j).eqn y') from rfl, hratio]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  -- the compatibility relation, restricted and respelled on the `appLE`-forms
  have hv' := congrArg ((relCurve C (T i j)).presheaf.map (homOfLE hle𝒲).op).hom hv
  rw [map_mul, res_res, res_res] at hv'
  have hres_i := Scheme.LocalEquations.pullbackEqn_res (relCurveMap C (S i) (T i j))
    (E i) w (h := show V'' ≤ ((E i).cover.pullback
      (relCurveMap C (S i) (T i j))).opens w from
      hlei.trans (Scheme.Hom.preimage_mono _ inf_le_right))
  have hres_j := Scheme.LocalEquations.pullbackEqn_res (relCurveMap C (S j) (T i j))
    (E j) w (h := show V'' ≤ ((E j).cover.pullback
      (relCurveMap C (S j) (T i j))).opens w from
      hlej.trans (Scheme.Hom.preimage_mono _ inf_le_right))
  have hv'' : ((relCurve C (T i j)).presheaf.map (homOfLE (show V'' ≤
      ((E i).cover.pullback (relCurveMap C (S i) (T i j))).opens w from
      hlei.trans (Scheme.Hom.preimage_mono _ inf_le_right))).op).hom
      (Scheme.LocalEquations.pullbackEqn (relCurveMap C (S i) (T i j)) (E i) w)
      = ((relCurve C (T i j)).presheaf.map (homOfLE hle𝒲).op).hom
          (v : Γ(relCurve C (T i j), 𝒲.opens w))
        * ((relCurve C (T i j)).presheaf.map (homOfLE (show V'' ≤
            ((E j).cover.pullback (relCurveMap C (S j) (T i j))).opens w from
            hlej.trans (Scheme.Hom.preimage_mono _ inf_le_right))).op).hom
          (Scheme.LocalEquations.pullbackEqn (relCurveMap C (S j) (T i j)) (E j) w) := hv'
  -- the key relation on the `appLE`-forms
  have hkey : ((relCurveMap C (S i) (T i j)).appLE
        ((E i).cover.opens ((relCurveMap C (S i) (T i j)).base w)) V''
        (hlei.trans (Scheme.Hom.preimage_mono _ inf_le_right))).hom
        ((E i).eqn ((relCurveMap C (S i) (T i j)).base w))
      = ((relCurve C (T i j)).presheaf.map (homOfLE hle𝒲).op).hom
          (v : Γ(relCurve C (T i j), 𝒲.opens w))
        * ((relCurveMap C (S j) (T i j)).appLE
            ((E j).cover.opens ((relCurveMap C (S j) (T i j)).base w)) V''
            (hlej.trans (Scheme.Hom.preimage_mono _ inf_le_right))).hom
          ((E j).eqn ((relCurveMap C (S j) (T i j)).base w)) := by
    rw [← hres_i, ← hres_j]
    exact hv''
  -- the `j`-side relation inverted, and the unit relation assembled upstairs
  have hjinv : ((relCurveMap C (S j) (T i j)).appLE
        ((E j).cover.opens ((relCurveMap C (S j) (T i j)).base w)) V''
        (hlej.trans (Scheme.Hom.preimage_mono _ inf_le_right))).hom
        ((E j).eqn ((relCurveMap C (S j) (T i j)).base w))
      = ((((relCurveMap C (S j) (T i j)).unitsAppLE Vj V'' hlej
            ((E j).ratioUnit y' ((relCurveMap C (S j) (T i j)).base w)))⁻¹ :
          Γ(relCurve C (T i j), V'')ˣ) : Γ(relCurve C (T i j), V''))
        * ((relCurveMap C R (T i j)).appLE
            (relCurveMap C R (S j) ''ᵁ (E j).cover.opens y') V'' eV₂).hom
          (((relCurveMap C R (S j)).appIso ((E j).cover.opens y')).inv.hom
            ((E j).eqn y')) := by
    rw [hj, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hrel : ((relCurveMap C R (T i j)).appLE
        (relCurveMap C R (S i) ''ᵁ (E i).cover.opens x') V'' eV₁).hom
        (((relCurveMap C R (S i)).appIso ((E i).cover.opens x')).inv.hom ((E i).eqn x'))
      = ((((relCurveMap C (S i) (T i j)).unitsAppLE Vi V'' hlei
              ((E i).ratioUnit x' ((relCurveMap C (S i) (T i j)).base w)))
            * (relCurve C (T i j)).unitsRestrict hle𝒲 v
            * ((relCurveMap C (S j) (T i j)).unitsAppLE Vj V'' hlej
                ((E j).ratioUnit y' ((relCurveMap C (S j) (T i j)).base w)))⁻¹ :
          Γ(relCurve C (T i j), V'')ˣ) : Γ(relCurve C (T i j), V''))
        * ((relCurveMap C R (T i j)).appLE
            (relCurveMap C R (S j) ''ᵁ (E j).cover.opens y') V'' eV₂).hom
          (((relCurveMap C R (S j)).appIso ((E j).cover.opens y')).inv.hom
            ((E j).eqn y')) := by
    rw [hi, hkey, hjinv, Units.val_mul, Units.val_mul, mul_assoc, mul_assoc]
    rfl
  -- descend along the overlap immersion and land inside `O`
  have hWO : relCurveMap C R (T i j) ''ᵁ V'' ≤ O :=
    ((relCurveMap C R (T i j)).image_mono hleO).trans
      ((relCurveMap C R (T i j)).image_preimage_le O)
  obtain ⟨u, hu⟩ := Scheme.Hom.exists_unit_res_of_appLE_eq_unit_mul
    (relCurveMap C R (T i j))
    (((relCurveMap C R (S i)).appIso ((E i).cover.opens x')).inv.hom ((E i).eqn x'))
    (((relCurveMap C R (S j)).appIso ((E j).cover.opens y')).inv.hom ((E j).eqn y'))
    eV₁ eV₂ (hWO.trans hOx) (hWO.trans hOy) _ hrel
  exact ⟨relCurveMap C R (T i j) ''ᵁ V'', hWO,
    Scheme.Hom.mem_image_of_base_eq _ hw hwV'', u, hu⟩

/-- **The glued local-equation system at bare input** (`informal/spec-dd-2.md` §5, the divisor
assembly): at a point `y` of the glued relative curve the member is the image of the chosen
chart's covering member under the open immersion `relCurveMap C R (S _)` and the equation is the
immersion transport of the chart equation.  Regularity transports along the immersion; the overlap
ratios are units by the pointwise cross units upgraded to the full member overlaps by the Kit's
unit-spreading engine.

Verbatim `awayGluedEquations` with the certified-family input replaced by the bare systems it
actually consumed — which is what lets the WIDENED carrier feed the same assembly. -/
noncomputable def awayGluedEquationsLoc (hg : Ideal.span (Set.range g) = ⊤)
    (hcompat : AwayCompatPullDivEq S E T) : (relCurve C R).LocalEquations where
  cover :=
    { opens := fun y => relCurveMap C R (S (awayGlueIndex g S hg y)) ''ᵁ
        (E (awayGlueIndex g S hg y)).cover.opens (awayGlueLift g S hg y)
      mem_opens := fun y => Scheme.Hom.mem_image_of_base_eq _
        (relCurveMap_base_awayGlueLift g S hg y)
        ((E (awayGlueIndex g S hg y)).cover.mem_opens (awayGlueLift g S hg y)) }
  eqn y := ((relCurveMap C R (S (awayGlueIndex g S hg y))).appIso
      ((E (awayGlueIndex g S hg y)).cover.opens (awayGlueLift g S hg y))).inv.hom
    ((E (awayGlueIndex g S hg y)).eqn (awayGlueLift g S hg y))
  regular y z hz := germ_awayTransportLoc_mem_nonZeroDivisors S E _ _ z hz
  ratio_isUnit x y := by
    refine Scheme.exists_unit_mul_of_locally_unit_mul ?_ ?_
    · -- germ regularity of the restricted transport of the second equation
      intro z hz
      rw [(relCurve C R).presheaf.germ_res_apply]
      exact germ_awayTransportLoc_mem_nonZeroDivisors S E _ _ z hz.2
    · -- the pointwise cross units on the member overlap
      intro z hz
      obtain ⟨W, hWO, hzW, u, hu⟩ := exists_res_awayTransportLoc_eq_unit_mul g S E T
        hcompat (inf_le_left :
          relCurveMap C R (S (awayGlueIndex g S hg x)) ''ᵁ
              (E (awayGlueIndex g S hg x)).cover.opens (awayGlueLift g S hg x)
            ⊓ relCurveMap C R (S (awayGlueIndex g S hg y)) ''ᵁ
              (E (awayGlueIndex g S hg y)).cover.opens (awayGlueLift g S hg y)
          ≤ _)
        (inf_le_right :
          relCurveMap C R (S (awayGlueIndex g S hg x)) ''ᵁ
              (E (awayGlueIndex g S hg x)).cover.opens (awayGlueLift g S hg x)
            ⊓ relCurveMap C R (S (awayGlueIndex g S hg y)) ''ᵁ
              (E (awayGlueIndex g S hg y)).cover.opens (awayGlueLift g S hg y)
          ≤ _) z hz
      refine ⟨W, hWO, hzW, u, ?_⟩
      rw [res_res, res_res]
      exact hu

/-- **Chart restriction of the glued system at bare input** (`informal/spec-dd-2.md` §5): the
pullback of `awayGluedEquationsLoc` along the open immersion `relCurveMap C R (S i)` is
divisor-equal to the `i`-th system.  Pointwise: on the overlap of the glued member with the image
of the chart member the transported equations differ by a unit (the cross unit spread by the Kit
engine), and the relation pulls back up the immersion, where the transported equation restricts
back to the chart equation (the immersion round trip). -/
theorem divEq_pullback_awayGluedEquationsLoc (hg : Ideal.span (Set.range g) = ⊤)
    (hcompat : AwayCompatPullDivEq S E T) (i : ι) (hreg) :
    Scheme.LocalEquations.DivEq
      ((awayGluedEquationsLoc g S E T hg hcompat).pullback (relCurveMap C R (S i)) hreg)
      (E i) := by
  classical
  refine ⟨((awayGluedEquationsLoc g S E T hg hcompat).cover.pullback
      (relCurveMap C R (S i))) ⊓ (E i).cover,
    fun z' => inf_le_left, fun z' => inf_le_right, fun z' => ?_⟩
  -- the downstairs overlap of the glued member with the image of the chart member
  obtain ⟨uO, huO⟩ := Scheme.exists_unit_mul_of_locally_unit_mul
    (X := relCurve C R)
    (V := (awayGluedEquationsLoc g S E T hg hcompat).cover.opens
        ((relCurveMap C R (S i)).base z')
      ⊓ relCurveMap C R (S i) ''ᵁ (E i).cover.opens z')
    (s := ((relCurve C R).presheaf.map (homOfLE inf_le_left).op).hom
      ((awayGluedEquationsLoc g S E T hg hcompat).eqn ((relCurveMap C R (S i)).base z')))
    (t := ((relCurve C R).presheaf.map (homOfLE inf_le_right).op).hom
      (((relCurveMap C R (S i)).appIso ((E i).cover.opens z')).inv.hom ((E i).eqn z')))
    (fun z hz => by
      rw [(relCurve C R).presheaf.germ_res_apply]
      exact germ_awayTransportLoc_mem_nonZeroDivisors S E i z' z hz.2)
    (fun z hz => by
      obtain ⟨W, hWO, hzW, u, hu⟩ := exists_res_awayTransportLoc_eq_unit_mul g S E T
        hcompat
        (inf_le_left :
          (awayGluedEquationsLoc g S E T hg hcompat).cover.opens
              ((relCurveMap C R (S i)).base z')
            ⊓ relCurveMap C R (S i) ''ᵁ (E i).cover.opens z' ≤ _)
        (inf_le_right :
          (awayGluedEquationsLoc g S E T hg hcompat).cover.opens
              ((relCurveMap C R (S i)).base z')
            ⊓ relCurveMap C R (S i) ''ᵁ (E i).cover.opens z' ≤ _)
        z hz
      refine ⟨W, hWO, hzW, u, ?_⟩
      rw [res_res, res_res]
      exact hu)
  -- pull the overlap unit up the immersion
  have hpre : ((awayGluedEquationsLoc g S E T hg hcompat).cover.pullback
        (relCurveMap C R (S i))).opens z' ⊓ (E i).cover.opens z'
      ≤ relCurveMap C R (S i) ⁻¹ᵁ
        ((awayGluedEquationsLoc g S E T hg hcompat).cover.opens
            ((relCurveMap C R (S i)).base z')
          ⊓ relCurveMap C R (S i) ''ᵁ (E i).cover.opens z') :=
    (relCurveMap C R (S i)).le_preimage_inf inf_le_left
      (inf_le_right.trans ((relCurveMap C R (S i)).preimage_image_eq _).ge)
  refine ⟨(relCurveMap C R (S i)).unitsAppLE _ _ hpre uO, ?_⟩
  -- transport the unit relation through `appLE`
  have hkey := congrArg ((relCurveMap C R (S i)).appLE _ _ hpre).hom huO
  rw [map_mul] at hkey
  -- the left factor: the restricted pulled equation
  have hL : ((relCurveMap C R (S i)).appLE _ _ hpre).hom
      (((relCurve C R).presheaf.map (homOfLE inf_le_left).op).hom
        ((awayGluedEquationsLoc g S E T hg hcompat).eqn
          ((relCurveMap C R (S i)).base z')))
      = ((relCurve C (S i)).presheaf.map (homOfLE (inf_le_left :
          ((awayGluedEquationsLoc g S E T hg hcompat).cover.pullback
              (relCurveMap C R (S i))).opens z' ⊓ (E i).cover.opens z' ≤ _)).op).hom
        (Scheme.LocalEquations.pullbackEqn (relCurveMap C R (S i))
          (awayGluedEquationsLoc g S E T hg hcompat) z') := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      Scheme.LocalEquations.pullbackEqn_res]
  -- the right factor: the immersion round trip back to the chart equation
  have hR : ((relCurveMap C R (S i)).appLE _ _ hpre).hom
      (((relCurve C R).presheaf.map (homOfLE inf_le_right).op).hom
        (((relCurveMap C R (S i)).appIso ((E i).cover.opens z')).inv.hom ((E i).eqn z')))
      = ((relCurve C (S i)).presheaf.map (homOfLE (inf_le_right :
          ((awayGluedEquationsLoc g S E T hg hcompat).cover.pullback
              (relCurveMap C R (S i))).opens z' ⊓ (E i).cover.opens z' ≤ _)).op).hom
        ((E i).eqn z') := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      Scheme.Hom.appIso_inv_appLE_apply]
  rw [hL, hR] at hkey
  exact hkey

end Overlap

end Glued

/-! ## The widened certified-input gluing core -/

section Core

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] {n : ℕ}

/-- **A widened global certificate is a widened local one** (the trivial cover `g = ![1]`) — the
missing widened counterpart of `CertifiedDivisorFamily.isLocallyCertified`.  The certified part
over `Localization.Away (1 : R)` is `mapAlg` of the family, whose equations ARE the pulled system
on the nose (`AffAdaptation.pulledEquations` IS `pullback` along the comparison; the regularity
proofs are proof-irrelevant), so the required `DivEq` is reflexivity.

Without this a widened certified family names no class in `DivFamZarAff`, and the gluing core
below could not say what its input restricts to. -/
theorem CertifiedDivisorFamilyAff.isLocallyCertifiedAff (F : CertifiedDivisorFamilyAff C R n) :
    IsLocallyCertifiedAff n F.eqns := by
  refine ⟨1, fun _ => (1 : R), ?_, fun i => ?_⟩
  · have hrange : Set.range (fun _ : Fin 1 => (1 : R)) = {1} := Set.range_const
    rw [hrange, Ideal.span_singleton_one]
  · haveI : IsOpenImmersion (relCurveMap C R (Localization.Away (1 : R))) :=
      isOpenImmersion_relCurveMap_away C R (Localization.Away (1 : R)) 1
    exact ⟨F.mapAlg (Localization.Away (1 : R)) n F.cover.hasAffineOverlaps_of_isProper,
      Scheme.LocalEquations.divEq_refl _⟩

/-- The class in `DivFamZarAff` named by a widened certified family. -/
noncomputable def CertifiedDivisorFamilyAff.toZarAff (F : CertifiedDivisorFamilyAff C R n) :
    DivFamZarAff C R n :=
  DivFamZarAff.mk F.eqns F.isLocallyCertifiedAff

/-- **The widened certified-input gluing core** (S5b at `DivFamZarAff`): a family of WIDENED
certified divisor families over a finite away cover of `R`, compatible on the overlap carriers,
glues to a widened LOCALLY certified class over `R` restricting to the given classes.

Verbatim the chart-typed `DivFamZar.exists_glue_of_certified_away_compat`, with the two
substitutions that are the whole content of the R2 port: the divisor assembly is
`awayGluedEquationsLoc` at the bare systems `(E q).eqns` rather than `awayGluedEquations` at
certified families, and local certifiability of the glue is witnessed by
`CertifiedDivisorFamilyAff.mapAlg`, whose extra `hinf` argument is free under `[IsProper C.hom]`
(`AffCoverData.hasAffineOverlaps_of_isProper`).

Nothing else changes, because the argument is entirely about the Zariski cover of the BASE: each
certified family transports along the identification of its carrier with `Localization.Away (r q)`
(`IsLocalization.algEquiv`) and stays divisor-equal to the pulled glue by witness transport at the
landed restriction law. -/
theorem DivFamZarAff.exists_glue_of_certified_away_compat
    {κ : Type u} [Finite κ] (r : κ → R) (S' : κ → Type u)
    [∀ q, CommRing (S' q)] [∀ q, Algebra k (S' q)] [∀ q, Algebra R (S' q)]
    [∀ q, IsScalarTower k R (S' q)] [∀ q, IsLocalization.Away (r q) (S' q)]
    (V : κ → κ → Type u) [∀ p q, CommRing (V p q)] [∀ p q, Algebra k (V p q)]
    [∀ p q, Algebra R (V p q)] [∀ p q, IsScalarTower k R (V p q)]
    [∀ p q, Algebra (S' p) (V p q)] [∀ p q, Algebra (S' q) (V p q)]
    [∀ p q, IsScalarTower k (S' p) (V p q)] [∀ p q, IsScalarTower k (S' q) (V p q)]
    [∀ p q, IsScalarTower R (S' p) (V p q)] [∀ p q, IsScalarTower R (S' q) (V p q)]
    [∀ p q, IsLocalization.Away (r p * r q) (V p q)]
    (hr : Ideal.span (Set.range r) = ⊤)
    (E : ∀ q, CertifiedDivisorFamilyAff C (S' q) n)
    (hcompat : AwayCompatPullDivEq S' (fun q => (E q).eqns) V) :
    ∃ F₀ : DivFamZarAff C R n,
      ∀ q, DivFamZarAff.mapAlg (S' q) n F₀ = (E q).toZarAff := by
  classical
  haveI himm : ∀ q, IsOpenImmersion (relCurveMap C R (S' q)) := fun q =>
    isOpenImmersion_relCurveMap_away C R (S' q) (r q)
  -- the glued local-equation system, at the bare systems of the certified input
  set glue := awayGluedEquationsLoc r S' (fun q => (E q).eqns) V hr hcompat with hglue
  -- the glue is widened-locally certified over the same cover
  have hloc : IsLocallyCertifiedAff (C := C) (R := R) n glue := by
    obtain ⟨M, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
    refine ⟨M, fun j => r (e.symm j), ?_, fun j => ?_⟩
    · have hrange : (Set.range fun j : Fin M => r (e.symm j)) = Set.range r :=
        e.symm.surjective.range_comp r
      rw [hrange, hr]
    · -- identify the carrier with the pinned localization and transport the witness
      set q := e.symm j with hq
      set B := Localization.Away (r q) with hB
      haveI : IsOpenImmersion (relCurveMap C R B) :=
        isOpenImmersion_relCurveMap_away C R B (r q)
      letI : Algebra (S' q) B :=
        ((IsLocalization.algEquiv (Submonoid.powers (r q)) (S' q)
          B).toAlgHom.toRingHom).toAlgebra
      haveI : IsScalarTower R (S' q) B :=
        IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x =>
          ((IsLocalization.algEquiv (Submonoid.powers (r q)) (S' q) B).commutes x).symm)
      haveI : IsScalarTower k (S' q) B :=
        isScalarTower_left_of_isScalarTower (R₀ := R)
      -- the chart restriction of the glue, transported along the identification
      have hdiv0 := (divEq_pullback_awayGluedEquationsLoc r S' (fun q => (E q).eqns) V hr
        hcompat q
        (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
          (relCurveMap C R (S' q)) glue)).symm
      exact ⟨(E q).mapAlg B n (E q).cover.hasAffineOverlaps_of_isProper,
        (E q).divEq_mapAlg_pullback n B (E q).cover.hasAffineOverlaps_of_isProper
          (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
            (relCurveMap C R B) glue) hdiv0⟩
  refine ⟨DivFamZarAff.mk glue hloc, fun q => ?_⟩
  -- the restriction law: the pulled glue is divisor-equal to the chart system
  exact DivFamZarAff.mk_eq_mk_iff.mpr
    (divEq_pullback_awayGluedEquationsLoc r S' (fun q => (E q).eqns) V hr hcompat q _)

end Core

end AlgebraicGeometry
