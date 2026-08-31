/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZariskiGlueKit
import AlgebraicJacobian.Picard.DivisorFamilyZariskiSep

/-!
# Zariski gluing of local-equation systems over an away cover (DD-2 stage S5)

The divisor-assembly half of the divisor-functor Zariski gluing
(`informal/spec-dd-2.md` §5): for a span-⊤ family `g : ι → R` with localization
carriers `S i` (the S4 packaging), representatives `(E i)` of compatible divisor classes
over the `S i` glue at the `LocalEquations` level to a system on the relative curve
over `R`, whose pullback along each comparison `relCurveMap C R (S i)` is
divisor-equal to the local system.

* `AlgebraicGeometry.exists_relCurveMap_base_eq_pair` — the **pairwise point lift**: a
  point of `C_R` lifting to both `C_{S₁}` and `C_{S₂}` lifts to the overlap curve
  `C_T`, `IsLocalization.Away (g₁ * g₂) T` (the S4 point-lift pattern at the product).
* `AlgebraicGeometry.awayGlueIndex`/`awayGlueLift` — the chosen chart index and
  preimage of a point of `C_R` (the S4 span-⊤ point lift, packaged by choice).
* `AlgebraicGeometry.AwayCompatDivEq` — the representative-level overlap
  compatibility: over each overlap carrier `T i j` the two pulled systems are
  divisor-equal.
* `AlgebraicGeometry.exists_res_awayTransport_eq_unit_mul` — **the pointwise cross
  unit**: near any point of an overlap of two transported members (possibly from
  different charts), the two transported equations differ by a unit — through the
  overlap curve `C_{T i j}`: the compatibility `DivEq` provides the unit upstairs,
  conjugated by the transition units of the two local systems, and the open immersion
  `relCurveMap C R (T i j)` descends it (the Kit's section-form unit descent).
* `AlgebraicGeometry.awayGluedEquations` — **the glued system**: at `y` the member is
  the image of the chosen chart's covering member and the equation is the immersion
  transport of the chart equation; `ratio_isUnit` upgrades the pointwise cross units to
  full overlap units by the Kit's unit-spreading engine (regularity gluing).
* `AlgebraicGeometry.divEq_pullback_awayGluedEquations` — **restriction to the charts**:
  the pullback of the glued system along `relCurveMap C R (S i)` is divisor-equal to
  the `i`-th local system (the members and equations restrict back by construction —
  the immersion round trip).

The class-level assembly (the conditional keystone) is
`AlgebraicJacobian.Picard.DivisorFamilyZariskiGlueClass`.
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

variable {k : Type u} [Field k]

/-- Restriction of a section along `W ≤ V ≤ U` composes to restriction along `W ≤ U`. -/
private lemma res_res {X : Scheme.{u}} {W V U : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s)
      = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- `appLE` at (propositionally) equal morphisms (the inclusion witness is
proof-irrelevant). -/
private lemma appLE_hom_congr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f')
    {U : Y.Opens} {W : X.Opens} (e : W ≤ f ⁻¹ᵁ U) :
    f.appLE U W e = f'.appLE U W (h ▸ e) := by
  subst h; rfl

/-! ## The pairwise point lift -/

section PairLift

variable (C : Over (Spec (.of k))) (R : Type u) [CommRing R] [Algebra k R]

/-- **The pairwise point lift** (`informal/spec-dd-2.md` §5): a point of the relative
curve `C_R` that lifts to the relative curves of two away localizations `S₁, S₂` lifts
to the relative curve of an overlap carrier `T`, `IsLocalization.Away (g₁ * g₂) T`.
The structure image avoids both `g₁` and `g₂` (it lies in both comap ranges), hence
avoids `g₁ * g₂`, and the whisker square is a pullback of topological images
(`Over.range_whiskerLeft` — the S4 point-lift pattern). -/
theorem exists_relCurveMap_base_eq_pair (g₁ g₂ : R) (S₁ S₂ T : Type u)
    [CommRing S₁] [CommRing S₂] [CommRing T]
    [Algebra k S₁] [Algebra k S₂] [Algebra k T]
    [Algebra R S₁] [Algebra R S₂] [Algebra R T]
    [IsScalarTower k R S₁] [IsScalarTower k R S₂] [IsScalarTower k R T]
    [IsLocalization.Away g₁ S₁] [IsLocalization.Away g₂ S₂]
    [IsLocalization.Away (g₁ * g₂) T]
    {y : relCurve C R} {z₁ : relCurve C S₁} (hz₁ : (relCurveMap C R S₁).base z₁ = y)
    {z₂ : relCurve C S₂} (hz₂ : (relCurveMap C R S₂).base z₂ = y) :
    ∃ z : relCurve C T, (relCurveMap C R T).base z = y := by
  haveI : IsOpenImmersion (overSpecMap (k := k) R S₁).left := by
    rw [overSpecMap_left]
    exact IsOpenImmersion.of_isLocalization g₁
  haveI : IsOpenImmersion (overSpecMap (k := k) R S₂).left := by
    rw [overSpecMap_left]
    exact IsOpenImmersion.of_isLocalization g₂
  haveI : IsOpenImmersion (overSpecMap (k := k) R T).left := by
    rw [overSpecMap_left]
    exact IsOpenImmersion.of_isLocalization (g₁ * g₂)
  -- the structure image of `y` lies in both comap ranges, hence avoids `g₁` and `g₂`
  have hmem₁ : (show PrimeSpectrum R from (snd C (overSpec k R)).left.base y)
      ∈ Set.range (PrimeSpectrum.comap (algebraMap R S₁)) := by
    have hy₁ : y ∈ Set.range ((C ◁ overSpecMap (k := k) R S₁).left).base := ⟨z₁, hz₁⟩
    rw [Over.range_whiskerLeft C (overSpecMap (k := k) R S₁)] at hy₁
    exact hy₁
  have hmem₂ : (show PrimeSpectrum R from (snd C (overSpec k R)).left.base y)
      ∈ Set.range (PrimeSpectrum.comap (algebraMap R S₂)) := by
    have hy₂ : y ∈ Set.range ((C ◁ overSpecMap (k := k) R S₂).left).base := ⟨z₂, hz₂⟩
    rw [Over.range_whiskerLeft C (overSpecMap (k := k) R S₂)] at hy₂
    exact hy₂
  rw [PrimeSpectrum.localization_away_comap_range (S := S₁) g₁] at hmem₁
  rw [PrimeSpectrum.localization_away_comap_range (S := S₂) g₂] at hmem₂
  -- hence it lies in the comap range of the overlap carrier
  have hmemT : (show PrimeSpectrum R from (snd C (overSpec k R)).left.base y)
      ∈ Set.range (PrimeSpectrum.comap (algebraMap R T)) := by
    rw [PrimeSpectrum.localization_away_comap_range (S := T) (g₁ * g₂),
      PrimeSpectrum.basicOpen_mul]
    exact ⟨hmem₁, hmem₂⟩
  change y ∈ Set.range ((C ◁ overSpecMap (k := k) R T).left).base
  rw [Over.range_whiskerLeft C (overSpecMap (k := k) R T)]
  obtain ⟨q, hq⟩ := hmemT
  exact ⟨q, hq⟩

end PairLift

/-! ## The glued local-equation system -/

section Glued

variable {C : Over (Spec (.of k))} {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable {ι : Type u} (g : ι → R) (S : ι → Type u) [∀ i, CommRing (S i)]
  [∀ i, Algebra k (S i)] [∀ i, Algebra R (S i)] [∀ i, IsScalarTower k R (S i)]
  [∀ i, IsLocalization.Away (g i) (S i)]

/-- The chosen chart index of a point of the glued relative curve (the S4 span-⊤ point
lift, packaged by choice). -/
noncomputable def awayGlueIndex (hg : Ideal.span (Set.range g) = ⊤)
    (y : relCurve C R) : ι :=
  (exists_relCurveMap_base_eq C R g S hg y).choose

/-- The chosen preimage of a point of the glued relative curve on its chart curve. -/
noncomputable def awayGlueLift (hg : Ideal.span (Set.range g) = ⊤)
    (y : relCurve C R) : relCurve C (S (awayGlueIndex g S hg y)) :=
  (exists_relCurveMap_base_eq C R g S hg y).choose_spec.choose

@[simp]
lemma relCurveMap_base_awayGlueLift (hg : Ideal.span (Set.range g) = ⊤)
    (y : relCurve C R) :
    (relCurveMap C R (S (awayGlueIndex g S hg y))).base (awayGlueLift g S hg y) = y :=
  (exists_relCurveMap_base_eq C R g S hg y).choose_spec.choose_spec

variable [∀ i, IsOpenImmersion (relCurveMap C R (S i))]
variable {n : ℕ} (E : ∀ i, CertifiedDivisorFamily C (S i) π n)

/-- Germ regularity of the immersion transport of a chart equation: the germs of the
transported equation are nonzerodivisors at every point of the image member (the Kit's
germ transport at the chart system's regularity). -/
lemma germ_awayTransport_mem_nonZeroDivisors (i : ι) (x' : relCurve C (S i))
    (z : relCurve C R)
    (hz : z ∈ relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens x') :
    ((relCurve C R).presheaf.germ
        (relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens x') z hz).hom
        (((relCurveMap C R (S i)).appIso ((E i).eqns.cover.opens x')).inv.hom
          ((E i).eqns.eqn x'))
      ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk z) :=
  Scheme.Hom.germ_appIso_inv_mem_nonZeroDivisors (relCurveMap C R (S i))
    (fun z' hz' => (E i).eqns.regular x' z' hz') z hz

section Overlap

variable (T : ι → ι → Type u) [∀ i j, CommRing (T i j)] [∀ i j, Algebra k (T i j)]
  [∀ i j, Algebra R (T i j)] [∀ i j, IsScalarTower k R (T i j)]
  [∀ i j, Algebra (S i) (T i j)] [∀ i j, Algebra (S j) (T i j)]
  [∀ i j, IsScalarTower k (S i) (T i j)] [∀ i j, IsScalarTower k (S j) (T i j)]
  [∀ i j, IsScalarTower R (S i) (T i j)] [∀ i j, IsScalarTower R (S j) (T i j)]
  [∀ i j, IsLocalization.Away (g i * g j) (T i j)]

/-- **The representative-level overlap compatibility** (`informal/spec-dd-2.md` §5):
over each overlap carrier `T i j` the two pulled systems are divisor-equal — the
`DivEq` unfolding of the class-level compatibility
`mapAlg (T i j) n (F i) = mapAlg (T i j) n (F j)` at chosen representatives. -/
def AwayCompatDivEq : Prop :=
  ∀ i j, Scheme.LocalEquations.DivEq
    ((E i).adaptation.pulledEquations (T i j) (E i).certified.projective_colength)
    ((E j).adaptation.pulledEquations (T i j) (E j).certified.projective_colength)

include g in
/-- **The pointwise cross unit** (`informal/spec-dd-2.md` §5): near any point `z` of an
open `O` inside the overlap of two transported members — from charts `i` and `j` at
points `x'`, `y'` — the two transported equations differ by a unit.  Route: `z` lifts
to the overlap curve `C_{T i j}` (pairwise point lift); upstairs, the compatibility
`DivEq` provides a unit between the two pulled equations at the lift, conjugated into
the transported equations by the transition units of the two chart systems; the open
immersion `relCurveMap C R (T i j)` descends the relation (the Kit's section-form unit
descent). -/
theorem exists_res_awayTransport_eq_unit_mul (hcompat : AwayCompatDivEq S E T)
    {i j : ι} {x' : relCurve C (S i)} {y' : relCurve C (S j)}
    {O : (relCurve C R).Opens}
    (hOx : O ≤ relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens x')
    (hOy : O ≤ relCurveMap C R (S j) ''ᵁ (E j).eqns.cover.opens y')
    (z : relCurve C R) (hz : z ∈ O) :
    ∃ (W : (relCurve C R).Opens) (hWO : W ≤ O) (_ : z ∈ W)
      (u : Γ(relCurve C R, W)ˣ),
      ((relCurve C R).presheaf.map (homOfLE (hWO.trans hOx)).op).hom
          (((relCurveMap C R (S i)).appIso ((E i).eqns.cover.opens x')).inv.hom
            ((E i).eqns.eqn x'))
        = (u : Γ(relCurve C R, W))
          * ((relCurve C R).presheaf.map (homOfLE (hWO.trans hOy)).op).hom
            (((relCurveMap C R (S j)).appIso ((E j).eqns.cover.opens y')).inv.hom
              ((E j).eqns.eqn y')) := by
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
  have hxwV : (relCurveMap C (S i) (T i j)).base w ∈ (E i).eqns.cover.opens x' := by
    have hmem := hOx hz
    rw [← hxwz] at hmem
    exact (Scheme.Hom.apply_mem_image_iff (relCurveMap C R (S i))).mp hmem
  have hywV : (relCurveMap C (S j) (T i j)).base w ∈ (E j).eqns.cover.opens y' := by
    have hmem := hOy hz
    rw [← hywz] at hmem
    exact (Scheme.Hom.apply_mem_image_iff (relCurveMap C R (S j))).mp hmem
  -- the compatibility unit at the lift
  obtain ⟨𝒲, h₁, h₂, H⟩ := hcompat i j
  obtain ⟨v, hv⟩ := H w
  -- the upstairs working open
  set Vi := (E i).eqns.cover.opens x'
    ⊓ (E i).eqns.cover.opens ((relCurveMap C (S i) (T i j)).base w) with hVi
  set Vj := (E j).eqns.cover.opens y'
    ⊓ (E j).eqns.cover.opens ((relCurveMap C (S j) (T i j)).base w) with hVj
  set V'' := 𝒲.opens w ⊓ relCurveMap C (S i) (T i j) ⁻¹ᵁ Vi
    ⊓ relCurveMap C (S j) (T i j) ⁻¹ᵁ Vj
    ⊓ relCurveMap C R (T i j) ⁻¹ᵁ O with hV''
  have hwV'' : w ∈ V'' := by
    refine ⟨⟨⟨𝒲.mem_opens w, ⟨hxwV, (E i).eqns.cover.mem_opens _⟩⟩,
      ⟨hywV, (E j).eqns.cover.mem_opens _⟩⟩, ?_⟩
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
      (relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens x') :=
    hleO.trans ((relCurveMap C R (T i j)).preimage_mono hOx)
  have eV₂ : V'' ≤ relCurveMap C R (T i j) ⁻¹ᵁ
      (relCurveMap C R (S j) ''ᵁ (E j).eqns.cover.opens y') :=
    hleO.trans ((relCurveMap C R (T i j)).preimage_mono hOy)
  -- the `i`-side collapse: the pulled transported equation is the pulled ratio unit
  -- times the pullback of the chart equation at the lift's anchor
  have hi : ((relCurveMap C R (T i j)).appLE
        (relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens x') V'' eV₁).hom
        (((relCurveMap C R (S i)).appIso ((E i).eqns.cover.opens x')).inv.hom
          ((E i).eqns.eqn x'))
      = (((relCurveMap C (S i) (T i j)).unitsAppLE Vi V'' hlei
            ((E i).eqns.ratioUnit x' ((relCurveMap C (S i) (T i j)).base w)))
          : Γ(relCurve C (T i j), V''))
        * ((relCurveMap C (S i) (T i j)).appLE
            ((E i).eqns.cover.opens ((relCurveMap C (S i) (T i j)).base w)) V''
            (hlei.trans (Scheme.Hom.preimage_mono _ inf_le_right))).hom
          ((E i).eqns.eqn ((relCurveMap C (S i) (T i j)).base w)) := by
    have hmid : Vi ≤ relCurveMap C R (S i) ⁻¹ᵁ
        (relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens x') :=
      inf_le_left.trans ((relCurveMap C R (S i)).preimage_image_eq _).ge
    have hsplit := Scheme.Hom.appLE_comp_appLE
      (relCurveMap C (S i) (T i j)) (relCurveMap C R (S i))
      (relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens x') Vi V'' hmid hlei
    have hcongr := appLE_hom_congr hcompi
      (U := relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens x') (W := V'')
      (hlei.trans ((relCurveMap C (S i) (T i j)).preimage_mono hmid))
    have h0 : ((relCurveMap C R (T i j)).appLE
        (relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens x') V'' eV₁).hom
        (((relCurveMap C R (S i)).appIso ((E i).eqns.cover.opens x')).inv.hom
          ((E i).eqns.eqn x'))
        = ((relCurveMap C (S i) (T i j)).appLE Vi V'' hlei).hom
          (((relCurveMap C R (S i)).appLE
              (relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens x') Vi hmid).hom
            (((relCurveMap C R (S i)).appIso ((E i).eqns.cover.opens x')).inv.hom
              ((E i).eqns.eqn x'))) := by
      rw [← hcongr, ← hsplit, CommRingCat.comp_apply]
    rw [h0, Scheme.Hom.appIso_inv_appLE_apply]
    -- the transition unit between the two chart anchors
    have hratio := congrArg ((relCurveMap C (S i) (T i j)).appLE Vi V'' hlei).hom
      ((E i).eqns.eqn_restrict_eq x' ((relCurveMap C (S i) (T i j)).base w))
    rw [map_mul] at hratio
    rw [show ((relCurve C (S i)).presheaf.map (homOfLE (by
        rwa [(relCurveMap C R (S i)).preimage_image_eq] at hmid)).op).hom
        ((E i).eqns.eqn x')
        = ((relCurve C (S i)).presheaf.map (homOfLE (inf_le_left : Vi ≤ _)).op).hom
          ((E i).eqns.eqn x') from rfl, hratio]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  -- the `j`-side collapse
  have hj : ((relCurveMap C R (T i j)).appLE
        (relCurveMap C R (S j) ''ᵁ (E j).eqns.cover.opens y') V'' eV₂).hom
        (((relCurveMap C R (S j)).appIso ((E j).eqns.cover.opens y')).inv.hom
          ((E j).eqns.eqn y'))
      = (((relCurveMap C (S j) (T i j)).unitsAppLE Vj V'' hlej
            ((E j).eqns.ratioUnit y' ((relCurveMap C (S j) (T i j)).base w)))
          : Γ(relCurve C (T i j), V''))
        * ((relCurveMap C (S j) (T i j)).appLE
            ((E j).eqns.cover.opens ((relCurveMap C (S j) (T i j)).base w)) V''
            (hlej.trans (Scheme.Hom.preimage_mono _ inf_le_right))).hom
          ((E j).eqns.eqn ((relCurveMap C (S j) (T i j)).base w)) := by
    have hmid : Vj ≤ relCurveMap C R (S j) ⁻¹ᵁ
        (relCurveMap C R (S j) ''ᵁ (E j).eqns.cover.opens y') :=
      inf_le_left.trans ((relCurveMap C R (S j)).preimage_image_eq _).ge
    have hsplit := Scheme.Hom.appLE_comp_appLE
      (relCurveMap C (S j) (T i j)) (relCurveMap C R (S j))
      (relCurveMap C R (S j) ''ᵁ (E j).eqns.cover.opens y') Vj V'' hmid hlej
    have hcongr := appLE_hom_congr hcompj
      (U := relCurveMap C R (S j) ''ᵁ (E j).eqns.cover.opens y') (W := V'')
      (hlej.trans ((relCurveMap C (S j) (T i j)).preimage_mono hmid))
    have h0 : ((relCurveMap C R (T i j)).appLE
        (relCurveMap C R (S j) ''ᵁ (E j).eqns.cover.opens y') V'' eV₂).hom
        (((relCurveMap C R (S j)).appIso ((E j).eqns.cover.opens y')).inv.hom
          ((E j).eqns.eqn y'))
        = ((relCurveMap C (S j) (T i j)).appLE Vj V'' hlej).hom
          (((relCurveMap C R (S j)).appLE
              (relCurveMap C R (S j) ''ᵁ (E j).eqns.cover.opens y') Vj hmid).hom
            (((relCurveMap C R (S j)).appIso ((E j).eqns.cover.opens y')).inv.hom
              ((E j).eqns.eqn y'))) := by
      rw [← hcongr, ← hsplit, CommRingCat.comp_apply]
    rw [h0, Scheme.Hom.appIso_inv_appLE_apply]
    have hratio := congrArg ((relCurveMap C (S j) (T i j)).appLE Vj V'' hlej).hom
      ((E j).eqns.eqn_restrict_eq y' ((relCurveMap C (S j) (T i j)).base w))
    rw [map_mul] at hratio
    rw [show ((relCurve C (S j)).presheaf.map (homOfLE (by
        rwa [(relCurveMap C R (S j)).preimage_image_eq] at hmid)).op).hom
        ((E j).eqns.eqn y')
        = ((relCurve C (S j)).presheaf.map (homOfLE (inf_le_left : Vj ≤ _)).op).hom
          ((E j).eqns.eqn y') from rfl, hratio]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  -- the compatibility relation, restricted and respelled on the `appLE`-forms
  have hv' := congrArg ((relCurve C (T i j)).presheaf.map (homOfLE hle𝒲).op).hom hv
  rw [map_mul, res_res, res_res] at hv'
  have hres_i := Scheme.LocalEquations.pullbackEqn_res (relCurveMap C (S i) (T i j))
    (E i).eqns w (h := show V'' ≤ ((E i).eqns.cover.pullback
      (relCurveMap C (S i) (T i j))).opens w from
      hlei.trans (Scheme.Hom.preimage_mono _ inf_le_right))
  have hres_j := Scheme.LocalEquations.pullbackEqn_res (relCurveMap C (S j) (T i j))
    (E j).eqns w (h := show V'' ≤ ((E j).eqns.cover.pullback
      (relCurveMap C (S j) (T i j))).opens w from
      hlej.trans (Scheme.Hom.preimage_mono _ inf_le_right))
  have hv'' : ((relCurve C (T i j)).presheaf.map (homOfLE (show V'' ≤
      ((E i).eqns.cover.pullback (relCurveMap C (S i) (T i j))).opens w from
      hlei.trans (Scheme.Hom.preimage_mono _ inf_le_right))).op).hom
      (Scheme.LocalEquations.pullbackEqn (relCurveMap C (S i) (T i j)) (E i).eqns w)
      = ((relCurve C (T i j)).presheaf.map (homOfLE hle𝒲).op).hom
          (v : Γ(relCurve C (T i j), 𝒲.opens w))
        * ((relCurve C (T i j)).presheaf.map (homOfLE (show V'' ≤
            ((E j).eqns.cover.pullback (relCurveMap C (S j) (T i j))).opens w from
            hlej.trans (Scheme.Hom.preimage_mono _ inf_le_right))).op).hom
          (Scheme.LocalEquations.pullbackEqn (relCurveMap C (S j) (T i j))
            (E j).eqns w) := hv'
  -- the key relation on the `appLE`-forms
  have hkey : ((relCurveMap C (S i) (T i j)).appLE
        ((E i).eqns.cover.opens ((relCurveMap C (S i) (T i j)).base w)) V''
        (hlei.trans (Scheme.Hom.preimage_mono _ inf_le_right))).hom
        ((E i).eqns.eqn ((relCurveMap C (S i) (T i j)).base w))
      = ((relCurve C (T i j)).presheaf.map (homOfLE hle𝒲).op).hom
          (v : Γ(relCurve C (T i j), 𝒲.opens w))
        * ((relCurveMap C (S j) (T i j)).appLE
            ((E j).eqns.cover.opens ((relCurveMap C (S j) (T i j)).base w)) V''
            (hlej.trans (Scheme.Hom.preimage_mono _ inf_le_right))).hom
          ((E j).eqns.eqn ((relCurveMap C (S j) (T i j)).base w)) := by
    rw [← hres_i, ← hres_j]
    exact hv''
  -- the `j`-side relation inverted, and the unit relation assembled upstairs
  have hjinv : ((relCurveMap C (S j) (T i j)).appLE
        ((E j).eqns.cover.opens ((relCurveMap C (S j) (T i j)).base w)) V''
        (hlej.trans (Scheme.Hom.preimage_mono _ inf_le_right))).hom
        ((E j).eqns.eqn ((relCurveMap C (S j) (T i j)).base w))
      = ((((relCurveMap C (S j) (T i j)).unitsAppLE Vj V'' hlej
            ((E j).eqns.ratioUnit y' ((relCurveMap C (S j) (T i j)).base w)))⁻¹ :
          Γ(relCurve C (T i j), V'')ˣ) : Γ(relCurve C (T i j), V''))
        * ((relCurveMap C R (T i j)).appLE
            (relCurveMap C R (S j) ''ᵁ (E j).eqns.cover.opens y') V'' eV₂).hom
          (((relCurveMap C R (S j)).appIso ((E j).eqns.cover.opens y')).inv.hom
            ((E j).eqns.eqn y')) := by
    rw [hj, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hrel : ((relCurveMap C R (T i j)).appLE
        (relCurveMap C R (S i) ''ᵁ (E i).eqns.cover.opens x') V'' eV₁).hom
        (((relCurveMap C R (S i)).appIso ((E i).eqns.cover.opens x')).inv.hom
          ((E i).eqns.eqn x'))
      = ((((relCurveMap C (S i) (T i j)).unitsAppLE Vi V'' hlei
              ((E i).eqns.ratioUnit x' ((relCurveMap C (S i) (T i j)).base w)))
            * (relCurve C (T i j)).unitsRestrict hle𝒲 v
            * ((relCurveMap C (S j) (T i j)).unitsAppLE Vj V'' hlej
                ((E j).eqns.ratioUnit y' ((relCurveMap C (S j) (T i j)).base w)))⁻¹ :
          Γ(relCurve C (T i j), V'')ˣ) : Γ(relCurve C (T i j), V''))
        * ((relCurveMap C R (T i j)).appLE
            (relCurveMap C R (S j) ''ᵁ (E j).eqns.cover.opens y') V'' eV₂).hom
          (((relCurveMap C R (S j)).appIso ((E j).eqns.cover.opens y')).inv.hom
            ((E j).eqns.eqn y')) := by
    rw [hi, hkey, hjinv, Units.val_mul, Units.val_mul, mul_assoc, mul_assoc]
    rfl
  -- descend along the overlap immersion and land inside `O`
  have hWO : relCurveMap C R (T i j) ''ᵁ V'' ≤ O :=
    ((relCurveMap C R (T i j)).image_mono hleO).trans
      ((relCurveMap C R (T i j)).image_preimage_le O)
  obtain ⟨u, hu⟩ := Scheme.Hom.exists_unit_res_of_appLE_eq_unit_mul
    (relCurveMap C R (T i j))
    (((relCurveMap C R (S i)).appIso ((E i).eqns.cover.opens x')).inv.hom
      ((E i).eqns.eqn x'))
    (((relCurveMap C R (S j)).appIso ((E j).eqns.cover.opens y')).inv.hom
      ((E j).eqns.eqn y'))
    eV₁ eV₂ (hWO.trans hOx) (hWO.trans hOy) _ hrel
  exact ⟨relCurveMap C R (T i j) ''ᵁ V'', hWO,
    Scheme.Hom.mem_image_of_base_eq _ hw hwV'', u, hu⟩

/-- **The glued local-equation system over the away cover** (`informal/spec-dd-2.md`
§5, the divisor assembly): at a point `y` of the glued relative curve the member is
the image of the chosen chart's covering member under the open immersion
`relCurveMap C R (S _)` and the equation is the immersion transport of the chart
equation.  Regularity transports along the immersion (the Kit's germ transport); the
overlap ratios are units by the pointwise cross units
(`exists_res_awayTransport_eq_unit_mul`) upgraded to the full member overlaps by the
Kit's unit-spreading engine (regularity gluing).

**SUBSUMED — see `awayGluedEquationsLoc` (`Picard/DivisorFamilyAffGlueZarKit.lean`).**  That
declaration is this one restated at **bare** local-equation systems, with the pullback regularity
this version takes from the certificate carried explicitly; at `(fun i => (E i).eqns)` the two are
**definitionally equal** (checked by `rfl`).  This body never projects `.adaptation` or
`.certified` out of `E` — only `.eqns` and `.cover` — so the certified input type here is stronger
than the proof needs, which is precisely what blocked the R2 port (`informal/spec-dd-r.md`
ADDENDUM 8 §8.5).

Consequence to respect when editing: the unit-spreading argument now exists in two copies that
must stay in sync.  Prefer editing the `Loc` version and, if you touch this one, check the other.
The standing plan is to redefine this family in terms of the `Loc` family (ADDENDUM 8 §8.7). -/
noncomputable def awayGluedEquations (hg : Ideal.span (Set.range g) = ⊤)
    (hcompat : AwayCompatDivEq S E T) : (relCurve C R).LocalEquations where
  cover :=
    { opens := fun y => relCurveMap C R (S (awayGlueIndex g S hg y)) ''ᵁ
        (E (awayGlueIndex g S hg y)).eqns.cover.opens (awayGlueLift g S hg y)
      mem_opens := fun y => Scheme.Hom.mem_image_of_base_eq _
        (relCurveMap_base_awayGlueLift g S hg y)
        ((E (awayGlueIndex g S hg y)).eqns.cover.mem_opens (awayGlueLift g S hg y)) }
  eqn y := ((relCurveMap C R (S (awayGlueIndex g S hg y))).appIso
      ((E (awayGlueIndex g S hg y)).eqns.cover.opens (awayGlueLift g S hg y))).inv.hom
    ((E (awayGlueIndex g S hg y)).eqns.eqn (awayGlueLift g S hg y))
  regular y z hz := germ_awayTransport_mem_nonZeroDivisors S E _ _ z hz
  ratio_isUnit x y := by
    refine Scheme.exists_unit_mul_of_locally_unit_mul ?_ ?_
    · -- germ regularity of the restricted transport of the second equation
      intro z hz
      rw [(relCurve C R).presheaf.germ_res_apply]
      exact germ_awayTransport_mem_nonZeroDivisors S E _ _ z hz.2
    · -- the pointwise cross units on the member overlap
      intro z hz
      obtain ⟨W, hWO, hzW, u, hu⟩ := exists_res_awayTransport_eq_unit_mul g S E T
        hcompat (inf_le_left :
          relCurveMap C R (S (awayGlueIndex g S hg x)) ''ᵁ
              (E (awayGlueIndex g S hg x)).eqns.cover.opens (awayGlueLift g S hg x)
            ⊓ relCurveMap C R (S (awayGlueIndex g S hg y)) ''ᵁ
              (E (awayGlueIndex g S hg y)).eqns.cover.opens (awayGlueLift g S hg y)
          ≤ _)
        (inf_le_right :
          relCurveMap C R (S (awayGlueIndex g S hg x)) ''ᵁ
              (E (awayGlueIndex g S hg x)).eqns.cover.opens (awayGlueLift g S hg x)
            ⊓ relCurveMap C R (S (awayGlueIndex g S hg y)) ''ᵁ
              (E (awayGlueIndex g S hg y)).eqns.cover.opens (awayGlueLift g S hg y)
          ≤ _) z hz
      refine ⟨W, hWO, hzW, u, ?_⟩
      rw [res_res, res_res]
      exact hu

end Overlap

end Glued

end AlgebraicGeometry
