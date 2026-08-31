/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyMapAlg
import AlgebraicJacobian.Picard.RelPicPi

/-!
# Zariski separation of the divisor functor (DD-2 stage S4)

The divisor functor `DivFam C · π n` is a separated presheaf for the Zariski topology of
affine tests (`informal/spec-dd-2.md` §4, mirroring
`AlgebraicGeometry.PicEtAff.eq_of_away_eq`): two divisor classes over `R` agreeing under
`DivFam.mapAlg` on every member of a finite covering family of localizations agree.

Route (equation rigidity — divisor equality `DivEq` is Zariski-local on the curve):

* `Scheme.LocalEquations.exists_unit_of_pullback_unit` — **the immersion `DivEq`-unit
  transport**: a pointwise unit relating the two pulled-back equations on a member `V`
  below a point `z` of an open immersion `w` transports to a unit on the image open
  `w ''ᵁ V` relating the two original equations, through the section retraction of the
  immersion (`Scheme.Hom.unitsPreimageEquiv`, the `OpenImmersionUnits` kit).
* `Scheme.LocalEquations.divEq_of_divEq_pullback` — **divisor equality is local for a
  cover by open immersions**: if the pullbacks of two local-equation systems along a
  jointly surjective family of open immersions are divisor-equal, so are the systems.
  `DivEq` demands NO cocycle across points, so locality is a pointwise patch: at `y`
  choose a piece and a preimage, take the local witness member and its unit, and
  transport both through the immersion.
* `AlgebraicGeometry.isOpenImmersion_relCurveMap_away` — the relative-curve comparison
  `relCurveMap C R S` of a localization `IsLocalization.Away f S` is an open immersion
  (base change of the basic open immersion `Spec S ⟶ Spec R` along the projection —
  `Over.isOpenImmersion_whiskerLeft`).
* `AlgebraicGeometry.exists_relCurveMap_base_eq` — **the point lift**: for a span-⊤
  family `g : ι → R`, every point of `relCurve C R` lifts to some
  `relCurve C (S i)`: its structure image in `Spec R` avoids some `g i` (no prime
  contains all of them), so it lies in the corresponding basic open, and the whisker
  square is a pullback (`Over.range_whiskerLeft`).
* `AlgebraicGeometry.DivFam.eq_of_away_eq` — **the keystone**: Zariski separation of
  the divisor functor, `∀ i, mapAlg (S i) n F = mapAlg (S i) n G → F = G` for a finite
  covering family of localizations (the `PicEtAffZariskiSep` packaging).

The gluing half (`informal/spec-dd-2.md` §5) is stage S5's brick and not in this file.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## Divisor equality is local for covers by open immersions

Generic in the scheme; this is pure `DivisorClass`-level material. -/

namespace Scheme.LocalEquations

variable {Y : Scheme.{u}}

/-- Restriction of a section along `W ≤ V ≤ U` composes to restriction along `W ≤ U`. -/
private lemma res_res {X : Scheme.{u}} {W V U : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s)
      = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- A point of the image open of an open immersion, from a preimage point and a member
witness. -/
private lemma mem_image_of_base_eq {Z : Scheme.{u}} (w : Z ⟶ Y) [IsOpenImmersion w]
    {z : Z} {y : Y} (hzy : w.base z = y) {U : Z.Opens} (hz : z ∈ U) : y ∈ w ''ᵁ U := by
  subst hzy
  exact (Scheme.Hom.apply_mem_image_iff w).mpr hz

/-- **Pointwise `DivEq`-unit transport across an open immersion** (the S4 workhorse,
`informal/spec-dd-2.md` §4): given an open immersion `w : Z ⟶ Y`, a point `z` over
`x = w z`, an open `V` below both pulled cover members at `z`, and a unit `v` on `V`
relating the two pulled-back equations, there is a unit on the image open `w ''ᵁ V`
relating the restrictions of the original equations at `x`. The unit is the inverse
transport of `v` through the section retraction of the immersion
(`Scheme.Hom.unitsPreimageEquiv`); the equation identity is checked after pulling back
to `w ⁻¹ᵁ (w ''ᵁ V)`, where pullback of sections is bijective. -/
theorem exists_unit_of_pullback_unit {Z : Scheme.{u}} (w : Z ⟶ Y) [IsOpenImmersion w]
    (d₁ d₂ : Y.LocalEquations) {z : Z} {x : Y} (hzx : w.base z = x) {V : Z.Opens}
    (hV₁ : V ≤ (d₁.cover.pullback w).opens z) (hV₂ : V ≤ (d₂.cover.pullback w).opens z)
    (hW₁ : w ''ᵁ V ≤ d₁.cover.opens x) (hW₂ : w ''ᵁ V ≤ d₂.cover.opens x)
    (v : Γ(Z, V)ˣ)
    (hv : (Z.presheaf.map (homOfLE hV₁).op).hom (pullbackEqn w d₁ z)
      = (v : Γ(Z, V)) * (Z.presheaf.map (homOfLE hV₂).op).hom (pullbackEqn w d₂ z)) :
    ∃ u : Γ(Y, w ''ᵁ V)ˣ,
      (Y.presheaf.map (homOfLE hW₁).op).hom (d₁.eqn x)
        = (u : Γ(Y, w ''ᵁ V)) * (Y.presheaf.map (homOfLE hW₂).op).hom (d₂.eqn x) := by
  subst hzx
  have hWrange : w ''ᵁ V ≤ w.opensRange := w.image_le_opensRange V
  have hpre : w ⁻¹ᵁ (w ''ᵁ V) ≤ V := (w.preimage_image_eq V).le
  haveI := Scheme.Hom.isIso_appLE_of_le_opensRange w hWrange
  refine ⟨(Scheme.Hom.unitsPreimageEquiv w hWrange).symm (Z.unitsRestrict hpre v), ?_⟩
  -- restrict the pulled relation to the preimage of the image member
  have hres := congrArg (Z.presheaf.map (homOfLE hpre).op).hom hv
  rw [map_mul, res_res, res_res, pullbackEqn_res w d₁ z (hpre.trans hV₁),
    pullbackEqn_res w d₂ z (hpre.trans hV₂)] at hres
  -- both restricted target equations pull back to `appLE` of the base equations
  have e₁ : (w.appLE (w ''ᵁ V) (w ⁻¹ᵁ (w ''ᵁ V)) le_rfl).hom
      ((Y.presheaf.map (homOfLE hW₁).op).hom (d₁.eqn (w.base z)))
      = (w.appLE (d₁.cover.opens (w.base z)) (w ⁻¹ᵁ (w ''ᵁ V))
          (hpre.trans hV₁)).hom (d₁.eqn (w.base z)) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have e₂ : (w.appLE (w ''ᵁ V) (w ⁻¹ᵁ (w ''ᵁ V)) le_rfl).hom
      ((Y.presheaf.map (homOfLE hW₂).op).hom (d₂.eqn (w.base z)))
      = (w.appLE (d₂.cover.opens (w.base z)) (w ⁻¹ᵁ (w ''ᵁ V))
          (hpre.trans hV₂)).hom (d₂.eqn (w.base z)) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  -- the unit factor: pullback of the inverse transport is restriction
  have hu := congrArg Units.val
    (Scheme.Hom.unitsAppLE_unitsPreimageEquiv_symm w hWrange
      (le_rfl : w ⁻¹ᵁ (w ''ᵁ V) ≤ w ⁻¹ᵁ (w ''ᵁ V)) (Z.unitsRestrict hpre v))
  rw [Scheme.unitsRestrict_unitsRestrict] at hu
  -- conclude by injectivity of pullback onto the preimage of the image member
  have key : (w.appLE (w ''ᵁ V) (w ⁻¹ᵁ (w ''ᵁ V)) le_rfl).hom
      ((Y.presheaf.map (homOfLE hW₁).op).hom (d₁.eqn (w.base z)))
      = (w.appLE (w ''ᵁ V) (w ⁻¹ᵁ (w ''ᵁ V)) le_rfl).hom
        ((((Scheme.Hom.unitsPreimageEquiv w hWrange).symm (Z.unitsRestrict hpre v)) :
            Γ(Y, w ''ᵁ V))
          * (Y.presheaf.map (homOfLE hW₂).op).hom (d₂.eqn (w.base z))) := by
    rw [map_mul]
    exact e₁.trans (hres.trans (congrArg₂ (· * ·) hu.symm e₂.symm))
  exact (ConcreteCategory.bijective_of_isIso
    (w.appLE (w ''ᵁ V) (w ⁻¹ᵁ (w ''ᵁ V)) le_rfl)).injective key

/-- **Divisor equality is local for a cover by open immersions**
(`informal/spec-dd-2.md` §4): if two local-equation systems on `Y` become
divisor-equal after pullback along every member of a jointly surjective family of open
immersions, they are divisor-equal. `DivEq` demands no cocycle across points, so
locality is a pointwise patch: the common refinement takes, at `y`, the image of the
local witness member at a chosen preimage of `y`, and the unit transports through the
immersion (`exists_unit_of_pullback_unit`). -/
theorem divEq_of_divEq_pullback {ι : Type u} {Z : ι → Scheme.{u}}
    (w : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (w i)]
    (hcover : ∀ y : Y, ∃ (i : ι) (z : Z i), (w i).base z = y)
    {d₁ d₂ : Y.LocalEquations}
    (hreg₁ : ∀ i (y z : Z i) (hz : z ∈ (d₁.cover.pullback (w i)).opens y),
      ((Z i).presheaf.germ ((d₁.cover.pullback (w i)).opens y) z hz).hom
          (pullbackEqn (w i) d₁ y) ∈ nonZeroDivisors ((Z i).presheaf.stalk z))
    (hreg₂ : ∀ i (y z : Z i) (hz : z ∈ (d₂.cover.pullback (w i)).opens y),
      ((Z i).presheaf.germ ((d₂.cover.pullback (w i)).opens y) z hz).hom
          (pullbackEqn (w i) d₂ y) ∈ nonZeroDivisors ((Z i).presheaf.stalk z))
    (h : ∀ i, DivEq (d₁.pullback (w i) (hreg₁ i)) (d₂.pullback (w i) (hreg₂ i))) :
    DivEq d₁ d₂ := by
  classical
  choose 𝒱 hV₁ hV₂ HV using h
  choose pick zsel hzsel using hcover
  -- the two refinement witnesses of the pointwise image cover
  have hle₁ : ∀ y : Y,
      w (pick y) ''ᵁ (𝒱 (pick y)).opens (zsel y) ≤ d₁.cover.opens y := by
    intro y
    have h00 : (𝒱 (pick y)).opens (zsel y)
        ≤ w (pick y) ⁻¹ᵁ d₁.cover.opens ((w (pick y)).base (zsel y)) :=
      hV₁ (pick y) (zsel y)
    have h0 := ((w (pick y)).image_mono h00).trans
      ((w (pick y)).image_preimage_le (d₁.cover.opens ((w (pick y)).base (zsel y))))
    rw [hzsel y] at h0
    exact h0
  have hle₂ : ∀ y : Y,
      w (pick y) ''ᵁ (𝒱 (pick y)).opens (zsel y) ≤ d₂.cover.opens y := by
    intro y
    have h00 : (𝒱 (pick y)).opens (zsel y)
        ≤ w (pick y) ⁻¹ᵁ d₂.cover.opens ((w (pick y)).base (zsel y)) :=
      hV₂ (pick y) (zsel y)
    have h0 := ((w (pick y)).image_mono h00).trans
      ((w (pick y)).image_preimage_le (d₂.cover.opens ((w (pick y)).base (zsel y))))
    rw [hzsel y] at h0
    exact h0
  -- assemble the common refinement and patch the units pointwise
  refine ⟨⟨fun y => w (pick y) ''ᵁ (𝒱 (pick y)).opens (zsel y),
    fun y => mem_image_of_base_eq (w (pick y)) (hzsel y)
      ((𝒱 (pick y)).mem_opens (zsel y))⟩, hle₁, hle₂, fun y => ?_⟩
  obtain ⟨v, hv⟩ := HV (pick y) (zsel y)
  exact exists_unit_of_pullback_unit (w (pick y)) d₁ d₂ (hzsel y)
    (hV₁ (pick y) (zsel y)) (hV₂ (pick y) (zsel y)) (hle₁ y) (hle₂ y) v hv

end Scheme.LocalEquations

/-! ## The relative-curve comparison of a localization is an open immersion -/

variable {k : Type u} [Field k]

section RelCurveAway

variable (C : Over (Spec (.of k))) (R : Type u) [CommRing R] [Algebra k R]

section OneLocalization

variable (S : Type u) [CommRing S] [Algebra k S] [Algebra R S] [IsScalarTower k R S]

/-- **The relative-curve comparison of a localization is an open immersion**: for
`IsLocalization.Away f S`, the comparison `relCurveMap C R S : C_S ⟶ C_R` is the
whiskering of the basic open immersion `Spec S ⟶ Spec R`, hence its base change along
the projection (`Over.isOpenImmersion_whiskerLeft`). -/
theorem isOpenImmersion_relCurveMap_away (f : R) [IsLocalization.Away f S] :
    IsOpenImmersion (relCurveMap C R S) := by
  haveI : IsOpenImmersion (overSpecMap (k := k) R S).left := by
    rw [overSpecMap_left]
    exact IsOpenImmersion.of_isLocalization f
  exact Over.isOpenImmersion_whiskerLeft C (overSpecMap (k := k) R S)

end OneLocalization

section Family

variable {ι : Type u} (g : ι → R) (S : ι → Type u) [∀ i, CommRing (S i)]
  [∀ i, Algebra k (S i)] [∀ i, Algebra R (S i)] [∀ i, IsScalarTower k R (S i)]
  [∀ i, IsLocalization.Away (g i) (S i)]

/-- **The point lift for a span-⊤ family of localizations**: every point of the
relative curve `C_R` lifts to the relative curve of some localization `S i`. The
structure image of the point in `Spec R` avoids some `g i` (the `g i` generate the unit
ideal, so no prime contains all of them), hence lies in the image of
`Spec (S i) ⟶ Spec R` (`PrimeSpectrum.localization_away_comap_range`), and the whisker
square is a pullback of topological images (`Over.range_whiskerLeft`). -/
theorem exists_relCurveMap_base_eq (hg : Ideal.span (Set.range g) = ⊤)
    (y : relCurve C R) :
    ∃ (i : ι) (z : relCurve C (S i)), (relCurveMap C R (S i)).base z = y := by
  classical
  -- the structure image of `y` in `Spec R` avoids some `g i`
  have hexists : ∃ i, g i ∉
      (show PrimeSpectrum R from (snd C (overSpec k R)).left.base y).asIdeal := by
    by_contra hall
    have hle : Ideal.span (Set.range g) ≤
        (show PrimeSpectrum R from (snd C (overSpec k R)).left.base y).asIdeal := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact of_not_not fun hc => hall ⟨i, hc⟩
    rw [hg] at hle
    exact (show PrimeSpectrum R from
      (snd C (overSpec k R)).left.base y).isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨i, hi⟩ := hexists
  haveI : IsOpenImmersion (overSpecMap (k := k) R (S i)).left := by
    rw [overSpecMap_left]
    exact IsOpenImmersion.of_isLocalization (g i)
  refine ⟨i, ?_⟩
  change y ∈ Set.range ((C ◁ overSpecMap (k := k) R (S i)).left).base
  rw [Over.range_whiskerLeft C (overSpecMap (k := k) R (S i))]
  -- the structure image lies in the image of the localization's spectrum
  have hmem : (show PrimeSpectrum R from (snd C (overSpec k R)).left.base y)
      ∈ Set.range (PrimeSpectrum.comap (algebraMap R (S i))) := by
    rw [PrimeSpectrum.localization_away_comap_range (S := S i) (g i)]
    exact hi
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, hq⟩

end Family

end RelCurveAway

/-! ## Zariski separation of the divisor functor -/

section Keystone

variable {C : Over (Spec (.of k))} {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsAffineHom π] (n : ℕ)

/-- **Zariski separation of the divisor functor** (`informal/spec-dd-2.md` §4, the
`PicEtAffZariskiSep` packaging): two divisor classes over `R` agreeing under
`DivFam.mapAlg` on every member of a finite covering family of localizations agree.
Representative level: the comparisons `relCurveMap C R (S i)` are open immersions
jointly covering the relative curve, and divisor equality is local for such a cover
(`Scheme.LocalEquations.divEq_of_divEq_pullback`). -/
theorem DivFam.eq_of_away_eq {ι : Type u} [Finite ι] (g : ι → R) (S : ι → Type u)
    [∀ i, CommRing (S i)] [∀ i, Algebra k (S i)] [∀ i, Algebra R (S i)]
    [∀ i, IsScalarTower k R (S i)] [∀ i, IsLocalization.Away (g i) (S i)]
    (hg : Ideal.span (Set.range g) = ⊤) {F G : DivFam C R π n}
    (h : ∀ i, DivFam.mapAlg (S i) n F = DivFam.mapAlg (S i) n G) :
    F = G := by
  haveI : ∀ i, IsOpenImmersion (relCurveMap C R (S i)) := fun i =>
    isOpenImmersion_relCurveMap_away C R (S i) (g i)
  revert h
  refine Quotient.inductionOn₂ F G fun F₀ G₀ h => ?_
  refine DivFam.mk_eq_mk_iff.mpr ?_
  refine Scheme.LocalEquations.divEq_of_divEq_pullback
    (fun i => relCurveMap C R (S i))
    (fun y => exists_relCurveMap_base_eq C R g S hg y)
    (fun i => F₀.adaptation.germ_pullbackEqn_mem_nonZeroDivisors (S i)
      F₀.certified.projective_colength)
    (fun i => G₀.adaptation.germ_pullbackEqn_mem_nonZeroDivisors (S i)
      G₀.certified.projective_colength)
    (fun i => ?_)
  have hi : DivFam.mk (F₀.mapAlg (S i) n) = DivFam.mk (G₀.mapAlg (S i) n) := h i
  exact DivFam.mk_eq_mk_iff.mp hi

end Keystone

end AlgebraicGeometry
