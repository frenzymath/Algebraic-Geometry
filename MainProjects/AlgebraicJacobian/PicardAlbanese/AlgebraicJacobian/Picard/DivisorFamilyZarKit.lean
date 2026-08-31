/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyMapAlg

/-!
# Germ-regularity engines for pulled local equations (DD-2 stage S5b kit)

Generic engines for the regularity side-condition of `LocalEquations.pullback`
(`informal/spec-dd-2.md`, Addendum 2 — the S5b `IsLocallyCertified` layer): germ
regularity of pulled equations is member-normalizable, `DivEq`-invariant, compatible
with composition of comparisons, and **Zariski-local on the source** for covers by
open immersions.

* `AlgebraicGeometry.Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_forall_self`
  — member normalization: regularity of each pulled equation at the base point of its
  own member suffices (the transition units of the base system pull back through
  `pullback_ratio_eq`).
* `…germ_self_pullbackEqn_mem_nonZeroDivisors_of_divEq` and the full form
  `…germ_pullbackEqn_mem_nonZeroDivisors_of_divEq` — germ regularity of pulled
  equations transports across `DivEq` (the pointwise units pull back through
  `unitsAppLE`).
* `…germ_pullbackEqn_comp` — the pulled-equation germ of a composite comparison is the
  germ of the two-stage pullback (`Scheme.Hom.appLE_comp_appLE` at the germ level).
* `…germ_pullbackEqn_congr` — the pulled-equation germ at propositionally equal
  comparisons.
* `…germ_pullbackEqn_mem_nonZeroDivisors_of_immersion_cover` — **Zariski locality**:
  pulled-equation germ regularity along `f : Y ⟶ X` may be checked after composing
  with any jointly surjective family of open immersions into `Y` (their stalk
  comparisons are isomorphisms).

Consumed by `AlgebraicJacobian.Picard.DivisorFamilyZar` (the `IsLocallyCertified`
carrier and its mapAlg-hreg engine) and the S5b gluing files.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)`-shaped sections with opens produced on other
spellings downstream; the S2 file's pinned defeq discipline is kept for coherence. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace Scheme.LocalEquations

variable {X Y : Scheme.{u}}

/-- A ring isomorphism carries nonzerodivisors to nonzerodivisors. -/
private lemma equiv_map_mem_nonZeroDivisors {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {a : A} (ha : a ∈ nonZeroDivisors A) : e a ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff] at ha ⊢
  obtain ⟨hl, hr⟩ := ha
  constructor
  · intro b hb
    have h := congrArg e.symm hb
    rw [map_mul, map_zero, e.symm_apply_apply] at h
    have hb0 : e.symm b = 0 := hl _ h
    calc b = e (e.symm b) := (e.apply_symm_apply b).symm
      _ = 0 := by rw [hb0, map_zero]
  · intro b hb
    have h := congrArg e.symm hb
    rw [map_mul, map_zero, e.symm_apply_apply] at h
    have hb0 : e.symm b = 0 := hr _ h
    calc b = e (e.symm b) := (e.apply_symm_apply b).symm
      _ = 0 := by rw [hb0, map_zero]

/-- `appLE` of a local equation at propositionally equal base points. -/
private lemma appLE_eqn_congr (f : Y ⟶ X) (E : X.LocalEquations)
    {x₁ x₂ : X} (hx : x₁ = x₂) {W : Y.Opens}
    (e₁ : W ≤ f ⁻¹ᵁ E.cover.opens x₁) (e₂ : W ≤ f ⁻¹ᵁ E.cover.opens x₂) :
    (f.appLE (E.cover.opens x₁) W e₁).hom (E.eqn x₁) =
      (f.appLE (E.cover.opens x₂) W e₂).hom (E.eqn x₂) := by
  subst hx
  rfl

/-- **Member normalization of pulled-equation germ regularity**: if the germ of each
pulled equation is a nonzerodivisor at the base point of its own member, it is a
nonzerodivisor at every point of the member — the transition unit of the base system
pulls back (`pullback_ratio_eq`) and relates the two pulled equations near the point. -/
theorem germ_pullbackEqn_mem_nonZeroDivisors_of_forall_self (f : Y ⟶ X)
    (E : X.LocalEquations)
    (h : ∀ z : Y, (Y.presheaf.germ ((E.cover.pullback f).opens z) z
        ((E.cover.pullback f).mem_opens z)).hom (pullbackEqn f E z)
        ∈ nonZeroDivisors (Y.presheaf.stalk z)) :
    ∀ (y z : Y) (hz : z ∈ (E.cover.pullback f).opens y),
      (Y.presheaf.germ ((E.cover.pullback f).opens y) z hz).hom (pullbackEqn f E y)
        ∈ nonZeroDivisors (Y.presheaf.stalk z) := by
  intro y z hz
  have hzmem : z ∈ (E.cover.pullback f).opens y ⊓ (E.cover.pullback f).opens z :=
    ⟨hz, (E.cover.pullback f).mem_opens z⟩
  have hrel := congrArg (Y.presheaf.germ
    ((E.cover.pullback f).opens y ⊓ (E.cover.pullback f).opens z) z hzmem).hom
    (pullback_ratio_eq f E y z)
  rw [map_mul, Y.presheaf.germ_res_apply, Y.presheaf.germ_res_apply] at hrel
  rw [hrel]
  refine mul_mem ?_ (h z)
  exact ((f.unitsAppLE (E.cover.opens (f.base y) ⊓ E.cover.opens (f.base z))
    ((E.cover.pullback f).opens y ⊓ (E.cover.pullback f).opens z)
    (f.le_preimage_inf inf_le_left inf_le_right)
    (E.ratioUnit (f.base y) (f.base z))).isUnit.map
      (Y.presheaf.germ _ z hzmem).hom).mem_nonZeroDivisors

/-- **Own-member germ regularity of pulled equations transports across `DivEq`**: the
pointwise unit of the divisor equality at the base point pulls back through `appLE`
and relates the two pulled equations near the point. -/
theorem germ_self_pullbackEqn_mem_nonZeroDivisors_of_divEq (f : Y ⟶ X)
    {E E' : X.LocalEquations} (h : DivEq E E') (z : Y)
    (hE : (Y.presheaf.germ ((E.cover.pullback f).opens z) z
        ((E.cover.pullback f).mem_opens z)).hom (pullbackEqn f E z)
        ∈ nonZeroDivisors (Y.presheaf.stalk z)) :
    (Y.presheaf.germ ((E'.cover.pullback f).opens z) z
        ((E'.cover.pullback f).mem_opens z)).hom (pullbackEqn f E' z)
      ∈ nonZeroDivisors (Y.presheaf.stalk z) := by
  obtain ⟨𝒲, h₁, h₂, H⟩ := h
  obtain ⟨u, hu⟩ := H (f.base z)
  have hle : (𝒲.pullback f).opens z ≤ f ⁻¹ᵁ 𝒲.opens (f.base z) := le_rfl
  have hW₁ : (𝒲.pullback f).opens z ≤ (E.cover.pullback f).opens z :=
    Scheme.Hom.preimage_mono f (h₁ (f.base z))
  have hW₂ : (𝒲.pullback f).opens z ≤ (E'.cover.pullback f).opens z :=
    Scheme.Hom.preimage_mono f (h₂ (f.base z))
  -- the section-level relation between the two pulled equations (the
  -- `divEq_pullback` collapse, at the point's own member)
  have hres₁ : (Y.presheaf.map (homOfLE hW₁).op).hom (pullbackEqn f E z)
      = (f.appLE (E.cover.opens (f.base z)) ((𝒲.pullback f).opens z)
          (hW₁.trans le_rfl)).hom (E.eqn (f.base z)) :=
    pullbackEqn_res f E z hW₁
  have hres₂ : (Y.presheaf.map (homOfLE hW₂).op).hom (pullbackEqn f E' z)
      = (f.appLE (E'.cover.opens (f.base z)) ((𝒲.pullback f).opens z)
          (hW₂.trans le_rfl)).hom (E'.eqn (f.base z)) :=
    pullbackEqn_res f E' z hW₂
  have e₁ := congr(($(Scheme.Hom.map_appLE f hle (homOfLE (h₁ (f.base z))).op)).hom
    (E.eqn (f.base z)))
  have e₂ := congr(($(Scheme.Hom.map_appLE f hle (homOfLE (h₂ (f.base z))).op)).hom
    (E'.eqn (f.base z)))
  have key := congrArg (f.appLE (𝒲.opens (f.base z)) ((𝒲.pullback f).opens z) hle).hom hu
  rw [map_mul] at key
  have hrel : (Y.presheaf.map (homOfLE hW₁).op).hom (pullbackEqn f E z)
      = ((f.unitsAppLE (𝒲.opens (f.base z)) ((𝒲.pullback f).opens z) hle u :
            Γ(Y, (𝒲.pullback f).opens z)))
        * (Y.presheaf.map (homOfLE hW₂).op).hom (pullbackEqn f E' z) :=
    hres₁.trans (e₁.symm.trans (key.trans (congrArg₂ (· * ·) rfl
      (e₂.trans hres₂.symm))))
  -- pass to germs at the point
  have hgerm := congrArg (Y.presheaf.germ ((𝒲.pullback f).opens z) z
    ((𝒲.pullback f).mem_opens z)).hom hrel
  rw [map_mul, Y.presheaf.germ_res_apply, Y.presheaf.germ_res_apply] at hgerm
  exact (mul_mem_nonZeroDivisors.mp (hgerm ▸ hE)).2

/-- **Germ regularity of pulled equations transports across `DivEq`** (the full
`(y, z)`-form): member normalization plus the pointwise `DivEq` transfer. -/
theorem germ_pullbackEqn_mem_nonZeroDivisors_of_divEq (f : Y ⟶ X)
    {E E' : X.LocalEquations} (h : DivEq E E')
    (hE : ∀ (y z : Y) (hz : z ∈ (E.cover.pullback f).opens y),
      (Y.presheaf.germ ((E.cover.pullback f).opens y) z hz).hom (pullbackEqn f E y)
        ∈ nonZeroDivisors (Y.presheaf.stalk z)) :
    ∀ (y z : Y) (hz : z ∈ (E'.cover.pullback f).opens y),
      (Y.presheaf.germ ((E'.cover.pullback f).opens y) z hz).hom (pullbackEqn f E' y)
        ∈ nonZeroDivisors (Y.presheaf.stalk z) :=
  germ_pullbackEqn_mem_nonZeroDivisors_of_forall_self f E' fun z =>
    germ_self_pullbackEqn_mem_nonZeroDivisors_of_divEq f h z
      (hE z z ((E.cover.pullback f).mem_opens z))

/-- **The pulled-equation germ of a composite is the germ of the two-stage pullback**
at the point's own member: the equations agree after restriction to the two-stage
member (`Scheme.Hom.appLE_comp_appLE`), and germs are restriction-invariant. -/
theorem germ_pullbackEqn_comp {Z : Scheme.{u}} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}
    (hgf : g ≫ f = h) (E : X.LocalEquations) (hregf) (ζ : Z) :
    (Z.presheaf.germ ((E.cover.pullback h).opens ζ) ζ
        ((E.cover.pullback h).mem_opens ζ)).hom (pullbackEqn h E ζ)
      = (Z.presheaf.germ (((E.pullback f hregf).cover.pullback g).opens ζ) ζ
          (((E.pullback f hregf).cover.pullback g).mem_opens ζ)).hom
          (pullbackEqn g (E.pullback f hregf) ζ) := by
  subst hgf
  have hcov : ((E.cover.pullback f).pullback g).opens ζ ≤
      (E.cover.pullback (g ≫ f)).opens ζ :=
    le_of_eq (by
      rw [Scheme.PointedCover.pullback_opens, Scheme.PointedCover.pullback_opens,
        Scheme.PointedCover.pullback_opens, Scheme.Hom.comp_preimage,
        Scheme.Hom.comp_apply])
  -- the section-level collapse on the two-stage member (the `divEq_pullback_pullback`
  -- calc)
  have h2 := congr(($(Scheme.Hom.appLE_comp_appLE g f
    (E.cover.opens (f.base (g.base ζ))) ((E.cover.pullback f).opens (g.base ζ))
    (((E.cover.pullback f).pullback g).opens ζ) le_rfl le_rfl)).hom
      (E.eqn (f.base (g.base ζ))))
  have hsec : (Z.presheaf.map (homOfLE (le_refl
      (((E.cover.pullback f).pullback g).opens ζ))).op).hom
      (pullbackEqn g (E.pullback f hregf) ζ)
      = (Z.presheaf.map (homOfLE hcov).op).hom (pullbackEqn (g ≫ f) E ζ) :=
    (pullbackEqn_res g (E.pullback f hregf) ζ le_rfl).trans
      (h2.trans (pullbackEqn_res (g ≫ f) E ζ hcov).symm)
  have hg₁ := Z.presheaf.germ_res_apply (homOfLE hcov) ζ
    (((E.cover.pullback f).pullback g).mem_opens ζ) (pullbackEqn (g ≫ f) E ζ)
  have hg₂ := Z.presheaf.germ_res_apply (homOfLE (le_refl
      (((E.cover.pullback f).pullback g).opens ζ))) ζ
    (((E.cover.pullback f).pullback g).mem_opens ζ)
    (pullbackEqn g (E.pullback f hregf) ζ)
  calc (Z.presheaf.germ ((E.cover.pullback (g ≫ f)).opens ζ) ζ
        ((E.cover.pullback (g ≫ f)).mem_opens ζ)).hom (pullbackEqn (g ≫ f) E ζ)
      = (Z.presheaf.germ (((E.cover.pullback f).pullback g).opens ζ) ζ
          (((E.cover.pullback f).pullback g).mem_opens ζ)).hom
          ((Z.presheaf.map (homOfLE hcov).op).hom (pullbackEqn (g ≫ f) E ζ)) :=
        hg₁.symm
    _ = (Z.presheaf.germ (((E.cover.pullback f).pullback g).opens ζ) ζ
          (((E.cover.pullback f).pullback g).mem_opens ζ)).hom
          ((Z.presheaf.map (homOfLE (le_refl _)).op).hom
            (pullbackEqn g (E.pullback f hregf) ζ)) := by rw [hsec]
    _ = (Z.presheaf.germ (((E.pullback f hregf).cover.pullback g).opens ζ) ζ
          (((E.pullback f hregf).cover.pullback g).mem_opens ζ)).hom
          (pullbackEqn g (E.pullback f hregf) ζ) := hg₂

/-- The pulled-equation germ at (propositionally) equal comparisons. -/
theorem germ_pullbackEqn_congr {Z : Scheme.{u}} {h h' : Z ⟶ X} (e : h = h')
    (E : X.LocalEquations) (ζ : Z) :
    (Z.presheaf.germ ((E.cover.pullback h).opens ζ) ζ
        ((E.cover.pullback h).mem_opens ζ)).hom (pullbackEqn h E ζ)
      = (Z.presheaf.germ ((E.cover.pullback h').opens ζ) ζ
          ((E.cover.pullback h').mem_opens ζ)).hom (pullbackEqn h' E ζ) := by
  subst e
  rfl

/-- **Pulled-equation germ regularity is Zariski-local on the source**
(the S5b mapAlg-hreg engine): for a jointly surjective family of open immersions
`w i : Z i ⟶ Y`, if the pulled equations of `E` along each composite `w i ≫ f` have
nonzerodivisor germs at the base points of their own members, then the pulled
equations of `E` along `f` have nonzerodivisor germs everywhere — each germ transports
through the stalk isomorphism of an immersion covering its point. -/
theorem germ_pullbackEqn_mem_nonZeroDivisors_of_immersion_cover
    {ι : Type*} {Z : ι → Scheme.{u}} (w : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (w i)]
    (hcover : ∀ y : Y, ∃ (i : ι) (z : Z i), (w i).base z = y)
    (f : Y ⟶ X) (E : X.LocalEquations)
    (hreg : ∀ (i : ι) (ζ : Z i),
      ((Z i).presheaf.germ ((E.cover.pullback (w i ≫ f)).opens ζ) ζ
          ((E.cover.pullback (w i ≫ f)).mem_opens ζ)).hom (pullbackEqn (w i ≫ f) E ζ)
        ∈ nonZeroDivisors ((Z i).presheaf.stalk ζ)) :
    ∀ (y z : Y) (hz : z ∈ (E.cover.pullback f).opens y),
      (Y.presheaf.germ ((E.cover.pullback f).opens y) z hz).hom (pullbackEqn f E y)
        ∈ nonZeroDivisors (Y.presheaf.stalk z) := by
  refine germ_pullbackEqn_mem_nonZeroDivisors_of_forall_self f E fun z => ?_
  obtain ⟨i, ζ, hζ⟩ := hcover z
  subst hζ
  -- push the germ through the stalk isomorphism of the covering immersion
  have hmem : ζ ∈ (w i) ⁻¹ᵁ (E.cover.pullback f).opens ((w i).base ζ) :=
    (E.cover.pullback f).mem_opens ((w i).base ζ)
  have hpush : ((w i).stalkMap ζ).hom
      ((Y.presheaf.germ ((E.cover.pullback f).opens ((w i).base ζ)) ((w i).base ζ)
        ((E.cover.pullback f).mem_opens ((w i).base ζ))).hom
        (pullbackEqn f E ((w i).base ζ)))
      = ((Z i).presheaf.germ ((w i) ⁻¹ᵁ (E.cover.pullback f).opens ((w i).base ζ)) ζ
          hmem).hom
        (((w i).app ((E.cover.pullback f).opens ((w i).base ζ))).hom
          (pullbackEqn f E ((w i).base ζ))) :=
    Scheme.Hom.germ_stalkMap_apply (w i) ((E.cover.pullback f).opens ((w i).base ζ))
      ζ hmem (pullbackEqn f E ((w i).base ζ))
  -- the transported germ is the composite pulled-equation germ, after restriction to
  -- the composite member
  have hle : (E.cover.pullback (w i ≫ f)).opens ζ ≤
      (w i) ⁻¹ᵁ (E.cover.pullback f).opens ((w i).base ζ) :=
    le_of_eq (by
      rw [Scheme.PointedCover.pullback_opens, Scheme.PointedCover.pullback_opens,
        Scheme.Hom.comp_preimage, Scheme.Hom.comp_apply])
  have happ : ((w i).app ((E.cover.pullback f).opens ((w i).base ζ))).hom
      (pullbackEqn f E ((w i).base ζ))
      = ((w i).appLE ((E.cover.pullback f).opens ((w i).base ζ))
          ((w i) ⁻¹ᵁ (E.cover.pullback f).opens ((w i).base ζ)) le_rfl).hom
        (pullbackEqn f E ((w i).base ζ)) := by
    rw [Scheme.Hom.appLE_eq_app]
  have hres : ((Z i).presheaf.map (homOfLE hle).op).hom
      (((w i).appLE ((E.cover.pullback f).opens ((w i).base ζ))
        ((w i) ⁻¹ᵁ (E.cover.pullback f).opens ((w i).base ζ)) le_rfl).hom
        (pullbackEqn f E ((w i).base ζ)))
      = ((w i).appLE ((E.cover.pullback f).opens ((w i).base ζ))
          ((E.cover.pullback (w i ≫ f)).opens ζ) hle).hom
        (pullbackEqn f E ((w i).base ζ)) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  -- the composite collapse: `appLE` after `appLE` is `appLE` of the composite
  have hcomp : ((w i).appLE ((E.cover.pullback f).opens ((w i).base ζ))
      ((E.cover.pullback (w i ≫ f)).opens ζ) hle).hom
      (pullbackEqn f E ((w i).base ζ))
      = pullbackEqn (w i ≫ f) E ζ := by
    have hsplit := Scheme.Hom.appLE_comp_appLE (w i) f
      (E.cover.opens (f.base ((w i).base ζ)))
      ((E.cover.pullback f).opens ((w i).base ζ))
      ((E.cover.pullback (w i ≫ f)).opens ζ) le_rfl hle
    have h0 : ((w i).appLE ((E.cover.pullback f).opens ((w i).base ζ))
        ((E.cover.pullback (w i ≫ f)).opens ζ) hle).hom
        (pullbackEqn f E ((w i).base ζ))
        = ((w i ≫ f).appLE (E.cover.opens (f.base ((w i).base ζ)))
            ((E.cover.pullback (w i ≫ f)).opens ζ)
            (hle.trans ((Opens.map (w i).base).map (homOfLE le_rfl)).le)).hom
          (E.eqn (f.base ((w i).base ζ))) := by
      rw [show pullbackEqn f E ((w i).base ζ)
          = (f.appLE (E.cover.opens (f.base ((w i).base ζ)))
              ((E.cover.pullback f).opens ((w i).base ζ)) le_rfl).hom
            (E.eqn (f.base ((w i).base ζ))) from rfl,
        ← CommRingCat.comp_apply, hsplit]
    rw [h0]
    exact appLE_eqn_congr (w i ≫ f) E (Scheme.Hom.comp_apply (w i) f ζ).symm _ le_rfl
  -- assemble: the target germ is the stalk-isomorphism preimage of the composite germ
  set e := (asIso ((w i).stalkMap ζ)).commRingCatIsoToRingEquiv with he
  have hval : (Y.presheaf.germ ((E.cover.pullback f).opens ((w i).base ζ))
      ((w i).base ζ) ((E.cover.pullback f).mem_opens ((w i).base ζ))).hom
      (pullbackEqn f E ((w i).base ζ))
      = e.symm (((Z i).presheaf.germ ((E.cover.pullback (w i ≫ f)).opens ζ) ζ
          ((E.cover.pullback (w i ≫ f)).mem_opens ζ)).hom
          (pullbackEqn (w i ≫ f) E ζ)) := by
    apply e.injective
    rw [e.apply_symm_apply]
    have hg := (Z i).presheaf.germ_res_apply (homOfLE hle) ζ
      ((E.cover.pullback (w i ≫ f)).mem_opens ζ)
      (((w i).appLE ((E.cover.pullback f).opens ((w i).base ζ))
        ((w i) ⁻¹ᵁ (E.cover.pullback f).opens ((w i).base ζ)) le_rfl).hom
        (pullbackEqn f E ((w i).base ζ)))
    calc e ((Y.presheaf.germ ((E.cover.pullback f).opens ((w i).base ζ))
          ((w i).base ζ) ((E.cover.pullback f).mem_opens ((w i).base ζ))).hom
          (pullbackEqn f E ((w i).base ζ)))
        = ((Z i).presheaf.germ
            ((w i) ⁻¹ᵁ (E.cover.pullback f).opens ((w i).base ζ)) ζ hmem).hom
            (((w i).appLE ((E.cover.pullback f).opens ((w i).base ζ))
              ((w i) ⁻¹ᵁ (E.cover.pullback f).opens ((w i).base ζ)) le_rfl).hom
              (pullbackEqn f E ((w i).base ζ))) := by
          rw [← happ]; exact hpush
      _ = ((Z i).presheaf.germ ((E.cover.pullback (w i ≫ f)).opens ζ) ζ
            ((E.cover.pullback (w i ≫ f)).mem_opens ζ)).hom
            (((Z i).presheaf.map (homOfLE hle).op).hom
              (((w i).appLE ((E.cover.pullback f).opens ((w i).base ζ))
                ((w i) ⁻¹ᵁ (E.cover.pullback f).opens ((w i).base ζ)) le_rfl).hom
                (pullbackEqn f E ((w i).base ζ)))) := hg.symm
      _ = ((Z i).presheaf.germ ((E.cover.pullback (w i ≫ f)).opens ζ) ζ
            ((E.cover.pullback (w i ≫ f)).mem_opens ζ)).hom
            (pullbackEqn (w i ≫ f) E ζ) := by rw [hres, hcomp]
  rw [hval]
  exact equiv_map_mem_nonZeroDivisors e.symm (hreg i ζ)

end Scheme.LocalEquations

end AlgebraicGeometry
