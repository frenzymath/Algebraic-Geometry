/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.OpenImmersionUnits
import AlgebraicJacobian.Picard.LocalEquationsPullback
import AlgebraicJacobian.Picard.DivisorStalkIdeal
import AlgebraicJacobian.Picard.RefinementInjectivity

/-!
# Zariski gluing kit: unit spreading and open-immersion section transport (DD-2 stage S5)

The generic engines of the divisor-functor Zariski gluing (`informal/spec-dd-2.md` §5),
stated once for reuse (the S1c `eqn_ratio_isUnit` shape):

* `AlgebraicGeometry.Scheme.exists_unit_mul_of_locally_unit_mul` — **the unit-spreading
  engine** (regularity gluing): two sections of an open whose germs are everywhere
  related by a unit — witnessed by a unit on a neighbourhood of each point — differ by a
  unit on the whole open.  Local cofactors are unique by regularity of the divisor
  section, so they glue by the sheaf property
  (`Scheme.mem_span_singleton_of_forall_germ`), and the glued cofactor has unit germs,
  hence is a unit (`RingedSpace.isUnit_of_isUnit_germ`).
* `AlgebraicGeometry.Scheme.Hom.exists_unit_res_of_appLE_eq_unit_mul` — **the
  open-immersion unit descent, section form**: a unit relation between the `appLE`
  pullbacks of two sections on an open below both preimages descends to a unit relation
  between their restrictions on the image open (the S4
  `exists_unit_of_pullback_unit` engine, freed of the `LocalEquations` carrier).
* `AlgebraicGeometry.Scheme.Hom.appLE_appIso_inv_apply` — the round trip: pulling an
  `appIso`-transported section back along the immersion is restriction.
* `AlgebraicGeometry.Scheme.Hom.germ_appIso_inv_mem_nonZeroDivisors` — germ regularity
  transports along the immersion section iso (the stalk comparison of an open immersion
  is an isomorphism).
* `AlgebraicGeometry.Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion`
  — the `hreg` discharge of `LocalEquations.pullback` is automatic along an open
  immersion (no certificate needed).
* `AlgebraicGeometry.Scheme.Hom.mem_image_of_base_eq` — image-open membership from a
  preimage point (public form of the S4 helper).
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace Scheme

/-- Restriction of a section along `W ≤ V ≤ U` composes to restriction along `W ≤ U`. -/
private lemma res_res {X : Scheme.{u}} {W V U : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s)
      = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

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

/-! ## The unit-spreading engine (regularity gluing) -/

/-- **The unit-spreading engine** (`informal/spec-dd-2.md` §5, the S1c
`eqn_ratio_isUnit` shape stated once for reuse): if `t` has nonzerodivisor germs on `V`
and, on a neighbourhood of every point of `V`, `s` is a unit multiple of `t`, then `s`
is a unit multiple of `t` on all of `V`.  The local cofactors are unique by regularity,
so they glue by the sheaf property (`Scheme.mem_span_singleton_of_forall_germ`); the
glued cofactor has unit germs at every point, hence is a unit
(`RingedSpace.isUnit_of_isUnit_germ`). -/
theorem exists_unit_mul_of_locally_unit_mul {X : Scheme.{u}} {V : X.Opens} {s t : Γ(X, V)}
    (ht : ∀ (z : X) (hz : z ∈ V),
      (X.presheaf.germ V z hz).hom t ∈ nonZeroDivisors (X.presheaf.stalk z))
    (h : ∀ (z : X) (_ : z ∈ V), ∃ (W : X.Opens) (hWV : W ≤ V) (_ : z ∈ W)
      (u : Γ(X, W)ˣ),
      (X.presheaf.map (homOfLE hWV).op).hom s
        = (u : Γ(X, W)) * (X.presheaf.map (homOfLE hWV).op).hom t) :
    ∃ u : Γ(X, V)ˣ, s = (u : Γ(X, V)) * t := by
  -- the germ of `s` is a unit multiple of the germ of `t` at every point of `V`
  have hgerm : ∀ (z : X) (hz : z ∈ V), ∃ w : (X.presheaf.stalk z)ˣ,
      (X.presheaf.germ V z hz).hom s
        = (w : X.presheaf.stalk z) * (X.presheaf.germ V z hz).hom t := by
    intro z hz
    obtain ⟨W, hWV, hzW, u, hu⟩ := h z hz
    have hg := congrArg (X.presheaf.germ W z hzW).hom hu
    rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply] at hg
    exact ⟨(u.isUnit.map (X.presheaf.germ W z hzW).hom).unit, by
      rw [IsUnit.unit_spec]; exact hg⟩
  -- glue the local cofactors: `s ∈ (t)`
  have hmem : s ∈ Ideal.span {t} := by
    refine Scheme.mem_span_singleton_of_forall_germ ht fun z hz => ?_
    obtain ⟨w, hw⟩ := hgerm z hz
    exact Ideal.mem_span_singleton'.mpr ⟨w, hw.symm⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  -- the glued cofactor has unit germs, hence is a unit
  have hcunit : IsUnit c := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    obtain ⟨w, hw⟩ := hgerm z hz
    have hct : (X.presheaf.germ V z hz).hom c * (X.presheaf.germ V z hz).hom t
        = (w : X.presheaf.stalk z) * (X.presheaf.germ V z hz).hom t := by
      rw [← map_mul, hc]
      exact hw
    have hcw := (mul_cancel_right_mem_nonZeroDivisors (ht z hz)).mp hct
    rw [hcw]
    exact w.isUnit
  exact ⟨hcunit.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩

/-! ## Open-immersion section transport -/

namespace Hom

variable {Z Y : Scheme.{u}}

/-- A point of the image open of an open immersion, from a preimage point and a
membership witness (public form of the S4 helper). -/
lemma mem_image_of_base_eq (w : Z ⟶ Y) [IsOpenImmersion w] {z : Z} {y : Y}
    (hzy : w.base z = y) {U : Z.Opens} (hz : z ∈ U) : y ∈ w ''ᵁ U := by
  subst hzy
  exact (Scheme.Hom.apply_mem_image_iff w).mpr hz

/-- **The round trip of the immersion section transport**: pulling the
`appIso`-transported section back along the immersion is restriction of the original
section (the apply-form of `Scheme.Hom.appIso_inv_appLE`). -/
lemma appIso_inv_appLE_apply (w : Z ⟶ Y) [IsOpenImmersion w] {V V' : Z.Opens}
    (e : V' ≤ w ⁻¹ᵁ (w ''ᵁ V)) (s : Γ(Z, V)) :
    (w.appLE (w ''ᵁ V) V' e).hom ((w.appIso V).inv.hom s)
      = (Z.presheaf.map (homOfLE (by rwa [w.preimage_image_eq] at e)).op).hom s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]

/-- **Germ regularity transports along the immersion section transport**: if all germs
of `s` on `V` are nonzerodivisors, so are all germs of the transported section on the
image open `w ''ᵁ V` — the stalk comparison of an open immersion is an isomorphism. -/
theorem germ_appIso_inv_mem_nonZeroDivisors (w : Z ⟶ Y) [IsOpenImmersion w]
    {V : Z.Opens} {s : Γ(Z, V)}
    (hs : ∀ (z : Z) (hz : z ∈ V),
      (Z.presheaf.germ V z hz).hom s ∈ nonZeroDivisors (Z.presheaf.stalk z))
    (y : Y) (hy : y ∈ w ''ᵁ V) :
    (Y.presheaf.germ (w ''ᵁ V) y hy).hom ((w.appIso V).inv.hom s)
      ∈ nonZeroDivisors (Y.presheaf.stalk y) := by
  obtain ⟨z, hz, rfl⟩ := hy
  have hzy : w.base z ∈ w ''ᵁ V := (Scheme.Hom.apply_mem_image_iff w).mpr hz
  -- push the germ through the stalk comparison of the immersion
  have hpush : (w.stalkMap z).hom
      ((Y.presheaf.germ (w ''ᵁ V) (w.base z) hzy).hom ((w.appIso V).inv.hom s))
      = (Z.presheaf.germ V z hz).hom s := by
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
    rw [show eqToHom (w.preimage_image_eq V)
        = homOfLE (w.preimage_image_eq V).le from Subsingleton.elim _ _]
    rw [Z.presheaf.germ_res_apply]
  -- transfer nonzerodivisibility along the stalk isomorphism
  set e := (asIso (w.stalkMap z)).commRingCatIsoToRingEquiv with he
  have hval : (Y.presheaf.germ (w ''ᵁ V) (w.base z) hzy).hom ((w.appIso V).inv.hom s)
      = e.symm ((Z.presheaf.germ V z hz).hom s) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact hpush
  have hmem := equiv_map_mem_nonZeroDivisors e.symm (hs z hz)
  rw [← hval] at hmem
  exact hmem

/-- **Open-immersion unit descent, section form** (the S4
`exists_unit_of_pullback_unit` engine freed of the `LocalEquations` carrier,
`informal/spec-dd-2.md` §5): a unit relation between the `appLE` pullbacks of two
sections `a`, `b` on an open `V` below both preimages descends to a unit relation
between their restrictions on the image open `w ''ᵁ V`.  The unit is the inverse
transport of `v` through the section retraction of the immersion
(`Scheme.Hom.unitsPreimageEquiv`); the identity is checked after pulling back to
`w ⁻¹ᵁ (w ''ᵁ V)`, where pullback of sections is bijective. -/
theorem exists_unit_res_of_appLE_eq_unit_mul (w : Z ⟶ Y) [IsOpenImmersion w]
    {U₁ U₂ : Y.Opens} (a : Γ(Y, U₁)) (b : Γ(Y, U₂)) {V : Z.Opens}
    (hV₁ : V ≤ w ⁻¹ᵁ U₁) (hV₂ : V ≤ w ⁻¹ᵁ U₂)
    (hW₁ : w ''ᵁ V ≤ U₁) (hW₂ : w ''ᵁ V ≤ U₂) (v : Γ(Z, V)ˣ)
    (hv : (w.appLE U₁ V hV₁).hom a = (v : Γ(Z, V)) * (w.appLE U₂ V hV₂).hom b) :
    ∃ u : Γ(Y, w ''ᵁ V)ˣ,
      (Y.presheaf.map (homOfLE hW₁).op).hom a
        = (u : Γ(Y, w ''ᵁ V)) * (Y.presheaf.map (homOfLE hW₂).op).hom b := by
  have hWrange : w ''ᵁ V ≤ w.opensRange := w.image_le_opensRange V
  have hpre : w ⁻¹ᵁ (w ''ᵁ V) ≤ V := (w.preimage_image_eq V).le
  haveI := Scheme.Hom.isIso_appLE_of_le_opensRange w hWrange
  refine ⟨(Scheme.Hom.unitsPreimageEquiv w hWrange).symm (Z.unitsRestrict hpre v), ?_⟩
  -- restrict the pulled relation to the preimage of the image open
  have h₁ : (Z.presheaf.map (homOfLE hpre).op).hom ((w.appLE U₁ V hV₁).hom a)
      = (w.appLE U₁ (w ⁻¹ᵁ (w ''ᵁ V)) (hpre.trans hV₁)).hom a := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have h₂ : (Z.presheaf.map (homOfLE hpre).op).hom ((w.appLE U₂ V hV₂).hom b)
      = (w.appLE U₂ (w ⁻¹ᵁ (w ''ᵁ V)) (hpre.trans hV₂)).hom b := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hres := congrArg (Z.presheaf.map (homOfLE hpre).op).hom hv
  rw [map_mul, h₁, h₂] at hres
  -- both restricted sections pull back to `appLE` of the originals
  have e₁ : (w.appLE (w ''ᵁ V) (w ⁻¹ᵁ (w ''ᵁ V)) le_rfl).hom
      ((Y.presheaf.map (homOfLE hW₁).op).hom a)
      = (w.appLE U₁ (w ⁻¹ᵁ (w ''ᵁ V)) (hpre.trans hV₁)).hom a := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have e₂ : (w.appLE (w ''ᵁ V) (w ⁻¹ᵁ (w ''ᵁ V)) le_rfl).hom
      ((Y.presheaf.map (homOfLE hW₂).op).hom b)
      = (w.appLE U₂ (w ⁻¹ᵁ (w ''ᵁ V)) (hpre.trans hV₂)).hom b := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  -- the unit factor: pullback of the inverse transport is restriction
  have hu := congrArg Units.val
    (Scheme.Hom.unitsAppLE_unitsPreimageEquiv_symm w hWrange
      (le_rfl : w ⁻¹ᵁ (w ''ᵁ V) ≤ w ⁻¹ᵁ (w ''ᵁ V)) (Z.unitsRestrict hpre v))
  rw [Scheme.unitsRestrict_unitsRestrict] at hu
  -- conclude by injectivity of pullback onto the preimage of the image open
  have key : (w.appLE (w ''ᵁ V) (w ⁻¹ᵁ (w ''ᵁ V)) le_rfl).hom
      ((Y.presheaf.map (homOfLE hW₁).op).hom a)
      = (w.appLE (w ''ᵁ V) (w ⁻¹ᵁ (w ''ᵁ V)) le_rfl).hom
        ((((Scheme.Hom.unitsPreimageEquiv w hWrange).symm (Z.unitsRestrict hpre v)) :
            Γ(Y, w ''ᵁ V))
          * (Y.presheaf.map (homOfLE hW₂).op).hom b) := by
    rw [map_mul]
    exact e₁.trans (hres.trans (congrArg₂ (· * ·) hu.symm e₂.symm))
  exact (ConcreteCategory.bijective_of_isIso
    (w.appLE (w ''ᵁ V) (w ⁻¹ᵁ (w ''ᵁ V)) le_rfl)).injective key

end Hom

/-! ## The `hreg` discharge along an open immersion -/

namespace LocalEquations

/-- **Pullback regularity is automatic along an open immersion**: the germs of the
pulled-back equations of any local-equation system are nonzerodivisors — the `hreg`
discharge of `LocalEquations.pullback` needs no certificate when the comparison is an
open immersion, since its stalk comparisons are isomorphisms. -/
theorem germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion {Z Y : Scheme.{u}}
    (w : Z ⟶ Y) [IsOpenImmersion w] (d : Y.LocalEquations) (y z : Z)
    (hz : z ∈ (d.cover.pullback w).opens y) :
    (Z.presheaf.germ ((d.cover.pullback w).opens y) z hz).hom (pullbackEqn w d y)
      ∈ nonZeroDivisors (Z.presheaf.stalk z) := by
  -- the germ of the pulled equation is the stalk image of the germ of the equation
  have hres : (Z.presheaf.germ ((d.cover.pullback w).opens y) z hz).hom
      (pullbackEqn w d y)
      = (Z.presheaf.germ (w ⁻¹ᵁ d.cover.opens (w.base y)) z hz).hom
        ((w.app (d.cover.opens (w.base y))).hom (d.eqn (w.base y))) := by
    rw [pullbackEqn]
    rw [show w.appLE (d.cover.opens (w.base y)) ((d.cover.pullback w).opens y) le_rfl
        = w.app (d.cover.opens (w.base y)) from Scheme.Hom.appLE_eq_app w]
    rfl
  have hpush : (Z.presheaf.germ (w ⁻¹ᵁ d.cover.opens (w.base y)) z hz).hom
      ((w.app (d.cover.opens (w.base y))).hom (d.eqn (w.base y)))
      = (w.stalkMap z).hom
        (((Y.presheaf.germ (d.cover.opens (w.base y)) (w.base z) hz).hom
          (d.eqn (w.base y)))) :=
    (Scheme.Hom.germ_stalkMap_apply w (d.cover.opens (w.base y)) z hz
      (d.eqn (w.base y))).symm
  rw [hres, hpush]
  set e := (asIso (w.stalkMap z)).commRingCatIsoToRingEquiv with he
  exact equiv_map_mem_nonZeroDivisors e (d.regular (w.base y) (w.base z) hz)

end LocalEquations

end Scheme

end AlgebraicGeometry
