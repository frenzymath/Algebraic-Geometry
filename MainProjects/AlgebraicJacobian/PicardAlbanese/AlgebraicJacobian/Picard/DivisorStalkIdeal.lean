/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamily
import AlgebraicJacobian.Cohomology.TwistedSheaf

/-!
# DD-4 (Tasks 4/5 substrate) — stalk ideals of a divisor family and the vanishing submodule

The cover-independent vocabulary behind the embedding `ε` of the DAT-D worksheet
(`informal/dat-d-worksheet.md` §2.3): a local-equation system `d` on a scheme `X` cuts, at
every point `z`, the **stalk ideal** `(germ_z (d.eqn z)) ⊆ 𝒪_{X,z}` — independent of the
choice of covering member through the unit ratios (`germ_eqn_span_eq`) and invariant under
divisor equality (`stalkIdeal_eq_of_divEq`).  A global section of a two-cover twisted sheaf
**vanishes along `d`** when its chart components lie in the stalk ideal at every point;
these form the submodule `Scheme.LocalEquations.vanishingSubmodule` — the DD-4 spelling of
`H⁰(𝒪(Θᴬ − d)) ⊆ H⁰(𝒪(Θᴬ))`, by design invariant under refinement and rescaling of `d`
(`vanishingSubmodule_eq_of_divEq`), which is what makes the embedding `ε` of the divisor
functor setoid-ready.

The bridge to the section-level evaluation of a finite chart adaptation (kernel of the
Θ-twisted colength evaluation) is `AlgebraicJacobian.Picard.DivisorFamilyTheta`; its `⊆`
direction runs through the present file's **stalk-locality of regular principal ideals**
(`Scheme.mem_span_singleton_of_forall_germ`): membership of a section in the span of a
germwise-regular section is a stalkwise condition — local cofactors are unique by
regularity, so they glue by the sheaf property.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

/-! ## Stalk-locality of membership in a regular principal ideal -/

section RegularSpan

variable {X : Scheme.{u}}

/-- Restriction of sections along `W ≤ V ≤ U` composes to restriction along `W ≤ U`. -/
private lemma res_res {W V U : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s)
      = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- **Germ-level regularity propagates to every restriction**: if all germs of `b` on `V`
are nonzerodivisors, the restriction of `b` to any `W ≤ V` is a nonzerodivisor in `Γ(X, W)`
(sections of a sheaf inject into the product of their germs; the
`LocalEquations.eqn_restrict_mem_nonZeroDivisors` pattern, freed of the carrier). -/
lemma Scheme.restriction_mem_nonZeroDivisors {V : X.Opens} {b : Γ(X, V)}
    (hb : ∀ (z : X) (hz : z ∈ V),
      (X.presheaf.germ V z hz).hom b ∈ nonZeroDivisors (X.presheaf.stalk z))
    {W : X.Opens} (hWV : W ≤ V) :
    (X.presheaf.map (homOfLE hWV).op).hom b ∈ nonZeroDivisors Γ(X, W) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro t ht
  apply TopCat.Presheaf.section_ext X.sheaf W t 0
  intro y hy
  rw [map_zero]
  have key : (X.presheaf.germ W y hy).hom t
      * (X.presheaf.germ W y hy).hom ((X.presheaf.map (homOfLE hWV).op).hom b) = 0 := by
    rw [← map_mul, ht, map_zero]
  rw [TopCat.Presheaf.germ_res_apply] at key
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff (hb y (hWV hy))).mp
    (by rw [mul_comm] at key; exact key)

/-- **Membership in a regular principal ideal is a stalkwise condition** (the `⊆` engine of
the DD-4 kernel bridge): if every germ of `b` on `V` is a nonzerodivisor and every germ of
`s` lies in the span of the corresponding germ of `b`, then `s ∈ (b) ⊆ Γ(X, V)`.  The local
cofactors are unique by regularity, hence compatible, hence glue by the sheaf property. -/
theorem Scheme.mem_span_singleton_of_forall_germ {V : X.Opens} {b s : Γ(X, V)}
    (hb : ∀ (z : X) (hz : z ∈ V),
      (X.presheaf.germ V z hz).hom b ∈ nonZeroDivisors (X.presheaf.stalk z))
    (h : ∀ (z : X) (hz : z ∈ V),
      (X.presheaf.germ V z hz).hom s
        ∈ Ideal.span {(X.presheaf.germ V z hz).hom b}) :
    s ∈ Ideal.span {b} := by
  -- local cofactors: on a neighbourhood of every point, `s = c · b`
  have key : ∀ z : {z : X // z ∈ V}, ∃ (W : X.Opens) (hWV : W ≤ V) (_ : z.1 ∈ W)
      (c : Γ(X, W)), (X.presheaf.map (homOfLE hWV).op).hom s
        = c * (X.presheaf.map (homOfLE hWV).op).hom b := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp (h z hz)
    obtain ⟨U, hUV, hzU, c, hc⟩ := X.presheaf.exists_le_germ_eq w hz
    have hgerm : (X.presheaf.germ U z hzU).hom ((X.presheaf.map (homOfLE hUV).op).hom s)
        = (X.presheaf.germ U z hzU).hom
            (c * (X.presheaf.map (homOfLE hUV).op).hom b) := by
      rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hc, hw,
        mul_comm]
    obtain ⟨W, hzW, iWU, iWU', heq⟩ := X.presheaf.germ_eq z hzU hzU _ _ hgerm
    rw [Subsingleton.elim iWU' iWU, show iWU = homOfLE iWU.le from Subsingleton.elim _ _]
      at heq
    rw [res_res, map_mul, res_res] at heq
    exact ⟨W, iWU.le.trans hUV, hzW, (X.presheaf.map (homOfLE iWU.le).op).hom c, heq⟩
  choose W hWV hzW c hc using key
  -- the cofactors agree on overlaps: their difference is killed by the regular `b`
  have hcompat : ∀ z y : {z : X // z ∈ V},
      (X.presheaf.map (homOfLE (inf_le_left : W z ⊓ W y ≤ W z)).op).hom (c z)
        = (X.presheaf.map (homOfLE (inf_le_right : W z ⊓ W y ≤ W y)).op).hom (c y) := by
    intro z y
    have hle : W z ⊓ W y ≤ V := inf_le_left.trans (hWV z)
    have hreg := Scheme.restriction_mem_nonZeroDivisors hb hle
    refine (mul_cancel_right_mem_nonZeroDivisors hreg).mp ?_
    have hL := congrArg (X.presheaf.map
      (homOfLE (inf_le_left : W z ⊓ W y ≤ W z)).op).hom (hc z)
    have hR := congrArg (X.presheaf.map
      (homOfLE (inf_le_right : W z ⊓ W y ≤ W y)).op).hom (hc y)
    rw [map_mul, res_res, res_res] at hL hR
    exact hL.symm.trans hR
  -- glue the cofactors
  obtain ⟨c₀, hc₀, -⟩ := X.sheaf.existsUnique_gluing'
    (fun z : {z : X // z ∈ V} => W z) V (fun z => homOfLE (hWV z))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hzW ⟨x, hx⟩⟩) c
    (fun z y => hcompat z y)
  -- retype the glued cofactor as a section and conclude `s = c₁ · b` by comparing germs
  obtain ⟨c₁, hc₀'⟩ : ∃ c₁ : Γ(X, V), ∀ z : {z : X // z ∈ V},
      (X.presheaf.map (homOfLE (hWV z)).op).hom c₁ = c z :=
    ⟨c₀, fun z => hc₀ z⟩
  have hs : s = c₁ * b := by
    apply TopCat.Presheaf.section_ext X.sheaf V
    intro z hz
    have h1 : (X.presheaf.germ V z hz).hom s
        = (X.presheaf.germ (W ⟨z, hz⟩) z (hzW ⟨z, hz⟩)).hom
            ((X.presheaf.map (homOfLE (hWV ⟨z, hz⟩)).op).hom s) :=
      (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    have h2 : (X.presheaf.germ V z hz).hom c₁
        = (X.presheaf.germ (W ⟨z, hz⟩) z (hzW ⟨z, hz⟩)).hom (c ⟨z, hz⟩) := by
      rw [← hc₀' ⟨z, hz⟩]
      exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    have h3 : (X.presheaf.germ V z hz).hom b
        = (X.presheaf.germ (W ⟨z, hz⟩) z (hzW ⟨z, hz⟩)).hom
            ((X.presheaf.map (homOfLE (hWV ⟨z, hz⟩)).op).hom b) :=
      (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    change (X.presheaf.germ V z hz).hom s = (X.presheaf.germ V z hz).hom (c₁ * b)
    rw [map_mul, h1, h2, h3, hc ⟨z, hz⟩, map_mul]
  exact Ideal.mem_span_singleton.mpr ⟨c₁, by rw [hs, mul_comm]⟩

end RegularSpan

/-! ## The stalk ideal of a local-equation system -/

namespace Scheme.LocalEquations

variable {X : Scheme.{u}}

/-- Two elements differing by a unit factor span the same ideal. -/
private lemma span_eq_of_unit_mul {S : Type u} [CommRing S] {a b c : S} (hc : IsUnit c)
    (h : a = c * b) : Ideal.span {a} = Ideal.span {b} := by
  obtain ⟨u, rfl⟩ := hc
  refine le_antisymm (Ideal.span_singleton_le_span_singleton.mpr ⟨u, by rw [h, mul_comm]⟩)
    (Ideal.span_singleton_le_span_singleton.mpr ⟨(↑u⁻¹ : S), ?_⟩)
  rw [h, mul_comm (u : S) b, mul_assoc, Units.mul_inv, mul_one]

/-- **The stalk ideal of a local-equation system at a point**: the span of the germ of the
equation at the tautological covering member.  This is `I_D ⊆ 𝒪_{X,z}`, the
cover-independent trace of the divisor (`germ_eqn_span_eq`). -/
noncomputable def stalkIdeal (d : X.LocalEquations) (z : X) :
    Ideal (X.presheaf.stalk z) :=
  Ideal.span {(X.presheaf.germ (d.cover.opens z) z (d.cover.mem_opens z)).hom (d.eqn z)}

/-- **Cover-independence of the stalk ideal**: the germ of the equation at *any* covering
member containing `z` spans the stalk ideal — the unit ratios of the system rescale the
generators into each other. -/
theorem germ_eqn_span_eq (d : X.LocalEquations) (x z : X) (hz : z ∈ d.cover.opens x) :
    Ideal.span {(X.presheaf.germ (d.cover.opens x) z hz).hom (d.eqn x)}
      = d.stalkIdeal z := by
  have hz' : z ∈ d.cover.opens x ⊓ d.cover.opens z := ⟨hz, d.cover.mem_opens z⟩
  have h := congrArg (X.presheaf.germ (d.cover.opens x ⊓ d.cover.opens z) z hz').hom
    (d.eqn_restrict_eq x z)
  rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
  exact span_eq_of_unit_mul ((d.ratioUnit x z).isUnit.map
    (X.presheaf.germ (d.cover.opens x ⊓ d.cover.opens z) z hz').hom) h

/-- **Divisor equality preserves the stalk ideals**: on the common refinement the
equations differ by a unit at every point, so their germs are associated. -/
theorem stalkIdeal_eq_of_divEq {d₁ d₂ : X.LocalEquations} (h : d₁.DivEq d₂) (z : X) :
    d₁.stalkIdeal z = d₂.stalkIdeal z := by
  obtain ⟨𝒲, h₁, h₂, H⟩ := h
  obtain ⟨u, hu⟩ := H z
  have hgerm := congrArg (X.presheaf.germ (𝒲.opens z) z (𝒲.mem_opens z)).hom hu
  rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hgerm
  calc d₁.stalkIdeal z
      = Ideal.span {(X.presheaf.germ (d₁.cover.opens z) z
          (h₁ z (𝒲.mem_opens z))).hom (d₁.eqn z)} :=
        (germ_eqn_span_eq d₁ z z _).symm
    _ = Ideal.span {(X.presheaf.germ (d₂.cover.opens z) z
          (h₂ z (𝒲.mem_opens z))).hom (d₂.eqn z)} :=
        span_eq_of_unit_mul (u.isUnit.map
          (X.presheaf.germ (𝒲.opens z) z (𝒲.mem_opens z)).hom) hgerm
    _ = d₂.stalkIdeal z := germ_eqn_span_eq d₂ z z _

end Scheme.LocalEquations

/-! ## The vanishing submodule of global twisted sections -/

section Vanishing

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
variable (V₀ V₁ : X.Opens) (g : Γ(X, V₀ ⊓ V₁)ˣ)

/-- **The vanishing submodule of a local-equation system** inside the global sections of a
two-cover twisted sheaf: the pairs whose chart components have all their germs in the
stalk ideals of `d`.  This is the DD-4 spelling of `H⁰(𝒪(Θᴬ − d)) ⊆ H⁰(𝒪(Θᴬ))`; it depends
only on the divisor of `d` (`vanishingSubmodule_eq_of_divEq`), not on any adaptation —
the kernel bridge to the Θ-twisted colength evaluation is
`AlgebraicJacobian.Picard.DivisorFamilyTheta`. -/
noncomputable def Scheme.LocalEquations.vanishingSubmodule (d : X.LocalEquations) :
    Submodule k ↥(twistSubmodule k V₀ V₁ g ⊤) where
  carrier := {x | (∀ (z : X) (hz : z ∈ ⊤ ⊓ V₀),
      (X.presheaf.germ (⊤ ⊓ V₀) z hz).hom x.val.1 ∈ d.stalkIdeal z) ∧
    ∀ (z : X) (hz : z ∈ ⊤ ⊓ V₁),
      (X.presheaf.germ (⊤ ⊓ V₁) z hz).hom x.val.2 ∈ d.stalkIdeal z}
  add_mem' := by
    rintro x y ⟨hx₀, hx₁⟩ ⟨hy₀, hy₁⟩
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · rw [Submodule.coe_add, Prod.fst_add, map_add]
      exact Ideal.add_mem _ (hx₀ z hz) (hy₀ z hz)
    · rw [Submodule.coe_add, Prod.snd_add, map_add]
      exact Ideal.add_mem _ (hx₁ z hz) (hy₁ z hz)
  zero_mem' := by
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩ <;>
      simp only [Submodule.coe_zero, Prod.fst_zero, Prod.snd_zero, map_zero] <;>
      exact Ideal.zero_mem _
  smul_mem' := by
    rintro r x ⟨hx₀, hx₁⟩
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · rw [Submodule.coe_smul, Prod.smul_fst, Scheme.overModule_smul_def, map_mul]
      exact Ideal.mul_mem_left _ _ (hx₀ z hz)
    · rw [Submodule.coe_smul, Prod.smul_snd, Scheme.overModule_smul_def, map_mul]
      exact Ideal.mul_mem_left _ _ (hx₁ z hz)

variable {V₀ V₁ g}

lemma Scheme.LocalEquations.mem_vanishingSubmodule_iff {d : X.LocalEquations}
    {x : ↥(twistSubmodule k V₀ V₁ g ⊤)} :
    x ∈ d.vanishingSubmodule k V₀ V₁ g ↔
      (∀ (z : X) (hz : z ∈ ⊤ ⊓ V₀),
        (X.presheaf.germ (⊤ ⊓ V₀) z hz).hom x.val.1 ∈ d.stalkIdeal z) ∧
      ∀ (z : X) (hz : z ∈ ⊤ ⊓ V₁),
        (X.presheaf.germ (⊤ ⊓ V₁) z hz).hom x.val.2 ∈ d.stalkIdeal z :=
  Iff.rfl

/-- **Setoid-readiness of the window submodule** (worksheet §2.3.4): divisor equality of
the local-equation systems does not move the vanishing submodule. -/
theorem Scheme.LocalEquations.vanishingSubmodule_eq_of_divEq {d₁ d₂ : X.LocalEquations}
    (h : d₁.DivEq d₂) :
    d₁.vanishingSubmodule k V₀ V₁ g = d₂.vanishingSubmodule k V₀ V₁ g := by
  ext x
  simp only [mem_vanishingSubmodule_iff, stalkIdeal_eq_of_divEq h]

end Vanishing

end AlgebraicGeometry
