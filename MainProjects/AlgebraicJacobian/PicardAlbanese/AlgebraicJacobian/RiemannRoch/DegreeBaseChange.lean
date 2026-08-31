/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.TransitionSectionsBaseChange
import AlgebraicJacobian.RiemannRoch.ChartColength

/-!
# The fiber-degree identity along the base-field transition (gap G-D5(b), SB-4)

For the challenge curve `C : Over (Spec k)`, a `k`-algebra map `φ : K₁ →ₐ[k] K₂` of field
extensions of `k`, and the base-field transition
`π := (C ◁ Over.overSpecMap φ).left : C_{K₂} ⟶ C_{K₁}`, this file proves the
**fiber-degree identity (†)** of `informal/deg-d5b-worksheet.md` §2: for an affine chart
`V ∋ η, x'` of `C_{K₁}` carrying a section `t` that is a unit at every closed point of `V`
other than `x'`,

`∑_{x''} ord_{x''}(π^♯ t) · [κ(x'') : K₂]  =  ord_{x'}(t) · [κ(x') : K₁]`  (†)

where the sum ranges over any finite set `S` of closed points of `π ⁻¹ᵁ V` outside which the
pulled-back section `π^♯ t` is a unit — the hypotheses force such an `S` to exhaust the
non-unit locus of `π^♯ t`, which is contained in the fiber `π⁻¹(x')`, so `S` plays the role
of the fiber and all other terms vanish.  Specialized to the tracked point uniformizer
(`ord_{x'}(t) = 1`) this is the worksheet's display (†); the E-iv-alg ladder
(`AlgebraicJacobian.RiemannRoch.DegreeBaseFieldInvariance`) consumes it in exactly this
`Finset`-parameterized form.

## Assembly (worksheet §2, all on one affine chart)

* the **chart colength dictionary** (SB-3, `AlgebraicJacobian.RiemannRoch.ChartColength`)
  fired at both ends: at `K₁` the vanishing set is `{x'}`, at `K₂` it is `S`;
* the **sections base change** (SB-2,
  `AlgebraicJacobian.Cohomology.TransitionSectionsBaseChange`):
  `Γ(C_{K₁}, V) ⊗[K₁] K₂ ≃+* Γ(C_{K₂}, π ⁻¹ᵁ V)` sending `t ⊗ 1` to `π^♯ t`;
* right-exactness of the tensor product
  (`Algebra.TensorProduct.tensorQuotientEquiv`): `(B₁ ⧸ (t)) ⊗[K₁] K₂ ≅ B₂ ⧸ (π^♯ t)`;
* invariance of dimension under base field extension (`Module.finrank_baseChange`).

The `K`-algebra structure on sections is `Scheme.overSectionsAlgebra` (the SB-3 convention),
which agrees definitionally with the SB-2 convention `baseChangeSectionsAlgebra`
(`baseChangeSectionsAlgebra_eq_overSectionsAlgebra`).  The interface statement (†) mentions
neither algebra structure, so its consumers need no local instances.

## Main declarations

* `AlgebraicGeometry.classDeg_zpow` — `classDeg K (L ^ n) = n * classDeg K L`, a small
  addition to the `classDeg` toolkit consumed by the E-iv-alg generator reduction.
* `AlgebraicGeometry.baseChangeSectionsAlgebra_eq_overSectionsAlgebra` — the SB-2/SB-3
  algebra-structure seam, closed by `rfl`.
* `AlgebraicGeometry.sum_ordZ_residueDeg_baseFieldTransition` — the identity (†).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TensorProduct
open Module (finrank)

namespace AlgebraicGeometry

/-! ## The degree of a power of a class

A small addition to the `classDeg` toolkit of `RiemannRoch/Degree.lean`, consumed by the
generator reduction of E-iv-alg. -/

/-- The degree of an integer power of a Čech Picard class: `classDeg (L ^ n) = n · classDeg L`. -/
theorem classDeg_zpow (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    [Module.Finite K (CategoryTheory.Sheaf.HModule (X.moduleKSheaf K) 0)]
    [Module.Finite K (CategoryTheory.Sheaf.HModule (X.moduleKSheaf K) 1)]
    (L : X.CechPic) (n : ℤ) :
    classDeg K (L ^ n) = n * classDeg K L := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, classDeg_one, zero_mul]
  | succ i ih =>
    rw [zpow_add_one, classDeg_mul, ih]
    ring
  | pred i ih =>
    rw [zpow_sub_one, classDeg_mul, ih, classDeg_inv]
    ring

attribute [local instance] Scheme.overSectionsAlgebra Scheme.residueFieldOverModule

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  {K₁ K₂ : Type u} [Field K₁] [Algebra k K₁] [Field K₂] [Algebra k K₂]

/-! ## The algebra-structure seam between SB-2 and SB-3

SB-2 (`TransitionSectionsBaseChange`) states its comparison isomorphism for the
second-projection algebra structure `baseChangeSectionsAlgebra`; the colength dictionary
SB-3 (`ChartColength`) speaks `Scheme.overSectionsAlgebra` through the `Over`-instance
`instOverBaseChange`, whose structure morphism is the same second projection
(`baseChange_over_eq_snd_left` is `rfl`).  The two algebra structures are definitionally
equal; we record the seam once, so that the bridge below may freely combine the two
vocabularies. -/

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- The SB-2 algebra structure on sections of the base-changed curve is definitionally the
SB-3 one: both are restriction of scalars along `ΓSpecIso.inv ≫ (snd C _).left.app`. -/
lemma baseChangeSectionsAlgebra_eq_overSectionsAlgebra (K : Type u) [Field K] [Algebra k K]
    (V : (C ⊗ overSpec k K).left.Opens) :
    baseChangeSectionsAlgebra C K V
      = Scheme.overSectionsAlgebra K (C ⊗ overSpec k K).left V :=
  rfl

/-! ## The colength bridge

`finrank K₂ (B₂ ⧸ (π^♯ t)) = finrank K₁ (B₁ ⧸ (t))` for an affine chart `V` with
`B₁ := Γ(C_{K₁}, V)` and `B₂ := Γ(C_{K₂}, π ⁻¹ᵁ V)`.  Proved in the scalar-tower situation
and consumed for a general `φ` through the `RingHom.toAlgebra`/`IsScalarTower` bridge of the
SB-2 consumer notes (the hypothesis `hφ` is discharged by `AlgHom.ext fun _ => rfl`). -/

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
private theorem finrank_quotient_span_transitionSection
    [Algebra K₁ K₂] [IsScalarTower k K₁ K₂] (φ : K₁ →ₐ[k] K₂)
    (hφ : IsScalarTower.toAlgHom k K₁ K₂ = φ)
    {V : (C ⊗ overSpec k K₁).left.Opens} (hV : IsAffineOpen V)
    (t : Γ((C ⊗ overSpec k K₁).left, V)) :
    finrank K₂ (Γ((C ⊗ overSpec k K₂).left, (C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) ⧸
        Ideal.span {((C ◁ Over.overSpecMap φ).left.appLE V
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) le_rfl).hom t})
      = finrank K₁ (Γ((C ⊗ overSpec k K₁).left, V) ⧸ Ideal.span {t}) := by
  subst hφ
  -- the SB-2 comparison isomorphism, flipped to put `K₂` in the left tensor factor
  set e := Over.transitionSectionsBaseChange C (K₂ := K₂) hV with he
  set e' : K₂ ⊗[K₁] Γ((C ⊗ overSpec k K₁).left, V) ≃+*
      Γ((C ⊗ overSpec k K₂).left,
        (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V) :=
    (Algebra.TensorProduct.comm K₁ K₂ Γ((C ⊗ overSpec k K₁).left, V)).toRingEquiv.trans e
    with he'
  -- `e'` is a `K₂`-algebra isomorphism
  have he'alg : ∀ c : K₂,
      e' (algebraMap K₂ (K₂ ⊗[K₁] Γ((C ⊗ overSpec k K₁).left, V)) c)
        = algebraMap K₂ Γ((C ⊗ overSpec k K₂).left,
            (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V) c := by
    intro c
    have h1 : e' (algebraMap K₂ (K₂ ⊗[K₁] Γ((C ⊗ overSpec k K₁).left, V)) c)
        = e ((1 : Γ((C ⊗ overSpec k K₁).left, V)) ⊗ₜ[K₁] c) := by
      rw [he', RingEquiv.trans_apply]
      congr 1
    rw [h1, Over.transitionSectionsBaseChange_one_tmul C hV c]
    exact (congr($(ofHom_algebraMap_baseChangeSections C K₂
      ((C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V)).hom c)).symm
  set e'' := AlgEquiv.ofRingEquiv (R := K₂) (f := e') he'alg with he''
  -- transport of the principal ideal along `e''`
  have hval : e'' ((1 : K₂) ⊗ₜ[K₁] t)
      = ((C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left.appLE V
          ((C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V) le_rfl).hom
        t := by
    have h1 : e'' ((1 : K₂) ⊗ₜ[K₁] t) = e (t ⊗ₜ[K₁] (1 : K₂)) := by
      rw [he'']
      change e' ((1 : K₂) ⊗ₜ[K₁] t) = e (t ⊗ₜ[K₁] (1 : K₂))
      rw [he', RingEquiv.trans_apply]
      congr 1
    rw [h1, he]
    exact Over.transitionSectionsBaseChange_tmul_one C hV t
  have hIJ : Ideal.span {((C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left.appLE
        V ((C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V) le_rfl).hom t}
      = (Ideal.span {(1 : K₂) ⊗ₜ[K₁] t}).map (e'' : _ →+* _) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    rw [← hval]
    rfl
  -- the ideal of the tensor-quotient equivalence is the same principal ideal
  have hmap : (Ideal.span {t}).map
        (Algebra.TensorProduct.includeRight (R := K₁) (A := K₂)
          (B := Γ((C ⊗ overSpec k K₁).left, V)))
      = Ideal.span {(1 : K₂) ⊗ₜ[K₁] t} := by
    rw [Ideal.map_span, Set.image_singleton, Algebra.TensorProduct.includeRight_apply]
  -- the three dimension transports
  have hq1 : finrank K₂ ((K₂ ⊗[K₁] Γ((C ⊗ overSpec k K₁).left, V)) ⧸
        Ideal.span {(1 : K₂) ⊗ₜ[K₁] t})
      = finrank K₂ (Γ((C ⊗ overSpec k K₂).left,
          (C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V) ⧸
        Ideal.span {((C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left.appLE V
          ((C ◁ Over.overSpecMap (IsScalarTower.toAlgHom k K₁ K₂)).left ⁻¹ᵁ V) le_rfl).hom
          t}) :=
    (Ideal.quotientEquivAlg _ _ e'' hIJ).toLinearEquiv.finrank_eq
  have hq2 : finrank K₂ (K₂ ⊗[K₁] (Γ((C ⊗ overSpec k K₁).left, V) ⧸ Ideal.span {t}))
      = finrank K₂ ((K₂ ⊗[K₁] Γ((C ⊗ overSpec k K₁).left, V)) ⧸
          Ideal.span {(1 : K₂) ⊗ₜ[K₁] t}) :=
    ((Algebra.TensorProduct.tensorQuotientEquiv (R := K₁) K₂
        Γ((C ⊗ overSpec k K₁).left, V) K₂ (Ideal.span {t})).trans
      (Ideal.quotientEquivAlgOfEq K₂ hmap)).toLinearEquiv.finrank_eq
  have hbc : finrank K₂ (K₂ ⊗[K₁] (Γ((C ⊗ overSpec k K₁).left, V) ⧸ Ideal.span {t}))
      = finrank K₁ (Γ((C ⊗ overSpec k K₁).left, V) ⧸ Ideal.span {t}) :=
    Module.finrank_baseChange
  omega

/-! ## The fiber-degree identity -/

omit [IsProper C.hom] in
/-- **The fiber-degree identity (†)** (worksheet §2, SB-4): let `V` be an affine chart of
the base-changed curve `C_{K₁}` containing the generic point, `t` a section of `V` whose
germ at `η` underlies the unit `g : K(C_{K₁})ˣ` and which is a unit at every closed point
of `V` other than `x' ∈ V`, and let `S` be a finite set of closed points of `π ⁻¹ᵁ V`
outside which the pulled-back section `π^♯ t` is a unit on `π ⁻¹ᵁ V`, where
`π := (C ◁ Over.overSpecMap φ).left` is the base-field transition.  Then

`∑_{x'' ∈ S} ord_{x''}(π^♯ g) · [κ(x'') : K₂] = ord_{x'}(g) · [κ(x') : K₁]`.

The hypotheses force `S` to exhaust the non-unit locus of `π^♯ t` on the chart, which is
contained in the fiber `π⁻¹(x')` (unit germs pull back to unit germs), so `S` is the fiber
up to terms of order zero.  Assembled from the chart colength dictionary at both ends, the
sections base change `Γ(C_{K₁}, V) ⊗[K₁] K₂ ≃+* Γ(C_{K₂}, π ⁻¹ᵁ V)`, right-exactness of
the tensor product, and `Module.finrank_baseChange`. -/
theorem sum_ordZ_residueDeg_baseFieldTransition (φ : K₁ →ₐ[k] K₂)
    {V : (C ⊗ overSpec k K₁).left.Opens} (hV : IsAffineOpen V)
    (hη : genericPoint (C ⊗ overSpec k K₁).left ∈ V)
    {t : Γ((C ⊗ overSpec k K₁).left, V)} (g : (C ⊗ overSpec k K₁).left.functionFieldˣ)
    (hg : (g : (C ⊗ overSpec k K₁).left.functionField)
      = ((C ⊗ overSpec k K₁).left.presheaf.germ V
          (genericPoint (C ⊗ overSpec k K₁).left) hη).hom t)
    {x' : (C ⊗ overSpec k K₁).left} (hx' : x' ≠ genericPoint (C ⊗ overSpec k K₁).left)
    (hx'V : x' ∈ V)
    (hunit : ∀ (z : (C ⊗ overSpec k K₁).left) (hz : z ∈ V), z ≠ x' →
      IsUnit (((C ⊗ overSpec k K₁).left.presheaf.germ V z hz).hom t))
    (S : Finset {y : (C ⊗ overSpec k K₂).left // y ≠ genericPoint (C ⊗ overSpec k K₂).left})
    (hSV : ∀ p ∈ S, p.1 ∈ (C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V)
    (hout : ∀ (z : (C ⊗ overSpec k K₂).left)
      (hz : z ∈ (C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V)
      (hzg : z ≠ genericPoint (C ⊗ overSpec k K₂).left),
      (⟨z, hzg⟩ : {y : (C ⊗ overSpec k K₂).left //
          y ≠ genericPoint (C ⊗ overSpec k K₂).left}) ∉ S →
      IsUnit (((C ⊗ overSpec k K₂).left.presheaf.germ
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) z hz).hom
        (((C ◁ Over.overSpecMap φ).left.appLE V
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) le_rfl).hom t))) :
    ∑ p ∈ S, Multiplicative.toAdd
        (Scheme.ordZ ((C ⊗ overSpec k K₂).left ↘ Spec (CommRingCat.of K₂)) p.2
          ((C ◁ Over.overSpecMap φ).left.functionFieldMapUnits
            (baseFieldTransition_genericPoint C φ) g))
        * ((C ⊗ overSpec k K₂).left.residueDeg K₂ p.1 : ℤ)
      = Multiplicative.toAdd
          (Scheme.ordZ ((C ⊗ overSpec k K₁).left ↘ Spec (CommRingCat.of K₁)) hx' g)
          * ((C ⊗ overSpec k K₁).left.residueDeg K₁ x' : ℤ) := by
  classical
  have hπη : ((C ◁ Over.overSpecMap φ).left).base
        (genericPoint (C ⊗ overSpec k K₂).left)
      = genericPoint (C ⊗ overSpec k K₁).left := baseFieldTransition_genericPoint C φ
  have hη₂ : genericPoint (C ⊗ overSpec k K₂).left
      ∈ (C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V := by
    change ((C ◁ Over.overSpecMap φ).left).base (genericPoint (C ⊗ overSpec k K₂).left) ∈ V
    rw [hπη]; exact hη
  have hV₂ : IsAffineOpen ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) :=
    hV.preimage (C ◁ Over.overSpecMap φ).left
  -- the pulled-back unit trivializes the pulled-back section at `η`
  have happ : ((C ◁ Over.overSpecMap φ).left.appLE V
        ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) le_rfl)
      = (C ◁ Over.overSpecMap φ).left.app V := Scheme.Hom.appLE_eq_app _
  have hg₂ : (((C ◁ Over.overSpecMap φ).left.functionFieldMapUnits hπη g :
        (C ⊗ overSpec k K₂).left.functionFieldˣ) :
        (C ⊗ overSpec k K₂).left.functionField)
      = ((C ⊗ overSpec k K₂).left.presheaf.germ
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V)
          (genericPoint (C ⊗ overSpec k K₂).left) hη₂).hom
        (((C ◁ Over.overSpecMap φ).left.appLE V
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) le_rfl).hom t) := by
    rw [Scheme.Hom.coe_functionFieldMapUnits, hg,
      (C ◁ Over.overSpecMap φ).left.functionFieldMap_germ hπη V hη hη₂ t, happ]
  -- the colength dictionary at `K₂`
  have hK₂ := finrank_quotient_span_section K₂ hV₂ hη₂
    ((C ◁ Over.overSpecMap φ).left.functionFieldMapUnits hπη g) hg₂ S hSV hout
  -- the colength dictionary at `K₁`, at the singleton `{x'}`
  have hK₁ := finrank_quotient_span_section K₁ hV hη g hg
    ({⟨x', hx'⟩} : Finset {x : (C ⊗ overSpec k K₁).left //
      x ≠ genericPoint (C ⊗ overSpec k K₁).left})
    (fun p hp => by rw [Finset.mem_singleton] at hp; rw [hp]; exact hx'V)
    (fun z hz hzg hzS => hunit z hz (fun hzx => hzS (by
      rw [Finset.mem_singleton]; exact Subtype.ext hzx)))
  rw [Finset.sum_singleton] at hK₁
  -- the colength bridge
  letI : Algebra K₁ K₂ := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k K₁ K₂ :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have hbr := finrank_quotient_span_transitionSection C φ (AlgHom.ext fun _ => rfl) hV t
  rw [← hK₂, ← hK₁, hbr]

end AlgebraicGeometry
