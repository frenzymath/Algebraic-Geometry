/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RigidEngine4Engine
import AlgebraicJacobian.Cohomology.RelativeH1BaseChange

/-!
# RE-4 — the ring-map base-change clause, threaded through CBC-1

The last clause of the worksheet's Level-2 statement
(`informal/w4-rigid-engine-worksheet.md` §1.2, `rigidEngine_baseChange`): on the
vanishing locus, formation of the twisted `H⁰` commutes **on the nose** with every
test-ring change `R → R'`, and the twisted `H¹` vanishes after base change.

The abstract half (`relTwistH0BaseChangeEquiv`, `RigidEngine4Engine`) lands in the kernel
of the base-changed Čech differential; this file threads it through the landed CBC-1 term
identifications (`relTwistTermBaseChange₀/₁`, `relTwistOverlapBaseChange`,
`RelativeH1BaseChange`) onto `H⁰` of the base-changed sheaf. The one genuinely new
ingredient is **the twisted δ-naturality square** (`relTwistPairDiffBaseChange`) — the
cocycle-conjugated analogue of the landed `relDiffBaseChange`, the frontier recorded in
`RelativeH1BaseChange`'s module docstring: in trivialized coordinates the twisted
differential is `(s₀, s₁) ↦ s₀|ov − g · s₁|ov` (`twistTriv₀_pairDiff`), and the square is
the same `relSectionsMap` bookkeeping with the extra `g`-factor carried through
`map_mul` and `relCocycleBaseChange`.

## Main declarations

* `twistTriv₀_pairDiff` — the twisted Čech differential in trivialized coordinates.
* `relTwistDomBaseChange` — CBC-1 for the degree-zero term of the twisted complex.
* `relTwistPairDiffBaseChange` — **the twisted δ-naturality square**.
* `relTwistH0BaseChange` — **`H⁰` base change on the nose**:
  `R' ⊗[R] H⁰(C_R, F_g) ≃ₗ[R'] H⁰(C_{R'}, F_{g'})` on the vanishing locus, for every
  test-ring change `R → R'` (`g' = relCocycleBaseChange g`).
* `relTwist_subsingleton_h1_baseChange` — **`H¹` vanishes after base change**:
  `Subsingleton H¹(C_{R'}, F_{g'})` on the vanishing locus.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

/-! ## The twisted differential in trivialized coordinates -/

section Trivialized

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
variable (V₀ V₁ : X.Opens) (g : Γ(X, V₀ ⊓ V₁)ˣ)

/-- **The twisted Čech differential in trivialized coordinates**: under the chart-0
trivialization of the overlap, `(p₀, p₁) ↦ p₀|ov − p₁|ov` becomes
`(s₀, s₁) ↦ s₀|ov − g · s₁|ov` (the `twistDefect` shape). -/
lemma twistTriv₀_pairDiff (p₀ : ↥(twistSubmodule k V₀ V₁ g V₀))
    (p₁ : ↥(twistSubmodule k V₀ V₁ g V₁)) :
    twistTriv₀ k V₀ V₁ g (inf_le_left : V₀ ⊓ V₁ ≤ V₀)
        (secRes (twistSheaf k V₀ V₁ g) (inf_le_left : V₀ ⊓ V₁ ≤ V₀) p₀
          - secRes (twistSheaf k V₀ V₁ g) (inf_le_right : V₀ ⊓ V₁ ≤ V₁) p₁)
      = X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀)
            (twistTriv₀ k V₀ V₁ g (le_refl V₀) p₀)
        - (g : Γ(X, V₀ ⊓ V₁)) *
            X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁)
              (twistTriv₁ k V₀ V₁ g (le_refl V₁) p₁) := by
  rw [map_sub, secRes_twistSheaf, secRes_twistSheaf]
  congr 1
  · exact twistTriv₀_res k V₀ V₁ g inf_le_left (le_refl V₀) p₀
  · rw [twistTriv₀_inf_eq]
    exact congrArg (fun y => (g : Γ(X, V₀ ⊓ V₁)) * y)
      (twistTriv₁_res k V₀ V₁ g inf_le_right (le_refl V₁) p₁)

end Trivialized

/-! ## CBC-1 for the twisted complex -/

section Square

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable (D : C.left.AffineTwoCover)
variable (g : Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁)ˣ)

/-- CBC-1 for the degree-zero term of the twisted complex: the product of the two
twisted chart-term equivalences. -/
noncomputable def relTwistDomBaseChange :
    R' ⊗[R] (↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
        (relCover C R D).V₀) ×
      ↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
        (relCover C R D).V₁)) ≃ₗ[R']
      ↥(twistSubmodule R' (relCover C R' D).V₀ (relCover C R' D).V₁
          (relCocycleBaseChange C R R' D g) (relCover C R' D).V₀) ×
        ↥(twistSubmodule R' (relCover C R' D).V₀ (relCover C R' D).V₁
          (relCocycleBaseChange C R R' D g) (relCover C R' D).V₁) :=
  (TensorProduct.prodRight R R' R' _ _).trans
    ((relTwistTermBaseChange₀ C R R' D g).prodCongr (relTwistTermBaseChange₁ C R R' D g))

/-- The chart-0 twisted term base change, in trivialized coordinates on a pure tensor. -/
lemma twistTriv₀_relTwistTermBaseChange₀ (r' : R')
    (p : ↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
      (relCover C R D).V₀)) :
    twistTriv₀ R' (relCover C R' D).V₀ (relCover C R' D).V₁
        (relCocycleBaseChange C R R' D g) (le_refl (relCover C R' D).V₀)
        (relTwistTermBaseChange₀ C R R' D g (r' ⊗ₜ p))
      = r' • relSectionsMap C R R' D.V₀
          (twistTriv₀ R (relCover C R D).V₀ (relCover C R D).V₁ g
            (le_refl (relCover C R D).V₀) p) := by
  rw [relTwistTermBaseChange₀, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.trans_apply]
  have happ := (twistTriv₀ R' (relCover C R' D).V₀ (relCover C R' D).V₁
    (relCocycleBaseChange C R R' D g)
    (le_refl (relCover C R' D).V₀)).apply_symm_apply
    (relTermBaseChange C R R' D.V₀ D.isAffineOpen₀.isCompact
      D.isAffineOpen₀.isQuasiSeparated
      (r' ⊗ₜ (twistTriv₀ R (relCover C R D).V₀ (relCover C R D).V₁ g le_rfl p)))
  exact happ.trans (relTermBaseChange_tmul C R R' D.isAffineOpen₀.isCompact
    D.isAffineOpen₀.isQuasiSeparated r'
    (twistTriv₀ R (relCover C R D).V₀ (relCover C R D).V₁ g le_rfl p))

/-- The chart-1 twisted term base change, in trivialized coordinates on a pure tensor. -/
lemma twistTriv₁_relTwistTermBaseChange₁ (r' : R')
    (p : ↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
      (relCover C R D).V₁)) :
    twistTriv₁ R' (relCover C R' D).V₀ (relCover C R' D).V₁
        (relCocycleBaseChange C R R' D g) (le_refl (relCover C R' D).V₁)
        (relTwistTermBaseChange₁ C R R' D g (r' ⊗ₜ p))
      = r' • relSectionsMap C R R' D.V₁
          (twistTriv₁ R (relCover C R D).V₀ (relCover C R D).V₁ g
            (le_refl (relCover C R D).V₁) p) := by
  rw [relTwistTermBaseChange₁, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.trans_apply]
  have happ := (twistTriv₁ R' (relCover C R' D).V₀ (relCover C R' D).V₁
    (relCocycleBaseChange C R R' D g)
    (le_refl (relCover C R' D).V₁)).apply_symm_apply
    (relTermBaseChange C R R' D.V₁ D.isAffineOpen₁.isCompact
      D.isAffineOpen₁.isQuasiSeparated
      (r' ⊗ₜ (twistTriv₁ R (relCover C R D).V₀ (relCover C R D).V₁ g le_rfl p)))
  exact happ.trans (relTermBaseChange_tmul C R R' D.isAffineOpen₁.isCompact
    D.isAffineOpen₁.isQuasiSeparated r'
    (twistTriv₁ R (relCover C R D).V₀ (relCover C R D).V₁ g le_rfl p))

/-- The overlap twisted term base change, in trivialized coordinates on a pure tensor. -/
lemma twistTriv₀_relTwistOverlapBaseChange (r' : R')
    (q : ↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
      ((relCover C R D).V₀ ⊓ (relCover C R D).V₁))) :
    twistTriv₀ R' (relCover C R' D).V₀ (relCover C R' D).V₁
        (relCocycleBaseChange C R R' D g)
        (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
          (relCover C R' D).V₀)
        (relTwistOverlapBaseChange C R R' D g (r' ⊗ₜ q))
      = r' • relSectionsMap C R R' (D.V₀ ⊓ D.V₁)
          (twistTriv₀ R (relCover C R D).V₀ (relCover C R D).V₁ g
            (inf_le_left : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
              (relCover C R D).V₀) q) := by
  rw [relTwistOverlapBaseChange, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.trans_apply]
  have happ := (twistTriv₀ R' (relCover C R' D).V₀ (relCover C R' D).V₁
    (relCocycleBaseChange C R R' D g)
    (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
      (relCover C R' D).V₀)).apply_symm_apply
    (relDiffCodBaseChange C R R' D
      (r' ⊗ₜ (twistTriv₀ R (relCover C R D).V₀ (relCover C R D).V₁ g inf_le_left q)))
  exact happ.trans (relDiffCodBaseChange_tmul C R R' D r'
    (twistTriv₀ R (relCover C R D).V₀ (relCover C R D).V₁ g inf_le_left q))

/-- (Implementation) Restriction to the overlap commutes with the `R'`-action on the
base-changed relative curve. -/
private lemma resHom_smul_rel {W V : (relCurve C R').Opens} (h : W ≤ V) (r' : R')
    (y : Γ(relCurve C R', V)) :
    (relCurve C R').resHom h (r' • y) = r' • (relCurve C R').resHom h y := by
  rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
  congr 1
  exact (relCurve C R').overAlgebraMap_apply_res R' (homOfLE h).op r'

/-- (Implementation) The cocycle comparison: the base-changed cocycle is the image of
the cocycle under the sections comparison map. -/
private lemma relCocycleBaseChange_coe :
    ((relCocycleBaseChange C R R' D g : Γ(relCurve C R',
        (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁)ˣ) :
      Γ(relCurve C R', (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁))
      = relSectionsMap C R R' (D.V₀ ⊓ D.V₁)
          ((g : Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁))) := rfl

set_option synthInstance.maxHeartbeats 400000 in
-- The instance searches through the `relCurve`/product spellings of the section modules
-- exceed the default limit (same reason as the landed `relDiffBaseChange`).
/-- The twisted two-cover restriction-difference map — the Čech differential of the
two-lattice pair of the twisted sheaf, in the pair-free spelling used by the base-change
square (`(relTwistPair _).diff` is definitionally this map). -/
noncomputable def relTwistDiff :
    (↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
        (relCover C R D).V₀) ×
      ↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
        (relCover C R D).V₁)) →ₗ[R]
      ↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
        ((relCover C R D).V₀ ⊓ (relCover C R D).V₁)) :=
  (secRes (twistSheaf R (relCover C R D).V₀ (relCover C R D).V₁ g)
      (inf_le_left : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
        (relCover C R D).V₀)).comp (LinearMap.fst R _ _)
    - (secRes (twistSheaf R (relCover C R D).V₀ (relCover C R D).V₁ g)
        (inf_le_right : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
          (relCover C R D).V₁)).comp (LinearMap.snd R _ _)

/-- The twisted differential elementwise. -/
lemma relTwistDiff_apply
    (p : ↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
        (relCover C R D).V₀) ×
      ↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
        (relCover C R D).V₁)) :
    relTwistDiff C R D g p
      = secRes (twistSheaf R (relCover C R D).V₀ (relCover C R D).V₁ g)
          (inf_le_left : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
            (relCover C R D).V₀) p.1
        - secRes (twistSheaf R (relCover C R D).V₀ (relCover C R D).V₁ g)
            (inf_le_right : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
              (relCover C R D).V₁) p.2 := rfl

set_option maxHeartbeats 1000000 in
-- The `respectTransparency false` defeq checks through the `relCurve`/product spellings
-- make elaboration exceed the default limit, as in the landed `relDiffBaseChange` ...
set_option synthInstance.maxHeartbeats 400000 in
-- ... and the instance searches on the large tensor types exceed the default limit.
/-- **The twisted δ-naturality square** (the cocycle-conjugated analogue of the landed
`relDiffBaseChange`; the frontier recorded in `RelativeH1BaseChange`): the base change of
the twisted Čech differential over `R` is carried to the twisted Čech differential over
`R'` under the CBC-1 term identifications. -/
theorem relTwistDiffBaseChange
    (x : R' ⊗[R] (↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
        (relCover C R D).V₀) ×
      ↥(twistSubmodule R (relCover C R D).V₀ (relCover C R D).V₁ g
        (relCover C R D).V₁))) :
    relTwistOverlapBaseChange C R R' D g ((relTwistDiff C R D g).baseChange R' x)
      = relTwistDiff C R' D (relCocycleBaseChange C R R' D g)
          (relTwistDomBaseChange C R R' D g x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r' p =>
    apply (twistTriv₀ R' (relCover C R' D).V₀ (relCover C R' D).V₁
      (relCocycleBaseChange C R R' D g)
      (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
        (relCover C R' D).V₀)).injective
    -- the shorthand sections
    set A := twistTriv₀ R (relCover C R D).V₀ (relCover C R D).V₁ g
      (le_refl (relCover C R D).V₀) p.1 with hA
    set B := twistTriv₁ R (relCover C R D).V₀ (relCover C R D).V₁ g
      (le_refl (relCover C R D).V₁) p.2 with hB
    set G : Γ(relCurve C R', (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁) :=
      relSectionsMap C R R' (D.V₀ ⊓ D.V₁)
        (g : Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁)) with hG
    -- Left side.
    have hL1 : (relTwistDiff C R D g).baseChange R' (r' ⊗ₜ p)
        = r' ⊗ₜ[R] relTwistDiff C R D g p := LinearMap.baseChange_tmul _ _ _
    have hL2 := twistTriv₀_relTwistOverlapBaseChange C R R' D g r'
      (relTwistDiff C R D g p)
    have hL3 : twistTriv₀ R (relCover C R D).V₀ (relCover C R D).V₁ g
        (inf_le_left : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤ (relCover C R D).V₀)
        (relTwistDiff C R D g p)
        = (relCurve C R).resHom
            (inf_le_left : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
              (relCover C R D).V₀) A
          - (g : Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁)) *
            (relCurve C R).resHom
              (inf_le_right : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
                (relCover C R D).V₁) B := by
      rw [relTwistDiff_apply]
      exact twistTriv₀_pairDiff R (relCover C R D).V₀ (relCover C R D).V₁ g p.1 p.2
    have hL4 : relSectionsMap C R R' (D.V₀ ⊓ D.V₁)
        ((relCurve C R).resHom
            (inf_le_left : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
              (relCover C R D).V₀) A
          - (g : Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁)) *
            (relCurve C R).resHom
              (inf_le_right : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
                (relCover C R D).V₁) B)
        = (relCurve C R').resHom
            (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
              (relCover C R' D).V₀) (relSectionsMap C R R' D.V₀ A)
          - G * (relCurve C R').resHom
              (inf_le_right : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
                (relCover C R' D).V₁) (relSectionsMap C R R' D.V₁ B) := by
      have e₀ : relSectionsMap C R R' (D.V₀ ⊓ D.V₁)
          ((relCurve C R).resHom
            (inf_le_left : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
              (relCover C R D).V₀) A)
          = (relCurve C R').resHom
              (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
                (relCover C R' D).V₀) (relSectionsMap C R R' D.V₀ A) :=
        relSectionsMap_resHom C R R' (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀) A
      have e₁ : relSectionsMap C R R' (D.V₀ ⊓ D.V₁)
          ((relCurve C R).resHom
            (inf_le_right : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
              (relCover C R D).V₁) B)
          = (relCurve C R').resHom
              (inf_le_right : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
                (relCover C R' D).V₁) (relSectionsMap C R R' D.V₁ B) :=
        relSectionsMap_resHom C R R' (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁) B
      rw [map_sub, map_mul, e₀, e₁]
    have hLHS : twistTriv₀ R' (relCover C R' D).V₀ (relCover C R' D).V₁
        (relCocycleBaseChange C R R' D g)
        (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
          (relCover C R' D).V₀)
        (relTwistOverlapBaseChange C R R' D g
          ((relTwistDiff C R D g).baseChange R' (r' ⊗ₜ p)))
        = r' • ((relCurve C R').resHom
              (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
                (relCover C R' D).V₀) (relSectionsMap C R R' D.V₀ A)
            - G * (relCurve C R').resHom
                (inf_le_right : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
                  (relCover C R' D).V₁) (relSectionsMap C R R' D.V₁ B)) := by
      rw [hL1]
      exact hL2.trans (by rw [hL3, hL4])
    -- Right side.
    have hdom : relTwistDomBaseChange C R R' D g (r' ⊗ₜ p)
        = (relTwistTermBaseChange₀ C R R' D g (r' ⊗ₜ p.1),
           relTwistTermBaseChange₁ C R R' D g (r' ⊗ₜ p.2)) := by
      rw [relTwistDomBaseChange, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul]
      rfl
    have hR1 : twistTriv₀ R' (relCover C R' D).V₀ (relCover C R' D).V₁
        (relCocycleBaseChange C R R' D g)
        (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
          (relCover C R' D).V₀)
        (relTwistDiff C R' D (relCocycleBaseChange C R R' D g)
          (relTwistTermBaseChange₀ C R R' D g (r' ⊗ₜ p.1),
           relTwistTermBaseChange₁ C R R' D g (r' ⊗ₜ p.2)))
        = (relCurve C R').resHom
            (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
              (relCover C R' D).V₀)
            (twistTriv₀ R' (relCover C R' D).V₀ (relCover C R' D).V₁
              (relCocycleBaseChange C R R' D g) (le_refl (relCover C R' D).V₀)
              (relTwistTermBaseChange₀ C R R' D g (r' ⊗ₜ p.1)))
          - ((relCocycleBaseChange C R R' D g :
              Γ(relCurve C R', (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁)ˣ) :
              Γ(relCurve C R', (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁)) *
            (relCurve C R').resHom
              (inf_le_right : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
                (relCover C R' D).V₁)
              (twistTriv₁ R' (relCover C R' D).V₀ (relCover C R' D).V₁
                (relCocycleBaseChange C R R' D g) (le_refl (relCover C R' D).V₁)
                (relTwistTermBaseChange₁ C R R' D g (r' ⊗ₜ p.2))) := by
      rw [relTwistDiff_apply]
      exact twistTriv₀_pairDiff R' (relCover C R' D).V₀ (relCover C R' D).V₁
        (relCocycleBaseChange C R R' D g)
        (relTwistTermBaseChange₀ C R R' D g (r' ⊗ₜ p.1))
        (relTwistTermBaseChange₁ C R R' D g (r' ⊗ₜ p.2))
    have hres₀ : (relCurve C R').resHom
        (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
          (relCover C R' D).V₀)
        (twistTriv₀ R' (relCover C R' D).V₀ (relCover C R' D).V₁
          (relCocycleBaseChange C R R' D g) (le_refl (relCover C R' D).V₀)
          (relTwistTermBaseChange₀ C R R' D g (r' ⊗ₜ p.1)))
        = r' • (relCurve C R').resHom
            (inf_le_left : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
              (relCover C R' D).V₀) (relSectionsMap C R R' D.V₀ A) := by
      rw [twistTriv₀_relTwistTermBaseChange₀]
      exact resHom_smul_rel C R' _ r' _
    have hres₁ : (relCurve C R').resHom
        (inf_le_right : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
          (relCover C R' D).V₁)
        (twistTriv₁ R' (relCover C R' D).V₀ (relCover C R' D).V₁
          (relCocycleBaseChange C R R' D g) (le_refl (relCover C R' D).V₁)
          (relTwistTermBaseChange₁ C R R' D g (r' ⊗ₜ p.2)))
        = r' • (relCurve C R').resHom
            (inf_le_right : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
              (relCover C R' D).V₁) (relSectionsMap C R R' D.V₁ B) := by
      rw [twistTriv₁_relTwistTermBaseChange₁]
      exact resHom_smul_rel C R' _ r' _
    have hcoe : ((relCocycleBaseChange C R R' D g :
        Γ(relCurve C R', (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁)ˣ) :
        Γ(relCurve C R', (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁)) = G :=
      relCocycleBaseChange_coe C R R' D g
    have hgmul : G * (r' • (relCurve C R').resHom
          (inf_le_right : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
            (relCover C R' D).V₁) (relSectionsMap C R R' D.V₁ B))
        = r' • (G * (relCurve C R').resHom
            (inf_le_right : (relCover C R' D).V₀ ⊓ (relCover C R' D).V₁ ≤
              (relCover C R' D).V₁) (relSectionsMap C R R' D.V₁ B)) := by
      rw [Scheme.overModule_smul_def, Scheme.overModule_smul_def, mul_left_comm]
    rw [hLHS, hdom, hR1, hres₀, hres₁, hcoe, hgmul, smul_sub]

end Square

/-! ## The on-the-nose clauses -/

section Final

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']
variable (π : C.left ⟶ P1 k) [IsFinite π]
variable (g : Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
  (relCover C R (fiberTwoCover π)).V₁)ˣ)

open AlgebraicJacobian

/-- The Čech differential of the relative twist pair is the pair-free
`relTwistDiff`. -/
lemma relTwistPair_diff :
    (relTwistPair C R π g).diff = relTwistDiff C R (fiberTwoCover π) g := rfl

/-- **The twisted δ-naturality square, pair form**: the square
`relTwistDiffBaseChange` read on the Čech differentials of the two relative twist
pairs. -/
theorem relTwistPairDiffBaseChange
    (a : R' ⊗[R] (↥(twistSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ g (relCover C R (fiberTwoCover π)).V₀) ×
      ↥(twistSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ g (relCover C R (fiberTwoCover π)).V₁))) :
    relTwistOverlapBaseChange C R R' (fiberTwoCover π) g
        (((relTwistPair C R π g).diff).baseChange R' a)
      = (relTwistPair C R' π (relCocycleBaseChange C R R' (fiberTwoCover π) g)).diff
          (relTwistDomBaseChange C R R' (fiberTwoCover π) g a) := by
  rw [relTwistPair_diff C R π g,
    relTwistPair_diff C R' π (relCocycleBaseChange C R R' (fiberTwoCover π) g)]
  exact relTwistDiffBaseChange C R R' (fiberTwoCover π) g a

/-- The base-changed twisted differential is surjective on the vanishing locus. -/
theorem relTwist_surjective_diff_baseChange
    (hH1 : Subsingleton (relTwistPair C R π g).H1) :
    Function.Surjective
      ((relTwistPair C R' π (relCocycleBaseChange C R R' (fiberTwoCover π) g)).diff) := by
  have hsurj : Function.Surjective (relTwistPair C R π g).diff :=
    (relTwistPairData C R π g).surjective_diff
      (relCover_isAffineOpen₀ C R (fiberTwoCover π))
      (relCover_isAffineOpen₁ C R (fiberTwoCover π)) hH1
  have hbc : Function.Surjective (((relTwistPair C R π g).diff).baseChange R') := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective R' hsurj
  exact RigidEngine.surjective_congr _ _
    (relTwistDomBaseChange C R R' (fiberTwoCover π) g)
    (relTwistOverlapBaseChange C R R' (fiberTwoCover π) g)
    (fun a => relTwistPairDiffBaseChange C R R' π g a) hbc

/-- **`H¹` vanishes after base change** (worksheet §1.2 `rigidEngine_baseChange`, second
clause): on the vanishing locus, the twisted `H¹` of the base-changed sheaf is zero, for
every test-ring change `R → R'`. -/
theorem relTwist_subsingleton_h1_baseChange
    (hH1 : Subsingleton (relTwistPair C R π g).H1) :
    Subsingleton (Sheaf.HModule (relTwistSheaf C R' (fiberTwoCover π)
      (relCocycleBaseChange C R R' (fiberTwoCover π) g)) 1) := by
  set g' := relCocycleBaseChange C R R' (fiberTwoCover π) g with hg'
  have hsurj' : Function.Surjective (relTwistPair C R' π g').diff :=
    relTwist_surjective_diff_baseChange C R R' π g hH1
  haveI : Subsingleton (relTwistPair C R' π g').H1 := by
    have h : (relTwistPair C R' π g').imageLattice = ⊤ := by
      rw [← (relTwistPair C R' π g').range_diff_eq, LinearMap.range_eq_top]
      exact hsurj'
    rw [TwoLatticePair.H1, h]
    infer_instance
  exact ((relTwistPairData C R' π g').h1Equiv
    (relCover_isAffineOpen₀ C R' (fiberTwoCover π))
    (relCover_isAffineOpen₁ C R' (fiberTwoCover π))
    (relCover_sup C R' (fiberTwoCover π))).toEquiv.subsingleton

/-- **`H⁰` base change on the nose** (worksheet §1.2 `rigidEngine_baseChange`, first
clause; Kleiman 3.10 (iii), curve-lite): on the vanishing locus, for every test-ring
change `R → R'`,

`R' ⊗[R] H⁰(C_R, F_g) ≃ₗ[R'] H⁰(C_{R'}, F_{g'})`

with `g' = relCocycleBaseChange g` — the abstract kernel clause threaded through the
CBC-1 term identifications by the twisted δ-naturality square. -/
noncomputable def relTwistH0BaseChange
    (hH1 : Subsingleton (relTwistPair C R π g).H1) :
    R' ⊗[R] (Sheaf.HModule (relTwistSheaf C R (fiberTwoCover π) g) 0) ≃ₗ[R']
      Sheaf.HModule (relTwistSheaf C R' (fiberTwoCover π)
        (relCocycleBaseChange C R R' (fiberTwoCover π) g)) 0 :=
  (relTwistH0BaseChangeEquiv C R π g hH1 R').trans
    ((RigidEngine.kerCongr ((relTwistPair C R π g).diff.baseChange R')
        ((relTwistPair C R' π (relCocycleBaseChange C R R' (fiberTwoCover π) g)).diff)
        (relTwistDomBaseChange C R R' (fiberTwoCover π) g)
        (relTwistOverlapBaseChange C R R' (fiberTwoCover π) g)
        (fun a => relTwistPairDiffBaseChange C R R' π g a)).trans
      ((relTwistPairData C R' π (relCocycleBaseChange C R R' (fiberTwoCover π) g)).h0Equiv
        (relCover_isAffineOpen₀ C R' (fiberTwoCover π))
        (relCover_isAffineOpen₁ C R' (fiberTwoCover π))
        (relCover_sup C R' (fiberTwoCover π))).symm)

end Final

end AlgebraicGeometry
