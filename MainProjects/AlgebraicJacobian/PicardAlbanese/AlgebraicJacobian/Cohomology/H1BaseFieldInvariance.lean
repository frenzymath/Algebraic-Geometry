/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Challenge
import AlgebraicJacobian.Curve.BaseChangeInstances
import AlgebraicJacobian.Cohomology.RelativeH1BaseChange
import AlgebraicJacobian.Cohomology.TransitionSectionsBaseChange

/-!
# `H¹` base-field invariance and base-field invariance of the genus (W5-X3)

For the challenge curve `C` over a field `k` and a field extension `K/k`
(`[Field K] [Algebra k K]`), this file proves *cohomology commutes with base change* for
the structure sheaf **from the absolute curve**: on the Rebuild carriers
(`Sheaf.HModule (·.moduleKSheaf ·) n`, two-cover Čech-definitional),

* `H⁰(C, 𝒪) ⊗[k] K ≃ₗ[K] H⁰(C_K, 𝒪)` (`AlgebraicGeometry.h0BaseFieldEquiv`),
* `H¹(C, 𝒪) ⊗[k] K ≃ₗ[K] H¹(C_K, 𝒪)` (`AlgebraicGeometry.h1BaseFieldEquiv`),

and deduces that **the genus is invariant under base field extension**
(`AlgebraicGeometry.genus_baseField`): the genus of `C_K = (C ⊗ overSpec k K).left`,
viewed as a legal curve over `K` through the `Curve.BaseChangeInstances` stack
(`baseChangeBundle C K`), equals `genus C`. The dimension count is scalar-identity-first
(W12 discipline): the one `finrank` identity is
`AlgebraicGeometry.finrank_h1_baseField`, with the `= genus C` form
`AlgebraicGeometry.finrank_h1_baseField_eq_genus` for the Wave-5 tangent count
(`dim T₀(J_k̄) = genus C`).

The engine is the flat/free cohomology-and-base-change mechanism of the landed
`Cohomology.RelativeH1BaseChange` (w4-2), run once more with the *absolute* curve as
source — NOT Mumford II.5 (no semicontinuity, no Exchange): the two-term Čech complex of
an affine two-cover base-changes termwise by the landed free identification
`relSectionsBaseChange` (`Γ(C, V) ⊗[k] R ≃ₗ[R] Γ(C_R, V_R)`), and `H¹` is its cokernel,
which commutes with any base change by right-exactness
(`LinearMap.quotRangeBaseChangeEquiv`). The intermediate statements are proved for an
arbitrary commutative `k`-algebra `R` (the `k → R` legs of the CBC ladder; the tower legs
`R → R'` are the landed `relH1BaseChange`), so the dual-numbers lane (`R = k[ε]`) can
consume them as well.

## Main declarations

* `AlgebraicGeometry.relPullbackSection_resHom` — pullback of sections to the relative
  curve commutes with restriction.
* `AlgebraicGeometry.curveDiffBaseChange` — **CBC-1 (`k → R`, the commuting square)**:
  the base change of the absolute two-cover restriction-difference map is carried to the
  relative difference map under the term equivalences.
* `AlgebraicGeometry.curveH1CokBaseChange` — **CBC-2 (`i = 1`), cokernel form**:
  `R ⊗[k] H1Cok k C ≃ₗ[R] H1Cok R C_R`, with the computation rule
  `curveH1CokBaseChange_tmul_mk`.
* `AlgebraicGeometry.curveH1BaseChange` — **CBC-2 (`i = 1`) on the cohomology carriers**:
  `R ⊗[k] H¹(C, 𝒪) ≃ₗ[R] H¹(C_R, 𝒪)` for every commutative `k`-algebra `R`.
* `AlgebraicGeometry.curveH0BaseChange` — the degree-zero analogue, free of charge from
  `relSectionsBaseChange` at `V = ⊤` (`C` proper makes `⊤` qcqs).
* `AlgebraicGeometry.h1BaseFieldEquiv`, `AlgebraicGeometry.h0BaseFieldEquiv` — the
  headline field-extension statements, keyed on the `(C ⊗ overSpec k K).left` spelling of
  `Curve.BaseChangeInstances`.
* `AlgebraicGeometry.finrank_h1_baseField`, `AlgebraicGeometry.finrank_h0_baseField`,
  `AlgebraicGeometry.finrank_h1_baseField_eq_genus` — the scalar `finrank` identities.
* `AlgebraicGeometry.genus_baseField` — `genus (baseChangeBundle C K) = genus C`.

## Implementation notes

The `k`-module structure on the absolute sections `Γ(C.left, V)` appears in two
definitionally equal presentations: `Scheme.overModule` under the
`letI : C.left.Over (Spec (.of k)) := .ofHom C.hom` of the frozen `genus` spelling (the
two-cover/`moduleKSheaf` side) and `Over.sectionsAlgebra` (the `relSectionsBaseChange`
side). Statements are given in the `genus`/two-cover spelling; the seams are crossed by
`exact`, as in `Cohomology.RelativeH1BaseChange` (see the transparency note there).
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`, and the two presentations of the `k`-module structure on
`Γ(C.left, V)`; see the module docstring and `Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TensorProduct
open Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Over.sectionsAlgebra

section CBC

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]

/-- **Pullback of sections to the relative curve commutes with restriction**: for
`W ≤ V ⊆ C.left`, restricting on the curve and then pulling back along the first
projection agrees with pulling back and then restricting on the relative curve. -/
lemma relPullbackSection_resHom {W V : C.left.Opens} (hWV : W ≤ V) (s : Γ(C.left, V)) :
    relPullbackSection C R W (C.left.resHom hWV s) =
      (relCurve C R).resHom
        (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left hWV)
        (relPullbackSection C R V s) := by
  have h1 : C.left.presheaf.map (homOfLE hWV).op ≫
      (fst C (overSpec k R)).left.appLE W ((fst C (overSpec k R)).left ⁻¹ᵁ W) le_rfl =
      (fst C (overSpec k R)).left.appLE V ((fst C (overSpec k R)).left ⁻¹ᵁ W)
        (le_rfl.trans (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left hWV)) :=
    Scheme.Hom.map_appLE _ le_rfl (homOfLE hWV).op
  have h2 : (fst C (overSpec k R)).left.appLE V ((fst C (overSpec k R)).left ⁻¹ᵁ V)
        le_rfl ≫
      (relCurve C R).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left hWV)).op =
      (fst C (overSpec k R)).left.appLE V ((fst C (overSpec k R)).left ⁻¹ᵁ W)
        (le_rfl.trans (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left hWV)) :=
    Scheme.Hom.appLE_map _ le_rfl
      (homOfLE (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left hWV)).op
  exact (congr($(h1).hom s)).trans (congr($(h2).hom s)).symm

variable (D : C.left.AffineTwoCover)

/-- The base change of the absolute two-cover complex's degree-zero term: the product of
the two chart-term identifications `relSectionsBaseChange`,
`R ⊗[k] (Γ(C, V₀) × Γ(C, V₁)) ≃ₗ[R] Γ(C_R, V₀ᴿ) × Γ(C_R, V₁ᴿ)`. -/
noncomputable def curveDiffDomBaseChange :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    R ⊗[k] (Γ(C.left, D.V₀) × Γ(C.left, D.V₁)) ≃ₗ[R]
      Γ(relCurve C R, (relCover C R D).V₀) × Γ(relCurve C R, (relCover C R D).V₁) :=
  (TensorProduct.prodRight k R R Γ(C.left, D.V₀) Γ(C.left, D.V₁)).trans
    ((relSectionsBaseChange C R D.isAffineOpen₀.isCompact
        D.isAffineOpen₀.isQuasiSeparated).prodCongr
      (relSectionsBaseChange C R D.isAffineOpen₁.isCompact
        D.isAffineOpen₁.isQuasiSeparated))

/-- The overlap-term base change of the absolute two-cover complex, in the `V₀ᴿ ⊓ V₁ᴿ`
spelling of the two-cover carrier. -/
noncomputable def curveDiffCodBaseChange :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    R ⊗[k] Γ(C.left, D.V₀ ⊓ D.V₁) ≃ₗ[R]
      Γ(relCurve C R, (relCover C R D).V₀ ⊓ (relCover C R D).V₁) :=
  relSectionsBaseChange C R D.isAffineOpen_inf.isCompact
    D.isAffineOpen_inf.isQuasiSeparated

/-- The overlap-term base change on a pure tensor: `a ⊗ s` goes to the `R`-action of `a`
on the pulled-back section. -/
lemma curveDiffCodBaseChange_tmul (a : R) (s : Γ(C.left, D.V₀ ⊓ D.V₁)) :
    curveDiffCodBaseChange C R D (a ⊗ₜ s) =
      a • relPullbackSection C R (D.V₀ ⊓ D.V₁) s :=
  (relSectionsBaseChange_tmul C R D.isAffineOpen_inf.isCompact
      D.isAffineOpen_inf.isQuasiSeparated a s).trans
    (Scheme.overModule_smul_def R (relCurve C R) a _).symm

set_option maxHeartbeats 800000 in
-- The `respectTransparency false` defeq checks through the `relCurve`/product spellings
-- and the two presentations of the `k`-structure on `Γ(C.left, ·)` exceed the default
-- elaboration limit (as in `Cohomology.RelativeH1BaseChange`).
set_option synthInstance.maxHeartbeats 400000 in
-- (Instance-search limit, same reason.)
/-- **CBC-1 (`k → R`, the commuting square, pointwise)**: the base change of the
absolute two-cover restriction-difference map is carried to the restriction-difference
map of the relative curve under the term equivalences. -/
lemma curveDiffBaseChange
    (x : R ⊗[k] (Γ(C.left, D.V₀) × Γ(C.left, D.V₁))) :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    curveDiffCodBaseChange C R D
        ((TwoCover.diff k C.left D.V₀ D.V₁).baseChange R x) =
      TwoCover.diff R (relCurve C R) (relCover C R D).V₀ (relCover C R D).V₁
        (curveDiffDomBaseChange C R D x) := by
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a p =>
    -- the pullback of the difference is the difference of the pullbacks
    have hsub : relPullbackSection C R (D.V₀ ⊓ D.V₁)
        (TwoCover.diff k C.left D.V₀ D.V₁ p) =
        relPullbackSection C R (D.V₀ ⊓ D.V₁) (C.left.resHom inf_le_left p.1) -
          relPullbackSection C R (D.V₀ ⊓ D.V₁) (C.left.resHom inf_le_right p.2) := by
      rw [TwoCover.diff_apply]
      exact map_sub ((fst C (overSpec k R)).left.appLE (D.V₀ ⊓ D.V₁)
        ((fst C (overSpec k R)).left ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) le_rfl).hom _ _
    -- spelling adapters: pullback commutes with the two chart restrictions
    have e₀ : relPullbackSection C R (D.V₀ ⊓ D.V₁) (C.left.resHom inf_le_left p.1) =
        (relCurve C R).resHom
          (inf_le_left : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
            (relCover C R D).V₀)
          (relPullbackSection C R D.V₀ p.1) :=
      relPullbackSection_resHom C R inf_le_left p.1
    have e₁ : relPullbackSection C R (D.V₀ ⊓ D.V₁) (C.left.resHom inf_le_right p.2) =
        (relCurve C R).resHom
          (inf_le_right : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
            (relCover C R D).V₁)
          (relPullbackSection C R D.V₁ p.2) :=
      relPullbackSection_resHom C R inf_le_right p.2
    -- restriction on the relative curve is `R`-linear
    have hres₀ : (relCurve C R).resHom
        (inf_le_left : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
          (relCover C R D).V₀)
        (a • relPullbackSection C R D.V₀ p.1) =
        a • (relCurve C R).resHom inf_le_left (relPullbackSection C R D.V₀ p.1) := by
      rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
      congr 1
      exact (relCurve C R).overAlgebraMap_apply_res R (homOfLE _).op a
    have hres₁ : (relCurve C R).resHom
        (inf_le_right : (relCover C R D).V₀ ⊓ (relCover C R D).V₁ ≤
          (relCover C R D).V₁)
        (a • relPullbackSection C R D.V₁ p.2) =
        a • (relCurve C R).resHom inf_le_right (relPullbackSection C R D.V₁ p.2) := by
      rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
      congr 1
      exact (relCurve C R).overAlgebraMap_apply_res R (homOfLE _).op a
    -- the degree-zero term equivalence on a pure tensor
    have hdom : curveDiffDomBaseChange C R D (a ⊗ₜ p) =
        (a • relPullbackSection C R D.V₀ p.1, a • relPullbackSection C R D.V₁ p.2) := by
      rw [curveDiffDomBaseChange, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul]
      exact Prod.ext
        ((relSectionsBaseChange_tmul C R D.isAffineOpen₀.isCompact
            D.isAffineOpen₀.isQuasiSeparated a p.1).trans
          (Scheme.overModule_smul_def R (relCurve C R) a _).symm)
        ((relSectionsBaseChange_tmul C R D.isAffineOpen₁.isCompact
            D.isAffineOpen₁.isQuasiSeparated a p.2).trans
          (Scheme.overModule_smul_def R (relCurve C R) a _).symm)
    rw [LinearMap.baseChange_tmul, curveDiffCodBaseChange_tmul, hsub, e₀, e₁, hdom,
      TwoCover.diff_apply, hres₀, hres₁]
    exact smul_sub a _ _

/-- The commuting square of CBC-1 in range form: the overlap-term equivalence carries
the range of the base-changed absolute difference map onto the range of the relative
difference map. -/
lemma curveDiffBaseChange_range :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    Submodule.map (curveDiffCodBaseChange C R D : _ →ₗ[R] _)
      (LinearMap.range ((TwoCover.diff k C.left D.V₀ D.V₁).baseChange R)) =
      LinearMap.range (TwoCover.diff R (relCurve C R) (relCover C R D).V₀
        (relCover C R D).V₁) := by
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  have hcomp : (curveDiffCodBaseChange C R D).toLinearMap.comp
      ((TwoCover.diff k C.left D.V₀ D.V₁).baseChange R) =
      (TwoCover.diff R (relCurve C R) (relCover C R D).V₀
        (relCover C R D).V₁).comp (curveDiffDomBaseChange C R D).toLinearMap :=
    LinearMap.ext fun x ↦ curveDiffBaseChange C R D x
  rw [← LinearMap.range_comp, hcomp,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- **CBC-2 (`i = 1`, `k → R`), cokernel form**: the two-cover `H¹` cokernel carrier of
the absolute curve base-changes onto the relative one, unconditionally in the
commutative `k`-algebra `R` —
`R ⊗[k] H1Cok k C ≃ₗ[R] H1Cok R C_R` (right-exactness needs no flatness). -/
noncomputable def curveH1CokBaseChange :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    R ⊗[k] TwoCover.H1Cok k C.left D.V₀ D.V₁ ≃ₗ[R]
      TwoCover.H1Cok R (relCurve C R) (relCover C R D).V₀ (relCover C R D).V₁ :=
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  (LinearMap.quotRangeBaseChangeEquiv R (TwoCover.diff k C.left D.V₀ D.V₁)).trans
    (Submodule.Quotient.equiv _ _ (curveDiffCodBaseChange C R D)
      (curveDiffBaseChange_range C R D))

/-- The `H¹` cokernel base change on the class of a pure tensor: `a ⊗ [s]` goes to the
class of `a • relPullbackSection s`. -/
lemma curveH1CokBaseChange_tmul_mk (a : R) (s : Γ(C.left, D.V₀ ⊓ D.V₁)) :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    curveH1CokBaseChange C R D (a ⊗ₜ Submodule.Quotient.mk s) =
      Submodule.Quotient.mk (a • relPullbackSection C R (D.V₀ ⊓ D.V₁) s) := by
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  rw [curveH1CokBaseChange, LinearEquiv.trans_apply,
    LinearMap.quotRangeBaseChangeEquiv_tmul_mk, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply]
  exact congrArg Submodule.Quotient.mk (curveDiffCodBaseChange_tmul C R D a s)

/-- **CBC-2 (`i = 1`, `k → R`)**: degree-one cohomology of the structure sheaf commutes
with base change from the absolute curve to the relative curve over any commutative
`k`-algebra `R` — `R ⊗[k] H¹(C, 𝒪) ≃ₗ[R] H¹(C_R, 𝒪)` on the Rebuild carriers, through
the two-cover cokernel identifications on both sides. The curve-lite, engine-grade form
of Kleiman's *"cohomology commutes with base change"* in degree one for the structure
sheaf (no flatness input: the two-term complex's cokernel is right-exact). -/
noncomputable def curveH1BaseChange :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    R ⊗[k] Sheaf.HModule (C.left.moduleKSheaf k) 1 ≃ₗ[R]
      Sheaf.HModule ((relCurve C R).moduleKSheaf R) 1 :=
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  (LinearEquiv.baseChange k R _ _
      (TwoCover.h1CokEquiv k C.left D.V₀ D.V₁ D.sup_eq_top D.isAffineOpen₀
        D.isAffineOpen₁)).trans
    ((curveH1CokBaseChange C R D).trans (relTwoCoverH1 C R D).symm)

end CBC

section StandingBundle

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- A fixed affine two-chart cover of the challenge curve (chosen once, from
`Scheme.AffineTwoCover.nonempty_of_curve`), so that every downstream base-change
equivalence is built on one and the same cover. -/
noncomputable def curveCover : C.left.AffineTwoCover :=
  (Scheme.AffineTwoCover.nonempty_of_curve C).some

variable (R : Type u) [CommRing R] [Algebra k R]

/-- **CBC-2 (`i = 0`, `k → R`)**: degree-zero cohomology of the structure sheaf commutes
with base change from the absolute (proper) curve to the relative curve over any
commutative `k`-algebra `R` — `R ⊗[k] H⁰(C, 𝒪) ≃ₗ[R] H⁰(C_R, 𝒪)`. Both carriers are
global sections (`Scheme.moduleKSheafHZero`), and global sections base-change freely by
`relSectionsBaseChange` at `V = ⊤` (qcqs since `C` is proper over a field). -/
noncomputable def curveH0BaseChange :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    R ⊗[k] Sheaf.HModule (C.left.moduleKSheaf k) 0 ≃ₗ[R]
      Sheaf.HModule ((relCurve C R).moduleKSheaf R) 0 :=
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  have hc : IsCompact ((⊤ : C.left.Opens) : Set C.left) := by
    have : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
    simpa using CompactSpace.isCompact_univ
  have hqs : IsQuasiSeparated ((⊤ : C.left.Opens) : Set C.left) := by
    have : QuasiSeparatedSpace C.left := quasiSeparatedSpace_of_quasiSeparated C.hom
    simpa using isQuasiSeparated_univ
  (LinearEquiv.baseChange k R _ _ (C.left.moduleKSheafHZero k)).trans
    ((relSectionsBaseChange C R hc hqs).trans
      ((relCurve C R).moduleKSheafHZero R).symm)

variable (K : Type u) [Field K] [Algebra k K]

/-- **`H¹` base-field invariance** (the parked deg-d5b D2 item, headline): for the
challenge curve `C` over `k` and any field extension `K/k`,

`H¹(C, 𝒪) ⊗[k] K ≃ₗ[K] H¹(C_K, 𝒪)`

on the Rebuild carriers, where `C_K = (C ⊗ overSpec k K).left` is the base-changed curve
of `Curve.BaseChangeInstances` (a legal curve over `K`, structure morphism the second
projection). Engine-grade flat/free CBC on the two-cover Čech complex — not Mumford
II.5. -/
noncomputable def h1BaseFieldEquiv :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    K ⊗[k] Sheaf.HModule (C.left.moduleKSheaf k) 1 ≃ₗ[K]
      Sheaf.HModule ((C ⊗ overSpec k K).left.moduleKSheaf K) 1 :=
  curveH1BaseChange C K (curveCover C)

/-- **`H⁰` base-field invariance**: `H⁰(C, 𝒪) ⊗[k] K ≃ₗ[K] H⁰(C_K, 𝒪)` for any field
extension `K/k`, on the Rebuild carriers, in the `Curve.BaseChangeInstances` spelling. -/
noncomputable def h0BaseFieldEquiv :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    K ⊗[k] Sheaf.HModule (C.left.moduleKSheaf k) 0 ≃ₗ[K]
      Sheaf.HModule ((C ⊗ overSpec k K).left.moduleKSheaf K) 0 :=
  curveH0BaseChange C K

/-- **The scalar identity (W12 discipline)**: the `K`-dimension of `H¹(C_K, 𝒪)` equals
the `k`-dimension of `H¹(C, 𝒪)`, for any field extension `K/k`. -/
theorem finrank_h1_baseField :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    Module.finrank K (Sheaf.HModule ((C ⊗ overSpec k K).left.moduleKSheaf K) 1) =
      Module.finrank k (Sheaf.HModule (C.left.moduleKSheaf k) 1) := by
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  rw [← (h1BaseFieldEquiv C K).finrank_eq]
  exact Module.finrank_baseChange

/-- The degree-zero scalar identity: the `K`-dimension of `H⁰(C_K, 𝒪)` equals the
`k`-dimension of `H⁰(C, 𝒪)`. -/
theorem finrank_h0_baseField :
    letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
    Module.finrank K (Sheaf.HModule ((C ⊗ overSpec k K).left.moduleKSheaf K) 0) =
      Module.finrank k (Sheaf.HModule (C.left.moduleKSheaf k) 0) := by
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  rw [← (h0BaseFieldEquiv C K).finrank_eq]
  exact Module.finrank_baseChange

/-- **The tangent-count form** (Wave-5 T5 consumer): the `K`-dimension of `H¹(C_K, 𝒪)`
is the genus of `C`, for any field extension `K/k` (in particular `K = k̄`). -/
theorem finrank_h1_baseField_eq_genus :
    Module.finrank K (Sheaf.HModule ((C ⊗ overSpec k K).left.moduleKSheaf K) 1) =
      genus C :=
  finrank_h1_baseField C K

/-- **Base-field invariance of the genus**: the genus of the base-changed curve
`C_K = baseChangeBundle C K` (a legal curve over `K` through the
`Curve.BaseChangeInstances` stack), computed by the frozen `genus` over `K`, equals the
genus of `C` over `k`. -/
theorem genus_baseField :
    haveI : IsProper (baseChangeBundle C K).hom := instIsProperSndLeft C K
    haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C K).hom :=
      instSmoothOfRelativeDimensionSndLeft C K
    haveI : GeometricallyIrreducible (baseChangeBundle C K).hom :=
      instGeometricallyIrreducibleSndLeft C K
    genus (baseChangeBundle C K) = genus C :=
  finrank_h1_baseField C K

end StandingBundle

end AlgebraicGeometry
