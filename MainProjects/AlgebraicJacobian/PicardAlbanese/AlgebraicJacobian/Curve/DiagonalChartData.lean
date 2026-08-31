/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.DiagonalChart

/-!
# Freezing the étale-coordinate chart data of a smooth curve (deg-D4b, brick B5, part 1)

For `C : Over (Spec k)` with `[SmoothOfRelativeDimension 1 C.hom]`, this file *freezes*, per
point `p` of `C.left`, a standard-smooth affine chart `U ∋ p` together with the full B0
étale-factorization package: an étale coordinate `Polynomial k → Γ(C.left, U)` (compatible
with the section `k`-algebra structure), and the consequent flatness / unramifiedness /
essential finiteness that brick B0 (`Algebra/DiagonalIdeal.lean`) needs to produce the
idempotent lift `elift`.

The extraction is the `Curve/StalksDVR.lean` pattern:
`SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension` gives a standard-smooth
chart over the one-point base `Spec k` (the base open collapses to `⊤`); its section ring is
standard smooth of relative dimension `1` over `Γ(Spec k, ⊤)`.  Transporting the base along
the ring isomorphism `k ≃+* Γ(Spec k, ⊤)` (`ΓSpecIso`) — standard-smoothness is stable under
composition with the rel-dimension-`0` iso — and applying the structure theorem
`RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` (Stacks 00T7) yields an
étale factorization `MvPolynomial (Fin 1) k → Γ(C.left, U)`; transporting the source along
`MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k` (`uniqueAlgEquiv`) gives the `Polynomial k`-shaped
coordinate that B0 consumes.

## Main declarations

* `AlgebraicGeometry.Over.exists_diagonalChartAt` — the per-point existence of a
  standard-smooth chart with an étale `Polynomial k`-coordinate compatible with the section
  `k`-algebra, packaged with `IsScalarTower` and `Algebra.Etale`.
* `AlgebraicGeometry.Over.DiagonalChartData` — the frozen per-curve choice of such charts, its
  coordinate-algebra / scalar-tower / étale projections re-exposed as instances.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Polynomial
open scoped TensorProduct

namespace AlgebraicGeometry

namespace Over

attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k]

/-! ## The per-point chart extraction -/

/-- **Per-point standard-smooth chart with étale coordinate.** For a curve `C` smooth of
relative dimension one over `Spec k` and a point `p : C.left`, there is an affine open `U ∋ p`
and an étale `Polynomial k`-algebra structure on the sections `Γ(C.left, U)`, compatible with
the section `k`-algebra structure (`Over.sectionsAlgebra`).  The coordinate is the étale
coordinate of a standard-smooth chart transported to `Polynomial k`; flatness / formal
unramifiedness / essential finiteness for brick B0 are consequences of `Algebra.Etale`. -/
theorem exists_diagonalChartAt (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] (p : C.left) :
    ∃ (U : C.left.Opens) (_ : IsAffineOpen U) (_ : p ∈ U)
      (alg : Algebra (Polynomial k) Γ(C.left, U)),
      (letI := alg; IsScalarTower k (Polynomial k) Γ(C.left, U)) ∧
      (letI := alg; Algebra.Etale (Polynomial k) Γ(C.left, U)) := by
  obtain ⟨U, _hU, V, hV, hpV, e, hsm⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := C.hom) p
  -- The base affine open is nonempty, hence all of the one-point space `Spec k`.
  have hUtop : U = ⊤ := by
    have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => ?_)
    exact Subsingleton.elim (C.hom.base p) y ▸ e hpV
  subst hUtop
  -- The étale coordinate lives over `Γ(Spec k, ⊤)`; the section `k`-algebra is its restriction
  -- of scalars along the ring iso `ε : k ≃+* Γ(Spec k, ⊤)`.
  set ε : k ≃+* Γ(Spec (.of k), (⊤ : (Spec (.of k)).Opens)) :=
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv with hε
  -- `algebraMap k Γ(C.left, V) = (C.hom.appLE ⊤ V e).hom ∘ ε`.
  have hfeq : (algebraMap k Γ(C.left, V)) = (C.hom.appLE ⊤ V e).hom.comp (ε : k →+* _) := by
    rw [RingHom.algebraMap_toAlgebra]
    change ((Scheme.ΓSpecIso (.of k)).inv ≫
      C.hom.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top C.hom).ge)).hom = _
    rw [CommRingCat.hom_comp, hε, Iso.commRingCatIsoToRingEquiv_toRingHom]
    rfl
  -- Standard-smoothness of `algebraMap k Γ(C.left, V)` (rel dim `1 = 1 + 0`).
  have hss : (algebraMap k Γ(C.left, V)).IsStandardSmoothOfRelativeDimension 1 := by
    rw [hfeq, show (1 : ℕ) = 1 + 0 from rfl]
    exact hsm.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv ε)
  -- The étale factorization over `Polynomial k` via `MvPolynomial (Fin 1) k`.
  obtain ⟨g, hgC, hget⟩ := hss.exists_etale_mvPolynomial
  set pEquiv : Polynomial k ≃ₐ[k] MvPolynomial (Fin 1) k :=
    (MvPolynomial.uniqueAlgEquiv (R := k) (Fin 1)).symm with hpEquiv
  -- The transported coordinate `Polynomial k → Γ(C.left, V)`.
  letI alg : Algebra (Polynomial k) Γ(C.left, V) :=
    (g.comp pEquiv.toRingHom).toAlgebra
  refine ⟨V, hV, hpV, alg, ?_, ?_⟩
  · -- scalar tower: `algebraMap (Polynomial k) Γ ∘ C = algebraMap k Γ`.
    have hpc : pEquiv.toRingHom.comp (algebraMap k (Polynomial k)) = MvPolynomial.C := by
      rw [← MvPolynomial.algebraMap_eq]
      exact pEquiv.toAlgHom.comp_algebraMap
    refine IsScalarTower.of_algebraMap_eq' ?_
    change algebraMap k Γ(C.left, V)
      = (g.comp pEquiv.toRingHom).comp (algebraMap k (Polynomial k))
    rw [RingHom.comp_assoc, hpc, hgC]
  · -- étale: composite of the étale `g` with the bijective `pEquiv`.
    have : (g.comp pEquiv.toRingHom).Etale :=
      RingHom.Etale.stableUnderComposition _ _
        (RingHom.Etale.of_bijective pEquiv.bijective) hget
    rwa [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]

/-! ## The frozen per-curve chart data -/

/-- **The frozen étale-coordinate chart data of the curve `C`.** A choice, per point `p` of
`C.left`, of a standard-smooth affine chart `chart p ∋ p` with an étale `Polynomial k`-algebra
structure on its sections (`coordAlgebra`), compatible with the section `k`-algebra structure
(`isScalarTower`).  All of brick B0's hypotheses on the chart — flatness, formal
unramifiedness, essential finiteness — are consequences of `etale`; frozen here once so that the
diagonal member, its equation, and the kernel computation (brick B4) all speak about the *same*
chart per point (the classic assembly discipline). -/
structure DiagonalChartData (C : Over (Spec (.of k))) where
  /-- The chosen affine chart at each point. -/
  chart : C.left → C.left.Opens
  /-- Each chart is an affine open. -/
  isAffineOpen : ∀ p, IsAffineOpen (chart p)
  /-- The point lies in its chart. -/
  mem : ∀ p, p ∈ chart p
  /-- The étale `Polynomial k`-coordinate on the chart sections. -/
  coordAlgebra : ∀ p, Algebra (Polynomial k) Γ(C.left, chart p)
  /-- The coordinate is compatible with the section `k`-algebra structure. -/
  isScalarTower : ∀ p, letI := coordAlgebra p; IsScalarTower k (Polynomial k) Γ(C.left, chart p)
  /-- The coordinate is étale. -/
  etale : ∀ p, letI := coordAlgebra p; Algebra.Etale (Polynomial k) Γ(C.left, chart p)

/-- **Existence of the frozen chart data** for a curve smooth of relative dimension one: apply
the per-point extraction `exists_diagonalChartAt` and choose. -/
noncomputable def diagonalChartData (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] : DiagonalChartData C := by
  choose chart hAff hmem alg htower hetale using exists_diagonalChartAt C
  exact
    { chart := chart
      isAffineOpen := hAff
      mem := hmem
      coordAlgebra := alg
      isScalarTower := htower
      etale := hetale }

namespace DiagonalChartData

variable {C : Over (Spec (.of k))} (data : DiagonalChartData C) (p : C.left)

/-- The frozen idempotent lift on the chart at `p`, from brick B0's packaged localization
statement `exists_diagonalLocalization` (whose formal-unramifiedness / essential-finiteness
hypotheses are supplied by `etale`).  This is the `elift` fed to brick B4's diagonal member and
equation. -/
noncomputable def elift : Γ(C.left, data.chart p) ⊗[k] Γ(C.left, data.chart p) :=
  letI := data.coordAlgebra p
  haveI := data.isScalarTower p
  haveI := data.etale p
  (AlgebraicJacobian.Diagonal.exists_diagonalLocalization
    (k := k) (B := Γ(C.left, data.chart p))).choose

/-- `mul (elift) = 0`: the idempotent lift lies in the `k`-diagonal ideal (B0). -/
lemma lmul'_elift :
    Algebra.TensorProduct.lmul' k (data.elift p) = 0 :=
  letI := data.coordAlgebra p
  haveI := data.isScalarTower p
  haveI := data.etale p
  (AlgebraicJacobian.Diagonal.exists_diagonalLocalization
    (k := k) (B := Γ(C.left, data.chart p))).choose_spec.1

/-- The lift's base-change idempotency (B0), in exactly brick B4's `hidem` shape. -/
lemma isIdempotentElem_baseChange_elift :
    letI := data.coordAlgebra p
    haveI := data.isScalarTower p
    IsIdempotentElem (AlgebraicJacobian.Diagonal.baseChange (data.elift p)) :=
  letI := data.coordAlgebra p
  haveI := data.isScalarTower p
  haveI := data.etale p
  (AlgebraicJacobian.Diagonal.exists_diagonalLocalization
    (k := k) (B := Γ(C.left, data.chart p))).choose_spec.2.1

/-- The `Polynomial k`-diagonal ideal is generated by the base-change of the lift (B0), in
exactly brick B4's `hgen` shape. -/
lemma ker_lmul'_eq_span_baseChange_elift :
    letI := data.coordAlgebra p
    haveI := data.isScalarTower p
    RingHom.ker (Algebra.TensorProduct.lmul'
        (R := Polynomial k) (S := Γ(C.left, data.chart p)))
      = Ideal.span {AlgebraicJacobian.Diagonal.baseChange (data.elift p)} :=
  letI := data.coordAlgebra p
  haveI := data.isScalarTower p
  haveI := data.etale p
  (AlgebraicJacobian.Diagonal.exists_diagonalLocalization
    (k := k) (B := Γ(C.left, data.chart p))).choose_spec.2.2.1

end DiagonalChartData

end Over

end AlgebraicGeometry
