/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafQcohAssembly
import AlgebraicJacobian.Cohomology.RigidEngine4Assembly

/-!
# The two-cover pair data of the m-chart glued sheaf (DAT-1, stage 1b-ii)

The mirror of `AlgebraicGeometry.twistPairData` (`RigidEngine4Twist.lean`) for the
m-chart glued sheaf: on a two-chart cover `V₀, V₁` carrying quasi-coherence packagings
whose actions are the **componentwise** ones (`gluedQsmul` — the hypothesis pair
`hq₀/hq₁`, discharged by `rfl` when the instances are built by `gluedQcohOn`), chart
coordinates `r₀, r₁` with the overlap-as-basic-open identities and `r₀ · r₁ = 1` on the
overlap yield the full `Scheme.TwoCoverPairData` for `gluedSheaf k U g`.

Unlike the 2-chart twisted sheaf (where the mutual-inverse law needed the cocycle
conjugation `twistTriv₀_inf_eq`), the m-chart law is pure componentwise ring algebra:
`gluedQsmul_inv_of_mul_res_eq_one`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

section Pair

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

attribute [local instance] Scheme.overModule

variable {J : Type u} (U : J → X.Opens) (g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ)
variable {V₀ V₁ : X.Opens}

/-- **The componentwise mutual-inverse law**: chart coordinates multiplying to `1` on
the overlap act inversely on the glued sections of the overlap. -/
lemma gluedQsmul_inv_of_mul_res_eq_one (r₀ : Γ(X, V₀)) (r₁ : Γ(X, V₁))
    (hmul : X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ *
      X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ = 1)
    (m : ↥(gluedSubmodule k U g (V₀ ⊓ V₁))) :
    gluedQsmul k U g (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀
      (gluedQsmul k U g (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ m) = m := by
  refine Subtype.ext (funext fun j => ?_)
  rw [gluedQsmul_coe, gluedQsmul_coe, ← mul_assoc]
  have hres := congrArg
    (X.resHom (inf_le_left : (V₀ ⊓ V₁) ⊓ U j ≤ V₀ ⊓ V₁)) hmul
  rw [map_mul, map_one] at hres
  simp only [Scheme.resHom_resHom] at hres
  rw [hres, one_mul]

/-- **The two-cover pair data of the m-chart glued sheaf** (the `twistPairData` mirror):
for packagings on the two charts whose actions are componentwise (`hq₀`, `hq₁` — `rfl`
for instances built by `gluedQcohOn`), chart coordinates `r₀, r₁` whose basic opens are
the overlap and whose product is `1` on the overlap yield the full
`Scheme.TwoCoverPairData` — hence, through `Scheme.TwoCoverPairData.pair`, the
two-lattice pair of the glued sheaf that the rigid engine consumes. -/
noncomputable def gluedPairData
    [Scheme.QcohOn (gluedSheaf k U g) V₀] [Scheme.QcohOn (gluedSheaf k U g) V₁]
    (hq₀ : ∀ {W : X.Opens} (hW : W ≤ V₀) (r : Γ(X, V₀))
      (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    (hq₁ : ∀ {W : X.Opens} (hW : W ≤ V₁) (r : Γ(X, V₁))
      (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    (r₀ : Γ(X, V₀)) (r₁ : Γ(X, V₁))
    (hb₀ : V₀ ⊓ V₁ = X.basicOpen r₀) (hb₁ : V₀ ⊓ V₁ = X.basicOpen r₁)
    (hmul : X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ *
      X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ = 1) :
    Scheme.TwoCoverPairData (gluedSheaf k U g) V₀ V₁ where
  g₀ := r₀
  g₁ := r₁
  inf_eq_basicOpen₀ := hb₀
  inf_eq_basicOpen₁ := hb₁
  smul_qsmul₀ hW c m := by
    rw [hq₀ hW r₀ m, hq₀ hW r₀ (c • m)]
    exact gluedQsmul_smul k U g hW r₀ c m
  smul_qsmul₁ hW c m := by
    rw [hq₁ hW r₁ m, hq₁ hW r₁ (c • m)]
    exact gluedQsmul_smul k U g hW r₁ c m
  qsmul₀_qsmul₁ m := by
    rw [hq₁ inf_le_right r₁ m, hq₀ inf_le_left r₀ _]
    exact gluedQsmul_inv_of_mul_res_eq_one k U g r₀ r₁ hmul m
  qsmul₁_qsmul₀ m := by
    rw [hq₀ inf_le_left r₀ m, hq₁ inf_le_right r₁ _]
    have hmul' : X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ *
        X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ = 1 := by
      rw [mul_comm]
      exact hmul
    refine Subtype.ext (funext fun j => ?_)
    rw [gluedQsmul_coe, gluedQsmul_coe, ← mul_assoc]
    have hres := congrArg
      (X.resHom (inf_le_left : (V₀ ⊓ V₁) ⊓ U j ≤ V₀ ⊓ V₁)) hmul'
    rw [map_mul, map_one] at hres
    simp only [Scheme.resHom_resHom] at hres
    rw [hres, one_mul]

end Pair

end AlgebraicGeometry
