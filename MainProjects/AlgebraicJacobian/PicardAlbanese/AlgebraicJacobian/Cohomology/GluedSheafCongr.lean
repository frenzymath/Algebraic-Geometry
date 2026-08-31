/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheaf
import AlgebraicJacobian.Cohomology.RigidEngine4Twist
import AlgebraicJacobian.RiemannRoch.Chi

/-!
# Cohomologous cocycles glue isomorphic sheaves (DAT-3, the `congrCoeff` transport)

For a scheme `X` over `Spec k`, pieces `U : J → X.Opens` and two multiplier families
`g, g'` on the pairwise overlaps, a unit `0`-cochain `c : ∀ j, Γ(X, U j)ˣ` with
`c_i · g_{ij} = g'_{ij} · c_j` on every double overlap (the landed `IsCohomologous`
convention of the Čech Picard lane, in `resHom` spelling —
`AlgebraicGeometry.Scheme.IsGluingCoboundary`) induces an isomorphism of the glued
sheaves, componentwise `s_j ↦ c_j · s_j`:

* `AlgebraicGeometry.gluedCongrEquiv` — the `k`-linear equivalence of glued sections
  over every open `W`;
* `AlgebraicGeometry.gluedSheafCongr` — the isomorphism of sheaves of `k`-modules
  `gluedSheaf k U g ≅ gluedSheaf k U g'`;
* `AlgebraicGeometry.subsingleton_hModule_gluedSheaf_congr` — transport of cohomology
  vanishing across the isomorphism (via `Sheaf.HModule.mapEquiv`).

This is the m-chart generalization of the landed two-cover `congrCoeff` pattern
(`CategoryTheory.Sheaf.HModule'.congrCoeff`, `Cohomology/RelativeTwoCover.lean`),
per the frozen W6-full spec (`informal/w4-datum-worksheet.md` §3.1(c)): cohomologous
cocycles present isomorphic glued sheaves. Neither multiplier family needs the cocycle
law — the transport is pure matching algebra.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- **The gluing coboundary relation**: the multiplier family `g'` is cohomologous to
`g` through the unit `0`-cochain `c`, i.e. `c_i · g_{ij} = g'_{ij} · c_j` in
`Γ(X, U i ⊓ U j)` for all `i, j` (the landed `IsCohomologous` convention of the Čech
Picard lane, in `resHom` spelling). -/
def Scheme.IsGluingCoboundary {X : Scheme.{u}} {J : Type u} (U : J → X.Opens)
    (g g' : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ) (c : ∀ j : J, Γ(X, U j)ˣ) : Prop :=
  ∀ i j : J,
    X.resHom (inf_le_left : U i ⊓ U j ≤ U i) (c i : Γ(X, U i)) *
        (g i j : Γ(X, U i ⊓ U j)) =
      (g' i j : Γ(X, U i ⊓ U j)) *
        X.resHom (inf_le_right : U i ⊓ U j ≤ U j) (c j : Γ(X, U j))

namespace Scheme.IsGluingCoboundary

variable {X : Scheme.{u}} {J : Type u} {U : J → X.Opens}
variable {g g' : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ} {c : ∀ j : J, Γ(X, U j)ˣ}

/-- **Inversion of the coboundary**: if `g'` is cohomologous to `g` through `c`, then
`g` is cohomologous to `g'` through the inverse cochain `c⁻¹`. -/
lemma inv (hc : Scheme.IsGluingCoboundary U g g' c) :
    Scheme.IsGluingCoboundary U g' g (fun j => (c j)⁻¹) := by
  intro i j
  set a := X.resHom (inf_le_left : U i ⊓ U j ≤ U i) (c i : Γ(X, U i)) with ha
  set a' := X.resHom (inf_le_left : U i ⊓ U j ≤ U i)
    (((c i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) with ha'
  set b := X.resHom (inf_le_right : U i ⊓ U j ≤ U j) (c j : Γ(X, U j)) with hb
  set b' := X.resHom (inf_le_right : U i ⊓ U j ≤ U j)
    (((c j)⁻¹ : Γ(X, U j)ˣ) : Γ(X, U j)) with hb'
  have haa : a' * a = 1 := by rw [ha, ha', ← map_mul, Units.inv_mul, map_one]
  have hbb : b * b' = 1 := by rw [hb, hb', ← map_mul, Units.mul_inv, map_one]
  have key : a * (g i j : Γ(X, U i ⊓ U j)) = (g' i j : Γ(X, U i ⊓ U j)) * b := hc i j
  calc a' * (g' i j : Γ(X, U i ⊓ U j))
      = a' * (g' i j : Γ(X, U i ⊓ U j)) * (b * b') := by rw [hbb, mul_one]
    _ = a' * ((g' i j : Γ(X, U i ⊓ U j)) * b) * b' := by ring
    _ = a' * (a * (g i j : Γ(X, U i ⊓ U j))) * b' := by rw [key]
    _ = (a' * a) * (g i j : Γ(X, U i ⊓ U j)) * b' := by ring
    _ = (g i j : Γ(X, U i ⊓ U j)) * b' := by rw [haa, one_mul]

end Scheme.IsGluingCoboundary

section Congr

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

attribute [local instance] Scheme.overModule

variable {J : Type u} {U : J → X.Opens} {g g' : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ}
variable (c : ∀ j : J, Γ(X, U j)ˣ)

/-- **The coboundary transport preserves matching**: multiplying the `j`-th component by
(the restriction of) `c j` carries families matching through `g` to families matching
through `g'`. -/
lemma gluedCongr_mem (hc : Scheme.IsGluingCoboundary U g g' c) {W : X.Opens}
    {s : ∀ j : J, Γ(X, W ⊓ U j)} (hs : s ∈ gluedSubmodule k U g W) :
    (fun j => X.resHom (inf_le_right : W ⊓ U j ≤ U j) (c j : Γ(X, U j)) * s j)
      ∈ gluedSubmodule k U g' W := by
  intro i j
  have hcob := congrArg (X.resHom (gluedInclCoc U W i j)) (hc i j)
  have hmatch := (mem_gluedSubmodule_iff k U g s).mp hs i j
  rw [map_mul, map_mul] at hcob
  rw [map_mul, map_mul]
  simp only [Scheme.resHom_resHom] at hcob hmatch ⊢
  rw [hmatch, ← mul_assoc, hcob, mul_assoc, mul_left_comm]

variable (g g') in
/-- **The coboundary transport of glued sections**, as a `k`-linear equivalence:
componentwise multiplication by the unit `0`-cochain `c` (inverse: componentwise
multiplication by `c⁻¹`). -/
noncomputable def gluedCongrEquiv (hc : Scheme.IsGluingCoboundary U g g' c)
    (W : X.Opens) :
    ↥(gluedSubmodule k U g W) ≃ₗ[k] ↥(gluedSubmodule k U g' W) where
  toFun s := ⟨fun j => X.resHom (inf_le_right : W ⊓ U j ≤ U j) (c j : Γ(X, U j)) *
    s.val j, gluedCongr_mem k c hc s.property⟩
  map_add' s t := Subtype.ext (funext fun j => by
    change X.resHom _ (c j : Γ(X, U j)) * (s.val j + t.val j) = _
    rw [mul_add]
    rfl)
  map_smul' r s := Subtype.ext (funext fun j => by
    change X.resHom _ (c j : Γ(X, U j)) * (r • s.val j) = _
    rw [Scheme.overModule_smul_def, mul_left_comm]
    rfl)
  invFun t := ⟨fun j => X.resHom (inf_le_right : W ⊓ U j ≤ U j)
    (((c j)⁻¹ : Γ(X, U j)ˣ) : Γ(X, U j)) * t.val j,
    gluedCongr_mem k (fun j => (c j)⁻¹) hc.inv t.property⟩
  left_inv s := Subtype.ext (funext fun j => by
    change X.resHom _ (((c j)⁻¹ : Γ(X, U j)ˣ) : Γ(X, U j)) *
      (X.resHom _ (c j : Γ(X, U j)) * s.val j) = s.val j
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul])
  right_inv t := Subtype.ext (funext fun j => by
    change X.resHom _ (c j : Γ(X, U j)) *
      (X.resHom _ (((c j)⁻¹ : Γ(X, U j)ˣ) : Γ(X, U j)) * t.val j) = t.val j
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul])

@[simp]
lemma gluedCongrEquiv_apply_coe (hc : Scheme.IsGluingCoboundary U g g' c)
    {W : X.Opens} (s : ↥(gluedSubmodule k U g W)) (j : J) :
    (gluedCongrEquiv k g g' c hc W s).val j =
      X.resHom (inf_le_right : W ⊓ U j ≤ U j) (c j : Γ(X, U j)) * s.val j :=
  rfl

/-- The coboundary transport commutes with restriction. -/
lemma gluedCongrEquiv_res (hc : Scheme.IsGluingCoboundary U g g' c)
    {W' W : X.Opens} (h : W' ≤ W) (s : ↥(gluedSubmodule k U g W)) :
    gluedCongrEquiv k g g' c hc W' (gluedRes k U g h s) =
      gluedRes k U g' h (gluedCongrEquiv k g g' c hc W s) := by
  refine Subtype.ext (funext fun j => ?_)
  rw [gluedCongrEquiv_apply_coe, gluedRes_coe, gluedRes_coe, gluedCongrEquiv_apply_coe,
    map_mul]
  simp only [Scheme.resHom_resHom]

variable (g g') in
/-- **The presheaf isomorphism of cohomologous glued presheaves**, componentwise
multiplication by the unit `0`-cochain. -/
noncomputable def gluedCongrPresheafIso (hc : Scheme.IsGluingCoboundary U g g' c) :
    gluedPresheaf k U g ≅ gluedPresheaf k U g' :=
  NatIso.ofComponents
    (fun W => (gluedCongrEquiv k g g' c hc W.unop).toModuleIso)
    (fun {A B} i => by
      ext s
      exact gluedCongrEquiv_res k c hc i.unop.le s)

variable (g g') in
/-- **Cohomologous cocycles glue isomorphic sheaves** (the m-chart `congrCoeff`
transport, W6-full spec §3.1(c)): a unit `0`-cochain `c` with `c_i g_{ij} = g'_{ij} c_j`
induces an isomorphism `gluedSheaf k U g ≅ gluedSheaf k U g'` of sheaves of
`k`-modules, componentwise `s_j ↦ c_j · s_j`. -/
noncomputable def gluedSheafCongr (hc : Scheme.IsGluingCoboundary U g g' c) :
    gluedSheaf k U g ≅ gluedSheaf k U g' :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (gluedCongrPresheafIso k g g' c hc)

/-- **Cohomology vanishing transports across the coboundary**: the glued sheaves of
cohomologous multiplier families have simultaneously vanishing cohomology in every
degree. -/
theorem subsingleton_hModule_gluedSheaf_congr (hc : Scheme.IsGluingCoboundary U g g' c)
    (n : ℕ) :
    Subsingleton (Sheaf.HModule (gluedSheaf k U g) n) ↔
      Subsingleton (Sheaf.HModule (gluedSheaf k U g') n) :=
  (Sheaf.HModule.mapEquiv (gluedSheafCongr k g g' c hc) n).toEquiv.subsingleton_congr

end Congr

end AlgebraicGeometry
