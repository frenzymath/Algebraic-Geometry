/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RigidEngine4Assembly
import AlgebraicJacobian.Cohomology.RigidEngine4AEval
import AlgebraicJacobian.Cohomology.TwistedSheaf

/-!
# RE-4 — the two-cover pair data of a twisted sheaf

The Layer-2 discharge of the abstract pair data (`Scheme.TwoCoverPairData`,
`RigidEngine4Assembly`) for the cocycle-glued twisted sheaf `twistSheaf k V₀ V₁ g`
(`TwistedSheaf.lean`), generic in the base ring `k` — the relative instantiation on the
pinned cover of the relative curve is in `AlgebraicJacobian.Cohomology.RigidEngine4Relative`.

The twisted sheaf's packaging `QcohOn (twistSheaf k V₀ V₁ g) Vᵢ` is the structure sheaf's,
transported along the chart trivializations `twistTriv₀/₁`; consequently every pair-data
field reduces to section algebra in `Γ(X, −)`:

* `twistSheaf_qsmul₀_eq`/`₁` — the packaged action is trivialize-multiply-untrivialize
  (definitional unfolding of `Scheme.QcohOn.ofSectionsEquiv`).
* `twistSheaf_smul_qsmul₀`/`₁` — `k`-linearity of the coordinate actions (multiplication
  commutes with the `Scheme.overModule` scalars).
* `twistTriv₀_inf_eq` — on the overlap the two trivializations differ by the cocycle:
  `triv₀ = g · triv₁` (the defining equation of the twisted sections, restricted along
  `V₀ ⊓ V₁ ≤ V₀ ⊓ V₁ ⊓ V₀ ⊓ V₁`).
* `twistSheaf_qsmul₀_qsmul₁`/`₁₀` — the mutual-inverse law of the coordinate actions from
  the section relation `r₀ · r₁ = 1` on the overlap.
* `AlgebraicGeometry.twistPairData` — **the pair data**, assembling the above; its
  `pair` (from `RigidEngine4Assembly`) is the two-lattice pair of the twisted sheaf.
* `moduleFinite_aeval'_twistPair_t₀`/`t₁` — the pinned `AEval'`-finiteness of the twist
  pair's chart lattices, transported through the trivializations from the corresponding
  multiplication endomorphisms on `Γ(X, Vᵢ)` (`Scheme.mulSectionEnd`); the finiteness of
  the latter is the relative E-i, discharged in `RigidEngine4Relative`.
* `free_twistSheafSections₀`/`₁` — freeness of the twisted section modules from freeness
  of the structure-sheaf sections (a `k`-basis transported along the trivialization),
  feeding the engine's flatness/projectivity hypotheses.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace Polynomial

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

attribute [local instance] Scheme.overModule

/-! ## Multiplication by a section as an endomorphism -/

/-- Multiplication by a fixed section, as a `k`-linear endomorphism of a section module
(with the `Scheme.overModule` structure). The comparison endomorphism through which the
twist pair's chart coordinate actions are identified with honest section multiplication. -/
noncomputable def Scheme.mulSectionEnd {U : X.Opens} (c : Γ(X, U)) :
    Module.End k Γ(X, U) where
  toFun s := c * s
  map_add' := mul_add c
  map_smul' r s := by
    rw [RingHom.id_apply, Scheme.overModule_smul_def, Scheme.overModule_smul_def,
      mul_left_comm]

@[simp]
lemma Scheme.mulSectionEnd_apply {U : X.Opens} (c s : Γ(X, U)) :
    Scheme.mulSectionEnd k c s = c * s := rfl

/-! ## The packaged coordinate actions of the twisted sheaf -/

variable (V₀ V₁ : X.Opens) (g : Γ(X, V₀ ⊓ V₁)ˣ)

/-- The packaged chart-0 action of the twisted sheaf is
trivialize-multiply-untrivialize. -/
lemma twistSheaf_qsmul₀_eq {W : X.Opens} (hW : W ≤ V₀) (r : Γ(X, V₀))
    (m : ↥(twistSubmodule k V₀ V₁ g W)) :
    Scheme.QcohOn.qsmul (F := twistSheaf k V₀ V₁ g) hW r m
      = (twistTriv₀ k V₀ V₁ g hW).symm
          (X.resHom hW r * twistTriv₀ k V₀ V₁ g hW m) := rfl

/-- The packaged chart-1 action of the twisted sheaf is
trivialize-multiply-untrivialize. -/
lemma twistSheaf_qsmul₁_eq {W : X.Opens} (hW : W ≤ V₁) (r : Γ(X, V₁))
    (m : ↥(twistSubmodule k V₀ V₁ g W)) :
    Scheme.QcohOn.qsmul (F := twistSheaf k V₀ V₁ g) hW r m
      = (twistTriv₁ k V₀ V₁ g hW).symm
          (X.resHom hW r * twistTriv₁ k V₀ V₁ g hW m) := rfl

/-- The packaged chart-0 action of the twisted sheaf is `k`-linear. -/
lemma twistSheaf_smul_qsmul₀ {W : X.Opens} (hW : W ≤ V₀) (r : Γ(X, V₀)) (c : k)
    (m : ↥(twistSubmodule k V₀ V₁ g W)) :
    Scheme.QcohOn.qsmul (F := twistSheaf k V₀ V₁ g) hW r (c • m)
      = c • Scheme.QcohOn.qsmul (F := twistSheaf k V₀ V₁ g) hW r m := by
  have hmul : X.resHom hW r * (c • twistTriv₀ k V₀ V₁ g hW m)
      = c • (X.resHom hW r * twistTriv₀ k V₀ V₁ g hW m) := by
    rw [Scheme.overModule_smul_def, Scheme.overModule_smul_def, mul_left_comm]
  rw [twistSheaf_qsmul₀_eq, twistSheaf_qsmul₀_eq, map_smul, hmul, map_smul]
  rfl

/-- The packaged chart-1 action of the twisted sheaf is `k`-linear. -/
lemma twistSheaf_smul_qsmul₁ {W : X.Opens} (hW : W ≤ V₁) (r : Γ(X, V₁)) (c : k)
    (m : ↥(twistSubmodule k V₀ V₁ g W)) :
    Scheme.QcohOn.qsmul (F := twistSheaf k V₀ V₁ g) hW r (c • m)
      = c • Scheme.QcohOn.qsmul (F := twistSheaf k V₀ V₁ g) hW r m := by
  have hmul : X.resHom hW r * (c • twistTriv₁ k V₀ V₁ g hW m)
      = c • (X.resHom hW r * twistTriv₁ k V₀ V₁ g hW m) := by
    rw [Scheme.overModule_smul_def, Scheme.overModule_smul_def, mul_left_comm]
  rw [twistSheaf_qsmul₁_eq, twistSheaf_qsmul₁_eq, map_smul, hmul, map_smul]
  rfl

/-! ## The two trivializations on the overlap -/

/-- **On the overlap the two trivializations differ by the cocycle**: `triv₀ = g · triv₁`
on `F_g(V₀ ⊓ V₁)` — the defining equation of the twisted sections, restricted along
`V₀ ⊓ V₁ ≤ V₀ ⊓ V₁ ⊓ V₀ ⊓ V₁`. -/
lemma twistTriv₀_inf_eq (p : ↥(twistSubmodule k V₀ V₁ g (V₀ ⊓ V₁))) :
    twistTriv₀ k V₀ V₁ g (inf_le_left : V₀ ⊓ V₁ ≤ V₀) p
      = (g : Γ(X, V₀ ⊓ V₁)) *
          twistTriv₁ k V₀ V₁ g (inf_le_right : V₀ ⊓ V₁ ≤ V₁) p := by
  have hp := (mem_twistSubmodule_iff k V₀ V₁ g
    (p.val : Γ(X, V₀ ⊓ V₁ ⊓ V₀) × Γ(X, V₀ ⊓ V₁ ⊓ V₁))).mp p.property
  have h := congrArg (X.resHom (le_inf (le_inf le_rfl inf_le_left) inf_le_right :
    V₀ ⊓ V₁ ≤ V₀ ⊓ V₁ ⊓ V₀ ⊓ V₁)) hp
  rw [map_mul] at h
  simp only [Scheme.resHom_resHom] at h
  rw [Scheme.resHom_self] at h
  exact h

/-- The inverse form of `twistTriv₀_inf_eq`: `triv₁ = g⁻¹ · triv₀` on the overlap. -/
lemma twistTriv₁_inf_eq (p : ↥(twistSubmodule k V₀ V₁ g (V₀ ⊓ V₁))) :
    twistTriv₁ k V₀ V₁ g (inf_le_right : V₀ ⊓ V₁ ≤ V₁) p
      = ((g⁻¹ : Γ(X, V₀ ⊓ V₁)ˣ) : Γ(X, V₀ ⊓ V₁)) *
          twistTriv₀ k V₀ V₁ g (inf_le_left : V₀ ⊓ V₁ ≤ V₀) p := by
  rw [twistTriv₀_inf_eq, Units.inv_mul_cancel_left]

/-! ## The mutual-inverse law of the coordinate actions -/

variable {V₀ V₁}

/-- The mutual-inverse law `r₀ r₁ = 1` on sections makes the two packaged coordinate
actions inverse on the overlap sections of the twisted sheaf (`g₀ ∘ g₁ = id`). -/
lemma twistSheaf_qsmul₀_qsmul₁ (r₀ : Γ(X, V₀)) (r₁ : Γ(X, V₁))
    (hmul : X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ *
      X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ = 1)
    (m : ↥(twistSubmodule k V₀ V₁ g (V₀ ⊓ V₁))) :
    Scheme.QcohOn.qsmul (F := twistSheaf k V₀ V₁ g) (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀
      (Scheme.QcohOn.qsmul (F := twistSheaf k V₀ V₁ g)
        (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ m) = m := by
  rw [twistSheaf_qsmul₁_eq, twistSheaf_qsmul₀_eq, twistTriv₀_inf_eq,
    LinearEquiv.apply_symm_apply]
  have hring : X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ *
      ((g : Γ(X, V₀ ⊓ V₁)) * (X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ *
        twistTriv₁ k V₀ V₁ g (inf_le_right : V₀ ⊓ V₁ ≤ V₁) m))
      = (g : Γ(X, V₀ ⊓ V₁)) *
          twistTriv₁ k V₀ V₁ g (inf_le_right : V₀ ⊓ V₁ ≤ V₁) m := by
    calc X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ *
        ((g : Γ(X, V₀ ⊓ V₁)) * (X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ *
          twistTriv₁ k V₀ V₁ g (inf_le_right : V₀ ⊓ V₁ ≤ V₁) m))
        = (X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ *
            X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁) *
            ((g : Γ(X, V₀ ⊓ V₁)) *
              twistTriv₁ k V₀ V₁ g (inf_le_right : V₀ ⊓ V₁ ≤ V₁) m) := by ring
      _ = _ := by rw [hmul, one_mul]
  rw [hring, ← twistTriv₀_inf_eq, LinearEquiv.symm_apply_apply]

/-- The mutual-inverse law `r₀ r₁ = 1` on sections makes the two packaged coordinate
actions inverse on the overlap sections of the twisted sheaf (`g₁ ∘ g₀ = id`). -/
lemma twistSheaf_qsmul₁_qsmul₀ (r₀ : Γ(X, V₀)) (r₁ : Γ(X, V₁))
    (hmul : X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ *
      X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ = 1)
    (m : ↥(twistSubmodule k V₀ V₁ g (V₀ ⊓ V₁))) :
    Scheme.QcohOn.qsmul (F := twistSheaf k V₀ V₁ g) (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁
      (Scheme.QcohOn.qsmul (F := twistSheaf k V₀ V₁ g)
        (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ m) = m := by
  rw [twistSheaf_qsmul₀_eq, twistSheaf_qsmul₁_eq, twistTriv₁_inf_eq,
    LinearEquiv.apply_symm_apply]
  have hring : X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ *
      (((g⁻¹ : Γ(X, V₀ ⊓ V₁)ˣ) : Γ(X, V₀ ⊓ V₁)) *
        (X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ *
          twistTriv₀ k V₀ V₁ g (inf_le_left : V₀ ⊓ V₁ ≤ V₀) m))
      = ((g⁻¹ : Γ(X, V₀ ⊓ V₁)ˣ) : Γ(X, V₀ ⊓ V₁)) *
          twistTriv₀ k V₀ V₁ g (inf_le_left : V₀ ⊓ V₁ ≤ V₀) m := by
    calc X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ *
        (((g⁻¹ : Γ(X, V₀ ⊓ V₁)ˣ) : Γ(X, V₀ ⊓ V₁)) *
          (X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ *
            twistTriv₀ k V₀ V₁ g (inf_le_left : V₀ ⊓ V₁ ≤ V₀) m))
        = (X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ *
            X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁) *
            (((g⁻¹ : Γ(X, V₀ ⊓ V₁)ˣ) : Γ(X, V₀ ⊓ V₁)) *
              twistTriv₀ k V₀ V₁ g (inf_le_left : V₀ ⊓ V₁ ≤ V₀) m) := by ring
      _ = _ := by rw [hmul, one_mul]
  rw [hring, ← twistTriv₁_inf_eq, LinearEquiv.symm_apply_apply]

/-! ## The pair data of the twisted sheaf -/

/-- **The two-cover pair data of the twisted sheaf** (RE-4, Layer 2, abstract half):
chart coordinates `r₀, r₁` whose basic opens are the overlap and whose product is `1` on
the overlap yield the full `Scheme.TwoCoverPairData` for `twistSheaf k V₀ V₁ g` — hence,
through `Scheme.TwoCoverPairData.pair`, the two-lattice pair of the twisted sheaf. -/
noncomputable def twistPairData (r₀ : Γ(X, V₀)) (r₁ : Γ(X, V₁))
    (hb₀ : V₀ ⊓ V₁ = X.basicOpen r₀) (hb₁ : V₀ ⊓ V₁ = X.basicOpen r₁)
    (hmul : X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ *
      X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ = 1) :
    Scheme.TwoCoverPairData (twistSheaf k V₀ V₁ g) V₀ V₁ where
  g₀ := r₀
  g₁ := r₁
  inf_eq_basicOpen₀ := hb₀
  inf_eq_basicOpen₁ := hb₁
  smul_qsmul₀ := fun hW c m => twistSheaf_smul_qsmul₀ k V₀ V₁ g hW r₀ c m
  smul_qsmul₁ := fun hW c m => twistSheaf_smul_qsmul₁ k V₀ V₁ g hW r₁ c m
  qsmul₀_qsmul₁ := fun m => twistSheaf_qsmul₀_qsmul₁ k g r₀ r₁ hmul m
  qsmul₁_qsmul₀ := fun m => twistSheaf_qsmul₁_qsmul₀ k g r₀ r₁ hmul m

section Finiteness

variable (r₀ : Γ(X, V₀)) (r₁ : Γ(X, V₁))
variable (hb₀ : V₀ ⊓ V₁ = X.basicOpen r₀) (hb₁ : V₀ ⊓ V₁ = X.basicOpen r₁)
variable (hmul : X.resHom (inf_le_left : V₀ ⊓ V₁ ≤ V₀) r₀ *
  X.resHom (inf_le_right : V₀ ⊓ V₁ ≤ V₁) r₁ = 1)
variable (hV₀ : IsAffineOpen V₀) (hV₁ : IsAffineOpen V₁)

open AlgebraicJacobian

/-- **The pinned `AEval'`-finiteness of the twist pair's chart-0 lattice**, transported
through the trivialization from the multiplication endomorphism on `Γ(X, V₀)`. -/
theorem moduleFinite_aeval'_twistPair_t₀
    [Module.Finite k[X]
      (Module.AEval' (Scheme.mulSectionEnd k (U := V₀) r₀))] :
    Module.Finite k[X] (Module.AEval'
      ((twistPairData k g r₀ r₁ hb₀ hb₁ hmul).pair hV₀ hV₁).t₀) := by
  refine RigidEngine.moduleFinite_aeval'_of_linearEquiv
    (Scheme.mulSectionEnd k (U := V₀) r₀) _
    (twistTriv₀ k V₀ V₁ g (le_refl V₀)).symm (fun s => ?_)
  change (twistTriv₀ k V₀ V₁ g (le_refl V₀)).symm (r₀ * s)
      = (twistTriv₀ k V₀ V₁ g (le_refl V₀)).symm
          (X.resHom (le_refl V₀) r₀ * twistTriv₀ k V₀ V₁ g (le_refl V₀)
            ((twistTriv₀ k V₀ V₁ g (le_refl V₀)).symm s))
  rw [LinearEquiv.apply_symm_apply, Scheme.resHom_self]

/-- **The pinned `AEval'`-finiteness of the twist pair's chart-1 lattice**, transported
through the trivialization from the multiplication endomorphism on `Γ(X, V₁)`. -/
theorem moduleFinite_aeval'_twistPair_t₁
    [Module.Finite k[X]
      (Module.AEval' (Scheme.mulSectionEnd k (U := V₁) r₁))] :
    Module.Finite k[X] (Module.AEval'
      ((twistPairData k g r₀ r₁ hb₀ hb₁ hmul).pair hV₀ hV₁).t₁) := by
  refine RigidEngine.moduleFinite_aeval'_of_linearEquiv
    (Scheme.mulSectionEnd k (U := V₁) r₁) _
    (twistTriv₁ k V₀ V₁ g (le_refl V₁)).symm (fun s => ?_)
  change (twistTriv₁ k V₀ V₁ g (le_refl V₁)).symm (r₁ * s)
      = (twistTriv₁ k V₀ V₁ g (le_refl V₁)).symm
          (X.resHom (le_refl V₁) r₁ * twistTriv₁ k V₀ V₁ g (le_refl V₁)
            ((twistTriv₁ k V₀ V₁ g (le_refl V₁)).symm s))
  rw [LinearEquiv.apply_symm_apply, Scheme.resHom_self]

end Finiteness

/-! ## Freeness of the twisted section modules -/

/-- Twisted sections over `W ≤ V₀` are free whenever the structure-sheaf sections are:
a `k`-basis transported along the chart trivialization. -/
theorem free_twistSheafSections₀ {W : X.Opens} (hW : W ≤ V₀)
    [Module.Free k Γ(X, W)] :
    Module.Free k ↥(twistSubmodule k V₀ V₁ g W) :=
  Module.Free.of_equiv (twistTriv₀ k V₀ V₁ g hW).symm

/-- Twisted sections over `W ≤ V₁` are free whenever the structure-sheaf sections are. -/
theorem free_twistSheafSections₁ {W : X.Opens} (hW : W ≤ V₁)
    [Module.Free k Γ(X, W)] :
    Module.Free k ↥(twistSubmodule k V₀ V₁ g W) :=
  Module.Free.of_equiv (twistTriv₁ k V₀ V₁ g hW).symm

end AlgebraicGeometry
