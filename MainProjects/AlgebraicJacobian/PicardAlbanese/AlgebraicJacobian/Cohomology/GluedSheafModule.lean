/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafQcohAssembly
import AlgebraicJacobian.Cohomology.RigidEngine0Toolkit
import AlgebraicJacobian.Cohomology.RigidEngine4Twist
import AlgebraicJacobian.Cohomology.GluedAlgebra

/-!
# Chart-module structure of the m-chart glued sheaf (DAT-1, stage 1c)

The `Γ(X, V)`-module and coefficient-ring properties of the glued section module
`F(V)` on an affine chart `V` carrying a finite subordinate trivializing basic-open
family (`informal/spec-dat-1.md`, decision (D5)): sections `h : ι → Γ(X, V)` whose
basic opens `D(h i)` lie in gluing pieces (`hP : D(h i) ≤ U (σ i)`) and span the unit
ideal (`hspan : Ideal.span (Set.range h) = ⊤` — the worksheet partition witness feeds
this through `Ideal.span_range_eq_top_of_sum_eq_one`).

All statements are relative to an ambient packaging
`[Scheme.QcohOn (gluedSheaf k U g) V]` whose action is componentwise (the hypothesis
`hq`, discharged by `rfl` for packagings built by `gluedQcohOn` — the same interface as
`gluedPairData`), with the chart module structure `Scheme.QcohOn.moduleOfLE` bound by
`letI` in statements (RE-0 pattern) and the section modules in the sheaf-object
spelling `(gluedSheaf k U g).obj.obj (op W)` — the spelling the engine consumes.

* `gluedPieceModule`/`gluedPieceEquiv` — each piece `F(D(h i))` is a free rank-one
  `Γ(X, D(h i))`-module through the piece trivialization `gluedTriv`;
* `isUnit_algebraMap_end_glued` — a chart section restricting to a unit acts invertibly
  on the glued sections of an open below a piece (trivialization conjugation);
* `isLocalizedModule_secResₗ_glued` — **the RE-0 bridge fired per piece**:
  `F(V) → F(D(h i))` is an `IsLocalizedModule (Submonoid.powers (h i))` (the abstract
  bridge at `V ⊓ D(h i)`, transported across the opens equality `V ⊓ D(h i) = D(h i)`
  by `IsLocalizedModule.of_linearEquiv`);
* the localization-local chart properties: `moduleFinite_glued`,
  `finitePresentation_glued`, `flat_glued`, `projective_glued` (over `Γ(X, V)`), and
  the coefficient-ring transports `flat_glued_of_flat` (under `Module.Flat k Γ(X, V)` —
  a benign weakening of the spec's freeness hypothesis: free ⟹ flat) and
  `projective_glued_of_free` (under `Module.Free k Γ(X, V)`);
* `moduleFinite_aeval'_glued` — the `AEval'`-finiteness export: an endomorphism acting
  as the packaged action of a chart coordinate `a₀` has `k[X]`-finite chart lattice
  whenever `Scheme.mulSectionEnd k a₀` does (the landed E-i input), through
  `RigidEngine.moduleFinite_aeval'_of_smul_finite` and `moduleFinite_glued`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace Polynomial

/-! ## A partition of unity spans the unit ideal -/

/-- **Span-⊤ from a partition of unity**: if `∑ i, a i * h i = 1` in a commutative ring,
the range of `h` generates the unit ideal. -/
theorem Ideal.span_range_eq_top_of_sum_eq_one {A : Type u} [CommRing A] {ι : Type*}
    [Fintype ι] (a h : ι → A) (hpart : ∑ i, a i * h i = 1) :
    Ideal.span (Set.range h) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← hpart]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

namespace AlgebraicGeometry

section Module

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

attribute [local instance] Scheme.overModule

variable {J : Type u} (U : J → X.Opens) (g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ)

/-! ## Restriction bookkeeping -/

/-- Componentwise restriction composes. -/
lemma gluedRes_gluedRes {W'' W' W : X.Opens} (h₁ : W'' ≤ W') (h₂ : W' ≤ W)
    (s : ↥(gluedSubmodule k U g W)) :
    gluedRes k U g h₁ (gluedRes k U g h₂ s) = gluedRes k U g (h₁.trans h₂) s :=
  Subtype.ext (funext fun _ => by
    simp only [gluedRes_coe, Scheme.resHom_resHom])

/-- Componentwise restriction along `W ≤ W` is the identity. -/
lemma gluedRes_self {W : X.Opens} (hW : W ≤ W) (s : ↥(gluedSubmodule k U g W)) :
    gluedRes k U g hW s = s :=
  Subtype.ext (funext fun _ => Scheme.resHom_self _ _)

/-! ## The coefficient action of a structure-morphism scalar -/

/-- The componentwise action of the image `X.overAlgebraMap k V c` of a coefficient
`c : k` agrees with the `k`-module action on glued sections. -/
lemma gluedQsmul_overAlgebraMap {V W : X.Opens} (hWV : W ≤ V) (c : k)
    (m : ↥(gluedSubmodule k U g W)) :
    gluedQsmul k U g hWV (X.overAlgebraMap k V c) m = c • m := by
  refine Subtype.ext (funext fun j => ?_)
  have hc : (c • m).val j = c • m.val j := rfl
  rw [gluedQsmul_coe, hc, Scheme.overModule_smul_def]
  congr 1
  exact X.overAlgebraMap_apply_res k (homOfLE (inf_le_left.trans hWV)).op c

variable {V : X.Opens} {ι : Type u} {σ : ι → J} {h : ι → Γ(X, V)}

/-! ## The piece module structure -/

/-- **The `Aᵢ := Γ(X, D(h i))`-module structure on a piece** `Mᵢ := F(D(h i))`,
transported through the `k`-linear piece trivialization `tᵢ : Mᵢ ≃ₗ[k] Γ(X, D(h i))`:
`a • m := tᵢ⁻¹ (a * tᵢ m)`. This makes `Mᵢ` free of rank one over `Aᵢ`
(`gluedPieceEquiv`). -/
@[reducible] noncomputable def gluedPieceModule (hc : Scheme.IsGluingCocycle U g)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i)) (i : ι) :
    Module Γ(X, X.basicOpen (h i)) ↥(gluedSubmodule k U g (X.basicOpen (h i))) where
  smul a m := (gluedTriv k hc (σ i) (hP i)).symm (a * gluedTriv k hc (σ i) (hP i) m)
  one_smul m := by
    change (gluedTriv k hc (σ i) (hP i)).symm (1 * gluedTriv k hc (σ i) (hP i) m) = m
    rw [one_mul, LinearEquiv.symm_apply_apply]
  mul_smul a b m := by
    change (gluedTriv k hc (σ i) (hP i)).symm (a * b * gluedTriv k hc (σ i) (hP i) m) =
      (gluedTriv k hc (σ i) (hP i)).symm
        (a * gluedTriv k hc (σ i) (hP i)
          ((gluedTriv k hc (σ i) (hP i)).symm (b * gluedTriv k hc (σ i) (hP i) m)))
    rw [LinearEquiv.apply_symm_apply, mul_assoc]
  smul_zero a := by
    change (gluedTriv k hc (σ i) (hP i)).symm (a * gluedTriv k hc (σ i) (hP i) 0) = 0
    rw [map_zero, mul_zero, map_zero]
  smul_add a m n := by
    change (gluedTriv k hc (σ i) (hP i)).symm (a * gluedTriv k hc (σ i) (hP i) (m + n)) =
      (gluedTriv k hc (σ i) (hP i)).symm (a * gluedTriv k hc (σ i) (hP i) m) +
        (gluedTriv k hc (σ i) (hP i)).symm (a * gluedTriv k hc (σ i) (hP i) n)
    rw [map_add, mul_add, map_add]
  add_smul a b m := by
    change (gluedTriv k hc (σ i) (hP i)).symm ((a + b) * gluedTriv k hc (σ i) (hP i) m) =
      (gluedTriv k hc (σ i) (hP i)).symm (a * gluedTriv k hc (σ i) (hP i) m) +
        (gluedTriv k hc (σ i) (hP i)).symm (b * gluedTriv k hc (σ i) (hP i) m)
    rw [add_mul, map_add]
  zero_smul m := by
    change (gluedTriv k hc (σ i) (hP i)).symm (0 * gluedTriv k hc (σ i) (hP i) m) = 0
    rw [zero_mul, map_zero]

lemma gluedPieceModule_smul_def (hc : Scheme.IsGluingCocycle U g)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i)) (i : ι)
    (a : Γ(X, X.basicOpen (h i))) (m : ↥(gluedSubmodule k U g (X.basicOpen (h i)))) :
    letI := gluedPieceModule k U g hc hP i
    a • m = (gluedTriv k hc (σ i) (hP i)).symm (a * gluedTriv k hc (σ i) (hP i) m) :=
  rfl

/-- **Each piece is `Aᵢ`-free of rank one**: the piece trivialization `tᵢ`, promoted to
an `Aᵢ`-linear equivalence `Mᵢ ≃ₗ[Aᵢ] Aᵢ` for the `gluedPieceModule` structure. -/
noncomputable def gluedPieceEquiv (hc : Scheme.IsGluingCocycle U g)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i)) (i : ι) :
    letI := gluedPieceModule k U g hc hP i
    ↥(gluedSubmodule k U g (X.basicOpen (h i))) ≃ₗ[Γ(X, X.basicOpen (h i))]
      Γ(X, X.basicOpen (h i)) :=
  letI := gluedPieceModule k U g hc hP i
  { toFun := gluedTriv k hc (σ i) (hP i)
    map_add' := (gluedTriv k hc (σ i) (hP i)).map_add
    map_smul' := fun a m => by
      change gluedTriv k hc (σ i) (hP i)
          ((gluedTriv k hc (σ i) (hP i)).symm (a * gluedTriv k hc (σ i) (hP i) m)) =
        a • gluedTriv k hc (σ i) (hP i) m
      rw [LinearEquiv.apply_symm_apply, smul_eq_mul]
    invFun := (gluedTriv k hc (σ i) (hP i)).symm
    left_inv := (gluedTriv k hc (σ i) (hP i)).left_inv
    right_inv := (gluedTriv k hc (σ i) (hP i)).right_inv }

@[simp]
lemma gluedPieceEquiv_apply (hc : Scheme.IsGluingCocycle U g)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i)) (i : ι)
    (m : ↥(gluedSubmodule k U g (X.basicOpen (h i)))) :
    gluedPieceEquiv k U g hc hP i m = gluedTriv k hc (σ i) (hP i) m :=
  rfl

@[simp]
lemma gluedPieceEquiv_symm_apply (hc : Scheme.IsGluingCocycle U g)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i)) (i : ι)
    (t : Γ(X, X.basicOpen (h i))) :
    (gluedPieceEquiv k U g hc hP i).symm t = (gluedTriv k hc (σ i) (hP i)).symm t :=
  rfl

/-- **The piece `Aᵢ`-action restricted along `A → Aᵢ` is the chart action**: for
`r : Γ(X, V)`, the `Aᵢ`-scalar `X.resHom … r` acts on `Mᵢ` as the componentwise chart
action `gluedQsmul`. -/
lemma gluedPieceModule_smul_resHom (hc : Scheme.IsGluingCocycle U g)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i)) (i : ι) (r : Γ(X, V))
    (m : ↥(gluedSubmodule k U g (X.basicOpen (h i)))) :
    letI := gluedPieceModule k U g hc hP i
    (X.resHom (X.basicOpen_le (h i)) r) • m =
      gluedQsmul k U g (X.basicOpen_le (h i)) r m := by
  letI := gluedPieceModule k U g hc hP i
  apply (gluedTriv k hc (σ i) (hP i)).injective
  rw [gluedTriv_gluedQsmul k U g hc, gluedPieceModule_smul_def,
    LinearEquiv.apply_symm_apply]

/-! ## The packaged chart module structure: scalar towers and the RE-0 bridge -/

section Packaged

variable [Scheme.QcohOn (gluedSheaf k U g) V]

/-- `IsScalarTower k Γ(X, V) F(W)` for any `W ≤ V`: the coefficient action of the
packaging factors through the structure map `k → Γ(X, V)`. -/
lemma isScalarTower_coeff
    (hq : ∀ {W : X.Opens} (hW : W ≤ V) (r : Γ(X, V)) (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    {W : X.Opens} (hWV : W ≤ V) :
    letI : Module Γ(X, V) ↥(gluedSubmodule k U g W) :=
      Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) hWV
    letI : Algebra k Γ(X, V) := (X.overAlgebraMap k V).toAlgebra
    IsScalarTower k Γ(X, V) ↥(gluedSubmodule k U g W) := by
  letI : Module Γ(X, V) ↥(gluedSubmodule k U g W) :=
    Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) hWV
  letI : Algebra k Γ(X, V) := (X.overAlgebraMap k V).toAlgebra
  refine IsScalarTower.of_algebraMap_smul fun c m => ?_
  change Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hWV (X.overAlgebraMap k V c) m
    = c • m
  rw [hq hWV (X.overAlgebraMap k V c) m]
  exact gluedQsmul_overAlgebraMap k U g hWV c m

/-- `IsScalarTower Γ(X, V) Γ(X, D(h i)) Mᵢ`: the packaged chart action factors through
the restriction `Γ(X, V) → Γ(X, D(h i))` and the piece module structure. -/
lemma isScalarTower_chart_piece (hc : Scheme.IsGluingCocycle U g)
    (hq : ∀ {W : X.Opens} (hW : W ≤ V) (r : Γ(X, V)) (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i)) (i : ι) :
    letI := gluedPieceModule k U g hc hP i
    letI : Module Γ(X, V) ↥(gluedSubmodule k U g (X.basicOpen (h i))) :=
      Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (X.basicOpen_le (h i))
    IsScalarTower Γ(X, V) Γ(X, X.basicOpen (h i))
      ↥(gluedSubmodule k U g (X.basicOpen (h i))) := by
  letI := gluedPieceModule k U g hc hP i
  letI : Module Γ(X, V) ↥(gluedSubmodule k U g (X.basicOpen (h i))) :=
    Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (X.basicOpen_le (h i))
  refine IsScalarTower.of_algebraMap_smul fun r m => ?_
  change (X.resHom (X.basicOpen_le (h i)) r) • m =
    Scheme.QcohOn.qsmul (F := gluedSheaf k U g) (X.basicOpen_le (h i)) r m
  rw [hq (X.basicOpen_le (h i)) r m]
  exact gluedPieceModule_smul_resHom k U g hc hP i r m

/-- **Invertibility of the packaged action of a unit**: a chart section `r` restricting
to a unit on an open `W` below a gluing piece acts invertibly on `F(W)` — the action is
conjugate, through the piece trivialization, to multiplication by the unit `r↾_W`. This
discharges the `map_units` hypothesis of the RE-0 bridge. -/
lemma isUnit_algebraMap_end_glued (hc : Scheme.IsGluingCocycle U g)
    (hq : ∀ {W : X.Opens} (hW : W ≤ V) (r : Γ(X, V)) (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    {W : X.Opens} (hWV : W ≤ V) {j : J} (hWj : W ≤ U j) (r : Γ(X, V))
    (hr : IsUnit (X.resHom hWV r)) :
    letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) hWV
    IsUnit (algebraMap Γ(X, V)
      (Module.End Γ(X, V) ((gluedSheaf k U g).obj.obj (op W))) r) := by
  letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) hWV
  have hE : ⇑(algebraMap Γ(X, V)
      (Module.End Γ(X, V) ((gluedSheaf k U g).obj.obj (op W))) r) =
      fun m : ↥(gluedSubmodule k U g W) => gluedQsmul k U g hWV r m := by
    funext m
    rw [Module.algebraMap_end_apply]
    exact hq hWV r m
  rw [Module.End.isUnit_iff, hE]
  obtain ⟨v, hv⟩ := hr
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun m => (gluedTriv k hc j hWj).symm
      ((↑v⁻¹ : Γ(X, W)) * gluedTriv k hc j hWj m), fun m => ?_, fun m => ?_⟩
  · change (gluedTriv k hc j hWj).symm
      ((↑v⁻¹ : Γ(X, W)) * gluedTriv k hc j hWj (gluedQsmul k U g hWV r m)) = m
    rw [gluedTriv_gluedQsmul k U g hc hWV hWj r m, ← hv, Units.inv_mul_cancel_left,
      LinearEquiv.symm_apply_apply]
  · change gluedQsmul k U g hWV r
      ((gluedTriv k hc j hWj).symm ((↑v⁻¹ : Γ(X, W)) * gluedTriv k hc j hWj m)) = m
    apply (gluedTriv k hc j hWj).injective
    rw [gluedTriv_gluedQsmul k U g hc hWV hWj, LinearEquiv.apply_symm_apply, ← hv,
      Units.mul_inv_cancel_left]

/-- **The RE-0 bridge fired on a piece** (DAT-1 (1c)): on an affine chart `V`, the
restriction `F(V) → F(D(h i))` exhibits the piece sections as the localization of the
chart sections at the powers of `h i`. The abstract bridge
(`Scheme.QcohOn.isLocalizedModule_secResₗ`) produces this at `V ⊓ D(h i)` — its
`map_units` hypothesis is the trivialization conjugation `isUnit_algebraMap_end_glued` —
and `IsLocalizedModule.of_linearEquiv` transports across the opens equality
`V ⊓ D(h i) = D(h i)`. -/
theorem isLocalizedModule_secResₗ_glued (hV : IsAffineOpen V)
    (hc : Scheme.IsGluingCocycle U g)
    (hq : ∀ {W : X.Opens} (hW : W ≤ V) (r : Γ(X, V)) (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i)) (i : ι) :
    letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V)
    letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (X.basicOpen_le (h i))
    IsLocalizedModule (Submonoid.powers (h i))
      (Scheme.QcohOn.secResₗ (F := gluedSheaf k U g)
        (X.basicOpen_le (h i)) (le_refl V)) := by
  letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V)
  letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (X.basicOpen_le (h i))
  letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g)
    (inf_le_left : V ⊓ X.basicOpen (h i) ≤ V)
  -- the unit-action hypothesis on `V ⊓ D(h i)`, an open below the piece `U (σ i)`
  have hru : IsUnit (X.resHom (inf_le_left : V ⊓ X.basicOpen (h i) ≤ V) (h i)) := by
    have h1 : IsUnit (X.resHom (X.basicOpen_le (h i)) (h i)) :=
      X.toRingedSpace.isUnit_res_basicOpen (h i)
    have h2 : X.resHom (inf_le_left : V ⊓ X.basicOpen (h i) ≤ V) (h i) =
        X.resHom (inf_le_right : V ⊓ X.basicOpen (h i) ≤ X.basicOpen (h i))
          (X.resHom (X.basicOpen_le (h i)) (h i)) := by
      rw [Scheme.resHom_resHom]
    rw [h2]
    exact (X.resHom
      (inf_le_right : V ⊓ X.basicOpen (h i) ≤ X.basicOpen (h i))).isUnit_map h1
  -- the abstract bridge at `V ⊓ D(h i)`
  haveI hbridge := Scheme.QcohOn.isLocalizedModule_secResₗ (F := gluedSheaf k U g)
    hV (h i)
    (isUnit_algebraMap_end_glued k U g hc hq
      (inf_le_left : V ⊓ X.basicOpen (h i) ≤ V)
      (inf_le_right.trans (hP i)) (h i) hru)
  -- transport across the opens equality `V ⊓ D(h i) = D(h i)`
  let e : ((gluedSheaf k U g).obj.obj (op (V ⊓ X.basicOpen (h i)))) ≃ₗ[Γ(X, V)]
      ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h i)))) :=
    LinearEquiv.ofLinear
      (Scheme.QcohOn.secResₗ (F := gluedSheaf k U g)
        (le_inf (X.basicOpen_le (h i)) le_rfl :
          X.basicOpen (h i) ≤ V ⊓ X.basicOpen (h i))
        (inf_le_left : V ⊓ X.basicOpen (h i) ≤ V))
      (Scheme.QcohOn.secResₗ (F := gluedSheaf k U g)
        (inf_le_right : V ⊓ X.basicOpen (h i) ≤ X.basicOpen (h i))
        (X.basicOpen_le (h i)))
      (LinearMap.ext fun m => by
        change gluedRes k U g (le_inf (X.basicOpen_le (h i)) le_rfl)
          (gluedRes k U g
            (inf_le_right : V ⊓ X.basicOpen (h i) ≤ X.basicOpen (h i)) m) = m
        rw [gluedRes_gluedRes]
        exact gluedRes_self k U g _ m)
      (LinearMap.ext fun m => by
        change gluedRes k U g
          (inf_le_right : V ⊓ X.basicOpen (h i) ≤ X.basicOpen (h i))
          (gluedRes k U g (le_inf (X.basicOpen_le (h i)) le_rfl) m) = m
        rw [gluedRes_gluedRes]
        exact gluedRes_self k U g _ m)
  have heq : (e : ((gluedSheaf k U g).obj.obj (op (V ⊓ X.basicOpen (h i)))) →ₗ[Γ(X, V)]
        ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h i))))) ∘ₗ
      Scheme.QcohOn.secResₗ (F := gluedSheaf k U g)
        (inf_le_left : V ⊓ X.basicOpen (h i) ≤ V) (le_refl V) =
      Scheme.QcohOn.secResₗ (F := gluedSheaf k U g)
        (X.basicOpen_le (h i)) (le_refl V) := by
    refine LinearMap.ext fun m => ?_
    change gluedRes k U g (le_inf (X.basicOpen_le (h i)) le_rfl)
        (gluedRes k U g (inf_le_left : V ⊓ X.basicOpen (h i) ≤ V) m) =
      gluedRes k U g (X.basicOpen_le (h i)) m
    rw [gluedRes_gluedRes]
  rw [← heq]
  exact IsLocalizedModule.of_linearEquiv _ _ _

/-! ## The chart-module properties -/

/-- **Finiteness over the chart** (DAT-1 (1c)): the glued sections on an affine chart
with a finite subordinate trivializing basic-open family whose generators span the unit
ideal form a finite `Γ(X, V)`-module — `Module.Finite.of_localizationSpan'` on the
piece localizations, each free of rank one. -/
theorem moduleFinite_glued (hV : IsAffineOpen V)
    (hc : Scheme.IsGluingCocycle U g)
    (hq : ∀ {W : X.Opens} (hW : W ≤ V) (r : Γ(X, V)) (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i))
    (hspan : Ideal.span (Set.range h) = ⊤) :
    letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V)
    Module.Finite Γ(X, V) ((gluedSheaf k U g).obj.obj (op V)) := by
  classical
  letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V)
  have hmem : ∀ gg : Set.range h, ∃ i : ι, h i = gg.1 := fun gg => gg.2
  letI iP : ∀ gg : Set.range h,
      Module Γ(X, V)
        ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))) :=
    fun gg => Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g)
      (X.basicOpen_le (h (hmem gg).choose))
  letI iA : ∀ gg : Set.range h,
      Module Γ(X, X.basicOpen (h (hmem gg).choose))
        ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))) :=
    fun gg => gluedPieceModule k U g hc hP (hmem gg).choose
  haveI iT : ∀ gg : Set.range h,
      IsScalarTower Γ(X, V) Γ(X, X.basicOpen (h (hmem gg).choose))
        ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))) :=
    fun gg => isScalarTower_chart_piece k U g hc hq hP (hmem gg).choose
  haveI iL : ∀ gg : Set.range h,
      IsLocalization.Away gg.1 Γ(X, X.basicOpen (h (hmem gg).choose)) := fun gg => by
    have hpow : Submonoid.powers (gg.1 : Γ(X, V)) =
        Submonoid.powers (h (hmem gg).choose) :=
      congrArg Submonoid.powers (hmem gg).choose_spec.symm
    change IsLocalization (Submonoid.powers (gg.1 : Γ(X, V)))
      Γ(X, X.basicOpen (h (hmem gg).choose))
    rw [hpow]
    exact hV.isLocalization_basicOpen (h (hmem gg).choose)
  haveI iM : ∀ gg : Set.range h,
      IsLocalizedModule.Away gg.1
        (Scheme.QcohOn.secResₗ (F := gluedSheaf k U g)
          (X.basicOpen_le (h (hmem gg).choose)) (le_refl V)) := fun gg => by
    have hpow : Submonoid.powers (gg.1 : Γ(X, V)) =
        Submonoid.powers (h (hmem gg).choose) :=
      congrArg Submonoid.powers (hmem gg).choose_spec.symm
    change IsLocalizedModule (Submonoid.powers (gg.1 : Γ(X, V))) _
    rw [hpow]
    exact isLocalizedModule_secResₗ_glued k U g hV hc hq hP (hmem gg).choose
  refine Module.Finite.of_localizationSpan' (Set.range h) hspan
    (Mₚ := fun gg =>
      ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))))
    (Rₚ := fun gg => Γ(X, X.basicOpen (h (hmem gg).choose)))
    (fun gg => Scheme.QcohOn.secResₗ (F := gluedSheaf k U g)
      (X.basicOpen_le (h (hmem gg).choose)) (le_refl V)) (fun gg => ?_)
  exact Module.Finite.equiv (gluedPieceEquiv k U g hc hP (hmem gg).choose).symm

/-- **Finite presentation over the chart** (DAT-1 (1c)):
`Module.FinitePresentation.of_localizationSpan'` on the free rank-one piece
localizations. -/
theorem finitePresentation_glued (hV : IsAffineOpen V)
    (hc : Scheme.IsGluingCocycle U g)
    (hq : ∀ {W : X.Opens} (hW : W ≤ V) (r : Γ(X, V)) (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i))
    (hspan : Ideal.span (Set.range h) = ⊤) :
    letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V)
    Module.FinitePresentation Γ(X, V) ((gluedSheaf k U g).obj.obj (op V)) := by
  classical
  letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V)
  have hmem : ∀ gg : Set.range h, ∃ i : ι, h i = gg.1 := fun gg => gg.2
  letI iP : ∀ gg : Set.range h,
      Module Γ(X, V)
        ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))) :=
    fun gg => Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g)
      (X.basicOpen_le (h (hmem gg).choose))
  letI iA : ∀ gg : Set.range h,
      Module Γ(X, X.basicOpen (h (hmem gg).choose))
        ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))) :=
    fun gg => gluedPieceModule k U g hc hP (hmem gg).choose
  haveI iT : ∀ gg : Set.range h,
      IsScalarTower Γ(X, V) Γ(X, X.basicOpen (h (hmem gg).choose))
        ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))) :=
    fun gg => isScalarTower_chart_piece k U g hc hq hP (hmem gg).choose
  haveI iL : ∀ gg : Set.range h,
      IsLocalization.Away gg.1 Γ(X, X.basicOpen (h (hmem gg).choose)) := fun gg => by
    have hpow : Submonoid.powers (gg.1 : Γ(X, V)) =
        Submonoid.powers (h (hmem gg).choose) :=
      congrArg Submonoid.powers (hmem gg).choose_spec.symm
    change IsLocalization (Submonoid.powers (gg.1 : Γ(X, V)))
      Γ(X, X.basicOpen (h (hmem gg).choose))
    rw [hpow]
    exact hV.isLocalization_basicOpen (h (hmem gg).choose)
  haveI iM : ∀ gg : Set.range h,
      IsLocalizedModule (Submonoid.powers (gg.1 : Γ(X, V)))
        (Scheme.QcohOn.secResₗ (F := gluedSheaf k U g)
          (X.basicOpen_le (h (hmem gg).choose)) (le_refl V)) := fun gg => by
    have hpow : Submonoid.powers (gg.1 : Γ(X, V)) =
        Submonoid.powers (h (hmem gg).choose) :=
      congrArg Submonoid.powers (hmem gg).choose_spec.symm
    rw [hpow]
    exact isLocalizedModule_secResₗ_glued k U g hV hc hq hP (hmem gg).choose
  refine Module.FinitePresentation.of_localizationSpan' (Set.range h) hspan
    (Mₚ := fun gg =>
      ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))))
    (Rₚ := fun gg => Γ(X, X.basicOpen (h (hmem gg).choose)))
    (fun gg => Scheme.QcohOn.secResₗ (F := gluedSheaf k U g)
      (X.basicOpen_le (h (hmem gg).choose)) (le_refl V)) (fun gg => ?_)
  haveI : Module.Free Γ(X, X.basicOpen (h (hmem gg).choose))
      ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))) :=
    Module.Free.of_equiv (gluedPieceEquiv k U g hc hP (hmem gg).choose).symm
  haveI : Module.Finite Γ(X, X.basicOpen (h (hmem gg).choose))
      ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))) :=
    Module.Finite.equiv (gluedPieceEquiv k U g hc hP (hmem gg).choose).symm
  exact Module.finitePresentation_of_projective _ _

/-- **Flatness over the chart** (DAT-1 (1c)): `Module.flat_of_isLocalized_span` — each
piece localization is flat over the chart ring (a localization is flat, and the piece
is free of rank one over it). -/
theorem flat_glued (hV : IsAffineOpen V)
    (hc : Scheme.IsGluingCocycle U g)
    (hq : ∀ {W : X.Opens} (hW : W ≤ V) (r : Γ(X, V)) (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i))
    (hspan : Ideal.span (Set.range h) = ⊤) :
    letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V)
    Module.Flat Γ(X, V) ((gluedSheaf k U g).obj.obj (op V)) := by
  classical
  letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V)
  have hmem : ∀ gg : Set.range h, ∃ i : ι, h i = gg.1 := fun gg => gg.2
  letI iP : ∀ gg : Set.range h,
      Module Γ(X, V)
        ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))) :=
    fun gg => Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g)
      (X.basicOpen_le (h (hmem gg).choose))
  letI iA : ∀ gg : Set.range h,
      Module Γ(X, X.basicOpen (h (hmem gg).choose))
        ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))) :=
    fun gg => gluedPieceModule k U g hc hP (hmem gg).choose
  haveI iT : ∀ gg : Set.range h,
      IsScalarTower Γ(X, V) Γ(X, X.basicOpen (h (hmem gg).choose))
        ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))) :=
    fun gg => isScalarTower_chart_piece k U g hc hq hP (hmem gg).choose
  haveI iM : ∀ gg : Set.range h,
      IsLocalizedModule.Away gg.1
        (Scheme.QcohOn.secResₗ (F := gluedSheaf k U g)
          (X.basicOpen_le (h (hmem gg).choose)) (le_refl V)) := fun gg => by
    have hpow : Submonoid.powers (gg.1 : Γ(X, V)) =
        Submonoid.powers (h (hmem gg).choose) :=
      congrArg Submonoid.powers (hmem gg).choose_spec.symm
    change IsLocalizedModule (Submonoid.powers (gg.1 : Γ(X, V))) _
    rw [hpow]
    exact isLocalizedModule_secResₗ_glued k U g hV hc hq hP (hmem gg).choose
  refine Module.flat_of_isLocalized_span Γ(X, V)
    ((gluedSheaf k U g).obj.obj (op V)) (Set.range h) hspan
    (fun gg =>
      ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))))
    (fun gg => Scheme.QcohOn.secResₗ (F := gluedSheaf k U g)
      (X.basicOpen_le (h (hmem gg).choose)) (le_refl V)) (fun gg => ?_)
  haveI : IsLocalization.Away (h (hmem gg).choose)
      Γ(X, X.basicOpen (h (hmem gg).choose)) :=
    hV.isLocalization_basicOpen (h (hmem gg).choose)
  haveI : Module.Flat Γ(X, V) Γ(X, X.basicOpen (h (hmem gg).choose)) :=
    IsLocalization.flat _ (Submonoid.powers (h (hmem gg).choose))
  haveI : Module.Free Γ(X, X.basicOpen (h (hmem gg).choose))
      ((gluedSheaf k U g).obj.obj (op (X.basicOpen (h (hmem gg).choose)))) :=
    Module.Free.of_equiv (gluedPieceEquiv k U g hc hP (hmem gg).choose).symm
  exact Module.Flat.trans Γ(X, V) Γ(X, X.basicOpen (h (hmem gg).choose)) _

/-- **Projectivity over the chart** (DAT-1 (1c)): flat + finitely presented. -/
theorem projective_glued (hV : IsAffineOpen V)
    (hc : Scheme.IsGluingCocycle U g)
    (hq : ∀ {W : X.Opens} (hW : W ≤ V) (r : Γ(X, V)) (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i))
    (hspan : Ideal.span (Set.range h) = ⊤) :
    letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V)
    Module.Projective Γ(X, V) ((gluedSheaf k U g).obj.obj (op V)) := by
  letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V)
  haveI := finitePresentation_glued k U g hV hc hq hP hspan
  haveI := flat_glued k U g hV hc hq hP hspan
  exact Module.Flat.projective_of_finitePresentation

/-- **Flatness over the coefficient ring** (DAT-1 (1c), (D5) transport): if the chart
ring is a flat `k`-module then so are the chart glued sections — `Module.Flat.trans`
through the chart. (A benign weakening of the spec's freeness hypothesis:
free ⟹ flat.) -/
theorem flat_glued_of_flat (hV : IsAffineOpen V)
    (hc : Scheme.IsGluingCocycle U g)
    (hq : ∀ {W : X.Opens} (hW : W ≤ V) (r : Γ(X, V)) (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i))
    (hspan : Ideal.span (Set.range h) = ⊤)
    (hflat : Module.Flat k Γ(X, V)) :
    Module.Flat k ((gluedSheaf k U g).obj.obj (op V)) := by
  letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V)
  letI : Algebra k Γ(X, V) := (X.overAlgebraMap k V).toAlgebra
  haveI : IsScalarTower k Γ(X, V) ((gluedSheaf k U g).obj.obj (op V)) :=
    isScalarTower_coeff k U g hq (le_refl V)
  haveI : Module.Flat k Γ(X, V) := hflat
  haveI : Module.Flat Γ(X, V) ((gluedSheaf k U g).obj.obj (op V)) :=
    flat_glued k U g hV hc hq hP hspan
  exact Module.Flat.trans k Γ(X, V) ((gluedSheaf k U g).obj.obj (op V))

/-- **Projectivity over the coefficient ring** (DAT-1 (1c), (D5) transport): if the
chart ring is a free `k`-module then the chart glued sections are `k`-projective —
`Module.Projective.of_free_algebra` through the chart. -/
theorem projective_glued_of_free (hV : IsAffineOpen V)
    (hc : Scheme.IsGluingCocycle U g)
    (hq : ∀ {W : X.Opens} (hW : W ≤ V) (r : Γ(X, V)) (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i))
    (hspan : Ideal.span (Set.range h) = ⊤)
    (hfree : Module.Free k Γ(X, V)) :
    Module.Projective k ((gluedSheaf k U g).obj.obj (op V)) := by
  letI := Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V)
  letI : Algebra k Γ(X, V) := (X.overAlgebraMap k V).toAlgebra
  haveI : IsScalarTower k Γ(X, V) ((gluedSheaf k U g).obj.obj (op V)) :=
    isScalarTower_coeff k U g hq (le_refl V)
  haveI : Module.Free k Γ(X, V) := hfree
  haveI : Module.Projective Γ(X, V) ((gluedSheaf k U g).obj.obj (op V)) :=
    projective_glued k U g hV hc hq hP hspan
  exact Module.Projective.of_free_algebra (R := k) (A := Γ(X, V))

/-- **The `AEval'`-finiteness export** (DAT-1 (1c), the (D5) transitivity): an
endomorphism `e` of the chart glued sections acting as the packaged action of a chart
coordinate `a₀` has `k[X]`-finite chart lattice, provided the multiplication
endomorphism of `a₀` on the chart ring does (the landed E-i input, hypothesis `hA`) —
through `RigidEngine.moduleFinite_aeval'_of_smul_finite` and the chart finiteness
`moduleFinite_glued`. -/
theorem moduleFinite_aeval'_glued (hV : IsAffineOpen V)
    (hc : Scheme.IsGluingCocycle U g)
    (hq : ∀ {W : X.Opens} (hW : W ≤ V) (r : Γ(X, V)) (s : ↥(gluedSubmodule k U g W)),
      Scheme.QcohOn.qsmul (F := gluedSheaf k U g) hW r s = gluedQsmul k U g hW r s)
    (hP : ∀ i : ι, X.basicOpen (h i) ≤ U (σ i))
    (hspan : Ideal.span (Set.range h) = ⊤) (a₀ : Γ(X, V))
    (hA : Module.Finite k[X] (Module.AEval' (Scheme.mulSectionEnd k a₀)))
    (e : Module.End k ((gluedSheaf k U g).obj.obj (op V)))
    (he : ∀ m : ((gluedSheaf k U g).obj.obj (op V)),
      e m = Scheme.QcohOn.qsmul (F := gluedSheaf k U g) (le_refl V) a₀ m) :
    Module.Finite k[X] (Module.AEval' e) :=
  @AlgebraicJacobian.RigidEngine.moduleFinite_aeval'_of_smul_finite
    k _ Γ(X, V) _ ((X.overAlgebraMap k V).toAlgebra)
    ((gluedSheaf k U g).obj.obj (op V)) _ _
    (Scheme.QcohOn.moduleOfLE (F := gluedSheaf k U g) (le_refl V))
    (isScalarTower_coeff k U g hq (le_refl V))
    a₀ (Scheme.mulSectionEnd k a₀)
    (fun x => Scheme.mulSectionEnd_apply k a₀ x) hA
    (moduleFinite_glued k U g hV hc hq hP hspan) e
    (fun m => by rw [he m]; rfl)

end Packaged

end Module

end AlgebraicGeometry
