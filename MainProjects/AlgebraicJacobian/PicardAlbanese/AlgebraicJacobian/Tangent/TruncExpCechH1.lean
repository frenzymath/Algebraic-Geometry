/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TruncExpCech
import AlgebraicJacobian.Cohomology.TwoCover

/-!
# `H¹(X, 𝒪) ≃+ ker(Ȟ¹ˣ(B[ε]) → Ȟ¹ˣ(B))` on a two-cover (W5-T2, stage 2)

The carrier assembly of the truncated-exponential Čech kernel on the Rebuild's pinned
two-cover section rings: for a scheme `X` over `Spec k` with two affine opens
`U₀ ⊔ U₁ = ⊤`, write `B = Γ(X, U₀ ⊓ U₁)` for the overlap ring and
`ρᵢ = X.resHom : Γ(X, Uᵢ) →+* B` for the restrictions. Composing

* the landed two-cover H¹ bridge `TwoCover.h1CokEquiv :
  H¹ₖ(X, 𝒪) ≃ₗ[k] Γ(U₀ ⊓ U₁) ⧸ range diff`,
* the carrier translation `range diff = ρ₁(A₁) + ρ₂(A₂)` (a difference and a sum of
  chart sections span the same additive subgroup — `range_diff_toAddSubgroup`), and
* the pure-algebra engine `TruncExpCech.truncExpCechKernelAddEquiv :
  B ⧸ (ρ₁A₁ + ρ₂A₂) ≃+ Additive (ker(Ȟ¹ˣ(B[ε]) →* Ȟ¹ˣ(B)))`

gives the Kleiman §5 Thm 5.11 cocycle-leg identification

```
H¹(X, 𝒪_X)  ≃+  ker( Ȟ¹ˣ(Γ(U₀ ⊓ U₁)[ε]) →* Ȟ¹ˣ(Γ(U₀ ⊓ U₁)) )
```

(`TwoCover.h1AddEquivTruncExpCechKernel`), the two-cover Čech form of
`H¹(C, 𝒪_C) ≅ ker(Pic(C_ε) → Pic(C))`. On generators it sends the connecting class
`delta s` of an overlap section to the class of the truncated exponential `1 + s ε`
(`h1AddEquivTruncExpCechKernel_delta`, with the generator map bundled as
`TwoCover.truncExpClass`). For the challenge curve, instantiate at an
`Scheme.AffineTwoCover` of `C.left` (which exists:
`Scheme.AffineTwoCover.nonempty_of_curve`); `Sheaf.HModule (C.left.moduleKSheaf k) 1`
is definitionally the carrier whose `finrank` is `genus C`.

**`k`-linearity interface (the D6/R5(iii) distributivity dodge).** The equivalence is
additive only, BY DESIGN: no `SMul k` is ever placed on the units-kernel side, so the
old draft's unproved `(a+b) • x` Mumford-scaling distributivity is never needed. The
`k`-action lives on the H¹/cokernel side, where it is the honest module structure, and
corresponds pointwise to the Mumford `ε ↦ aε` scaling (`TwoCover.mumfordScaling`)
through the equivalence: `mumfordScaling_h1AddEquivTruncExpCechKernel`. Dimension
counts (W5-T5) should be run on the cocycle side and transported along these pointwise
lemmas — never by putting a module structure on the kernel.

## Main declarations

* `TruncExpCech.submoduleQuotientAddEquiv` — generic bridge: the quotient of a module
  by a submodule is, additively, the quotient by the underlying additive subgroup.
* `AlgebraicGeometry.TwoCover.unitsReduction` — the Čech-units reduction
  `Ȟ¹ˣ(Γ(U₀ ⊓ U₁)[ε]) →* Ȟ¹ˣ(Γ(U₀ ⊓ U₁))` of the two-cover.
* `AlgebraicGeometry.TwoCover.truncExpClass` — the kernel class of `1 + b ε` for an
  overlap section `b`, with `truncExpClass_add`, `truncExpClass_eq_zero_iff`,
  `truncExpClass_surjective`.
* `AlgebraicGeometry.TwoCover.h1AddEquivTruncExpCechKernel` — the keystone
  `H¹ₖ(X, 𝒪) ≃+ Additive (unitsReduction X U₀ U₁).ker`, with generator formula
  `h1AddEquivTruncExpCechKernel_delta`.
* `AlgebraicGeometry.TwoCover.mumfordScaling` + equivariance lemmas — the `k`-action
  interface for W5-T5.

## References

Kleiman, "The Picard scheme", §5, proof of Thm 5.11 (arXiv:math/0504020); Mumford,
"Abelian varieties", §II.4.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u v w

open CategoryTheory Limits Opposite TopologicalSpace

namespace TruncExpCech

/-- **The quotient of a module by a submodule is, additively, the quotient by the
underlying additive subgroup.** The two quotients have definitionally the same carrier
and additive structure (`Submodule.quotientRel` is `QuotientAddGroup.leftRel` of
`p.toAddSubgroup` by definition); this packages the identity as an `AddEquiv`, sending
`Submodule.Quotient.mk x` to `QuotientAddGroup.mk x`
(`submoduleQuotientAddEquiv_mk`). -/
def submoduleQuotientAddEquiv {R : Type v} {M : Type w} [Ring R] [AddCommGroup M]
    [Module R M] (p : Submodule R M) : (M ⧸ p) ≃+ (M ⧸ p.toAddSubgroup) :=
  { Equiv.refl (M ⧸ p) with map_add' := fun _ _ => rfl }

@[simp]
theorem submoduleQuotientAddEquiv_mk {R : Type v} {M : Type w} [Ring R]
    [AddCommGroup M] [Module R M] (p : Submodule R M) (x : M) :
    submoduleQuotientAddEquiv p (Submodule.Quotient.mk x) = QuotientAddGroup.mk x :=
  rfl

end TruncExpCech

namespace AlgebraicGeometry

namespace TwoCover

open TruncExpCech DualNumber

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
variable (U₀ U₁ : X.Opens)

attribute [local instance] Scheme.overModule

/-! ## The two-chart datum of the cover and its compatibility with the constants -/

/-- Restriction to the overlap intertwines the structure constants of the two charts:
`ρ₁ ∘ (k → Γ(U₀)) = (k → Γ(U₀ ⊓ U₁))`. -/
theorem resHom_overAlgebraMap_left (a : k) :
    X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀) (X.overAlgebraMap k U₀ a)
      = X.overAlgebraMap k (U₀ ⊓ U₁) a :=
  X.overAlgebraMap_apply_res k (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op a

/-- Restriction to the overlap intertwines the structure constants of the two charts:
`ρ₂ ∘ (k → Γ(U₁)) = (k → Γ(U₀ ⊓ U₁))`. -/
theorem resHom_overAlgebraMap_right (a : k) :
    X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁) (X.overAlgebraMap k U₁ a)
      = X.overAlgebraMap k (U₀ ⊓ U₁) a :=
  X.overAlgebraMap_apply_res k (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op a

/-! ## The Čech-units reduction of the two-cover -/

/-- **The Čech-units reduction of the two-cover at the dual-number thickening**:
`Ȟ¹ˣ(Γ(U₀ ⊓ U₁)[ε]) →* Ȟ¹ˣ(Γ(U₀ ⊓ U₁))` for the two-chart datum of restriction ring
homomorphisms — the Čech-cocycle incarnation of the restriction
`Pic(X ×ₖ Spec k[ε]) → Pic(X)` along `ε ↦ 0`. Reducible wrapper
(`unitsReduction_def`) around `TruncExpCech.cechUnitsReduction`, naming the pinned
two-cover instance once (reducible so that all statements below unify transparently
with the engine's `cechUnitsReduction` spelling). Its kernel is computed from
`H¹(X, 𝒪)` by `h1AddEquivTruncExpCechKernel` below. -/
noncomputable abbrev unitsReduction :
    ((Γ(X, U₀ ⊓ U₁)[ε])ˣ ⧸ cechCoboundaryUnits
        (mapRingHom (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀)))
        (mapRingHom (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁)))) →*
      (Γ(X, U₀ ⊓ U₁))ˣ ⧸ cechCoboundaryUnits
        (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀))
        (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁)) :=
  cechUnitsReduction (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀))
    (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁))

/-- `unitsReduction` is `TruncExpCech.cechUnitsReduction` at the two-cover restriction
datum, definitionally. -/
theorem unitsReduction_def :
    unitsReduction X U₀ U₁
      = cechUnitsReduction (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀))
          (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁)) :=
  rfl

/-! ## The truncated-exponential kernel classes of overlap sections -/

/-- **The truncated-exponential kernel class of an overlap section**: the class of the
unit `1 + b ε` in the kernel of the Čech-units reduction, written additively. This is
the generator map of the ε-kernel: `h1AddEquivTruncExpCechKernel` sends the connecting
class `delta s` to `truncExpClass s`. -/
noncomputable def truncExpClass (b : Γ(X, U₀ ⊓ U₁)) :
    Additive (unitsReduction X U₀ U₁).ker :=
  Additive.ofMul (α := (unitsReduction X U₀ U₁).ker)
    ⟨QuotientGroup.mk (truncExpUnit b),
      MonoidHom.mem_ker.mpr
        (cechUnitsReduction_mk_truncExpUnit
          (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀))
          (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁)) b)⟩

/-- **The underlying thickened Čech class of an element of the ε-kernel** — the
coercion `Additive (ker) → Ȟ¹ˣ(Γ(U₀ ⊓ U₁)[ε])` as a named map. Kernel discipline: one
opaque head for the coercion seam, so that rewriting under it never re-elaborates the
scheme-tower coercions (`kerVal_eq_coe` recovers the raw coercion). -/
noncomputable def kerVal (y : Additive (unitsReduction X U₀ U₁).ker) :
    (Γ(X, U₀ ⊓ U₁)[ε])ˣ ⧸ cechCoboundaryUnits
      (mapRingHom (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀)))
      (mapRingHom (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁))) :=
  (Additive.toMul y : (unitsReduction X U₀ U₁).ker).1

/-- `kerVal` is the raw coercion, definitionally. -/
theorem kerVal_eq_coe (y : Additive (unitsReduction X U₀ U₁).ker) :
    kerVal X U₀ U₁ y
      = ((Additive.toMul y : (unitsReduction X U₀ U₁).ker) :
          (Γ(X, U₀ ⊓ U₁)[ε])ˣ ⧸ cechCoboundaryUnits
            (mapRingHom (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀)))
            (mapRingHom (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁)))) :=
  rfl

/-- The underlying thickened Čech class of `truncExpClass b` is `[1 + b ε]`.
Definitional. -/
theorem truncExpClass_val (b : Γ(X, U₀ ⊓ U₁)) :
    kerVal X U₀ U₁ (truncExpClass X U₀ U₁ b) = QuotientGroup.mk (truncExpUnit b) :=
  rfl

/-- `truncExpClass` is the truncated-exponential kernel engine applied to the residue
class of the section: `truncExpClass b = truncExpCechKernelAddEquiv ρ₁ ρ₂ [b]`.
Definitional; the workhorse normal form for the lemmas below. -/
theorem truncExpClass_eq_engine (b : Γ(X, U₀ ⊓ U₁)) :
    truncExpClass X U₀ U₁ b
      = truncExpCechKernelAddEquiv (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀))
          (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁)) (QuotientAddGroup.mk b) :=
  rfl

/-- Additivity of the truncated-exponential kernel classes:
`(1 + bε)(1 + cε) = 1 + (b+c)ε`. -/
theorem truncExpClass_add (b c : Γ(X, U₀ ⊓ U₁)) :
    truncExpClass X U₀ U₁ (b + c)
      = truncExpClass X U₀ U₁ b + truncExpClass X U₀ U₁ c := by
  rw [truncExpClass_eq_engine X U₀ U₁ b, truncExpClass_eq_engine X U₀ U₁ c, ← map_add,
    ← QuotientAddGroup.mk_add, ← truncExpClass_eq_engine]

/-- Vanishing of a truncated-exponential kernel class: `[1 + b ε] = 0` iff `b` is a
Čech coboundary `ρ₁ a₁ + ρ₂ a₂` of the two charts. -/
theorem truncExpClass_eq_zero_iff (b : Γ(X, U₀ ⊓ U₁)) :
    truncExpClass X U₀ U₁ b = 0
      ↔ b ∈ cechCoboundaryAdd (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀))
          (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁)) := by
  rw [truncExpClass_eq_engine, EmbeddingLike.map_eq_zero_iff,
    QuotientAddGroup.eq_zero_iff]

/-- Every class in the kernel of the Čech-units reduction is a truncated-exponential
class of an overlap section. -/
theorem truncExpClass_surjective :
    Function.Surjective (truncExpClass X U₀ U₁) := by
  intro y
  obtain ⟨q, hq⟩ := (truncExpCechKernelAddEquiv
    (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀))
    (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁))).surjective y
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact ⟨b, by rw [truncExpClass_eq_engine]; exact hq⟩

/-! ## The carrier translation: `range diff` is the additive coboundary subgroup -/

/-- **Carrier translation**: the range of the two-cover restriction-difference map
`TwoCover.diff` is, as an additive subgroup of the overlap ring, exactly the additive
Čech coboundary subgroup `ρ₁(Γ(U₀)) + ρ₂(Γ(U₁))` of the restriction two-chart datum (a
difference and a sum of chart sections span the same subgroup). -/
theorem range_diff_toAddSubgroup :
    (LinearMap.range (diff k X U₀ U₁)).toAddSubgroup
      = cechCoboundaryAdd (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀))
          (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁)) := by
  ext b
  rw [Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    rw [diff_apply]
    exact sub_mem_cechCoboundaryAdd _ _ t.1 t.2
  · intro hb
    obtain ⟨a₁, a₂, ha⟩ := exists_sub_of_mem_cechCoboundaryAdd hb
    exact ⟨(a₁, a₂), by rw [diff_apply]; exact ha⟩

/-- The two-cover H¹ cokernel `H1Cok`, additively, is the quotient of the overlap ring
by the additive Čech coboundaries — the carrier the truncated-exponential engine
consumes. Sends `Submodule.Quotient.mk s` to `QuotientAddGroup.mk s`
(`h1CokAddEquivCechQuot_mk`). -/
noncomputable def h1CokAddEquivCechQuot :
    H1Cok k X U₀ U₁ ≃+
      Γ(X, U₀ ⊓ U₁) ⧸ cechCoboundaryAdd (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀))
        (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁)) :=
  (submoduleQuotientAddEquiv (LinearMap.range (diff k X U₀ U₁))).trans
    (QuotientAddGroup.quotientAddEquivOfEq (range_diff_toAddSubgroup k X U₀ U₁))

@[simp]
theorem h1CokAddEquivCechQuot_mk (s : Γ(X, U₀ ⊓ U₁)) :
    h1CokAddEquivCechQuot k X U₀ U₁ (Submodule.Quotient.mk s)
      = QuotientAddGroup.mk s :=
  rfl

/-! ## The keystone: `H¹(X, 𝒪) ≃+ ker(Ȟ¹ˣ(B[ε]) → Ȟ¹ˣ(B))` -/

/-- **The truncated-exponential Čech kernel computation of `H¹`** (Kleiman §5
Thm 5.11, cocycle leg, carrier form — W5-T2 keystone): for a scheme `X` over `Spec k`
and two affine opens `U₀ ⊔ U₁ = ⊤`, the degree-one cohomology of the structure sheaf
is additively the kernel of the dual-number Čech-units reduction of the cover:

```
H¹ₖ(X, 𝒪)  ≃+  ker( Ȟ¹ˣ(Γ(U₀ ⊓ U₁)[ε]) →* Ȟ¹ˣ(Γ(U₀ ⊓ U₁)) )
```

— the two-cover Čech form of `H¹(C, 𝒪_C) ≅ ker(Pic(C_ε) → Pic(C))`. Composite of the
landed `h1CokEquiv`, the carrier translation `h1CokAddEquivCechQuot`, and the engine
`TruncExpCech.truncExpCechKernelAddEquiv`. On generators: `delta s ↦ truncExpClass s`
(`h1AddEquivTruncExpCechKernel_delta`). Additive only, BY DESIGN — see the module
docstring for the `k`-action interface (`mumfordScaling` equivariance). -/
noncomputable def h1AddEquivTruncExpCechKernel (hcov : U₀ ⊔ U₁ = ⊤)
    (hU₀ : IsAffineOpen U₀) (hU₁ : IsAffineOpen U₁) :
    Sheaf.HModule (X.moduleKSheaf k) 1 ≃+ Additive (unitsReduction X U₀ U₁).ker :=
  (h1CokEquiv k X U₀ U₁ hcov hU₀ hU₁).toAddEquiv.trans
    ((h1CokAddEquivCechQuot k X U₀ U₁).trans
      (truncExpCechKernelAddEquiv (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀))
        (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁))))

variable (hcov : U₀ ⊔ U₁ = ⊤) (hU₀ : IsAffineOpen U₀) (hU₁ : IsAffineOpen U₁)

/-- **Generator formula for the keystone**: the H¹ ↔ ε-kernel identification sends the
connecting class `delta s` of an overlap section `s` to the truncated-exponential
class `[1 + s ε]`. -/
theorem h1AddEquivTruncExpCechKernel_delta (s : Γ(X, U₀ ⊓ U₁)) :
    h1AddEquivTruncExpCechKernel k X U₀ U₁ hcov hU₀ hU₁ (delta k X U₀ U₁ hcov s)
      = truncExpClass X U₀ U₁ s := by
  have hsplit : h1AddEquivTruncExpCechKernel k X U₀ U₁ hcov hU₀ hU₁
      (delta k X U₀ U₁ hcov s)
      = truncExpCechKernelAddEquiv (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀))
          (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁))
          (h1CokAddEquivCechQuot k X U₀ U₁
            (h1CokEquiv k X U₀ U₁ hcov hU₀ hU₁ (delta k X U₀ U₁ hcov s))) := rfl
  rw [hsplit, h1CokEquiv_delta, h1CokAddEquivCechQuot_mk, truncExpClass_eq_engine]

/-! ## The `k`-action interface (W5-T5): Mumford scaling through the keystone

No `SMul k` is placed on the units-kernel side (the D6 distributivity dodge). The
`k`-action on `H¹` corresponds pointwise to the Mumford `ε ↦ aε` scaling of the
thickened Čech `Ȟ¹`, acting on truncated-exponential classes by
`b ↦ (X.overAlgebraMap k (U₀ ⊓ U₁) a) * b`. -/

/-- Scaling a connecting class: the `k`-action on `H¹` hits `delta` as multiplication
of the overlap section by the structure constant. -/
theorem smul_delta (a : k) (s : Γ(X, U₀ ⊓ U₁)) :
    a • delta k X U₀ U₁ hcov s
      = delta k X U₀ U₁ hcov (X.overAlgebraMap k (U₀ ⊓ U₁) a * s) := by
  rw [← map_smul]
  rfl

/-- The keystone on a scaled generator: `a • delta s` goes to the
truncated-exponential class of `(X.overAlgebraMap k (U₀ ⊓ U₁) a) * s`. -/
theorem h1AddEquivTruncExpCechKernel_smul_delta (a : k) (s : Γ(X, U₀ ⊓ U₁)) :
    h1AddEquivTruncExpCechKernel k X U₀ U₁ hcov hU₀ hU₁
        (a • delta k X U₀ U₁ hcov s)
      = truncExpClass X U₀ U₁ (X.overAlgebraMap k (U₀ ⊓ U₁) a * s) := by
  rw [smul_delta, h1AddEquivTruncExpCechKernel_delta]

/-- **The Mumford `ε ↦ aε` scaling of the thickened Čech `Ȟ¹`** of the two-cover, for
a scalar `a : k` (acting through the structure constant
`X.overAlgebraMap k (U₀ ⊓ U₁) a`). Descends to the quotient because the scaling
preserves the thickened coboundaries
(`TruncExpCech.cechCoboundaryUnits_le_comap_unitsScale`, with the chart compatibility
`resHom_overAlgebraMap_left/right`). -/
noncomputable def mumfordScaling (a : k) :
    ((Γ(X, U₀ ⊓ U₁)[ε])ˣ ⧸ cechCoboundaryUnits
        (mapRingHom (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀)))
        (mapRingHom (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁)))) →*
      (Γ(X, U₀ ⊓ U₁)[ε])ˣ ⧸ cechCoboundaryUnits
        (mapRingHom (X.resHom (inf_le_left : U₀ ⊓ U₁ ≤ U₀)))
        (mapRingHom (X.resHom (inf_le_right : U₀ ⊓ U₁ ≤ U₁))) :=
  QuotientGroup.map _ _
    (Units.map (scaleRingHom (X.overAlgebraMap k (U₀ ⊓ U₁) a)).toMonoidHom)
    (cechCoboundaryUnits_le_comap_unitsScale _ _
      (resHom_overAlgebraMap_left k X U₀ U₁ a)
      (resHom_overAlgebraMap_right k X U₀ U₁ a))

/-- The Mumford scaling acts on truncated-exponential classes by multiplying the
overlap section by the structure constant: `[1 + b ε] ↦ [1 + (a·b) ε]`. -/
theorem mumfordScaling_mk_truncExpUnit (a : k) (b : Γ(X, U₀ ⊓ U₁)) :
    mumfordScaling k X U₀ U₁ a (QuotientGroup.mk (truncExpUnit b))
      = QuotientGroup.mk (truncExpUnit (X.overAlgebraMap k (U₀ ⊓ U₁) a * b)) :=
  unitsScale_mk_truncExpUnit _ _
    (resHom_overAlgebraMap_left k X U₀ U₁ a)
    (resHom_overAlgebraMap_right k X U₀ U₁ a) b

/-- **Mumford-scaling equivariance of the keystone** (the W5 `k`-linearity interface):
through `h1AddEquivTruncExpCechKernel`, the honest `k`-action on `H¹(X, 𝒪)`
corresponds to the Mumford `ε ↦ aε` scaling of the thickened Čech `Ȟ¹`. Consumers
(W5-T5) run all dimension bookkeeping on the cocycle side — where `k`-linearity is the
module structure — and transport pointwise along this lemma; the units-kernel side
never carries an `SMul` (the D6 distributivity dodge). Stated on the generators
`delta s`; since `delta` is surjective (`delta_surjective`) and both sides are
additive in `s`, this determines the correspondence on all of `H¹`. -/
theorem mumfordScaling_h1AddEquivTruncExpCechKernel_delta (a : k)
    (s : Γ(X, U₀ ⊓ U₁)) :
    kerVal X U₀ U₁ (h1AddEquivTruncExpCechKernel k X U₀ U₁ hcov hU₀ hU₁
        (a • delta k X U₀ U₁ hcov s))
      = mumfordScaling k X U₀ U₁ a
          (kerVal X U₀ U₁ (h1AddEquivTruncExpCechKernel k X U₀ U₁ hcov hU₀ hU₁
            (delta k X U₀ U₁ hcov s))) := by
  rw [h1AddEquivTruncExpCechKernel_smul_delta, h1AddEquivTruncExpCechKernel_delta,
    truncExpClass_val, truncExpClass_val]
  exact (mumfordScaling_mk_truncExpUnit k X U₀ U₁ a s).symm

end TwoCover

end AlgebraicGeometry
