/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.ChiLedger

/-!
# Adelic Riemann–Roch — the multiplication isomorphism and class invariance

This file supplies the **class-invariance layer** of the adelic χ-ledger: the
statement that all three numerical invariants of the ledger — `ℓ(D)`, `h¹(D)` and
`χ(D)` — depend only on the *linear-equivalence class* of `D`, together with the
elementary effective-witness dictionary that turns a nonzero global section into
an effective divisor in the same class.

Everything here is **unconditional**: no gate class, no ledger exactness
hypothesis, no finiteness input.  The only mechanism is that multiplication by a
nonzero rational function `g ∈ K(X)^×` is a `k`-linear automorphism of `K(X)`
which carries the section subspace `Γ(U, 𝒪(D))` *onto* `Γ(U, 𝒪(D − div g))`.

## Main declarations

* `Adelic.mul_mem_sectionOfDivisor` — the order computation
  `ord_P (g·f) = ord_P g + ord_P f`, in section-membership form: the single
  arithmetic fact behind everything else in this file.
* `Adelic.mulEquivFunctionField` — multiplication by `g ≠ 0` as a `k`-linear
  automorphism of `K(X)` (`k` a field of constants).
* `Adelic.map_sectionSub_mulEquiv` — `(Γ(U, 𝒪(D))).map (g·) = Γ(U, 𝒪(D'))`
  whenever `D'(P) = D(P) − ord_P g` for every prime divisor `P`.
* `Adelic.sectionSubMulEquiv` — the resulting `k`-linear isomorphism
  `Γ(U, 𝒪(D)) ≃ₗ[k] Γ(U, 𝒪(D'))`.
* `Adelic.ell_eq_of_shift`, `Adelic.h1dim_eq_of_shift`, `Adelic.chi_eq_of_shift`
  — `ℓ`, `h¹` and `χ` are invariant under the shift `D ↦ D − div g`.
* `Adelic.chi_eq_of_principal_shift`, `Adelic.chi_eq_of_linearEquivalence`
  — the same statements spelled with `Scheme.WeilDivisor.principal` and with the
  project's `LinearEquivalence` relation.
* `Adelic.exists_effective_linearEquiv_of_ne_zero_mem` — the effective-witness
  brick: a nonzero `f ∈ L(D)` exhibits `D + div f ≥ 0` in the class of `D`.
* `Adelic.one_le_ell_of_nonneg` — conversely an effective divisor has `ℓ ≥ 1`.

## Provenance

The mathematical content is the adelic (function-field) incarnation of the
sibling project's sheaf-theoretic `mulEquivDivisorSheaf` /
`chi_divisorSheaf_eq_of_picClass_eq` pair
(`Algebraic-Jacobian-Challenge-Rebuild`, `RiemannRoch/MulEquiv.lean` and
`RiemannRoch/Degree.lean`).  **No code was ported**: that development is built on
a different substrate (`CurveDivisor` on closed points, `divisorSheaf`,
`Sheaf.chi`, `CechPic`), none of whose names exist in this project.  What is
reused is the *argument*: transport `χ` along multiplication by `g` and cancel in
the ledger.  Here the transport is elementary linear algebra on subspaces of
`K(X)`, which is why this file needs no finiteness or exactness input at all —
whereas the sheaf-theoretic form needs the χ-additivity machinery even to state
the transport.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits IsDedekindDomain
open scoped WithZero

namespace AlgebraicGeometry
namespace Adelic

/-! ## §1. The order arithmetic behind the multiplication isomorphism -/

section Order

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X]

/-- **Multiplication by `g` shifts the section bound by `div g`.**  If
`D'(P) ≥ D(P) − ord_P g` at every prime divisor `P` of `U`, then multiplication
by `g ≠ 0` carries `Γ(U, 𝒪(D))` into `Γ(U, 𝒪(D'))`.

This is `ord_P (g·f) = ord_P g + ord_P f` (`order_mul_of_ne_zero`) rearranged:
`ord_P (g·f) ≥ ord_P g − D(P) ≥ −D'(P)`.  Stated with an inequality rather than
an equality on `D'` so that the same lemma serves both directions of the
isomorphism (apply it to `g⁻¹` for the inverse). -/
theorem mul_mem_sectionOfDivisor {U : X.Opens} {D D' : X.WeilDivisor}
    {g : X.functionField} (hg : g ≠ 0)
    (hD' : ∀ P : X.PrimeDivisor, P.point ∈ U →
      (show X.PrimeDivisor →₀ ℤ from D) P - Scheme.RationalMap.order P g ≤
        (show X.PrimeDivisor →₀ ℤ from D') P)
    {f : X.functionField} (hf : f ∈ sectionOfDivisor U D) :
    g * f ∈ sectionOfDivisor U D' := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  refine Or.inr fun P hP => ?_
  have hord := (mem_sectionOfDivisor_of_ne_zero hf0).mp hf P hP
  rw [Scheme.RationalMap.order_mul_of_ne_zero P hg hf0]
  have := hD' P hP
  linarith

end Order

/-! ## §2. Multiplication by `g` as a `k`-linear automorphism -/

section MulEquiv

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X]

/-- **Multiplication by a nonzero rational function, as a `k`-linear
automorphism of `K(X)`.**  The inverse is multiplication by `g⁻¹`.  `k`-linearity
is automatic: multiplication by a fixed element of `K(X)` commutes with the
`k`-action. -/
noncomputable def mulEquivFunctionField (g : X.functionField) (hg : g ≠ 0) :
    X.functionField ≃ₗ[k] X.functionField :=
  LinearEquiv.ofLinear (LinearMap.mulLeft k g) (LinearMap.mulLeft k g⁻¹)
    (by ext x; simp [mul_inv_cancel_left₀ hg])
    (by ext x; simp [inv_mul_cancel_left₀ hg])

omit [IsLocallyNoetherian X] [X.IsRegularInCodimensionOne] [IsConstantField k X] in
@[simp] theorem mulEquivFunctionField_apply (g : X.functionField) (hg : g ≠ 0)
    (f : X.functionField) : mulEquivFunctionField k g hg f = g * f := rfl

/-- **The section subspace is carried onto the shifted section subspace.**
`(Γ(U, 𝒪(D))).map (g·) = Γ(U, 𝒪(D'))` whenever `D'(P) = D(P) − ord_P g` at every
prime divisor of `U`.  Both inclusions are `mul_mem_sectionOfDivisor`, the second
applied to `g⁻¹` (whose order is `−ord_P g`). -/
theorem map_sectionSub_mulEquiv {U : X.Opens} {D D' : X.WeilDivisor}
    {g : X.functionField} (hg : g ≠ 0)
    (hD' : ∀ P : X.PrimeDivisor, P.point ∈ U →
      (show X.PrimeDivisor →₀ ℤ from D') P =
        (show X.PrimeDivisor →₀ ℤ from D) P - Scheme.RationalMap.order P g) :
    Submodule.map (mulEquivFunctionField k g hg : X.functionField →ₗ[k] X.functionField)
        (sectionSub k U D) = sectionSub k U D' := by
  apply le_antisymm
  · rintro x ⟨f, hf, rfl⟩
    exact mul_mem_sectionOfDivisor hg (fun P hP => by rw [hD' P hP]) hf
  · intro x hx
    refine ⟨g⁻¹ * x, ?_, by simp [mul_inv_cancel_left₀ hg]⟩
    refine mul_mem_sectionOfDivisor (inv_ne_zero hg) (fun P hP => ?_) hx
    rw [Scheme.RationalMap.order_inv, hD' P hP]
    linarith

/-- **The multiplication isomorphism on section subspaces.**
`Γ(U, 𝒪(D)) ≃ₗ[k] Γ(U, 𝒪(D − div g))`, the `k`-linear incarnation of the sheaf
isomorphism `𝒪(D) ≅ 𝒪(D − div g)` given by multiplication by `g`. -/
noncomputable def sectionSubMulEquiv {U : X.Opens} {D D' : X.WeilDivisor}
    {g : X.functionField} (hg : g ≠ 0)
    (hD' : ∀ P : X.PrimeDivisor, P.point ∈ U →
      (show X.PrimeDivisor →₀ ℤ from D') P =
        (show X.PrimeDivisor →₀ ℤ from D) P - Scheme.RationalMap.order P g) :
    sectionSub k U D ≃ₗ[k] sectionSub k U D' :=
  ((mulEquivFunctionField k g hg).submoduleMap (sectionSub k U D)).trans
    (LinearEquiv.ofEq _ _ (map_sectionSub_mulEquiv k hg hD'))

/-- The multiplication isomorphism is multiplication by `g` on underlying
elements. -/
@[simp] theorem sectionSubMulEquiv_coe_apply {U : X.Opens} {D D' : X.WeilDivisor}
    {g : X.functionField} (hg : g ≠ 0)
    (hD' : ∀ P : X.PrimeDivisor, P.point ∈ U →
      (show X.PrimeDivisor →₀ ℤ from D') P =
        (show X.PrimeDivisor →₀ ℤ from D) P - Scheme.RationalMap.order P g)
    (x : sectionSub k U D) :
    ((sectionSubMulEquiv k hg hD' x : sectionSub k U D') : X.functionField) =
      g * (x : X.functionField) := rfl

end MulEquiv

/-! ## §3. Invariance of `ℓ`, `h¹` and `χ` under the class shift

The shift condition is stated as the pointwise identity
`D'(P) = D(P) − ord_P g` **at every** prime divisor (not merely on an open), which
is exactly `D' = D − div g` coordinatewise.  Under it, the multiplication
isomorphism transports the whole ledger data — the two chart subspaces, their sum
(the coboundary) and the overlap subspace — hence `Ȟ¹` as well.
-/

section Invariance

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X]

/-- **`ℓ` is invariant under the class shift `D ↦ D − div g`.** -/
theorem ell_eq_of_shift {D D' : X.WeilDivisor} {g : X.functionField} (hg : g ≠ 0)
    (hD' : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P - Scheme.RationalMap.order P g) :
    ell k D' = ell k D :=
  ((sectionSubMulEquiv k (U := ⊤) hg (fun P _ => hD' P)).symm).finrank_eq

variable (U₀ U₁ : X.Opens)

/-- **The coboundary subspace is carried onto the shifted coboundary subspace.**
`B(D) = Γ(U₀,𝒪(D)) + Γ(U₁,𝒪(D))` is a sum of two subspaces, each transported by
`map_sectionSub_mulEquiv`, and `Submodule.map` preserves `⊔`. -/
theorem map_coboundarySub_mulEquiv {D D' : X.WeilDivisor} {g : X.functionField}
    (hg : g ≠ 0)
    (hD' : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P - Scheme.RationalMap.order P g) :
    Submodule.map (mulEquivFunctionField k g hg : X.functionField →ₗ[k] X.functionField)
        (coboundarySub k U₀ U₁ D) = coboundarySub k U₀ U₁ D' := by
  rw [coboundarySub, coboundarySub, Submodule.map_sup,
    map_sectionSub_mulEquiv k hg (fun P _ => hD' P),
    map_sectionSub_mulEquiv k hg (fun P _ => hD' P)]

/-- **Monotonicity of the coboundary subspace in the divisor.** The `k`-linear
form of `coboundary_mono`: `D ≤ D'` gives `B(D) ⊆ B(D')`. -/
theorem coboundarySub_mono {D D' : X.WeilDivisor}
    (hle : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) P ≤
      (show X.PrimeDivisor →₀ ℤ from D') P) :
    coboundarySub k U₀ U₁ D ≤ coboundarySub k U₀ U₁ D' :=
  sup_le_sup (sectionSub_mono k U₀ hle) (sectionSub_mono k U₁ hle)

/-- **`Ȟ¹` is carried isomorphically onto the shifted `Ȟ¹`.**  Multiplication by
`g` is a `k`-linear automorphism of `K(X)` mapping the overlap subspace `𝒜(D)`
onto `𝒜(D')` and the coboundary `B(D)` onto `B(D')`, hence it descends to a
`k`-linear isomorphism of the quotients `Ȟ¹(D) ≃ₗ[k] Ȟ¹(D')`. -/
noncomputable def h1ModMulEquiv {D D' : X.WeilDivisor} {g : X.functionField}
    (hg : g ≠ 0)
    (hD' : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P - Scheme.RationalMap.order P g) :
    H1Mod k U₀ U₁ D ≃ₗ[k] H1Mod k U₀ U₁ D' :=
  Submodule.Quotient.equiv _ _
    (sectionSubMulEquiv k (U := U₀ ⊓ U₁) hg (fun P _ => hD' P))
    (by
      have hB := map_coboundarySub_mulEquiv k U₀ U₁ hg hD'
      apply Submodule.ext
      intro x
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [← hB]
        exact ⟨(y : X.functionField), hy, rfl⟩
      · intro hx
        rw [← hB] at hx
        obtain ⟨y, hy, hyx⟩ := hx
        refine ⟨⟨y, coboundarySub_le_overlap k U₀ U₁ D hy⟩, hy, ?_⟩
        exact Subtype.ext hyx)

/-- **`h¹` is invariant under the class shift `D ↦ D − div g`.** -/
theorem h1dim_eq_of_shift {D D' : X.WeilDivisor} {g : X.functionField}
    (hg : g ≠ 0)
    (hD' : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P - Scheme.RationalMap.order P g) :
    h1dim k U₀ U₁ D' = h1dim k U₀ U₁ D :=
  ((h1ModMulEquiv k U₀ U₁ hg hD').symm).finrank_eq

/-- **χ is invariant under the class shift `D ↦ D − div g`** — the adelic
class-invariance of the Euler characteristic, unconditional (no finiteness, no
ledger exactness input). -/
theorem chi_eq_of_shift {D D' : X.WeilDivisor} {g : X.functionField} (hg : g ≠ 0)
    (hD' : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P - Scheme.RationalMap.order P g) :
    chi k U₀ U₁ D' = chi k U₀ U₁ D := by
  rw [chi, chi, ell_eq_of_shift k hg hD', h1dim_eq_of_shift k U₀ U₁ hg hD']

end Invariance

/-! ## §4. The `principal`/`LinearEquivalence` spellings

`Scheme.WeilDivisor.principal` needs the stronger `[IsNoetherian X]` (global
Noetherianness is what makes `ord_P f` finitely supported), so this section
strengthens the hypothesis; §1–§3 deliberately do not.
-/

section Principal

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X] (U₀ U₁ : X.Opens)

/-- **The shift condition holds for `D' = D − div g`.**  The coordinatewise
unfolding of `Scheme.WeilDivisor.principal` (`principal_apply`), packaged as the
`hD'` hypothesis of §3. -/
theorem sub_principal_apply {D : X.WeilDivisor} {g : X.functionField} (hg : g ≠ 0)
    (P : X.PrimeDivisor) :
    (show X.PrimeDivisor →₀ ℤ from D - Scheme.WeilDivisor.principal g hg) P =
      (show X.PrimeDivisor →₀ ℤ from D) P - Scheme.RationalMap.order P g := by
  rw [show (show X.PrimeDivisor →₀ ℤ from D - Scheme.WeilDivisor.principal g hg) P =
        (show X.PrimeDivisor →₀ ℤ from D) P -
          (show X.PrimeDivisor →₀ ℤ from Scheme.WeilDivisor.principal g hg) P from
      Finsupp.sub_apply _ _ _,
    Scheme.WeilDivisor.principal_apply g hg P]

/-- **χ is invariant under subtracting a principal divisor.**
`χ(D − div g) = χ(D)`.  This is the adelic form of the sibling project's
`chi_divisorSheaf_eq_of_picClass_eq`, obtained here without any finiteness
input. -/
theorem chi_eq_of_principal_shift (D : X.WeilDivisor) {g : X.functionField}
    (hg : g ≠ 0) :
    chi k U₀ U₁ (D - Scheme.WeilDivisor.principal g hg) = chi k U₀ U₁ D :=
  chi_eq_of_shift k U₀ U₁ hg (sub_principal_apply hg)

/-- **`ℓ` is invariant under subtracting a principal divisor.** -/
theorem ell_eq_of_principal_shift (D : X.WeilDivisor) {g : X.functionField}
    (hg : g ≠ 0) :
    ell k (D - Scheme.WeilDivisor.principal g hg) = ell k D :=
  ell_eq_of_shift k hg (sub_principal_apply hg)

/-- **`h¹` is invariant under subtracting a principal divisor.** -/
theorem h1dim_eq_of_principal_shift (D : X.WeilDivisor) {g : X.functionField}
    (hg : g ≠ 0) :
    h1dim k U₀ U₁ (D - Scheme.WeilDivisor.principal g hg) = h1dim k U₀ U₁ D :=
  h1dim_eq_of_shift k U₀ U₁ hg (sub_principal_apply hg)

/-- **χ is a linear-equivalence invariant.**  If `D ~ D'` in the sense of
`Scheme.WeilDivisor.LinearEquivalence` (i.e. `D − D' = div g`), then
`χ(D) = χ(D')`; likewise for `ℓ` and `h¹` (`ell_eq_of_linearEquivalence`,
`h1dim_eq_of_linearEquivalence`).  This is the statement the downstream
Picard-representability route consumes: numerical invariants are functions of the
class, not of the representative. -/
theorem chi_eq_of_linearEquivalence {D D' : X.WeilDivisor}
    (h : Scheme.WeilDivisor.LinearEquivalence D D') :
    chi k U₀ U₁ D = chi k U₀ U₁ D' := by
  obtain ⟨g, hg, hDD'⟩ := h
  have hD' : D' = D - Scheme.WeilDivisor.principal g hg := by
    rw [← hDD']; abel
  rw [hD', chi_eq_of_principal_shift k U₀ U₁ D hg]

/-- **`ℓ` is a linear-equivalence invariant.** -/
theorem ell_eq_of_linearEquivalence {D D' : X.WeilDivisor}
    (h : Scheme.WeilDivisor.LinearEquivalence D D') :
    ell k D = ell k D' := by
  obtain ⟨g, hg, hDD'⟩ := h
  have hD' : D' = D - Scheme.WeilDivisor.principal g hg := by
    rw [← hDD']; abel
  rw [hD', ell_eq_of_principal_shift k D hg]

/-- **`h¹` is a linear-equivalence invariant.** -/
theorem h1dim_eq_of_linearEquivalence {D D' : X.WeilDivisor}
    (h : Scheme.WeilDivisor.LinearEquivalence D D') :
    h1dim k U₀ U₁ D = h1dim k U₀ U₁ D' := by
  obtain ⟨g, hg, hDD'⟩ := h
  have hD' : D' = D - Scheme.WeilDivisor.principal g hg := by
    rw [← hDD']; abel
  rw [hD', h1dim_eq_of_principal_shift k U₀ U₁ D hg]

/-! ### The effective-witness dictionary

A nonzero global section `f ∈ L(D)` exhibits an **effective** divisor
`D + div f ≥ 0` in the linear-equivalence class of `D`.  Conversely an effective
divisor has `ℓ ≥ 1` (the constant `1` is a section).  This pair is the
"`ℓ(D) ≥ 1 ⟺ D ~ E ≥ 0`" dictionary that the peel-an-effective-divisor form of
uniform `H¹` vanishing consumes: the sibling project's
`exists_effective_of_picClass` is the same statement over there, phrased on
`CechPic` classes rather than on the linear-equivalence relation. -/

/-- **A nonzero section makes `D` linearly equivalent to an effective divisor.**
For `0 ≠ f ∈ L(D) = Γ(⊤, 𝒪(D))`, the divisor `E := D + div f` satisfies `E ≥ 0`
coordinatewise and `E ~ D` (indeed `E − D = div f`).

`E(P) = D(P) + ord_P f ≥ 0` is exactly the section condition
`ord_P f ≥ −D(P)`. -/
theorem exists_effective_linearEquiv_of_ne_zero_mem {D : X.WeilDivisor}
    {f : X.functionField} (hf : f ≠ 0) (hfD : f ∈ sectionOfDivisor ⊤ D) :
    ∃ E : X.WeilDivisor,
      (∀ P : X.PrimeDivisor, 0 ≤ (show X.PrimeDivisor →₀ ℤ from E) P) ∧
        Scheme.WeilDivisor.LinearEquivalence E D := by
  refine ⟨D + Scheme.WeilDivisor.principal f hf, fun P => ?_, ⟨f, hf, ?_⟩⟩
  · rw [show (show X.PrimeDivisor →₀ ℤ from D + Scheme.WeilDivisor.principal f hf) P =
          (show X.PrimeDivisor →₀ ℤ from D) P +
            (show X.PrimeDivisor →₀ ℤ from Scheme.WeilDivisor.principal f hf) P from
        Finsupp.add_apply _ _ _,
      Scheme.WeilDivisor.principal_apply f hf P]
    have := (mem_sectionOfDivisor_of_ne_zero hf).mp hfD P
      (TopologicalSpace.Opens.mem_top P.point)
    linarith
  · abel

/-- **An effective divisor has at least the constants as sections**, hence
`1 ≤ ℓ(D)` once `Γ(⊤, 𝒪(D))` is finite-dimensional.  `1 ∈ Γ(⊤, 𝒪(0)) ⊆
Γ(⊤, 𝒪(D))` by monotonicity, and a submodule containing a nonzero vector has
positive rank. -/
theorem one_le_ell_of_nonneg {D : X.WeilDivisor}
    (hD : ∀ P : X.PrimeDivisor, 0 ≤ (show X.PrimeDivisor →₀ ℤ from D) P)
    [Module.Finite k (sectionSub k ⊤ D)] : 1 ≤ ell k D := by
  have hone : (1 : X.functionField) ∈ sectionSub k ⊤ D := by
    refine sectionOfDivisor_mono ⊤ (fun P => ?_) (one_mem_sectionOfDivisor_zero ⊤)
    have h0 : (show X.PrimeDivisor →₀ ℤ from (0 : X.WeilDivisor)) P = (0 : ℤ) :=
      Finsupp.zero_apply
    rw [h0]
    exact hD P
  have hne : (⟨1, hone⟩ : sectionSub k ⊤ D) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Subtype.val h)
  rw [ell, Nat.one_le_iff_ne_zero]
  intro h
  have hsub : Subsingleton (sectionSub k ⊤ D) :=
    (Module.finrank_zero_iff (R := k)).mp h
  exact hne (Subsingleton.elim _ _)

end Principal

end Adelic
end AlgebraicGeometry
