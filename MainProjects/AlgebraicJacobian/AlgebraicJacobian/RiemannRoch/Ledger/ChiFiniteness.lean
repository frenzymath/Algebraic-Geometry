/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.ChiSlice
import AlgebraicJacobian.RiemannRoch.Ledger.DivisorSheafZero
import AlgebraicJacobian.RiemannRoch.Ledger.DevissageExact
import AlgebraicJacobian.RiemannRoch.Ledger.JumpDimension

/-!
# Finiteness of the cohomology of divisor sheaves, by dévissage

For the curve bundle `X` (integral, smooth of relative dimension one and quasi-compact over
a field `K`) whose structure sheaf has finite `H⁰` and `H¹` — the two properness inputs,
taken here as instance hypotheses — this file proves that **every** divisor sheaf `𝒪(D)`
has finite `H⁰` and `H¹`:

* `AlgebraicGeometry.Scheme.CurveDivisor.single`: the one-point Weil divisor `n · x`, as a
  `CurveDivisor`-valued smart constructor (the wrapper type blocks elaboration of mixed
  `Finsupp`/`CurveDivisor` sums, so downstream arithmetic goes through this constructor).
* `AlgebraicGeometry.Scheme.CurveDivisor.induction_devissage`: the induction scaffolding —
  a predicate on Weil divisors that holds for `0` and transfers along one-point dévissage
  `D ↭ D − x` holds everywhere (per-point `ℤ`-recursion on top of `Finsupp.induction`).
* `AlgebraicGeometry.devissageDivisor_eq_sub` / `devissageDivisor_add_single` /
  `deg_devissageDivisor`: divisor and degree bookkeeping for the dévissage twist `D − x`.
* `AlgebraicGeometry.moduleFinite_hModule_skyModule_zero` / `_one`: the cohomology of a
  skyscraper with finite value module is finite.
* `AlgebraicGeometry.moduleFinite_hModule_divisorSheaf_zero` / `_one` (instances):
  `Module.Finite K (HModule (𝒪(D)) i)` for `i = 0, 1` — base case transported across
  `𝒪_X ≅ 𝒪(0)`, dévissage step through the six-term slice of `devissageSES`.

## The step, in both directions

At a closed point `x` the slice of `0 → 𝒪(D−x) → 𝒪(D) → sky_x J → 0` gives, with
`H⁰(sky) = J` finite (`moduleFinite_jumpModule`) and `H¹(sky) = 0`:

* up: `H⁰(𝒪(D))`, `H¹(𝒪(D))` finite from `𝒪(D−x)` (middle-of-slice extension);
* down: `H⁰(𝒪(D−x))` embeds in `H⁰(𝒪(D))`; `H¹(𝒪(D−x))` is an extension of a submodule
  of `H¹(𝒪(D))` by the image of `H⁰(sky)`.

All identifications of the terms of `devissageSES` with their divisor-sheaf spellings are
definitional; they are performed by type ascription (`haveI`/`exact` with the target
spelling), never by rewriting hypotheses.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

/-! ## Induction scaffolding on Weil divisors -/

section Scaffolding

variable {X : Scheme.{u}} [IsIntegral X]

/-- The one-point Weil divisor `n · x` at a closed point `x`, as a `CurveDivisor`. The
wrapper `CurveDivisor` is a plain `def` over `Finsupp`, which blocks elaboration of mixed
`Finsupp`/`CurveDivisor` arithmetic; this smart constructor keeps one-point divisors on
the `CurveDivisor` side of the seam. -/
noncomputable def Scheme.CurveDivisor.single {x : X} (hx : x ≠ genericPoint X) (n : ℤ) :
    X.CurveDivisor :=
  Finsupp.single (⟨x, hx⟩ : {p : X // p ≠ genericPoint X}) n

/-- The underlying finitely supported function of a one-point divisor. -/
lemma Scheme.CurveDivisor.toFinsupp_single {x : X} (hx : x ≠ genericPoint X) (n : ℤ) :
    toFinsupp (CurveDivisor.single hx n) =
      Finsupp.single (⟨x, hx⟩ : {p : X // p ≠ genericPoint X}) n :=
  rfl

/-- The dévissage twist is subtraction of the one-point divisor: `D − x` literally. -/
lemma devissageDivisor_eq_sub {x : X} (hx : x ≠ genericPoint X) (D : X.CurveDivisor) :
    devissageDivisor hx D = D - CurveDivisor.single hx 1 :=
  rfl

/-- The one-point divisor with multiplicity `0` is the zero divisor. -/
lemma Scheme.CurveDivisor.single_zero {x : X} (hx : x ≠ genericPoint X) :
    CurveDivisor.single hx 0 = (0 : X.CurveDivisor) := by
  change Finsupp.single (⟨x, hx⟩ : {p : X // p ≠ genericPoint X}) (0 : ℤ) = 0
  exact Finsupp.single_zero _

/-- One-point divisors at the same point add their multiplicities. -/
lemma Scheme.CurveDivisor.single_add {x : X} (hx : x ≠ genericPoint X) (m n : ℤ) :
    CurveDivisor.single hx m + CurveDivisor.single hx n = CurveDivisor.single hx (m + n) := by
  change Finsupp.single (⟨x, hx⟩ : {p : X // p ≠ genericPoint X}) m +
      Finsupp.single ⟨x, hx⟩ n = Finsupp.single ⟨x, hx⟩ (m + n)
  exact (Finsupp.single_add _ _ _).symm

/-- `n` copies of the point `x`, as a one-point divisor: `n • x = (n : ℤ) · x`. -/
lemma Scheme.CurveDivisor.nsmul_single_one {x : X} (hx : x ≠ genericPoint X) (n : ℕ) :
    n • CurveDivisor.single hx 1 = CurveDivisor.single hx (n : ℤ) := by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, Scheme.CurveDivisor.single_zero]
  | succ n ih =>
    rw [succ_nsmul, ih, Scheme.CurveDivisor.single_add, Nat.cast_add, Nat.cast_one]

/-- The degree of a one-point divisor: `deg (n · x) = n · [κ(x) : K]`. -/
lemma Scheme.CurveDivisor.deg_single' (K : Type u) [CommRing K]
    [X.Over (Spec (CommRingCat.of K))] {x : X} (hx : x ≠ genericPoint X) (n : ℤ) :
    CurveDivisor.deg K (CurveDivisor.single hx n) = n * X.residueDeg K x :=
  CurveDivisor.deg_single K (X := X) (⟨x, hx⟩ : {p : X // p ≠ genericPoint X}) n

/-- Single-bump induction for finitely supported `ℤ`-valued functions: a predicate that
holds at `0` and is invariant under adding a single generator holds everywhere. -/
private theorem finsupp_induction_bump {α : Type u} {P : (α →₀ ℤ) → Prop} (zero : P 0)
    (bump : ∀ (a : α) (f : α →₀ ℤ), P (f + Finsupp.single a 1) ↔ P f) (f : α →₀ ℤ) :
    P f := by
  have hn : ∀ (n : ℤ), ∀ (a : α) (f : α →₀ ℤ), P (f + Finsupp.single a n) ↔ P f := by
    intro n
    induction n using Int.induction_on with
    | zero => intro a f; rw [Finsupp.single_zero, add_zero]
    | succ n ih =>
      intro a f
      have h1 : f + Finsupp.single a ((n : ℤ) + 1) =
          f + Finsupp.single a (n : ℤ) + Finsupp.single a 1 := by
        rw [Finsupp.single_add, add_assoc]
      rw [h1, bump a (f + Finsupp.single a (n : ℤ)), ih a f]
    | pred n ih =>
      intro a f
      have h1 : f + Finsupp.single a (-(n : ℤ) - 1) + Finsupp.single a 1 =
          f + Finsupp.single a (-(n : ℤ)) := by
        rw [add_assoc, ← Finsupp.single_add]
        norm_num
      rw [← ih a f, ← bump a (f + Finsupp.single a (-(n : ℤ) - 1)), h1]
  induction f using Finsupp.induction with
  | zero => exact zero
  | single_add a b f _ _ ih =>
    rw [show Finsupp.single a b + f = f + Finsupp.single a b from add_comm _ _]
    exact (hn b a f).mpr ih

/-- **Dévissage induction on Weil divisors.** A predicate on `X.CurveDivisor` that holds
for the zero divisor and transfers (in both directions) along the one-point dévissage
`D ↭ devissageDivisor hx D = D − x` holds for every divisor. This is the induction
scaffolding shared by the finiteness dévissage and the χ-ledger `chi_divisorSheaf`. -/
theorem Scheme.CurveDivisor.induction_devissage {P : X.CurveDivisor → Prop} (zero : P 0)
    (step : ∀ {x : X} (hx : x ≠ genericPoint X) (D : X.CurveDivisor),
      P D ↔ P (devissageDivisor hx D))
    (D : X.CurveDivisor) : P D := by
  refine finsupp_induction_bump (P := fun F : {p : X // p ≠ genericPoint X} →₀ ℤ => P F)
    zero (fun p F => ?_) D
  have h := step p.2 (F + Finsupp.single p 1)
  have h2 : P (devissageDivisor p.2 (F + Finsupp.single p 1)) ↔ P F := by
    have heq : devissageDivisor p.2 (F + Finsupp.single p 1) = (F : X.CurveDivisor) := by
      change F + Finsupp.single p 1 - Finsupp.single p 1 = F
      abel
    rw [heq]
  exact h.trans h2

/-- Adding the point back: `(D − x) + x = D` for the dévissage twist. -/
lemma devissageDivisor_add_single {x : X} (hx : x ≠ genericPoint X) (D : X.CurveDivisor) :
    devissageDivisor hx D + CurveDivisor.single hx 1 = D := by
  rw [devissageDivisor_eq_sub]
  abel

/-- The degree drops by the residue degree along the dévissage twist:
`deg (D − x) = deg D − [κ(x) : K]`. -/
lemma deg_devissageDivisor (K : Type u) [CommRing K] [X.Over (Spec (CommRingCat.of K))]
    {x : X} (hx : x ≠ genericPoint X) (D : X.CurveDivisor) :
    CurveDivisor.deg K (devissageDivisor hx D) =
      CurveDivisor.deg K D - X.residueDeg K x := by
  have h := CurveDivisor.deg_add K (devissageDivisor hx D) (CurveDivisor.single hx 1)
  rw [devissageDivisor_add_single hx D] at h
  have hsingle : CurveDivisor.deg K (CurveDivisor.single hx 1) = X.residueDeg K x := by
    have h1 := CurveDivisor.deg_single K (X := X)
      (⟨x, hx⟩ : {p : X // p ≠ genericPoint X}) 1
    rw [one_mul] at h1
    exact h1
  rw [hsingle] at h
  omega

end Scaffolding

/-! ## The cohomology of a skyscraper is finite -/

section Skyscraper

variable {K : Type u} [CommRing K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

/-- `H⁰` of a skyscraper sheaf with finite value module is a finite `K`-module
(transport of the value module along `skyModuleGammaEquiv`). -/
theorem moduleFinite_hModule_skyModule_zero (x : X) (M : ModuleCat.{u} K)
    [Module.Finite K M] :
    Module.Finite K (Sheaf.HModule (skyModule x M) 0) :=
  Module.Finite.equiv (skyModuleGammaEquiv x M).symm

/-- `H¹` of a skyscraper sheaf is a finite `K`-module (it vanishes). -/
theorem moduleFinite_hModule_skyModule_one (x : X) (M : ModuleCat.{u} K) :
    Module.Finite K (Sheaf.HModule (skyModule x M) 1) :=
  haveI : Finite (Sheaf.HModule (skyModule x M) 1) := Finite.of_subsingleton
  Module.Finite.of_finite

end Skyscraper

/-! ## Finiteness dévissage for divisor sheaves -/

section Devissage

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

private theorem moduleFinite_hModule_divisorSheaf_aux (D : X.CurveDivisor) :
    Module.Finite K (Sheaf.HModule (X.divisorSheaf K D) 0) ∧
      Module.Finite K (Sheaf.HModule (X.divisorSheaf K D) 1) := by
  refine Scheme.CurveDivisor.induction_devissage
    (P := fun D => Module.Finite K (Sheaf.HModule (X.divisorSheaf K D) 0) ∧
      Module.Finite K (Sheaf.HModule (X.divisorSheaf K D) 1))
    ⟨?_, ?_⟩ (fun {x} hx D => ?_) D
  · exact Module.Finite.equiv (Sheaf.HModule.mapEquiv (moduleKSheafDivisorSheafZeroIso K) 0)
  · exact Module.Finite.equiv (Sheaf.HModule.mapEquiv (moduleKSheafDivisorSheafZeroIso K) 1)
  · -- the dévissage step, both ways, through the six-term slice
    have hS := devissageSES_shortExact K hx D
    -- the skyscraper term of the slice, in the `devissageSES` spelling
    haveI hsky0 : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₃ 0) :=
      haveI := moduleFinite_jumpModule K hx D
      moduleFinite_hModule_skyModule_zero x (jumpModule K hx D)
    haveI hsky1 : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₃ 1) :=
      moduleFinite_hModule_skyModule_one x (jumpModule K hx D)
    haveI hskysub : Subsingleton (Sheaf.HModule (devissageSES K hx D).X₃ 1) :=
      skyModule_subsingleton_hModule_one x (jumpModule K hx D)
    constructor
    · rintro ⟨h0D, h1D⟩
      haveI hX₂0 : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₂ 0) := h0D
      haveI hX₂1 : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₂ 1) := h1D
      exact ⟨Sheaf.HModule.moduleFinite_left_zero hS,
        Sheaf.HModule.moduleFinite_left_succ hS (show 0 + 1 = 1 from rfl)⟩
    · rintro ⟨h0D', h1D'⟩
      haveI hX₁0 : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₁ 0) := h0D'
      haveI hX₁1 : Module.Finite K (Sheaf.HModule (devissageSES K hx D).X₁ 1) := h1D'
      exact ⟨Sheaf.HModule.moduleFinite_middle hS 0, Sheaf.HModule.moduleFinite_middle hS 1⟩

/-- **Finiteness of `H⁰(𝒪(D))`** for every Weil divisor `D` on the curve bundle `X`, by
dévissage from the structure sheaf (whose `H⁰`/`H¹` finiteness are the two instance
hypotheses — properness enters only through them). -/
instance moduleFinite_hModule_divisorSheaf_zero (D : X.CurveDivisor) :
    Module.Finite K (Sheaf.HModule (X.divisorSheaf K D) 0) :=
  (moduleFinite_hModule_divisorSheaf_aux K D).1

/-- **Finiteness of `H¹(𝒪(D))`** for every Weil divisor `D` on the curve bundle `X`, by
dévissage from the structure sheaf (whose `H⁰`/`H¹` finiteness are the two instance
hypotheses — properness enters only through them). -/
instance moduleFinite_hModule_divisorSheaf_one (D : X.CurveDivisor) :
    Module.Finite K (Sheaf.HModule (X.divisorSheaf K D) 1) :=
  (moduleFinite_hModule_divisorSheaf_aux K D).2

end Devissage

end AlgebraicGeometry
