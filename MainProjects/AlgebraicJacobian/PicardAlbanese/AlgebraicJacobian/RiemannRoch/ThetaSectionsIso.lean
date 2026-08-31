/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.ThetaSections
import AlgebraicJacobian.Picard.OpenImmersionUnits

/-!
# DD-4 (field level) — the sheaf isomorphism `Θⁿ ≅ 𝒪(n·F)` and its `H⁰`/`H¹` exports

The assembly of the W6-lite transport seam (`informal/dat-d-worksheet.md` §2.1, §5 DD-4):
the section-wise bijections of `RiemannRoch/ThetaSections.lean` are packaged into an
isomorphism of sheaves of `K`-modules, the two-chart mirror of
`MeromorphicPresentation.gluedDivisorSheafIso`:

* `AlgebraicGeometry.thetaTwistDivisorPresheafIso` — the presheaf isomorphism
  `twistPresheaf … (thetaUnit π ^ n) ≅ divisorPresheaf K (n • F)`;
* `AlgebraicGeometry.thetaTwistDivisorSheafIso` —
  **`thetaTwistSheaf π n ≅ Y.divisorSheaf K (n • fiberWeilDivisor π)`**, the engine-side
  `𝒪(Θⁿ)` identified with the divisor sheaf `𝒪(n·F)` (`F = fiberWeilDivisor π`);
* `AlgebraicGeometry.thetaTwistH0Equiv` — the `H⁰` reading
  `H⁰(Θⁿ) ≃ₗ[K] divisorSections K (n • F) ⊤` (the `H_A` spaces in DD-F's `divisorSections`
  spelling), and
* `AlgebraicGeometry.subsingleton_hModule_thetaTwistSheaf_one_iff` — the `H¹`-vanishing
  transport `Subsingleton (H¹(Θⁿ)) ↔ Subsingleton (H¹(𝒪(n·F)))` that lets the DD-0 window
  ledger (DAT-0a) fire on the twist sheaf.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

section Iso

variable (K : Type u) [Field K] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))] [IsIntegral Y]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  (π : Y ⟶ P1 K) [IsDominant π] (n : ℕ)

omit [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))] [IsIntegral Y]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsDominant π] in
/-- Twisted sections over an empty open form a subsingleton (both component rings do). -/
lemma twistSubmodule_subsingleton_of_empty {W : Y.Opens} (hW : ¬ (W : Set Y).Nonempty) :
    Subsingleton
      ↥(twistSubmodule K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) W) := by
  have hbot : W = ⊥ := by
    apply Opens.ext
    rw [Set.not_nonempty_iff_eq_empty.mp hW, Opens.coe_bot]
  haveI : Subsingleton Γ(Y, W ⊓ fiberChart₀ π) :=
    subsingleton_sections_of_le_bot Y (inf_le_left.trans hbot.le)
  haveI : Subsingleton Γ(Y, W ⊓ fiberChart₁ π) :=
    subsingleton_sections_of_le_bot Y (inf_le_left.trans hbot.le)
  exact ⟨fun a b => Subtype.ext (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩

open Classical in
/-- The section-wise map for all opens: the value map on nonempty opens, the zero map into
the terminal sections on the empty open. -/
noncomputable def thetaToDivisorPresheafApp (W : Y.Opens) :
    ↥(twistSubmodule K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) W) →ₗ[K]
      ↥(divisorSections K (n • fiberWeilDivisor π) W) :=
  if hW : (W : Set Y).Nonempty then
    thetaToDivisorApp K π n (genericPoint_mem_of_nonempty hW)
  else 0

lemma thetaToDivisorPresheafApp_of_nonempty {W : Y.Opens} (hW : (W : Set Y).Nonempty) :
    thetaToDivisorPresheafApp K π n W =
      thetaToDivisorApp K π n (genericPoint_mem_of_nonempty hW) :=
  dif_pos hW

/-- **The presheaf morphism `Θⁿ → 𝒪(n·F)`** of `K`-modules. -/
noncomputable def thetaToDivisorPresheaf :
    twistPresheaf K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) ⟶
      divisorPresheaf K (n • fiberWeilDivisor π) where
  app W := ModuleCat.ofHom (thetaToDivisorPresheafApp K π n W.unop)
  naturality {A B} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    by_cases hB : (B.unop : Set Y).Nonempty
    · have hA : (A.unop : Set Y).Nonempty := hB.mono (leOfHom i.unop)
      apply Subtype.ext
      change ((thetaToDivisorPresheafApp K π n B.unop
          (twistRes K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) i.unop.le s) :
          divisorSections K (n • fiberWeilDivisor π) B.unop) : Y.functionField) =
        ((divisorSectionsRes K (n • fiberWeilDivisor π) (leOfHom i.unop)
          (thetaToDivisorPresheafApp K π n A.unop s) :
          divisorSections K (n • fiberWeilDivisor π) B.unop) : Y.functionField)
      rw [divisorSectionsRes_coe K (leOfHom i.unop) hB,
        thetaToDivisorPresheafApp_of_nonempty K π n hB,
        thetaToDivisorPresheafApp_of_nonempty K π n hA, thetaToDivisorApp_coe,
        thetaToDivisorApp_coe, thetaVal_res]
    · haveI := divisorPresheaf_obj_subsingleton K
        (D := n • fiberWeilDivisor π) (W := B.unop) hB
      exact Subsingleton.elim _ _

/-- The section-wise map is bijective on every open: an isomorphism on nonempty opens, a
map of subsingletons on the empty open. -/
lemma thetaToDivisorPresheafApp_bijective (W : Y.Opens) :
    Function.Bijective (thetaToDivisorPresheafApp K π n W) := by
  by_cases hW : (W : Set Y).Nonempty
  · rw [thetaToDivisorPresheafApp_of_nonempty K π n hW]
    exact thetaToDivisorApp_bijective K π n _
  · haveI := twistSubmodule_subsingleton_of_empty K π n (W := W) hW
    haveI := divisorSections_subsingleton_of_empty K
      (D := n • fiberWeilDivisor π) (U := W) hW
    exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

lemma thetaToDivisorPresheaf_app_isIso (W : (Y.Opens)ᵒᵖ) :
    IsIso ((thetaToDivisorPresheaf K π n).app W) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact thetaToDivisorPresheafApp_bijective K π n W.unop

/-- The presheaf isomorphism `Θⁿ ≅ 𝒪(n·F)`. -/
noncomputable def thetaTwistDivisorPresheafIso :
    twistPresheaf K (fiberChart₀ π) (fiberChart₁ π) (thetaUnit π ^ n) ≅
      divisorPresheaf K (n • fiberWeilDivisor π) :=
  NatIso.ofComponents
    (fun W => by
      haveI := thetaToDivisorPresheaf_app_isIso K π n W
      exact asIso ((thetaToDivisorPresheaf K π n).app W))
    (fun i => (thetaToDivisorPresheaf K π n).naturality i)

/-- **DD-4 (1), the field-level bridge**: the engine-side twisted sheaf `Θⁿ =
thetaTwistSheaf π n` is the divisor sheaf `𝒪(n·F)` (`F = fiberWeilDivisor π`), as sheaves of
`K`-modules — over a nonempty open a matching pair `(s₀, s₁)` corresponds to the rational
function `(uⁿ)⁻¹ · germ_η s₀ = germ_η s₁` (`u = fiberCoordUnit π`), the two-chart mirror of
`MeromorphicPresentation.gluedDivisorSheafIso`. -/
noncomputable def thetaTwistDivisorSheafIso :
    thetaTwistSheaf π n ≅ Y.divisorSheaf K (n • fiberWeilDivisor π) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (thetaTwistDivisorPresheafIso K π n)

end Iso

/-! ## The `H⁰`/`H¹` exports -/

section Exports

variable (K : Type u) [Field K] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))] [IsIntegral Y]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  (π : Y ⟶ P1 K) [IsDominant π] (n : ℕ)

/-- **The `H⁰` reading of the twist sheaf** as the `H_A` space in `divisorSections` form:
`H⁰(Θⁿ) ≃ₗ[K] divisorSections K (n·F) ⊤`. The `H_A` spaces `H⁰(𝒪(A·F))` DD-F consumes are
this equivalence at the window twists `A ∈ {s, M, M+s}`. -/
noncomputable def thetaTwistH0Equiv :
    Sheaf.HModule (thetaTwistSheaf π n) 0 ≃ₗ[K]
      ↥(divisorSections K (n • fiberWeilDivisor π) ⊤) :=
  (Sheaf.HModule.mapEquiv (thetaTwistDivisorSheafIso K π n) 0).trans
    (divisorSectionsEquivH0 K (n • fiberWeilDivisor π))

/-- **The `H¹`-vanishing transport**: `H¹(Θⁿ)` vanishes iff `H¹(𝒪(n·F))` does — the seam
that lets the DD-0 window ledger (DAT-0a) fire on the engine-side twist sheaf. -/
theorem subsingleton_hModule_thetaTwistSheaf_one_iff :
    Subsingleton (Sheaf.HModule (thetaTwistSheaf π n) 1) ↔
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K (n • fiberWeilDivisor π)) 1) :=
  (Sheaf.HModule.mapEquiv (thetaTwistDivisorSheafIso K π n) 1).toEquiv.subsingleton_congr

end Exports

end AlgebraicGeometry
