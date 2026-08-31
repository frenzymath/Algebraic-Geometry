/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.GluedDivisorSheaf
import AlgebraicJacobian.RiemannRoch.FLVClass

/-!
# W6-full, the assembly: `hfib` in sheaf form and the rank export (DAT-3 (d))

The step-(d) keystones of the W6-full discharge chain (`informal/w4-datum-worksheet.md`
§3.1, spec FROZEN there), for the curve bundle `X` over a field `K`: the FLV class form
and the rank anchor, transported from the divisor sheaf of the `(S)`-witness to the
cocycle-glued sheaf of a meromorphic presentation through the core isomorphism
`gluedDivisorSheafIso` (`RiemannRoch/GluedDivisorSheaf.lean`).

* `AlgebraicGeometry.subsingleton_hModule_gluedSheaf_one_iff` — vanishing of
  `H¹(glued(P))` is vanishing of `H¹(𝒪(presentationDivisor P))`;
* `AlgebraicGeometry.subsingleton_hModule_gluedSheaf_one_of_picClass_eq` — **`hfib` in
  the sheaf form the engine consumes**: vanishing of `H¹(𝒪(D))` for ANY witness divisor
  `D` of the presented class discharges vanishing of `H¹` of the glued sheaf (W6-lite
  witness-independence + the core isomorphism — Kleiman 3.10 (v)⟹(i) at a fibre);
* `AlgebraicGeometry.exists_subsingleton_hModule_gluedSheaf_one_of_one_le_classDeg_of_isFinite_toP1`
  — **the FLV class form on glued sheaves**: for classes `l · θⁿ` with `1 ≤ classDeg θ`
  and `n` large, `H¹` of the glued sheaf of every presentation of the class vanishes;
* `AlgebraicGeometry.h0_gluedSheaf_eq_classDeg_add_chi` — **the `rigidEngine_rank`
  clause**: under the vanishing, `h⁰(glued(P)) = classDeg P.picClass + χ(𝒪_X)` — with
  `χ = 1 − g` this is Kleiman's `rank Q = d + 1 − g`, read through
  `h0_eq_deg_add_chi_of_subsingleton_hModule_one` and E-i (`classDeg_picClass`).

## Consumption (DAT-C / DAT-B)

At a fibre `p` of a test ring `B`, the full discharge chain runs: (a) the complex-form
`hfib p` criterion `datum_subsingleton_h1_residueField_tensor_iff`
(`Cohomology/GluedSheafFibre.lean`; its term-identification half is the recorded DAT-1
stage (1d-ii) seam), (b) `datumH1Equiv` at the fibre datum over `κ(p)`, then the
present file's (c)+(d) exports at `K := κ(p)` with the fibre class's degree supplied by
the DAT-4 degree seam (`degAt_pic0_mul_pow`: for `λ ∈ pic0`, the fibre degree of
`λ·θ^m` is `m · degAt θ` on the nose).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- **Vanishing transports across the core isomorphism**: `H¹` of the glued sheaf of a
presentation vanishes iff `H¹` of the divisor sheaf of its presentation divisor does. -/
theorem subsingleton_hModule_gluedSheaf_one_iff (P : X.MeromorphicPresentation) :
    Subsingleton (Sheaf.HModule (P.gluedSheaf K) 1) ↔
      Subsingleton
        (Sheaf.HModule (X.divisorSheaf K (presentationDivisor K P)) 1) :=
  (Sheaf.HModule.mapEquiv (MeromorphicPresentation.gluedDivisorSheafIso K P)
    1).toEquiv.subsingleton_congr

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- **`hfib` in the sheaf form the engine consumes** (W6-full × W6-lite): vanishing of
`H¹(𝒪(D))` for any witness divisor `D` of the presented class — e.g. the `(S)`-witness
of `CurveDivisor.exists_picClass_eq` — discharges vanishing of `H¹` of the glued sheaf
of the presentation. This is the sheaf-level form of Kleiman 3.10 (v)⟹(i) at a fibre:
the engine's complex-form `hfib` follows through steps (a)/(b)
(`Cohomology/GluedSheafFibre.lean`). -/
theorem subsingleton_hModule_gluedSheaf_one_of_picClass_eq
    (P : X.MeromorphicPresentation) {D : X.CurveDivisor}
    (h : CurveDivisor.picClass K D = P.picClass)
    (hsub : Subsingleton (Sheaf.HModule (X.divisorSheaf K D) 1)) :
    Subsingleton (Sheaf.HModule (P.gluedSheaf K) 1) := by
  refine (subsingleton_hModule_gluedSheaf_one_iff K P).mpr ?_
  refine subsingleton_hModule_one_of_picClass_eq K ?_ hsub
  rw [CurveDivisor.picClass_presentationDivisor]
  exact h

/-- **The FLV class form on glued sheaves** (the step-(d) vanishing export): for a
finite dominant `π : X ⟶ ℙ¹` and classes `l`, `θ` with `1 ≤ classDeg θ`, the degree-one
cohomology of the glued sheaf of EVERY meromorphic presentation of the class `l · θⁿ`
vanishes for all sufficiently large `n` — FLV on the `(S)`-witness divisor, transported
through the core isomorphism. The per-class bound `n₀` is non-effective. -/
theorem exists_subsingleton_hModule_gluedSheaf_one_of_one_le_classDeg_of_isFinite_toP1
    [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]
    (π : X ⟶ P1 K) [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap K = X ↘ Spec (CommRingCat.of K))
    (l θ : X.CechPic) (hθ : 1 ≤ classDeg K θ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ P : X.MeromorphicPresentation,
      P.picClass = l * θ ^ n →
      Subsingleton (Sheaf.HModule (P.gluedSheaf K) 1) := by
  obtain ⟨n₀, hn₀⟩ :=
    exists_subsingleton_hModule_one_of_one_le_classDeg_of_isFinite_toP1 π hπ l θ hθ
  refine ⟨n₀, fun n hn P hP => ?_⟩
  refine (subsingleton_hModule_gluedSheaf_one_iff K P).mpr ?_
  refine hn₀ n hn (presentationDivisor K P) ?_
  rw [CurveDivisor.picClass_presentationDivisor]
  exact hP

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- **The `rigidEngine_rank` clause** (the step-(d) rank export, Kleiman's
`rank Q = d + 1 − g`): under the vanishing of `H¹`, the global-section count of the
glued sheaf of a presentation is `h⁰(glued(P)) = classDeg P.picClass + χ(𝒪_X)` —
through the core isomorphism, the rank anchor
`h0_eq_deg_add_chi_of_subsingleton_hModule_one`, and E-i (`classDeg_picClass`). With
`χ(𝒪_X) = 1 − g` and the fibre degree `d` of the class from the DAT-4 degree seam this
is the `rank Q = d + 1 − g` normalization of every Stage-B/C engine firing. -/
theorem h0_gluedSheaf_eq_classDeg_add_chi
    [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]
    (P : X.MeromorphicPresentation)
    (hsub : Subsingleton (Sheaf.HModule (P.gluedSheaf K) 1)) :
    (Sheaf.h0 (P.gluedSheaf K) : ℤ) =
      classDeg K P.picClass + Sheaf.chi (X.moduleKSheaf K) := by
  have hdiv : Subsingleton
      (Sheaf.HModule (X.divisorSheaf K (presentationDivisor K P)) 1) :=
    (subsingleton_hModule_gluedSheaf_one_iff K P).mp hsub
  have h0eq : Sheaf.h0 (P.gluedSheaf K) =
      Sheaf.h0 (X.divisorSheaf K (presentationDivisor K P)) :=
    Sheaf.h0_congr (MeromorphicPresentation.gluedDivisorSheafIso K P)
  have hrank :=
    h0_eq_deg_add_chi_of_subsingleton_hModule_one (presentationDivisor K P) hdiv
  have hdeg : classDeg K P.picClass =
      CurveDivisor.deg K (presentationDivisor K P) := by
    rw [← CurveDivisor.picClass_presentationDivisor K P, classDeg_picClass]
  rw [h0eq, hrank, hdeg]

end AlgebraicGeometry
