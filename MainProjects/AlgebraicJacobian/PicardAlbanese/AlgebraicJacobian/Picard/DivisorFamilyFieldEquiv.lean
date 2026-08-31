/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyFieldDegree
import AlgebraicJacobian.RiemannRoch.DivisorSheafZero

/-!
# The field-dictionary endgame: the DivEq converse, forward injectivity, the equiv reduction
(`informal/spec-dd-1.md` §3 (f), the DD-1c inverse-law adjudication)

The forward map `divFamDivisor` (`AlgebraicJacobian.Picard.DivisorFamilyField`) sends a
certified divisor family over the field `K` to its Weil divisor, and is `DivEq`-invariant
(`Scheme.presentationDivisor_eq_of_divEq`). This file lands the **converse** and the
**injectivity** it powers, and packages the **equiv reduction** — the exact assembly of the
frozen `divFamFieldEquiv` from the two remaining, precisely-named gaps.

* `Scheme.divEq_of_presentationDivisor_eq` — the **converse of DivEq-invariance**: two
  local-equation systems on the curve with the *same* Weil divisor are divisor-equal. On the
  common refinement of the two covers the ratio of the anchor equations is a unit at every
  closed point (equal orders read the equal divisor coefficient off any piece,
  `MeromorphicPresentation.ordZ_elem_eq` + `coeffAt_presentationDivisor`), hence — being an
  `𝒪(0)`-section together with its inverse (`exists_section_germ_eq`) — a genuine unit
  section that rescales one system to the other. Together with the landed
  `presentationDivisor_eq_of_divEq` this is the characterization
  `DivEq d₁ d₂ ↔ presentationDivisor d₁ = presentationDivisor d₂`.

* `divFamDivisor_injective` — the **forward map is injective**: two families with equal
  divisor are `DivEq`, hence equal in the setoid `DivFam`. This is *unconditional* (no
  Mayer–Vietoris, no backward construction); it is the injective half of `divFamFieldEquiv`,
  and it *is* the second inverse law `divFamOfDivisor (divFamDivisor F) = F` once the
  backward map exists (both sides then present the same divisor).

* `divFamFieldEquivOfDegOfSurj` — the **equiv reduction**: given the two remaining gaps —
  `hdeg` (the general colength↔degree identity `deg (divFamDivisor F) = n` for an *arbitrary*
  certified family, the honest Mayer–Vietoris wall) and `hsurj` (backward realization: every
  effective degree-`n` divisor is the divisor of some certified family, discharged over `K`
  by the support-separated construction whose certificate rank is `deg = n` *for free* via
  `deg_divFamDivisor_of_separated`, no general MV) — the equiv
  `DivFam C K π n ≃ {D // 0 ≤ D ∧ deg K D = n}` drops out (injectivity is already free).

## Adjudication verdict (for the DD-R spec that consumes this dictionary)

The full `divFamFieldEquiv` needs **exactly two** further inputs, and neither is the second
inverse law (that is landed here as `divFamDivisor_injective`):

1. `hdeg` — LANDED (2026-07-18, I-0230): `deg_divFamDivisor` in
   `AlgebraicJacobian.Picard.DivisorFamilyFieldCRT` proves the forward degree
   unconditionally; the glued colength is adaptation-independent
   (`DivisorAdaptation.deg_presentationDivisor`), dissolving the I-0179 MV wall this
   paragraph used to describe.
2. `hsurj` — the backward realization (a support-separated certified family per effective
   degree-`n` divisor, via `PointPresentation.pointEquations` products). Large but **does
   not** need general MV: its certificate's `finrank W = deg D = n` is the *separated*
   identity applied to the constructed adaptation with `deg D = n` an input hypothesis.

**One-sidedness for DD-R.** If P-fib supplies a *unique* effective degree-`n` divisor `D`,
then `hsurj`'s family for `D` feeds the dictionary and the one landed law
`divFamDivisor (family) = D` round-trips through the divisor; and because `divFamDivisor` is
mono (`divFamDivisor_injective`) — so its section is determined — the second inverse law is
not separately required. DD-R can therefore consume the one-sided dictionary (backward map +
`divFamDivisor_injective`) and need **not** fund the general-MV brick, provided ε (DD-4) is
mono so family equality can be tested after ε.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **The converse of DivEq-invariance** (`informal/spec-dd-1.md` §3 (f), the second
inverse-law core): two local-equation systems on the curve `X` with the *same* Weil divisor
are divisor-equal. On the common refinement `d₁.cover ⊓ d₂.cover`, at each point `x`, the
ratio `r = elem₁ x / elem₂ x` of the anchor equations has order `1` at every closed point of
the overlap — the equal divisor coefficient read off either piece
(`MeromorphicPresentation.ordZ_elem_eq`, `coeffAt_presentationDivisor`) — so both `r` and
`r⁻¹` are `𝒪(0)`-sections (`exists_section_germ_eq`), i.e. `r` is a unit section rescaling
`d₂.eqn x` to `d₁.eqn x`. The converse of `Scheme.presentationDivisor_eq_of_divEq`. -/
theorem divEq_of_presentationDivisor_eq {d₁ d₂ : X.LocalEquations}
    (h : presentationDivisor K d₁.presentation = presentationDivisor K d₂.presentation) :
    LocalEquations.DivEq d₁ d₂ := by
  refine ⟨d₁.cover ⊓ d₂.cover, inf_le_left, inf_le_right, fun x => ?_⟩
  have hηW : genericPoint X ∈ d₁.cover.opens x ⊓ d₂.cover.opens x :=
    ⟨d₁.cover.genericPoint_mem_opens x, d₂.cover.genericPoint_mem_opens x⟩
  have hWne : ((d₁.cover.opens x ⊓ d₂.cover.opens x : X.Opens) : Set X).Nonempty :=
    ⟨genericPoint X, hηW⟩
  simp only [PointedCover.inf_opens]
  set r : X.functionFieldˣ :=
    d₁.presentation.elem x * (d₂.presentation.elem x)⁻¹ with hr
  -- `r` is a stalk-unit at every closed point of the overlap
  have hru : ∀ (z : X) (hz : z ≠ genericPoint X),
      z ∈ d₁.cover.opens x ⊓ d₂.cover.opens x →
      Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz r = 1 := by
    intro z hz hzW
    have e1 := d₁.presentation.ordZ_elem_eq K hz (y := x) hzW.1
    have e2 := d₂.presentation.ordZ_elem_eq K hz (y := x) hzW.2
    have hcoeff := congrArg (coeffAt hz) h
    rw [coeffAt_presentationDivisor, coeffAt_presentationDivisor] at hcoeff
    have hzz : Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (d₁.presentation.elem z)
        = Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (d₂.presentation.elem z) :=
      Multiplicative.toAdd.injective hcoeff
    have hkey : Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (d₁.presentation.elem x)
        = Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz (d₂.presentation.elem x) :=
      e1.trans (hzz.trans e2.symm)
    rw [hr, map_mul, map_inv, hkey, mul_inv_cancel]
  -- both `r` and `r⁻¹` are `𝒪(0)`-sections over the overlap
  have hmem : ∀ (g : X.functionFieldˣ),
      (∀ (z : X) (hz : z ≠ genericPoint X), z ∈ d₁.cover.opens x ⊓ d₂.cover.opens x →
        Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz g = 1) →
      (g : X.functionField) ∈ divisorSections K 0 (d₁.cover.opens x ⊓ d₂.cover.opens x) := by
    intro g hg
    rw [mem_divisorSections_of_nonempty K hWne]
    intro z hz hzW
    rw [divisorBound_zero]
    exact le_of_eq
      ((Scheme.ordZ_eq_one_iff (X ↘ Spec (CommRingCat.of K)) hz g).mp (hg z hz hzW))
  have hrinv : ∀ (z : X) (hz : z ≠ genericPoint X),
      z ∈ d₁.cover.opens x ⊓ d₂.cover.opens x →
      Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hz r⁻¹ = 1 := by
    intro z hz hzW
    rw [map_inv, hru z hz hzW, inv_one]
  obtain ⟨s, hs⟩ := exists_section_germ_eq K hηW (hmem r hru)
  obtain ⟨s', hs'⟩ := exists_section_germ_eq K hηW (hmem r⁻¹ hrinv)
  -- `s` and `s'` are inverse sections, giving the rescaling unit
  have hss' : s * s' = 1 :=
    germ_injective_of_isIntegral X (genericPoint X) hηW (by
      rw [map_mul, hs, hs', map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hs's : s' * s = 1 := by rw [mul_comm]; exact hss'
  have hu : (↑(⟨s, s', hss', hs's⟩ : Γ(X, d₁.cover.opens x ⊓ d₂.cover.opens x)ˣ) :
      Γ(X, d₁.cover.opens x ⊓ d₂.cover.opens x)) = s := rfl
  refine ⟨⟨s, s', hss', hs's⟩, ?_⟩
  -- the rescaling equation, verified at `η` by germ injectivity
  refine germ_injective_of_isIntegral X (genericPoint X) hηW ?_
  have hL : (X.presheaf.germ (d₁.cover.opens x ⊓ d₂.cover.opens x) (genericPoint X) hηW).hom
        ((X.presheaf.map (homOfLE inf_le_left).op).hom (d₁.eqn x))
      = (d₁.presentation.elem x : X.functionField) := by
    rw [X.presheaf.germ_res_apply]; exact (d₁.presentation_elem_val x).symm
  have hR : (X.presheaf.germ (d₁.cover.opens x ⊓ d₂.cover.opens x) (genericPoint X) hηW).hom
        ((X.presheaf.map (homOfLE inf_le_right).op).hom (d₂.eqn x))
      = (d₂.presentation.elem x : X.functionField) := by
    rw [X.presheaf.germ_res_apply]; exact (d₂.presentation_elem_val x).symm
  rw [map_mul, hu, hs, hL, hR, hr, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc,
    inv_mul_cancel₀ (d₂.presentation.elem x).ne_zero, mul_one]

end Scheme

/-! ## Forward injectivity and the equiv reduction on `DivFam` over a field -/

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {K : Type u} [Field K] [Algebra k K]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
variable {n : ℕ}

/-- **The forward map `divFamDivisor` is injective** (`informal/spec-dd-1.md` §3 (f)): two
divisor families over the field `K` with the same Weil divisor are `DivEq`
(`Scheme.divEq_of_presentationDivisor_eq`), hence equal in the setoid `DivFam`.

This is *unconditional* — no Mayer–Vietoris degree identity, no backward construction — and
it is the injective half of the field dictionary `divFamFieldEquiv`. It is also the second
inverse law `divFamOfDivisor (divFamDivisor F) = F` once the backward map exists: both sides
present the same divisor `divFamDivisor F`, so injectivity forces them equal. -/
theorem divFamDivisor_injective :
    Function.Injective (divFamDivisor : DivFam C K π n → (relCurve C K).CurveDivisor) := by
  refine fun F G => Quotient.inductionOn₂ F G (fun F' G' hFG => ?_)
  exact Quotient.sound (Scheme.divEq_of_presentationDivisor_eq K
    (d₁ := F'.eqns) (d₂ := G'.eqns) hFG)

/-- **The field dictionary, assembled from the two remaining named gaps**
(`informal/spec-dd-1.md` §3 (f), the frozen `divFamFieldEquiv`). Given

* `hdeg` — the **general** colength↔degree identity `deg (divFamDivisor F) = n` for an
  *arbitrary* certified family (the honest Mayer–Vietoris wall of I-0179; needed even to land
  the forward map in the degree-`n` subtype), and
* `hsurj` — **backward realization**: every effective degree-`n` divisor is the divisor of
  some family (discharged over `K` by the `PointPresentation.pointEquations`-product
  support-separated construction, whose certificate rank is `deg D = n` *for free* via
  `deg_divFamDivisor_of_separated` — this direction needs no general MV),

the field dictionary `DivFam C K π n ≃ {D // 0 ≤ D ∧ deg K D = n}` drops out: injectivity is
already free (`divFamDivisor_injective`), effectivity is landed (`zero_le_divFamDivisor`).

The two hypotheses are exactly the DD-1c residue: `hsurj` is a fundable construction, `hdeg`
is the sole general-MV obligation. See the module docstring for the DD-R consumption note. -/
noncomputable def divFamFieldEquivOfDegOfSurj
    (hdeg : ∀ F : DivFam C K π n,
      Scheme.CurveDivisor.deg K (divFamDivisor F) = (n : ℤ))
    (hsurj : ∀ D : (relCurve C K).CurveDivisor, 0 ≤ D →
      Scheme.CurveDivisor.deg K D = (n : ℤ) → ∃ F : DivFam C K π n, divFamDivisor F = D) :
    DivFam C K π n
      ≃ {D : (relCurve C K).CurveDivisor // 0 ≤ D ∧ Scheme.CurveDivisor.deg K D = (n : ℤ)} :=
  Equiv.ofBijective
    (fun F => ⟨divFamDivisor F, zero_le_divFamDivisor F, hdeg F⟩)
    ⟨fun F G hFG => divFamDivisor_injective (Subtype.ext_iff.mp hFG),
     fun D => by
       obtain ⟨F, hF⟩ := hsurj D.1 D.2.1 D.2.2
       exact ⟨F, Subtype.ext hF⟩⟩

end AlgebraicGeometry
