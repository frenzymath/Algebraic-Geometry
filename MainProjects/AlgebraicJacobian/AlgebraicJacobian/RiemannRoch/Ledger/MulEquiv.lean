/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.DivisorSheaf
import AlgebraicJacobian.RiemannRoch.Ledger.PrincipalDivisor

/-!
# Multiplication isomorphism of divisor sheaves `𝒪(D) ≅ 𝒪(D - div g)`

For the curve bundle `X` — integral, smooth of relative dimension one, quasi-compact and locally
of finite type over a field `K` — a nonzero rational function `g : K(X)ˣ` induces, by
multiplication `s ↦ g · s`, an isomorphism of sheaves of `K`-modules

  `Scheme.mulEquivDivisorSheaf : divisorSheaf K D ≅ divisorSheaf K (D - div g)`

between the divisor sheaf of any Weil divisor `D` and that of `D - div g`. This is the engine of
`deg (div g) = 0`: since `𝒪(D)` and `𝒪(D - div g)` are isomorphic they have equal Euler
characteristics, and `deg` is read off from `χ` via Riemann–Roch.

## The bridge

The single geometric input is `Scheme.ord_val_eq`: the order valuation of `g` at a closed point
`x`, read in `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`, is the divisor bound of the *negated* principal
divisor, `ord_x g = divisorBound (-div g) x`. Everything reduces to it: multiplicativity of the
valuation (`ord_x (g · h) = ord_x g · ord_x h`) and additivity of `divisorBound` turn the pole
bound at `x` for `g · h` under `D - div g` into the pole bound for `h` under `D`, since the
nonzero constant `ord_x g` cancels (`Scheme.mem_boundedSections_mul_iff`).

## Assembly

Sectionwise (`Scheme.mulByUnit`, `Scheme.divisorMulApp`) the map is the restriction of the
`K`-linear automorphism `s ↦ g · s` of `K(X)`; it is bijective on every nonempty open (inverse
`s ↦ g⁻¹ · s`) and a map of subsingletons over the empty open. The components assemble into a
presheaf isomorphism (`Scheme.divisorMulPresheafIso`) and, via the fully faithful
`sheafToPresheaf`, into the sheaf isomorphism.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  (g : X.functionFieldˣ) (D : X.CurveDivisor)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- **Raw bridge.** The order valuation of a unit `g` at a closed point `x` is the coercion of
the inverse of the classical `ℤ`-order `ordZ f hx g`, since `ordZ` was defined by inverting the
units-extraction of the mathlib valuation `Scheme.ord`. -/
theorem ord_val_eq_ordZ {x : X} (hx : x ≠ genericPoint X) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (g : X.functionField)
      = ((Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx g)⁻¹ : Multiplicative ℤ) := by
  rw [Scheme.ordZ]
  simp only [MonoidHom.comp_apply, invMonoidHom_apply, inv_inv, MulEquiv.coe_toMonoidHom,
    WithZero.coe_unitsWithZeroEquiv_eq_units_val, Units.coe_map]
  rfl

/-- **Bridging lemma.** The order valuation of `g` at a closed point `x`, read in `ℤᵐ⁰`, is the
divisor bound of the *negated* principal divisor `-div(g)`: a pole of order `n` (`div(g) x = -n`)
contributes valuation `ofAdd n`, matching the classical sign convention (uniformizer ↦ order `+1`,
valuation `ofAdd (-1)`). This is the single geometric input; the whole sheaf isomorphism reduces
to it. -/
theorem ord_val_eq {x : X} (hx : x ≠ genericPoint X) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (g : X.functionField)
      = divisorBound (- Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) hx := by
  rw [ord_val_eq_ordZ, divisorBound]
  congr 1

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- The order valuation of a unit `g` at a closed point is nonzero (units of a field are
nonzero, and the valuation of a nonzero element is nonzero). -/
theorem ord_val_ne_zero {x : X} (hx : x ≠ genericPoint X) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (g : X.functionField) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr (Units.ne_zero g)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- The order valuation of a unit `g` at a closed point is positive in `ℤᵐ⁰`. -/
theorem ord_val_pos {x : X} (hx : x ≠ genericPoint X) :
    0 < Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (g : X.functionField) :=
  zero_lt_iff.mpr (ord_val_ne_zero K g hx)

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
/-- The divisor bound turns divisor addition into multiplication in `ℤᵐ⁰`: `divisorBound` is the
composite `ofAdd`-coercion of the (additive) coefficient at `x`, hence a monoid homomorphism. -/
theorem divisorBound_add (D₁ D₂ : X.CurveDivisor) {x : X} (hx : x ≠ genericPoint X) :
    divisorBound (D₁ + D₂) hx = divisorBound D₁ hx * divisorBound D₂ hx := by
  simp only [divisorBound, ← WithZero.coe_mul, ← ofAdd_add]
  congr 2

/-- **Bound-shift at a point.** The valuation bound imposed by `D - div(g)` factors as the
valuation of `g` times the bound imposed by `D`: `divisorBound (D - div g)` equals `v_x(g)` times
`divisorBound D` in `ℤᵐ⁰`, from the bridging lemma and additivity of `divisorBound`. -/
theorem divisorBound_sub_divOf {x : X} (hx : x ≠ genericPoint X) :
    divisorBound (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) hx
      = Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (g : X.functionField) * divisorBound D hx := by
  rw [sub_eq_add_neg, divisorBound_add, ← ord_val_eq, mul_comm]

/-- **The abstract bound-shift.** Multiplication by the unit `g` shifts the pole bound from `D` to
`D - div(g)`: at every closed point `z ∈ U` the nonzero constant valuation `v_z(g)` cancels, so
`g · h` lies in `𝒪(D - div g)` over `U` exactly when `h` lies in `𝒪(D)` over `U`. This single
lemma is the engine of the sheaf isomorphism. -/
theorem mem_boundedSections_mul_iff {U : X.Opens} (h : X.functionField) :
    (g : X.functionField) * h
        ∈ boundedSections K (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) U
      ↔ h ∈ boundedSections K D U := by
  simp only [mem_boundedSections]
  refine ⟨fun H z hz hzU => ?_, fun H z hz hzU => ?_⟩
  · have key := H z hz hzU
    rw [map_mul, divisorBound_sub_divOf] at key
    exact (mul_le_mul_iff_of_pos_left (ord_val_pos K g hz)).mp key
  · rw [map_mul, divisorBound_sub_divOf]
    exact (mul_le_mul_iff_of_pos_left (ord_val_pos K g hz)).mpr (H z hz hzU)

/-- **Multiplication by the unit `g` on the function field**, as a `K`-linear automorphism of
`K(X)`: `s ↦ g · s`, with inverse `s ↦ g⁻¹ · s`. `K`-linearity holds because the `K`-action is
multiplication by the image of `K` in `K(X)`, which commutes with multiplication by `g`. -/
noncomputable def mulByUnit : X.functionField ≃ₗ[K] X.functionField where
  toFun s := (g : X.functionField) * s
  map_add' a b := mul_add _ _ _
  map_smul' r s := by
    simp only [RingHom.id_apply, functionFieldOverModule_smul_def]
    exact mul_left_comm _ _ _
  invFun s := (↑g⁻¹ : X.functionField) * s
  left_inv s := by
    change (↑g⁻¹ : X.functionField) * ((g : X.functionField) * s) = s
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv s := by
    change (g : X.functionField) * ((↑g⁻¹ : X.functionField) * s) = s
    rw [← mul_assoc, Units.mul_inv, one_mul]

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] in
@[simp] lemma mulByUnit_apply (s : X.functionField) :
    mulByUnit K g s = (g : X.functionField) * s := rfl

/-- **The section-wise `K`-linear map `𝒪(D)(U) → 𝒪(D - div g)(U)`** for a nonempty open `U`:
multiplication by `g`. Well-defined by the bound-shift `mem_boundedSections_mul_iff`. -/
noncomputable def divisorMulApp {U : X.Opens} (hU : (U : Set X).Nonempty) :
    divisorSections K D U →ₗ[K]
      divisorSections K (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) U :=
  LinearMap.codRestrict _ ((mulByUnit K g).toLinearMap ∘ₗ (divisorSections K D U).subtype)
    (fun s => by
      rw [divisorSections_of_nonempty K hU]
      have hs : (s : X.functionField) ∈ boundedSections K D U := by
        rw [← divisorSections_of_nonempty K hU]; exact s.2
      exact (mem_boundedSections_mul_iff K g D (s : X.functionField)).mpr hs)

@[simp] lemma divisorMulApp_coe {U : X.Opens} (hU : (U : Set X).Nonempty)
    (s : divisorSections K D U) :
    ((divisorMulApp K g D hU s :
        divisorSections K (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) U) : X.functionField)
      = (g : X.functionField) * (s : X.functionField) := rfl

open Classical in
/-- **The section-wise map for all opens**: multiplication by `g` when `U` is nonempty, the zero
map into the terminal sections when `U` is empty. -/
noncomputable def divisorMulPresheafApp (U : X.Opens) :
    divisorSections K D U →ₗ[K]
      divisorSections K (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) U :=
  if hU : (U : Set X).Nonempty then divisorMulApp K g D hU else 0

lemma divisorMulPresheafApp_of_nonempty {U : X.Opens} (hU : (U : Set X).Nonempty) :
    divisorMulPresheafApp K g D U = divisorMulApp K g D hU :=
  dif_pos hU

/-- The underlying rational function of the section-wise map over a nonempty open is `g · s`. -/
lemma divisorMulPresheafApp_coe_of_nonempty {U : X.Opens} (hU : (U : Set X).Nonempty)
    (s : divisorSections K D U) :
    ((divisorMulPresheafApp K g D U s :
        divisorSections K (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) U) : X.functionField)
      = (g : X.functionField) * (s : X.functionField) := by
  rw [divisorMulPresheafApp_of_nonempty K g D hU, divisorMulApp_coe]

/-- The section-wise map is bijective on every open: an isomorphism (multiplication by the unit
`g`, inverse multiplication by `g⁻¹`) on nonempty opens, and a map of subsingletons on the empty
open. -/
lemma divisorMulPresheafApp_bijective (U : X.Opens) :
    Function.Bijective (divisorMulPresheafApp K g D U) := by
  by_cases hU : (U : Set X).Nonempty
  · rw [divisorMulPresheafApp_of_nonempty K g D hU]
    refine ⟨fun a b hab => ?_, fun t => ?_⟩
    · apply Subtype.ext
      have hval : (g : X.functionField) * (a : X.functionField)
          = (g : X.functionField) * (b : X.functionField) := by
        have := congrArg (Subtype.val) hab
        rwa [divisorMulApp_coe, divisorMulApp_coe] at this
      exact mul_left_cancel₀ (Units.ne_zero g) hval
    · have htmem : (t : X.functionField)
          ∈ boundedSections K (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) U := by
        rw [← divisorSections_of_nonempty K hU]; exact t.2
      have hpre : (↑g⁻¹ : X.functionField) * (t : X.functionField) ∈ boundedSections K D U := by
        rw [← mem_boundedSections_mul_iff K g D, ← mul_assoc, Units.mul_inv, one_mul]
        exact htmem
      refine ⟨⟨(↑g⁻¹ : X.functionField) * (t : X.functionField),
        by rw [divisorSections_of_nonempty K hU]; exact hpre⟩, ?_⟩
      apply Subtype.ext
      rw [divisorMulApp_coe, ← mul_assoc, Units.mul_inv, one_mul]
  · haveI := divisorSections_subsingleton_of_empty K (D := D) hU
    haveI := divisorSections_subsingleton_of_empty K
      (D := D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) hU
    exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- **The presheaf morphism `𝒪(D) → 𝒪(D - div g)`** of `K`-modules, section-wise `s ↦ g · s`. -/
noncomputable def divisorMulPresheaf :
    divisorPresheaf K D ⟶
      divisorPresheaf K (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) where
  app U := ModuleCat.ofHom (divisorMulPresheafApp K g D U.unop)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    by_cases hV : (V.unop : Set X).Nonempty
    · have hU : (U.unop : Set X).Nonempty := hV.mono (leOfHom i.unop)
      apply Subtype.ext
      change ((divisorMulPresheafApp K g D (unop V) (divisorSectionsRes K D (leOfHom i.unop) s) :
            divisorSections K (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) (unop V)) :
          X.functionField)
        = ((divisorSectionsRes K (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g)
            (leOfHom i.unop) (divisorMulPresheafApp K g D (unop U) s) :
            divisorSections K (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) (unop V)) :
          X.functionField)
      rw [divisorMulPresheafApp_coe_of_nonempty K g D hV,
        divisorSectionsRes_coe K (leOfHom i.unop) hV,
        divisorSectionsRes_coe K (leOfHom i.unop) hV,
        divisorMulPresheafApp_coe_of_nonempty K g D hU]
    · haveI := divisorPresheaf_obj_subsingleton K
        (D := D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) (W := V.unop) hV
      exact Subsingleton.elim _ _

/-- Every component of `divisorMulPresheaf` is an isomorphism (it is bijective). -/
lemma divisorMulPresheaf_app_isIso (U : (X.Opens)ᵒᵖ) :
    IsIso ((divisorMulPresheaf K g D).app U) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact divisorMulPresheafApp_bijective K g D U.unop

/-- **The presheaf isomorphism `𝒪(D) ≅ 𝒪(D - div g)`** of `K`-modules, multiplication by `g`. -/
noncomputable def divisorMulPresheafIso :
    divisorPresheaf K D ≅
      divisorPresheaf K (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) :=
  NatIso.ofComponents
    (fun U => by
      haveI := divisorMulPresheaf_app_isIso K g D U
      exact asIso ((divisorMulPresheaf K g D).app U))
    (fun i => (divisorMulPresheaf K g D).naturality i)

/-- **The isomorphism of divisor sheaves `𝒪(D) ≅ 𝒪(D - div g)`** of `K`-modules, given
section-wise by multiplication by the rational function `g` (with inverse multiplication by
`g⁻¹`). Combined with the additivity of `divOf`, this is the engine behind `deg (div g) = 0`: it
identifies `𝒪(D)` and `𝒪(D - div g)`, forcing their Euler characteristics to agree. -/
noncomputable def mulEquivDivisorSheaf :
    divisorSheaf K D ≅ divisorSheaf K (D - Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (divisorMulPresheafIso K g D)

/-- **Behaviour of the multiplication isomorphism on section values.** Over a nonempty open the
forward map of `divisorMulPresheaf` sends a section to `g` times its underlying rational
function. -/
theorem divisorVal_mulEquiv {U : X.Opens} (hU : (U : Set X).Nonempty)
    (s : (divisorPresheaf K D).obj (op U)) :
    divisorVal K ((divisorMulPresheaf K g D).app (op U) s)
      = (g : X.functionField) * divisorVal K s :=
  divisorMulPresheafApp_coe_of_nonempty K g D hU s

end Scheme

end AlgebraicGeometry
