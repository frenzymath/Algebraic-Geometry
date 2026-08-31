/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.SectionSpaces
import AlgebraicJacobian.Picard.EntriesIdeal

/-!
# DD-4 (Task 3) — the multiplication `μ` on divisor sections and its base change

The multiplication data of the DAT-D carve `(♦)` (`informal/dat-d-worksheet.md` §2.3, §3.1):
the `K`-bilinear multiplication of divisor sections `H⁰(𝒪(A)) × H⁰(𝒪(B)) → H⁰(𝒪(A + B))`
(the pole-bound product rule `mul_mem_divisorSections_top`), packaged as a linear map on the
tensor product, together with its extension of scalars to a test ring `R`.

At the DAT-D windows `A = s·F`, `B = M·F` this is the map `μ : H_s ⊗ H_M → H_{M+s}` whose
`R`-base change `μ ⊗ R` is the carve arrow `H_s ⊗ K → H_{M+s} ⊗ R` of `(♦)`: the carve is
literally *the composite `μ ⊗ R` restricted to `K`, followed by the projection to
`(H_{M+s} ⊗ R)/K′`, vanishes* — a single `R`-linear-map-is-zero condition, exactly the shape
`AlgebraicGeometry.Grassmannian.baseChange_eq_zero_iff` consumes through its `entriesIdeal`.

* `AlgebraicGeometry.sectionMulBilin` — the `K`-bilinear product
  `H⁰(𝒪(A)) →ₗ H⁰(𝒪(B)) →ₗ H⁰(𝒪(A + B))`.
* `AlgebraicGeometry.sectionMul` — its uncurrying `H⁰(𝒪(A)) ⊗[K] H⁰(𝒪(B)) →ₗ H⁰(𝒪(A + B))`.
* `AlgebraicGeometry.relSectionMul` — the extension of scalars `μ ⊗ R`, an `R`-linear map
  `R ⊗[K] (H⁰(𝒪(A)) ⊗[K] H⁰(𝒪(B))) →ₗ[R] R ⊗[K] H⁰(𝒪(A + B))`, the relative multiplication
  the carve is cut from.
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

section Mul

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]

/-- **The multiplication of divisor sections**, as a `K`-bilinear map
`H⁰(𝒪(A)) →ₗ H⁰(𝒪(B)) →ₗ H⁰(𝒪(A + B))`: on representatives `(f, h) ↦ f · h`, landing in
`H⁰(𝒪(A + B))` by the pole-bound product rule `mul_mem_divisorSections_top`. This is the
field-level `μ` of the DAT-D carve. -/
noncomputable def sectionMulBilin (A B : X.CurveDivisor) :
    ↥(divisorSections K A ⊤) →ₗ[K] ↥(divisorSections K B ⊤) →ₗ[K]
      ↥(divisorSections K (A + B) ⊤) :=
  LinearMap.mk₂ K
    (fun f h => ⟨f.val * h.val, mul_mem_divisorSections_top K f.property h.property⟩)
    (fun f₁ f₂ h => Subtype.ext (by simp only [Submodule.coe_add]; ring))
    (fun c f h => Subtype.ext (by
      simp only [SetLike.val_smul, Scheme.functionFieldOverModule_smul_def]
      ring))
    (fun f h₁ h₂ => Subtype.ext (by simp only [Submodule.coe_add]; ring))
    (fun c f h => Subtype.ext (by
      simp only [SetLike.val_smul, Scheme.functionFieldOverModule_smul_def]
      ring))

@[simp]
lemma sectionMulBilin_apply_coe (A B : X.CurveDivisor)
    (f : ↥(divisorSections K A ⊤)) (h : ↥(divisorSections K B ⊤)) :
    ((sectionMulBilin K A B f h : ↥(divisorSections K (A + B) ⊤)) : X.functionField)
      = f.val * h.val :=
  rfl

/-- **The multiplication `μ` on the tensor product**: the uncurried section product
`H⁰(𝒪(A)) ⊗[K] H⁰(𝒪(B)) →ₗ[K] H⁰(𝒪(A + B))`. -/
noncomputable def sectionMul (A B : X.CurveDivisor) :
    ↥(divisorSections K A ⊤) ⊗[K] ↥(divisorSections K B ⊤) →ₗ[K]
      ↥(divisorSections K (A + B) ⊤) :=
  TensorProduct.lift (sectionMulBilin K A B)

@[simp]
lemma sectionMul_tmul (A B : X.CurveDivisor)
    (f : ↥(divisorSections K A ⊤)) (h : ↥(divisorSections K B ⊤)) :
    sectionMul K A B (f ⊗ₜ h) = sectionMulBilin K A B f h :=
  TensorProduct.lift.tmul _ _

variable (R : Type u) [CommRing R] [Algebra K R]

/-- **The relative multiplication `μ ⊗ R`** (worksheet §3.1, the carve arrow): the
extension of scalars of the section product `sectionMul` to the test ring `R`, an
`R`-linear map
`R ⊗[K] (H⁰(𝒪(A)) ⊗[K] H⁰(𝒪(B))) →ₗ[R] R ⊗[K] H⁰(𝒪(A + B))`.

For the carve `(♦)` this is restricted to `H_s ⊗ K` (a Grassmannian point `K`) and composed
with the projection to `(H_{M+s} ⊗ R)/K′`; the resulting `R`-linear map's vanishing after a
further base change `R → S` is exactly `Grassmannian.baseChange_eq_zero_iff`, i.e. the closed
condition cutting `Div^g` out of the Grassmannian pair. -/
noncomputable def relSectionMul (A B : X.CurveDivisor) :
    R ⊗[K] (↥(divisorSections K A ⊤) ⊗[K] ↥(divisorSections K B ⊤)) →ₗ[R]
      R ⊗[K] ↥(divisorSections K (A + B) ⊤) :=
  LinearMap.baseChange R (sectionMul K A B)

@[simp]
lemma relSectionMul_tmul (A B : X.CurveDivisor) (r : R)
    (x : ↥(divisorSections K A ⊤) ⊗[K] ↥(divisorSections K B ⊤)) :
    relSectionMul K R A B (r ⊗ₜ x) = r ⊗ₜ sectionMul K A B x :=
  LinearMap.baseChange_tmul _ _ _

/-! ## The carve `(♦)` at a section, matching `baseChange_eq_zero_iff` -/

/-- **Right multiplication by a section `a ∈ H⁰(𝒪(A))`, relatively**: the `R`-linear map
`R ⊗ H⁰(𝒪(B)) →ₗ[R] R ⊗ H⁰(𝒪(A + B))` given by the base change of `sectionMulBilin K A B a`
(`s ↦ a · s`). This is the field-level `μ_a` extended to the test ring `R`. -/
noncomputable def relSectionMulRight (A B : X.CurveDivisor)
    (a : ↥(divisorSections K A ⊤)) :
    R ⊗[K] ↥(divisorSections K B ⊤) →ₗ[R] R ⊗[K] ↥(divisorSections K (A + B) ⊤) :=
  LinearMap.baseChange R (sectionMulBilin K A B a)

@[simp]
lemma relSectionMulRight_tmul (A B : X.CurveDivisor) (a : ↥(divisorSections K A ⊤))
    (r : R) (s : ↥(divisorSections K B ⊤)) :
    relSectionMulRight K R A B a (r ⊗ₜ s) = r ⊗ₜ sectionMulBilin K A B a s :=
  LinearMap.baseChange_tmul _ _ _

/-- **The carve arrow `(♦)` at a section `a`** (worksheet §3.1): given a Grassmannian point
`Km ⊆ R ⊗ H⁰(𝒪(B))` (the `B`-window submodule) and `K' ⊆ R ⊗ H⁰(𝒪(A + B))` (the
`(A+B)`-window submodule), the composite

`Km ↪ R ⊗ H⁰(𝒪(B)) →^{a·} R ⊗ H⁰(𝒪(A + B)) ↠ (R ⊗ H⁰(𝒪(A + B))) ⧸ K′`.

The single closed condition of the carve is that this map is zero, for `a` ranging over
`H⁰(𝒪(A))` (equivalently a `K`-spanning set); the `A = s·F`, `B = M·F` instance is exactly
the `H_s · K ⊆ K′` carve `(♦)` inside the Grassmannian pair. -/
noncomputable def carveArrow (A B : X.CurveDivisor) (a : ↥(divisorSections K A ⊤))
    (Km : Submodule R (R ⊗[K] ↥(divisorSections K B ⊤)))
    (K' : Submodule R (R ⊗[K] ↥(divisorSections K (A + B) ⊤))) :
    ↥Km →ₗ[R] (R ⊗[K] ↥(divisorSections K (A + B) ⊤)) ⧸ K' :=
  K'.mkQ ∘ₗ (relSectionMulRight K R A B a) ∘ₗ Km.subtype

/-- **The carve `(♦)` is literally `baseChange_eq_zero_iff`**: for a test-ring change
`R → S`, the carve arrow at `a` vanishes after base change iff `S` kills its entries ideal.
This is the closed (equalizer-gift) shape the DAT-D carve is cut by — no open condition, the
`Grassmannian.entriesIdeal`/`spec_of_surjective` gift applies verbatim. -/
theorem carveArrow_baseChange_eq_zero_iff (A B : X.CurveDivisor)
    (a : ↥(divisorSections K A ⊤))
    (Km : Submodule R (R ⊗[K] ↥(divisorSections K B ⊤)))
    (K' : Submodule R (R ⊗[K] ↥(divisorSections K (A + B) ⊤)))
    [Module.Finite R ↥Km]
    [Module.Finite R ((R ⊗[K] ↥(divisorSections K (A + B) ⊤)) ⧸ K')]
    [Module.Projective R ((R ⊗[K] ↥(divisorSections K (A + B) ⊤)) ⧸ K')]
    (S : Type u) [CommRing S] [Algebra R S] :
    LinearMap.baseChange S (carveArrow K R A B a Km K') = 0 ↔
      Grassmannian.entriesIdeal (carveArrow K R A B a Km K')
        ≤ RingHom.ker (algebraMap R S) :=
  Grassmannian.baseChange_eq_zero_iff (carveArrow K R A B a Km K') S

end Mul

end AlgebraicGeometry
