/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FibrewiseRegular
import AlgebraicJacobian.Cohomology.GluedSheafEngine
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Sections to divisors — the DAT-A2 germ-regularity bridge

The geometry layer of the `lm:ctn` (iii)⟹(i) slicing criterion
(`informal/spec-dat-a.md` §2; core: `AlgebraicJacobian.Picard.FibrewiseRegular`):

* **(α) germ transport** — `IsAffineOpen.germ_mem_nonZeroDivisors`: a nonzerodivisor of
  the section ring of an affine open has nonzerodivisor germs at all of its points
  (stalks are localizations of the affine section ring; regularity passes to
  localizations). This is also the "germ-level regularity by localization-exactness"
  consumption surface of DD-1a (dat-d-worksheet §1.2).
* **(the field-level slice case, Kleiman tex 2013–2022)** —
  `Scheme.germ_mem_nonZeroDivisors_of_ne_zero`: on an **integral** scheme a nonzero
  section has nonzerodivisor germs everywhere on its open. This is the named lemma
  DAT-C discharges at field-level fibres ("nonzero on the integral fibre ⟹ regular").
* **(β) piece flatness** — `flat_sections_basicOpen`: over `Spec k`, if the affine
  chart ring is `k`-flat (`Scheme.overModule`) then so is every basic-open piece ring
  (tower `k → Γ(V) → Γ(D(h))` through `IsAffineOpen.isLocalization_basicOpen`).
* **(γ) the generic A2 bridge** — `mem_nonZeroDivisors_of_fibrewise_regular` (+ germ
  form): over a Noetherian `k`, a section of a basic-open piece of a `k`-flat affine
  chart that is **fibrewise regular** (multiplication injective on every residue-field
  fibre of the piece ring, in `Scheme.mulSectionEnd`/`rTensor` form) is a nonzerodivisor
  with nonzerodivisor germs. The tensor-RING form of the fibre hypothesis converts
  through `injective_rTensor_mulSectionEnd_of_tmul_mem_nonZeroDivisors`.
* **(δ) A2 on the pinned datum** — for `D : BasicOpenCocycleDatum C B π` and a global
  section `s` of the DAT-1 glued sheaf, each component `D.component s j` (the section on
  the trivializing basic-open piece `D(h_j)`) is a nonzerodivisor with nonzerodivisor
  germs, given its fibrewise regularity (`component_mem_nonZeroDivisors`,
  `germ_component_mem_nonZeroDivisors`). These are exactly the `regular` inputs of
  `Scheme.LocalEquations` — the LocalEquations construction and the class law are in
  `AlgebraicJacobian.Picard.SectionsToDivisorsClass`.

The fibrewise hypothesis is deliberately the *piece-ring residue-fibre* spelling
(worksheet §2.2.2 with §5 risk 4 discharged): it is vacuous on pieces missing a fibre
(zero ring), it is exactly what the integral-fibre slice case produces where the fibre
ring is a domain, and it keeps the un-landed 1d-ii/DAT-3 fibre-sheaf identifications
with their owners (DAT-C/DD-R bridge their fibre-curve statements to this spelling).
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## `nonZeroDivisors` ↔ `IsSMulRegular` on a commutative ring -/

section Bridges

variable {A : Type u} [CommRing A]

/-- A nonzerodivisor of a commutative ring is a regular element for the
self-multiplication action. -/
theorem isSMulRegular_self_of_mem_nonZeroDivisors {t : A}
    (ht : t ∈ nonZeroDivisors A) : IsSMulRegular A t := by
  intro u v huv
  have h0 : (u - v) * t = 0 := by
    have hm : t * u = t * v := huv
    rw [sub_mul, mul_comm u, mul_comm v, hm, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp ht).2 (u - v) h0)

/-- A regular element for the self-multiplication action of a commutative ring is a
nonzerodivisor. -/
theorem mem_nonZeroDivisors_of_isSMulRegular_self {t : A}
    (h : IsSMulRegular A t) : t ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · refine h (show t • z = t • 0 by
      rw [smul_eq_mul, smul_eq_mul, mul_zero]; exact hz)
  · refine h (show t • z = t • 0 by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, mul_comm]; exact hz)

end Bridges

/-! ## (α) Germ transport on an affine open, and the field-level slice case -/

section Germ

variable {X : Scheme.{u}}

/-- **Germ transport on an affine open**: a nonzerodivisor of `Γ(X, U)` has
nonzerodivisor germs at every point of `U`. The stalk is the localization of the affine
section ring at the point's prime (`IsAffineOpen.isLocalization_stalk`), and regularity
passes to localizations. -/
theorem IsAffineOpen.germ_mem_nonZeroDivisors {U : X.Opens} (hU : IsAffineOpen U)
    {t : Γ(X, U)} (ht : t ∈ nonZeroDivisors Γ(X, U)) (y : X) (hy : y ∈ U) :
    (X.presheaf.germ U y hy).hom t ∈ nonZeroDivisors (X.presheaf.stalk y) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    X.presheaf.algebra_section_stalk ⟨y, hy⟩
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  have hreg : IsSMulRegular (X.presheaf.stalk y)
      (algebraMap Γ(X, U) (X.presheaf.stalk y) t) :=
    (isSMulRegular_self_of_mem_nonZeroDivisors ht).of_isLocalization
      (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  exact mem_nonZeroDivisors_of_isSMulRegular_self hreg

/-- **The field-level slice case** (Kleiman tex 2013–2022, "`σ_t ≠ 0` on the integral
fibre, hence `σ_t` is regular"): on an integral scheme, a nonzero section has
nonzerodivisor germs at every point of its open. Named separately for DAT-C's canonical
-section normalization at field-level fibres. -/
theorem Scheme.germ_mem_nonZeroDivisors_of_ne_zero [IsIntegral X]
    {U : X.Opens} {t : Γ(X, U)} (ht : t ≠ 0) (y : X) (hy : y ∈ U) :
    (X.presheaf.germ U y hy).hom t ∈ nonZeroDivisors (X.presheaf.stalk y) := by
  refine mem_nonZeroDivisors_of_ne_zero (fun h0 => ht ?_)
  exact germ_injective_of_isIntegral X y hy (by rw [h0, map_zero])

end Germ

/-! ## (β) Piece flatness and (γ) the generic A2 bridge -/

section Piece

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

attribute [local instance] Scheme.overModule

/-- **Piece flatness**: if the section ring of an affine open `V` is a flat `k`-module
(`Scheme.overModule`), then so is the section ring of every basic open `D(h) ⊆ V` —
the tower `k → Γ(V) → Γ(D(h))` with `Γ(D(h))` a localization of `Γ(V)`.
`private`: the public copy (same content, binder order `hV hflat f`) lives in
`DivSchemeFamilySide` — same-day concurrent coinage (the I-0190 pattern), collision
surfaced at the first full root build; external consumers use that copy. -/
private theorem flat_sections_basicOpen {V : X.Opens} (hV : IsAffineOpen V) (h : Γ(X, V))
    (hflat : Module.Flat k Γ(X, V)) :
    Module.Flat k Γ(X, X.basicOpen h) := by
  letI : Algebra k Γ(X, V) := (X.overAlgebraMap k V).toAlgebra
  letI : Algebra k Γ(X, X.basicOpen h) :=
    (X.overAlgebraMap k (X.basicOpen h)).toAlgebra
  haveI : IsLocalization.Away h Γ(X, X.basicOpen h) := hV.isLocalization_basicOpen h
  haveI : Module.Flat Γ(X, V) Γ(X, X.basicOpen h) :=
    IsLocalization.flat _ (Submonoid.powers h)
  haveI : Module.Flat k Γ(X, V) := hflat
  haveI : IsScalarTower k Γ(X, V) Γ(X, X.basicOpen h) :=
    IsScalarTower.of_algebraMap_eq'
      (X.overAlgebraMap_naturality k (homOfLE (X.basicOpen_le h)).op).symm
  exact Module.Flat.trans k Γ(X, V) Γ(X, X.basicOpen h)

/-- **The generic A2 bridge** (`lm:ctn` (iii)⟹(i) on a basic-open piece of a flat
affine chart): over a Noetherian `k`, a section `t` of `D(h) ⊆ V` whose multiplication
endomorphism is injective on every residue-field fibre of the piece ring is a
nonzerodivisor. -/
theorem mem_nonZeroDivisors_of_fibrewise_regular [IsNoetherianRing k]
    {V : X.Opens} (hV : IsAffineOpen V) (h : Γ(X, V))
    (hflat : Module.Flat k Γ(X, V)) (t : Γ(X, X.basicOpen h))
    (hfib : ∀ p : PrimeSpectrum k, Function.Injective
      ((Scheme.mulSectionEnd k t).rTensor p.asIdeal.ResidueField)) :
    t ∈ nonZeroDivisors Γ(X, X.basicOpen h) := by
  haveI : Module.Flat k Γ(X, X.basicOpen h) := flat_sections_basicOpen k hV h hflat
  have hinj : Function.Injective (Scheme.mulSectionEnd k t) :=
    Module.Flat.injective_of_forall_rTensor_residueField_injective
      (Scheme.mulSectionEnd k t) hfib
  refine mem_nonZeroDivisors_of_isSMulRegular_self (fun u v huv => hinj ?_)
  rw [Scheme.mulSectionEnd_apply, Scheme.mulSectionEnd_apply]
  exact huv

/-- The germ form of the generic A2 bridge: fibrewise-regular sections of basic-open
pieces have nonzerodivisor germs (feeds `Scheme.LocalEquations.regular`). -/
theorem germ_mem_nonZeroDivisors_of_fibrewise_regular [IsNoetherianRing k]
    {V : X.Opens} (hV : IsAffineOpen V) (h : Γ(X, V))
    (hflat : Module.Flat k Γ(X, V)) (t : Γ(X, X.basicOpen h))
    (hfib : ∀ p : PrimeSpectrum k, Function.Injective
      ((Scheme.mulSectionEnd k t).rTensor p.asIdeal.ResidueField))
    (y : X) (hy : y ∈ X.basicOpen h) :
    (X.presheaf.germ (X.basicOpen h) y hy).hom t
      ∈ nonZeroDivisors (X.presheaf.stalk y) :=
  (hV.basicOpen h).germ_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_fibrewise_regular k hV h hflat t hfib) y hy

/-- Conversion from the tensor-RING spelling of the fibre hypothesis (`t ⊗ 1` a
nonzerodivisor of the piece-ring fibre `Γ(W) ⊗[k] κ(p)`) to the `rTensor` spelling the
A2 bridge consumes. The `k`-algebra structure on the section ring is the structure
morphism (`Scheme.overAlgebraMap`), whose module structure is `Scheme.overModule` on
the nose. -/
theorem injective_rTensor_mulSectionEnd_of_tmul_mem_nonZeroDivisors
    {W : X.Opens} (t : Γ(X, W)) (p : PrimeSpectrum k)
    (hfib : letI : Algebra k Γ(X, W) := (X.overAlgebraMap k W).toAlgebra
      (t ⊗ₜ[k] (1 : p.asIdeal.ResidueField) :
          Γ(X, W) ⊗[k] p.asIdeal.ResidueField) ∈
        nonZeroDivisors (Γ(X, W) ⊗[k] p.asIdeal.ResidueField)) :
    Function.Injective
      ((Scheme.mulSectionEnd k t).rTensor p.asIdeal.ResidueField) := by
  letI : Algebra k Γ(X, W) := (X.overAlgebraMap k W).toAlgebra
  have hend : Scheme.mulSectionEnd k t = LinearMap.mulLeft k t := by
    ext s
    simp [Scheme.mulSectionEnd_apply]
  rw [hend, rTensor_mulLeft_eq_mulLeft_tmul p.asIdeal.ResidueField t]
  intro u v huv
  have hzero : (u - v) * (t ⊗ₜ[k] (1 : p.asIdeal.ResidueField)) = 0 := by
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply] at huv
    rw [sub_mul, mul_comm u, mul_comm v, huv, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hfib).2 (u - v) hzero)

end Piece

/-! ## (δ) A2 on the pinned cocycle datum -/

namespace BasicOpenCocycleDatum

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]

section AffineHom

variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable (D : BasicOpenCocycleDatum C B π)

/-- The `j`-th **component** of a global section of the datum's glued sheaf, as a
section of the trivializing basic-open piece `D(h_j)` (the `⊤ ⊓ pieces j`-to-`pieces j`
restriction of the matching family's `j`-th entry). -/
noncomputable def component (s : ↥(gluedSubmodule B D.pieces D.unit ⊤))
    (j : D.index) : Γ(relCurve C B, D.pieces j) :=
  (relCurve C B).resHom (le_inf le_top le_rfl) (s.val j)

/-- Every piece of the pinned datum is an affine open (a basic open of a pinned affine
chart). -/
theorem isAffineOpen_pieces (j : D.index) : IsAffineOpen (D.pieces j) := by
  cases j with
  | inl j₀ => exact (relCover_isAffineOpen₀ C B (fiberTwoCover π)).basicOpen (D.h₀ j₀)
  | inr j₁ => exact (relCover_isAffineOpen₁ C B (fiberTwoCover π)).basicOpen (D.h₁ j₁)

end AffineHom

variable {π : C.left ⟶ P1 k} [IsFinite π]
variable (D : BasicOpenCocycleDatum C B π)

/-- **DAT-A2 on the datum, section-ring form**: a fibrewise-regular component of a
global section of the DAT-1 glued sheaf is a nonzerodivisor of its piece ring
(fibrewise-regular + flat ⟹ regular; the chart rings are free `B`-modules by
`free_relSections`, so the pieces are flat, and the `lm:ctn`-lite core fires). -/
theorem component_mem_nonZeroDivisors [IsNoetherianRing B]
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤)) (j : D.index)
    (hfib : ∀ p : PrimeSpectrum B, Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField)) :
    D.component s j ∈ nonZeroDivisors Γ(relCurve C B, D.pieces j) := by
  cases j with
  | inl j₀ =>
      haveI : Module.Free B Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₀) :=
        free_relSections C B (fiberChart₀ π)
          (isAffineOpen_preimage_chartOpen π 0).isCompact
          (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated
      exact mem_nonZeroDivisors_of_fibrewise_regular B
        (relCover_isAffineOpen₀ C B (fiberTwoCover π)) (D.h₀ j₀)
        Module.Flat.of_free (D.component s (Sum.inl j₀)) hfib
  | inr j₁ =>
      haveI : Module.Free B Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₁) :=
        free_relSections C B (fiberChart₁ π)
          (isAffineOpen_preimage_chartOpen π 1).isCompact
          (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated
      exact mem_nonZeroDivisors_of_fibrewise_regular B
        (relCover_isAffineOpen₁ C B (fiberTwoCover π)) (D.h₁ j₁)
        Module.Flat.of_free (D.component s (Sum.inr j₁)) hfib

/-- **DAT-A2 on the datum, germ form** (the `Scheme.LocalEquations.regular` input): a
fibrewise-regular component has nonzerodivisor germs at every point of its piece. -/
theorem germ_component_mem_nonZeroDivisors [IsNoetherianRing B]
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤)) (j : D.index)
    (hfib : ∀ p : PrimeSpectrum B, Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField))
    (y : ↑(relCurve C B).toPresheafedSpace) (hy : y ∈ D.pieces j) :
    ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom (D.component s j)
      ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk y) :=
  (D.isAffineOpen_pieces j).germ_mem_nonZeroDivisors
    (D.component_mem_nonZeroDivisors s j hfib) y hy

end BasicOpenCocycleDatum

end AlgebraicGeometry
