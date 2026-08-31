/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.Flat.Localization
import AlgebraicJacobian.Curve.DiagonalClosed
import AlgebraicJacobian.Algebra.DiagonalIdeal
import AlgebraicJacobian.Algebra.DiagonalRegular

/-!
# The per-chart kernel of the diagonal (deg-D4b, brick B4)

Fix an affine chart `U` of the curve `C : Over (Spec k)` and write `B := Γ(C.left, U)`
(with the `Over.sectionsAlgebra` `k`-algebra structure).  Following the worksheet
(`informal/deg-d4b-worksheet.md` §D1/D3), the étale-factorization data of the chart enters
**abstractly**, matching brick B0's package: instances `[Algebra (Polynomial k) B]`,
`[IsScalarTower k (Polynomial k) B]`, an idempotent lift `elift : B ⊗[k] B` with
`IsIdempotentElem (baseChange elift)` and the generation `hgen` of the `Polynomial k`-diagonal
ideal — brick B5 discharges them from `exists_etale_mvPolynomial` when freezing the chart
choice in `DiagonalChartData`.

This file splices B0 (the localized principality of the diagonal ideal) through B2 (the
product charts and their basic-open localization) against Mathlib's kernel ideal sheaf:

* `Over.diagonalChart` — the **diagonal member** `𝔇(U) := D(1 − ẽ)`, the basic open of the
  transported `1 - elift` inside the product chart `𝔚(U, U)`; affine
  (`isAffineOpen_diagonalChart`), and containing every diagonal point of the chart
  (`diagonal_preimage_diagonalChart : δ ⁻¹ 𝔇(U) = U`, `diagonal_base_mem_diagonalChart`).
* `Over.diagonalChartEqn` — the **local equation of the diagonal**: the transport of
  `u ⊗ 1 − 1 ⊗ u` to `Γ(𝔇(U))`.
* `Over.diagonal_appLE_productChartSections` — *the app of `δ` on the chart is
  multiplication*: the pullback of an identified tensor `x` along `δ` is the restriction of
  `lmul' k x` (the `a = b = 𝟙` instance of B2's lift-app rule).
* `Over.diagonal_ker_ideal_diagonalChart` — **the D3 display**: the kernel ideal sheaf of
  `δ` evaluated on the affine open `𝔇(U)` is principal on the diagonal equation,
  `((δ C).left.ker).ideal ⟨𝔇(U), _⟩ = Ideal.span {diagonalChartEqn}`.
* `Over.diagonalChartEqn_mem_nonZeroDivisors` / `germ_diagonalChartEqn_mem_nonZeroDivisors`
  — **regularity** (worksheet D2): the B1 engine transported along the flat
  `B ⊗[k] B → Γ(𝔇(U))`, plus the germ form in exactly the shape of the
  `Scheme.LocalEquations.regular` field.
* `AlgebraicGeometry.IsAffineOpen.germ_mem_nonZeroDivisors` — the **affine germ helper**
  (worksheet D2/D6): on an affine open, a section-level nonzerodivisor has nonzerodivisor
  germs (stalks are localizations, localizations are flat, flat maps preserve `⁰`) — the
  converse of the landed `LocalEquations.eqn_restrict_mem_nonZeroDivisors`.
* `Over.diagonalChart_inf_diagonalComplement` — the **diag–off overlap** (worksheet D4):
  `𝔇(U) ⊓ Δᶜ = D(diagonalChartEqn)`, from the D3 display and `Hom.support_ker`, so the
  restricted equation is a unit there and the ratio against the off-diagonal equation `1`
  is a unit.

The file opens with the smoke tests the worksheet mandated for the two seams it flagged as
untested in-tree: `Scheme.IdealSheafData` being keyed on `affineOpens` *subtypes* while the
in-tree calculus carries raw opens with separate `IsAffineOpen` proofs, and the
`app`-vs-`appLE` normal forms of `Hom.ker_apply`.

## Design notes

* The `k`-algebra structure on section rings is `Over.sectionsAlgebra`, reactivated here as
  a local instance; consumers (B5) must reactivate it for these statements to elaborate
  identically.
* The `IsLocalization.Away` splice uses B2's
  `isLocalization_away_basicOpen_productChartSections` with its exact `letI` algebra term
  (the sections identification followed by restriction); the D3 display itself carries no
  algebra instance — the equation is spelled by presheaf restriction.
* `Hom.ker_apply` produces `app`-normal forms; the bridge to the in-tree `appLE`-normal
  calculus is `Scheme.Hom.app_eq_appLE`, rewritten in that single direction.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct nonZeroDivisors

namespace AlgebraicGeometry

/-! ## Smoke tests: the `affineOpens`-subtype and `app`-vs-`appLE` seams

The worksheet (risk 4) flagged that `Scheme.IdealSheafData` is keyed on the subtype
`X.affineOpens` while the in-tree covers carry raw `X.Opens` with separate `IsAffineOpen`
proofs, and that `Hom.ker_apply` produces `f.app U`-normal forms against the in-tree
`appLE`-normal calculus.  The examples below are the mandated first-contact smoke tests;
all pass without friction (anonymous-constructor subtypes, `Subtype`-`≤` coercion into
`homOfLE`, and the `app = appLE _ _ le_rfl` bridge all behave). -/

section SmokeTests

variable {R S : CommRingCat.{u}}

-- (i) `Hom.ker_apply` on an `affineOpens` subtype assembled from a raw open + proof;
-- the `QuasiCompact` side condition is found by instance inference.
example (f : R ⟶ S) :
    (Spec.map f).ker.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩
      = RingHom.ker ((Spec.map f).app ⊤).hom :=
  Scheme.Hom.ker_apply _ _

-- (ii) the `app`/`appLE` seam: the kernel in `appLE`-normal form.
example (f : R ⟶ S) :
    (Spec.map f).ker.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩
      = RingHom.ker ((Spec.map f).appLE ⊤ (Spec.map f ⁻¹ᵁ ⊤) le_rfl).hom := by
  rw [Scheme.Hom.ker_apply, Scheme.Hom.appLE_eq_app]

-- (iii) `map_ideal` between `affineOpens` subtypes assembled from raw opens, with the
-- inequality supplied at the level of the underlying opens.
example (I : Scheme.IdealSheafData (Spec R)) {U V : (Spec R).Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    (I.ideal ⟨V, hV⟩).map ((Spec R).presheaf.map (homOfLE h).op).hom = I.ideal ⟨U, hU⟩ :=
  I.map_ideal (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h

end SmokeTests

/-! ## The affine germ helper (worksheet D2, second exported regularity helper) -/

/-- **Germ regularity from section regularity on an affine open**: if a section over an
affine open `W` is a nonzerodivisor in `Γ(X, W)`, its germ at every point of `W` is a
nonzerodivisor in the stalk.  The stalk is a localization of `Γ(X, W)`
(`IsAffineOpen.isLocalization_stalk`), localizations are flat (`IsLocalization.flat`), and
flat ring homomorphisms preserve nonzerodivisors (`RingHom.Flat.mem_nonZeroDivisors`,
brick B1).  This is the converse, on affine opens, of the landed
`Scheme.LocalEquations.eqn_restrict_mem_nonZeroDivisors`; together with the section-level
regularity of the diagonal equation it discharges the `regular` field of the diagonal
`LocalEquations` (B5) and deg-D4c's pullback regularity. -/
theorem IsAffineOpen.germ_mem_nonZeroDivisors {X : Scheme.{u}} {W : X.Opens}
    (hW : IsAffineOpen W) {s : Γ(X, W)} (hs : s ∈ Γ(X, W)⁰) {y : X} (hy : y ∈ W) :
    (X.presheaf.germ W y hy).hom s ∈ (X.presheaf.stalk y)⁰ := by
  letI : Algebra Γ(X, W) (X.presheaf.stalk y) :=
    X.presheaf.algebra_section_stalk ⟨y, hy⟩
  haveI := hW.isLocalization_stalk ⟨y, hy⟩
  have hflat : (algebraMap Γ(X, W) (X.presheaf.stalk y)).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat _ (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)
  exact RingHom.Flat.mem_nonZeroDivisors hflat hs

namespace Over

-- The `k`-algebra structure on sections of objects over `Spec k`
-- (`Cohomology/SectionsBaseChange.lean`); consumers must reactivate the same instance.
attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k]

/-! ## The diagonal member `𝔇(U)` and its equation -/

/-- **The diagonal member attached to an affine chart** (worksheet D1(c)): for an affine
open `U ⊆ C.left` and an (abstract) idempotent lift `elift ∈ Γ(U) ⊗[k] Γ(U)`, the basic
open `𝔇(U) := D(1 − ẽ)` of the transport of `1 - elift` through the product-chart
identification — the open on which the diagonal ideal becomes principal on the diagonal
equation.  Consumed only through the named lemmas of this file. -/
noncomputable def diagonalChart (C : Over (Spec (.of k))) {U : C.left.Opens}
    (hU : IsAffineOpen U) (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U)) :
    (C ⊗ C).left.Opens :=
  (C ⊗ C).left.basicOpen (productChartSections C C hU hU (1 - elift))

/-- Unfolding lemma for `Over.diagonalChart`. -/
lemma diagonalChart_def (C : Over (Spec (.of k))) {U : C.left.Opens}
    (hU : IsAffineOpen U) (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U)) :
    diagonalChart C hU elift
      = (C ⊗ C).left.basicOpen (productChartSections C C hU hU (1 - elift)) :=
  rfl

/-- The diagonal member lies in the product chart `𝔚(U, U)`. -/
lemma diagonalChart_le_productChart (C : Over (Spec (.of k))) {U : C.left.Opens}
    (hU : IsAffineOpen U) (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U)) :
    diagonalChart C hU elift ≤ productChart C C U U :=
  (C ⊗ C).left.basicOpen_le _

/-- The diagonal member is an affine open. -/
theorem isAffineOpen_diagonalChart (C : Over (Spec (.of k))) {U : C.left.Opens}
    (hU : IsAffineOpen U) (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U)) :
    IsAffineOpen (diagonalChart C hU elift) :=
  isAffineOpen_basicOpen_productChartSections C C hU hU _

/-- **The local equation of the diagonal on the chart**: the transport of the diagonal
generator `u ⊗ 1 − 1 ⊗ u` (`AlgebraicJacobian.Diagonal.diagGen`, with `u` the étale
coordinate `algebraMap (Polynomial k) Γ(U) X`) through the product-chart identification,
restricted to the diagonal member `𝔇(U)`. -/
noncomputable def diagonalChartEqn (C : Over (Spec (.of k))) {U : C.left.Opens}
    (hU : IsAffineOpen U) [Algebra (Polynomial k) Γ(C.left, U)]
    (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U)) :
    Γ((C ⊗ C).left, diagonalChart C hU elift) :=
  ((C ⊗ C).left.presheaf.map
      (homOfLE (diagonalChart_le_productChart C hU elift)).op).hom
    (productChartSections C C hU hU
      (AlgebraicJacobian.Diagonal.diagGen (k := k) (B := Γ(C.left, U))))

/-- Unfolding lemma for `Over.diagonalChartEqn`. -/
lemma diagonalChartEqn_def (C : Over (Spec (.of k))) {U : C.left.Opens}
    (hU : IsAffineOpen U) [Algebra (Polynomial k) Γ(C.left, U)]
    (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U)) :
    diagonalChartEqn C hU elift
      = ((C ⊗ C).left.presheaf.map
            (homOfLE (diagonalChart_le_productChart C hU elift)).op).hom
          (productChartSections C C hU hU
            (AlgebraicJacobian.Diagonal.diagGen (k := k) (B := Γ(C.left, U)))) :=
  rfl

/-! ## The app of `δ` on the chart is multiplication -/

private lemma appLE_congr_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (U : Z.Opens)
    (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

private lemma id_over_appLE {C : Over (Spec (.of k))} {U W : C.left.Opens}
    (h : W ≤ (𝟙 C : C ⟶ C).left ⁻¹ᵁ U) (hWU : W ≤ U) :
    (𝟙 C : C ⟶ C).left.appLE U W h = C.left.presheaf.map (homOfLE hWU).op := by
  rw [appLE_congr_hom (Over.id_left C) U W h, Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact Category.id_comp _

/-- **The app of the diagonal on the product chart is multiplication** (worksheet D5(iii)
instantiated at `q = δ`, `a = b = 𝟙`): pulling an identified tensor `x` back along `δ` to
any `W ≤ δ ⁻¹ 𝔚(U, U)` inside `U` gives the restriction of `mul x = lmul' k x`. -/
theorem diagonal_appLE_productChartSections (C : Over (Spec (.of k))) {U : C.left.Opens}
    (hU : IsAffineOpen U) {W : C.left.Opens}
    (hW : W ≤ (diagonal C).left ⁻¹ᵁ productChart C C U U) (hWU : W ≤ U)
    (x : Γ(C.left, U) ⊗[k] Γ(C.left, U)) :
    (diagonal C).left.appLE (productChart C C U U) W hW (productChartSections C C hU hU x)
      = C.left.presheaf.map (homOfLE hWU).op (Algebra.TensorProduct.lmul' k x) := by
  induction x with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s t =>
    rw [appLE_productChartSections_tmul hU hU (diagonal_fst C) (diagonal_snd C) hW
        (hW.trans (preimage_productChart_le_fst (diagonal_fst C) U U))
        (hW.trans (preimage_productChart_le_snd (diagonal_snd C) U U)) s t,
      id_over_appLE _ hWU, Algebra.TensorProduct.lmul'_apply_tmul, map_mul]

/-! ## The `δ`-preimage of the diagonal member -/

/-- **The `δ`-preimage of the diagonal member is the whole chart** (worksheet D1(c)):
since `mul elift = 0`, the `δ`-pullback of the transported `1 − elift` is `1`, so
`δ ⁻¹ 𝔇(U) = δ ⁻¹ 𝔚(U, U) = U`.  In particular `Δ ∩ 𝔚(U, U) ⊆ 𝔇(U)`: the diagonal member
covers all diagonal points of the chart in one piece. -/
theorem diagonal_preimage_diagonalChart (C : Over (Spec (.of k))) {U : C.left.Opens}
    (hU : IsAffineOpen U) (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U))
    (hmul : Algebra.TensorProduct.lmul' k elift = 0) :
    (diagonal C).left ⁻¹ᵁ diagonalChart C hU elift = U := by
  have hpre : (diagonal C).left ⁻¹ᵁ productChart C C U U ≤ U :=
    (diagonal_preimage_productChart C U U).le.trans inf_le_left
  rw [diagonalChart_def, Scheme.preimage_basicOpen, Scheme.Hom.app_eq_appLE,
    diagonal_appLE_productChartSections C hU le_rfl hpre (1 - elift), map_sub, map_one,
    hmul, sub_zero, map_one, Scheme.basicOpen_one, diagonal_preimage_productChart,
    inf_idem]

/-- **The `p ↦ z` membership** (worksheet D4): the diagonal image of any point of the
chart `U` lies in the diagonal member `𝔇(U)`. -/
theorem diagonal_base_mem_diagonalChart (C : Over (Spec (.of k))) {U : C.left.Opens}
    (hU : IsAffineOpen U) (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U))
    (hmul : Algebra.TensorProduct.lmul' k elift = 0) {p : C.left} (hp : p ∈ U) :
    (diagonal C).left.base p ∈ diagonalChart C hU elift := by
  rw [← diagonal_preimage_diagonalChart C hU elift hmul] at hp
  exact hp

/-! ## The kernel ideal sheaf of `δ` on the diagonal member (the D3 display) -/

/-- **The per-chart kernel computation** (worksheet D3, the deg-D4b heart): on the diagonal
member `𝔇(U)` of an affine chart carrying B0's abstract étale-factorization package (an
idempotent lift `elift` of a generator of the `Polynomial k`-diagonal ideal), the kernel
ideal sheaf of the diagonal `δ` is **exactly principal on the diagonal equation**:

`((δ C).left.ker).ideal ⟨𝔇(U), _⟩ = Ideal.span {diagonalChartEqn}`.

The proof splices B0's localized principality (`ker_map_localization_eq`) through B2's
localization seam (`isLocalization_away_basicOpen_productChartSections`) against Mathlib's
`Scheme.Hom.ker_apply`, using that the app of `δ` on the chart is multiplication and that
sections restrict isomorphically along `δ ⁻¹ 𝔇(U) = U`. -/
theorem diagonal_ker_ideal_diagonalChart (C : Over (Spec (.of k))) [IsSeparated C.hom]
    {U : C.left.Opens} (hU : IsAffineOpen U)
    [Algebra (Polynomial k) Γ(C.left, U)] [IsScalarTower k (Polynomial k) Γ(C.left, U)]
    (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U))
    (hidem : IsIdempotentElem (AlgebraicJacobian.Diagonal.baseChange elift))
    (hgen : RingHom.ker
        (Algebra.TensorProduct.lmul' (R := Polynomial k) (S := Γ(C.left, U)))
      = Ideal.span {AlgebraicJacobian.Diagonal.baseChange elift}) :
    ((diagonal C).left.ker).ideal
        ⟨diagonalChart C hU elift, isAffineOpen_diagonalChart C hU elift⟩
      = Ideal.span {diagonalChartEqn C hU elift} := by
  have hmul : Algebra.TensorProduct.lmul' k elift = 0 :=
    AlgebraicJacobian.Diagonal.lmul'_lift elift hgen
  have hpre : (diagonal C).left ⁻¹ᵁ diagonalChart C hU elift = U :=
    diagonal_preimage_diagonalChart C hU elift hmul
  have hpre' : (diagonal C).left ⁻¹ᵁ diagonalChart C hU elift ≤ U := hpre.le
  -- B2's localization splice: `Γ(𝔇(U))` is the localization of `Γ(U) ⊗[k] Γ(U)` away
  -- from `1 - elift`, through the sections identification followed by restriction.
  letI : Algebra (Γ(C.left, U) ⊗[k] Γ(C.left, U))
      Γ((C ⊗ C).left, diagonalChart C hU elift) :=
    ((algebraMap Γ((C ⊗ C).left, productChart C C U U)
        Γ((C ⊗ C).left,
          (C ⊗ C).left.basicOpen (productChartSections C C hU hU (1 - elift)))).comp
      (productChartSections C C hU hU).toRingHom).toAlgebra
  haveI hloc : IsLocalization.Away (1 - elift)
      Γ((C ⊗ C).left, diagonalChart C hU elift) :=
    isLocalization_away_basicOpen_productChartSections C C hU hU (1 - elift)
  -- B0's localized principality, instantiated at the chart sections.
  have hker := AlgebraicJacobian.Diagonal.ker_map_localization_eq elift hidem hgen
    Γ((C ⊗ C).left, diagonalChart C hU elift)
  -- The diagonal equation is the image of the diagonal generator.
  have heqn : algebraMap (Γ(C.left, U) ⊗[k] Γ(C.left, U))
        Γ((C ⊗ C).left, diagonalChart C hU elift)
        (AlgebraicJacobian.Diagonal.diagGen (k := k) (B := Γ(C.left, U)))
      = diagonalChartEqn C hU elift := rfl
  -- The app of `δ` on `𝔇(U)`, precomposed with the localization structure map, is the
  -- restriction of the multiplication `lmul' k` to `δ ⁻¹ 𝔇(U) = U`.
  have happ : ∀ r : Γ(C.left, U) ⊗[k] Γ(C.left, U),
      ((diagonal C).left.app (diagonalChart C hU elift)).hom
          (algebraMap (Γ(C.left, U) ⊗[k] Γ(C.left, U))
            Γ((C ⊗ C).left, diagonalChart C hU elift) r)
        = (C.left.presheaf.map (homOfLE hpre').op).hom
            (Algebra.TensorProduct.lmul' k r) := by
    intro r
    have h1 : algebraMap (Γ(C.left, U) ⊗[k] Γ(C.left, U))
          Γ((C ⊗ C).left, diagonalChart C hU elift) r
        = ((C ⊗ C).left.presheaf.map
              (homOfLE (diagonalChart_le_productChart C hU elift)).op).hom
            (productChartSections C C hU hU r) := rfl
    rw [h1, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    exact diagonal_appLE_productChartSections C hU _ hpre' r
  -- Restriction along the equality of opens `δ ⁻¹ 𝔇(U) = U` is injective.
  have hres : Function.Injective (C.left.presheaf.map (homOfLE hpre').op).hom := by
    have h2 : homOfLE hpre' = eqToHom hpre := Subsingleton.elim _ _
    rw [h2]
    exact (ConcreteCategory.bijective_of_isIso
      (C.left.presheaf.map (eqToHom hpre).op)).injective
  rw [Scheme.Hom.ker_apply]
  apply le_antisymm
  · -- every element of the kernel is a multiple of the diagonal equation
    intro s hs
    rw [RingHom.mem_ker] at hs
    obtain ⟨⟨r, m⟩, hsr⟩ :=
      IsLocalization.surj (M := Submonoid.powers (1 - elift)) s
    -- the numerator multiplies to zero, hence lies in the diagonal ideal
    have h0 : (C.left.presheaf.map (homOfLE hpre').op).hom
        (Algebra.TensorProduct.lmul' k r) = 0 := by
      rw [← happ r, ← hsr, map_mul, hs, zero_mul]
    have hr : Algebra.TensorProduct.lmul' k r = 0 := by
      apply hres
      rw [h0, map_zero]
    have hrmem : algebraMap (Γ(C.left, U) ⊗[k] Γ(C.left, U))
        Γ((C ⊗ C).left, diagonalChart C hU elift) r
        ∈ Ideal.span {diagonalChartEqn C hU elift} := by
      rw [← heqn, ← hker]
      exact Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker]; exact hr)
    -- divide by the unit denominator
    obtain ⟨v, hv⟩ := (IsLocalization.map_units
      Γ((C ⊗ C).left, diagonalChart C hU elift) m).exists_right_inv
    have hs' : s = algebraMap (Γ(C.left, U) ⊗[k] Γ(C.left, U))
        Γ((C ⊗ C).left, diagonalChart C hU elift) r * v := by
      calc s = s * (algebraMap (Γ(C.left, U) ⊗[k] Γ(C.left, U))
            Γ((C ⊗ C).left, diagonalChart C hU elift) ↑m * v) := by
            rw [hv, mul_one]
        _ = s * algebraMap (Γ(C.left, U) ⊗[k] Γ(C.left, U))
            Γ((C ⊗ C).left, diagonalChart C hU elift) ↑m * v := by
            rw [mul_assoc]
        _ = _ := by rw [hsr]
    rw [hs']
    exact Ideal.mul_mem_right _ _ hrmem
  · -- the diagonal equation is killed by the app of `δ`
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      ← heqn, happ, AlgebraicJacobian.Diagonal.lmul'_diagGen, map_zero]

/-! ## Regularity of the diagonal equation (worksheet D2) -/

/-- **Section-level regularity of the diagonal equation**: the diagonal equation is a
nonzerodivisor in `Γ(𝔇(U))`, for a flat étale coordinate `Polynomial k → Γ(U)`.  The
B1 engine gives that the diagonal generator is a nonzerodivisor of `Γ(U) ⊗[k] Γ(U)`
(`diagGen_mem_nonZeroDivisors`), and the structure map to the localized chart sections —
the sections identification followed by restriction to the basic open — is flat, so
nonzerodivisibility transports (`RingHom.Flat.mem_nonZeroDivisors`). -/
theorem diagonalChartEqn_mem_nonZeroDivisors (C : Over (Spec (.of k)))
    {U : C.left.Opens} (hU : IsAffineOpen U)
    [Algebra (Polynomial k) Γ(C.left, U)] [IsScalarTower k (Polynomial k) Γ(C.left, U)]
    [Module.Flat (Polynomial k) Γ(C.left, U)]
    (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U)) :
    diagonalChartEqn C hU elift ∈ Γ((C ⊗ C).left, diagonalChart C hU elift)⁰ := by
  haveI := (isAffineOpen_productChart C C hU hU).isLocalization_basicOpen
    (productChartSections C C hU hU (1 - elift))
  have hrest : (algebraMap Γ((C ⊗ C).left, productChart C C U U)
      Γ((C ⊗ C).left,
        (C ⊗ C).left.basicOpen (productChartSections C C hU hU (1 - elift)))).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat _
        (Submonoid.powers (productChartSections C C hU hU (1 - elift))))
  have hpcs : ((productChartSections C C hU hU).toRingHom :
      Γ(C.left, U) ⊗[k] Γ(C.left, U) →+* Γ((C ⊗ C).left, productChart C C U U)).Flat :=
    RingHom.Flat.of_bijective (productChartSections C C hU hU).bijective
  exact RingHom.Flat.mem_nonZeroDivisors (RingHom.Flat.comp hpcs hrest)
    (AlgebraicJacobian.Diagonal.diagGen_mem_nonZeroDivisors (k := k)
      (B := Γ(C.left, U)))

/-- **Germ-level regularity of the diagonal equation**, in exactly the shape of the
`Scheme.LocalEquations.regular` field (B5): the germ of the diagonal equation at every
point of the diagonal member is a nonzerodivisor in the stalk. -/
theorem germ_diagonalChartEqn_mem_nonZeroDivisors (C : Over (Spec (.of k)))
    {U : C.left.Opens} (hU : IsAffineOpen U)
    [Algebra (Polynomial k) Γ(C.left, U)] [IsScalarTower k (Polynomial k) Γ(C.left, U)]
    [Module.Flat (Polynomial k) Γ(C.left, U)]
    (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U)) {y : (C ⊗ C).left}
    (hy : y ∈ diagonalChart C hU elift) :
    ((C ⊗ C).left.presheaf.germ (diagonalChart C hU elift) y hy).hom
        (diagonalChartEqn C hU elift)
      ∈ ((C ⊗ C).left.presheaf.stalk y)⁰ :=
  (isAffineOpen_diagonalChart C hU elift).germ_mem_nonZeroDivisors
    (diagonalChartEqn_mem_nonZeroDivisors C hU elift) hy

/-! ## The diag–off overlap (worksheet D4) -/

/-- **The overlap of the diagonal member with the off-diagonal member is the basic open of
the diagonal equation**: `𝔇(U) ⊓ Δᶜ = D(diagonalChartEqn)`.  Set-theoretically,
`Δ ∩ 𝔇(U) = V(diagonalChartEqn) ∩ 𝔇(U)` by the D3 display and `Hom.support_ker`, and
passing to complements inside `𝔇(U)` gives the claim.  Consequence for B5's cocycle: on
this overlap the restricted diagonal equation is a unit
(`RingedSpace.isUnit_res_basicOpen`), so the ratio against the off-diagonal equation `1`
is a unit. -/
theorem diagonalChart_inf_diagonalComplement (C : Over (Spec (.of k)))
    [IsSeparated C.hom] {U : C.left.Opens} (hU : IsAffineOpen U)
    [Algebra (Polynomial k) Γ(C.left, U)] [IsScalarTower k (Polynomial k) Γ(C.left, U)]
    (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U))
    (hidem : IsIdempotentElem (AlgebraicJacobian.Diagonal.baseChange elift))
    (hgen : RingHom.ker
        (Algebra.TensorProduct.lmul' (R := Polynomial k) (S := Γ(C.left, U)))
      = Ideal.span {AlgebraicJacobian.Diagonal.baseChange elift}) :
    diagonalChart C hU elift ⊓ diagonalComplement C
      = (C ⊗ C).left.basicOpen (diagonalChartEqn C hU elift) := by
  have hsupp := ((diagonal C).left.ker).coe_support_inter
    ⟨diagonalChart C hU elift, isAffineOpen_diagonalChart C hU elift⟩
  rw [diagonal_ker_ideal_diagonalChart C hU elift hidem hgen, coe_support_ker_diagonal,
    Scheme.zeroLocus_span, Scheme.zeroLocus_singleton] at hsupp
  -- hsupp : Δ ∩ 𝔇(U) = (D(eqn))ᶜ ∩ 𝔇(U)  (as sets)
  ext z
  have h := Set.ext_iff.mp hsupp z
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe] at h
  constructor
  · rintro ⟨hz𝔇, hzc⟩
    by_contra hnb
    exact (mem_diagonalComplement_iff C).mp hzc (h.mpr ⟨hnb, hz𝔇⟩).1
  · intro hzb
    have hz𝔇 : z ∈ diagonalChart C hU elift :=
      (C ⊗ C).left.basicOpen_le (diagonalChartEqn C hU elift) hzb
    exact ⟨hz𝔇, fun hzr => (h.mp ⟨hzr, hz𝔇⟩).1 hzb⟩

/-- **The diagonal equation is a unit on the diag–off overlap** — the exact
`ratio_isUnit` input of B5's diag–off case: the restriction of `diagonalChartEqn` to
`𝔇(U) ⊓ Δᶜ` is a unit, because that overlap *is* the basic open of the equation
(`diagonalChart_inf_diagonalComplement`) and a section is a unit on its own basic open
(`RingedSpace.isUnit_res_basicOpen`). -/
theorem isUnit_res_diagonalChartEqn (C : Over (Spec (.of k)))
    [IsSeparated C.hom] {U : C.left.Opens} (hU : IsAffineOpen U)
    [Algebra (Polynomial k) Γ(C.left, U)] [IsScalarTower k (Polynomial k) Γ(C.left, U)]
    (elift : Γ(C.left, U) ⊗[k] Γ(C.left, U))
    (hidem : IsIdempotentElem (AlgebraicJacobian.Diagonal.baseChange elift))
    (hgen : RingHom.ker
        (Algebra.TensorProduct.lmul' (R := Polynomial k) (S := Γ(C.left, U)))
      = Ideal.span {AlgebraicJacobian.Diagonal.baseChange elift}) :
    IsUnit (((C ⊗ C).left.presheaf.map
        (homOfLE (inf_le_left :
          diagonalChart C hU elift ⊓ diagonalComplement C
            ≤ diagonalChart C hU elift)).op).hom
      (diagonalChartEqn C hU elift)) := by
  have hovl := diagonalChart_inf_diagonalComplement C hU elift hidem hgen
  have hsplit : (homOfLE (inf_le_left :
        diagonalChart C hU elift ⊓ diagonalComplement C ≤ diagonalChart C hU elift))
      = eqToHom hovl ≫ homOfLE ((C ⊗ C).left.basicOpen_le (diagonalChartEqn C hU elift)) :=
    Subsingleton.elim _ _
  rw [hsplit, op_comp, Functor.map_comp, CommRingCat.comp_apply]
  exact ((C ⊗ C).left.toRingedSpace.isUnit_res_basicOpen
    (diagonalChartEqn C hU elift)).map _

end Over

end AlgebraicGeometry
