/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafDatumBaseChange
import AlgebraicJacobian.Cohomology.DescentSkeleton

/-!
# The RE-5 toolkit: denominator clearing into the chart rings (RE-5, stage ii prep)

The worksheet §3.2 mechanism note: *"localization rings `Γ(D(h_j))` are
`Away`-localizations of the tensor ring, handled by clearing denominators into the
chart rings first — that is why the datum is normalized to basic opens."* This file is
that clearing, in two layers.

**Scheme-general away-helpers** (all opens flexible via an equality hypothesis
`O = X.basicOpen σ`, so consumers never cast):

* `AlgebraicGeometry.Scheme.isUnit_resHom_of_eq_basicOpen` — the restriction of `σ` to
  its basic open is a unit;
* `AlgebraicGeometry.IsAffineOpen.exists_pow_mul_eq_resHom` — denominator clearing: a
  section of `D(σ)` under an affine ambient becomes ambient after multiplication by a
  power of `σ`;
* `AlgebraicGeometry.IsAffineOpen.exists_pow_mul_eq_zero_of_resHom_eq_zero` —
  annihilation: an ambient section restricting to zero on `D(σ)` is killed by a power
  of `σ`;
* `AlgebraicGeometry.Scheme.Hom.injective_appLE_of_eq_basicOpen` — injectivity descends
  to the basic opens: if `f^* : Γ(Y, U) → Γ(X, U')` is injective (affine `U`, `U'`),
  so is `f^* : Γ(Y, D(σ)) → Γ(X, D(f^*σ))` (the localized comparison is
  `IsLocalization.Away.map` by mathlib's `appLE_eq_away_map`);
* `AlgebraicGeometry.Scheme.Hom.exists_unit_val_appLE_eq` — the unit reconstruction: a
  unit `g` on `D(f^*σ)` whose value clears to `f^*u` with an ambient certificate
  `u·v·σ^e = σ^(e+N+N')` (the descended two-sided fraction data) is the image of a unit
  on `D(σ)`.

**Chart vocabulary of the pinned cover data** (`BasicOpenCoverData`, any test ring):
the chart `chartAt i ∈ {V₀, V₁}` of each index on the base curve, the generator `genAt`
retyped on the chart preimage, and the products `sigmaAt`/`sigma₃At` whose basic opens
are exactly the pairwise/triple piece overlaps (`pieces_inf_eq_basicOpen_sigmaAt`,
`pieces_inf₃_eq_basicOpen_sigma₃At`) under the affine ambients
`fst⁻¹(chartAt i ⊓ chartAt j)` (`isAffineOpen_chartAt_inf`, case analysis on the two
pinned charts).

Consumed by `AlgebraicJacobian.Cohomology.DatumDescent` (the RE-5 keystone).
-/

set_option autoImplicit false
/- The chart vocabulary mixes `Γ(relCurve C R, ·)` with the `relCover`/`pullbackProd`
spellings (definitionally equal through semireducible definitions), as in
`GluedSheafDatum.lean`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

/-! ## Away-helpers on flexible basic opens -/

section Away

variable {X : Scheme.{u}}

/-- The restriction of `σ` to (an open equal to) its basic open is a unit. -/
lemma Scheme.isUnit_resHom_of_eq_basicOpen {U O : X.Opens} (σ : Γ(X, U))
    (hO : O = X.basicOpen σ) (hOU : O ≤ U) : IsUnit (X.resHom hOU σ) := by
  subst hO
  exact X.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen σ

/-- **Denominator clearing into an affine ambient** (flexible-open form): a section `x`
of an open equal to `D(σ)`, `σ` a section of an affine ambient `U`, satisfies
`σ^n · x = u|_O` for some ambient section `u` and some `n`. -/
theorem IsAffineOpen.exists_pow_mul_eq_resHom {U O : X.Opens} (hU : IsAffineOpen U)
    (σ : Γ(X, U)) (hO : O = X.basicOpen σ) (hOU : O ≤ U) (x : Γ(X, O)) :
    ∃ (u : Γ(X, U)) (n : ℕ), X.resHom hOU σ ^ n * x = X.resHom hOU u := by
  subst hO
  haveI := hU.isLocalization_basicOpen σ
  obtain ⟨⟨u, m⟩, hy⟩ := IsLocalization.surj (M := Submonoid.powers σ) x
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m : Γ(X, U)) σ).mp m.2
  refine ⟨u, n, ?_⟩
  rw [Scheme.algebraMap_basicOpen_eq_resHom] at hy
  have hn' : σ ^ n = (m : Γ(X, U)) := hn
  rw [← hn', map_pow] at hy
  rw [mul_comm]
  exact hy

/-- **Annihilation on an affine ambient** (flexible-open form): an ambient section
restricting to zero on `D(σ)` is killed by a power of `σ`. -/
theorem IsAffineOpen.exists_pow_mul_eq_zero_of_resHom_eq_zero {U O : X.Opens}
    (hU : IsAffineOpen U) (σ : Γ(X, U)) (hO : O = X.basicOpen σ) (hOU : O ≤ U)
    (t : Γ(X, U)) (ht : X.resHom hOU t = 0) : ∃ n : ℕ, σ ^ n * t = 0 := by
  subst hO
  haveI := hU.isLocalization_basicOpen σ
  have h0 : algebraMap Γ(X, U) Γ(X, X.basicOpen σ) t = 0 := by
    rw [Scheme.algebraMap_basicOpen_eq_resHom]
    exact ht
  obtain ⟨m, hmt⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers σ) _ t).mp h0
  obtain ⟨n, hn⟩ := m.2
  refine ⟨n, ?_⟩
  have hn' : σ ^ n = (m : Γ(X, U)) := hn
  rw [hn']
  exact hmt

variable {Y : Scheme.{u}}

/-- **Injectivity descends to basic opens**: if the comparison `f^* : Γ(Y, U) → Γ(X, U')`
is injective with `U`, `U'` affine, then the comparison on (opens equal to) the basic
opens of `σ` and `f^*σ` is injective — it is the `IsLocalization.Away.map` of an
injective map. -/
theorem Scheme.Hom.injective_appLE_of_eq_basicOpen (f : X ⟶ Y) {U : Y.Opens}
    {U' : X.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hle : U' ≤ f ⁻¹ᵁ U)
    (hinj : Function.Injective (f.appLE U U' hle).hom) (σ : Γ(Y, U))
    {O : Y.Opens} {O' : X.Opens} (hO : O = Y.basicOpen σ)
    (hO' : O' = X.basicOpen ((f.appLE U U' hle).hom σ)) (hleO : O' ≤ f ⁻¹ᵁ O) :
    Function.Injective (f.appLE O O' hleO).hom := by
  subst hO hO'
  haveI := hU.isLocalization_basicOpen σ
  haveI := hU'.isLocalization_basicOpen ((f.appLE U U' hle).hom σ)
  have he : f.appLE (Y.basicOpen σ) (X.basicOpen ((f.appLE U U' hle).hom σ)) hleO =
      CommRingCat.ofHom (IsLocalization.Away.map _ _ (f.appLE U U' hle).hom σ) :=
    IsAffineOpen.appLE_eq_away_map f hU hU' hle σ
  rw [he]
  exact (IsLocalization.Away.map_injective_iff
      (Q := Γ(X, X.basicOpen ((f.appLE U U' hle).hom σ)))
      (f.appLE U U' hle).hom σ).mpr
    fun a ha => ⟨0, by rw [pow_zero, one_mul]; exact hinj (ha.trans (map_zero _).symm)⟩

/-- **The unit reconstruction** (the heart of the RE-5 unit descent): let `g` be a unit
on (an open equal to) `D(f^*σ)`. Suppose the descended fraction data are in hand — an
ambient `u` on the `Y`-side with the clearing certificate
`(f^*u)|_{O'} = (f^*σ)^N|_{O'} · g` and a `v` with the two-sided ambient certificate
`u·v·σ^e = σ^(e+N+N')` (over `Y`!). Then `g` is the `f^*`-image of a unit on `D(σ)`,
namely `u|_O · (σ|_O)^{-N}`. -/
theorem Scheme.Hom.exists_unit_val_appLE_eq (f : X ⟶ Y) {U : Y.Opens} {U' : X.Opens}
    (hle : U' ≤ f ⁻¹ᵁ U) (σ u v : Γ(Y, U)) (N N' e : ℕ)
    (hE3 : u * v * σ ^ e = σ ^ (e + N + N'))
    {O : Y.Opens} {O' : X.Opens} (hO : O = Y.basicOpen σ) (hOU : O ≤ U)
    (hO'U' : O' ≤ U') (hleO : O' ≤ f ⁻¹ᵁ O) (g : Γ(X, O')ˣ)
    (hE1 : X.resHom hO'U' ((f.appLE U U' hle).hom u) =
      X.resHom hO'U' ((f.appLE U U' hle).hom σ) ^ N * (g : Γ(X, O'))) :
    ∃ ĝ : Γ(Y, O)ˣ, (f.appLE O O' hleO).hom (ĝ : Γ(Y, O)) = (g : Γ(X, O')) := by
  -- the restricted `σ` is a unit on the `Y`-side
  obtain ⟨s, hs_val⟩ : ∃ s : Γ(Y, O)ˣ, (s : Γ(Y, O)) = Y.resHom hOU σ :=
    ⟨(Y.isUnit_resHom_of_eq_basicOpen σ hO hOU).unit,
      (Y.isUnit_resHom_of_eq_basicOpen σ hO hOU).unit_spec⟩
  have hsw : Y.resHom hOU σ * ((s⁻¹ : Γ(Y, O)ˣ) : Γ(Y, O)) = 1 := by
    rw [← hs_val]
    exact s.mul_inv
  -- the restricted two-sided certificate
  have hres : Y.resHom hOU u * Y.resHom hOU v * Y.resHom hOU σ ^ e =
      Y.resHom hOU σ ^ (e + N + N') := by
    have h := congrArg (Y.resHom hOU) hE3
    rwa [map_mul, map_mul, map_pow, map_pow] at h
  -- the descended unit
  have hpow : ∀ m : ℕ,
      Y.resHom hOU σ ^ m * ((s⁻¹ : Γ(Y, O)ˣ) : Γ(Y, O)) ^ m = 1 := fun m => by
    rw [← mul_pow, hsw, one_pow]
  have hkey : (Y.resHom hOU u * ((s⁻¹ : Γ(Y, O)ˣ) : Γ(Y, O)) ^ N) *
      (Y.resHom hOU v * ((s⁻¹ : Γ(Y, O)ˣ) : Γ(Y, O)) ^ N') = 1 := by
    have h1 : (Y.resHom hOU u * Y.resHom hOU v * Y.resHom hOU σ ^ e) *
        ((s⁻¹ : Γ(Y, O)ˣ) : Γ(Y, O)) ^ (e + N + N') = 1 := by
      rw [hres, hpow]
    have h2 : (Y.resHom hOU u * Y.resHom hOU v * Y.resHom hOU σ ^ e) *
        ((s⁻¹ : Γ(Y, O)ˣ) : Γ(Y, O)) ^ (e + N + N') =
        (Y.resHom hOU u * ((s⁻¹ : Γ(Y, O)ˣ) : Γ(Y, O)) ^ N) *
          (Y.resHom hOU v * ((s⁻¹ : Γ(Y, O)ˣ) : Γ(Y, O)) ^ N') *
          (Y.resHom hOU σ ^ e * ((s⁻¹ : Γ(Y, O)ˣ) : Γ(Y, O)) ^ e) := by
      rw [pow_add, pow_add]
      ring
    rw [h2, hpow e, mul_one] at h1
    exact h1
  refine ⟨Units.mkOfMulEqOne _ _ hkey, ?_⟩
  -- the comparison certificate
  have hφs : (f.appLE O O' hleO).hom (Y.resHom hOU σ) =
      X.resHom hO'U' ((f.appLE U U' hle).hom σ) :=
    (f.appLE_resHom hOU hle hleO hO'U' σ).symm
  have hφu : (f.appLE O O' hleO).hom (Y.resHom hOU u) =
      X.resHom hO'U' ((f.appLE U U' hle).hom u) :=
    (f.appLE_resHom hOU hle hleO hO'U' u).symm
  obtain ⟨t, ht_val, ht_inv⟩ : ∃ t : Γ(X, O')ˣ,
      (t : Γ(X, O')) = (f.appLE O O' hleO).hom ((s : Γ(Y, O))) ∧
      ((t⁻¹ : Γ(X, O')ˣ) : Γ(X, O')) =
        (f.appLE O O' hleO).hom (((s⁻¹ : Γ(Y, O)ˣ) : Γ(Y, O))) :=
    ⟨Units.map (f.appLE O O' hleO).hom.toMonoidHom s, rfl, rfl⟩
  change (f.appLE O O' hleO).hom
      (Y.resHom hOU u * ((s⁻¹ : Γ(Y, O)ˣ) : Γ(Y, O)) ^ N) = (g : Γ(X, O'))
  rw [map_mul, map_pow, hφu, ← ht_inv, hE1]
  have ht_val' : (t : Γ(X, O')) = X.resHom hO'U' ((f.appLE U U' hle).hom σ) := by
    rw [ht_val, hs_val, hφs]
  have hcancel : X.resHom hO'U' ((f.appLE U U' hle).hom σ) ^ N *
      ((t⁻¹ : Γ(X, O')ˣ) : Γ(X, O')) ^ N = 1 := by
    rw [← ht_val', ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]
  calc X.resHom hO'U' ((f.appLE U U' hle).hom σ) ^ N * (g : Γ(X, O')) *
      ((t⁻¹ : Γ(X, O')ˣ) : Γ(X, O')) ^ N
      = (g : Γ(X, O')) * (X.resHom hO'U' ((f.appLE U U' hle).hom σ) ^ N *
        ((t⁻¹ : Γ(X, O')ˣ) : Γ(X, O')) ^ N) := by ring
    _ = (g : Γ(X, O')) := by rw [hcancel, mul_one]

end Away

/-! ## The chart vocabulary of the pinned cover data -/

section Chart

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

namespace BasicOpenCoverData

variable (D : BasicOpenCoverData C R π)

/-- The pinned chart (on the base curve) of a datum index: `V₀` for chart-0 indices,
`V₁` for chart-1 indices. -/
noncomputable def chartAt : D.index → C.left.Opens :=
  Sum.elim (fun _ => (fiberTwoCover π).V₀) (fun _ => (fiberTwoCover π).V₁)

@[simp]
lemma chartAt_inl (j : D.J₀) : D.chartAt (Sum.inl j) = (fiberTwoCover π).V₀ := rfl

@[simp]
lemma chartAt_inr (j : D.J₁) : D.chartAt (Sum.inr j) = (fiberTwoCover π).V₁ := rfl

lemma isAffineOpen_chartAt (i : D.index) : IsAffineOpen (D.chartAt i) := by
  cases i with
  | inl j => exact (fiberTwoCover π).isAffineOpen₀
  | inr j => exact (fiberTwoCover π).isAffineOpen₁

/-- Pairwise chart intersections are affine (the four cases of the two pinned
charts). -/
lemma isAffineOpen_chartAt_inf (i j : D.index) :
    IsAffineOpen (D.chartAt i ⊓ D.chartAt j) := by
  have h10 : IsAffineOpen ((fiberTwoCover π).V₁ ⊓ (fiberTwoCover π).V₀) := by
    rw [inf_comm]
    exact (fiberTwoCover π).isAffineOpen_inf
  cases i <;> cases j <;>
    simp only [chartAt_inl, chartAt_inr, inf_idem] <;>
    first
      | exact (fiberTwoCover π).isAffineOpen₀
      | exact (fiberTwoCover π).isAffineOpen₁
      | exact (fiberTwoCover π).isAffineOpen_inf
      | exact h10

/-- Triple chart intersections are affine (each is `V₀`, `V₁` or `V₀ ⊓ V₁` after
lattice collapse). -/
lemma isAffineOpen_chartAt_inf₃ (i j l : D.index) :
    IsAffineOpen (D.chartAt i ⊓ D.chartAt j ⊓ D.chartAt l) := by
  cases i <;> cases j <;> cases l <;>
    simp only [chartAt_inl, chartAt_inr, inf_idem, inf_left_idem, inf_comm,
      inf_left_comm] <;>
    first
      | exact (fiberTwoCover π).isAffineOpen₀
      | exact (fiberTwoCover π).isAffineOpen₁
      | exact (fiberTwoCover π).isAffineOpen_inf

/-- The generator of a datum index, retyped on the preimage of its chart. -/
noncomputable def genAt :
    ∀ i : D.index, Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ D.chartAt i)
  | Sum.inl j => D.h₀ j
  | Sum.inr j => D.h₁ j

/-- The pieces are the basic opens of the retyped generators. -/
lemma pieces_eq_basicOpen_genAt (i : D.index) :
    D.pieces i = (relCurve C R).basicOpen (D.genAt i) := by
  cases i <;> rfl

/-- Each piece sits inside the preimage of its chart. -/
lemma pieces_le_preimage_chartAt (i : D.index) :
    D.pieces i ≤ (fst C (overSpec k R)).left ⁻¹ᵁ D.chartAt i := by
  rw [D.pieces_eq_basicOpen_genAt i]
  exact Scheme.basicOpen_le _ _

/-- **The pairwise overlap generator**: the product of the two restricted generators on
the preimage of the chart intersection. Its basic open is the piece overlap
(`pieces_inf_eq_basicOpen_sigmaAt`). -/
noncomputable def sigmaAt (i j : D.index) :
    Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ (D.chartAt i ⊓ D.chartAt j)) :=
  (relCurve C R).resHom
      (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left inf_le_left) (D.genAt i) *
    (relCurve C R).resHom
      (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left inf_le_right) (D.genAt j)

/-- **The triple overlap generator**. -/
noncomputable def sigma₃At (i j l : D.index) :
    Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ
      (D.chartAt i ⊓ D.chartAt j ⊓ D.chartAt l)) :=
  (relCurve C R).resHom
      (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left
        (inf_le_left.trans inf_le_left)) (D.genAt i) *
    (relCurve C R).resHom
      (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left
        (inf_le_left.trans inf_le_right)) (D.genAt j) *
    (relCurve C R).resHom
      (Scheme.Hom.preimage_mono (fst C (overSpec k R)).left inf_le_right) (D.genAt l)

/-- **The pairwise-overlap normal form** (worksheet §3.2 basic-open normalization):
the overlap of two pieces is the basic open of `sigmaAt` under the affine ambient
`fst⁻¹(chartAt i ⊓ chartAt j)`. -/
lemma pieces_inf_eq_basicOpen_sigmaAt (i j : D.index) :
    D.pieces i ⊓ D.pieces j = (relCurve C R).basicOpen (D.sigmaAt i j) := by
  rw [sigmaAt, Scheme.basicOpen_mul, Scheme.basicOpen_resHom, Scheme.basicOpen_resHom,
    D.pieces_eq_basicOpen_genAt i, D.pieces_eq_basicOpen_genAt j]
  refine le_antisymm (le_inf (le_inf ?_ inf_le_left) (le_inf ?_ inf_le_right))
    (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  · refine le_trans (inf_le_inf (Scheme.basicOpen_le _ _) (Scheme.basicOpen_le _ _)) ?_
    rw [Scheme.Hom.preimage_inf]
  · refine le_trans (inf_le_inf (Scheme.basicOpen_le _ _) (Scheme.basicOpen_le _ _)) ?_
    rw [Scheme.Hom.preimage_inf]

/-- **The triple-overlap normal form**. -/
lemma pieces_inf₃_eq_basicOpen_sigma₃At (i j l : D.index) :
    D.pieces i ⊓ D.pieces j ⊓ D.pieces l =
      (relCurve C R).basicOpen (D.sigma₃At i j l) := by
  rw [sigma₃At, Scheme.basicOpen_mul, Scheme.basicOpen_mul, Scheme.basicOpen_resHom,
    Scheme.basicOpen_resHom, Scheme.basicOpen_resHom,
    D.pieces_eq_basicOpen_genAt i, D.pieces_eq_basicOpen_genAt j,
    D.pieces_eq_basicOpen_genAt l]
  have hle : (relCurve C R).basicOpen (D.genAt i) ⊓
      (relCurve C R).basicOpen (D.genAt j) ⊓ (relCurve C R).basicOpen (D.genAt l) ≤
      (fst C (overSpec k R)).left ⁻¹ᵁ (D.chartAt i ⊓ D.chartAt j ⊓ D.chartAt l) := by
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf]
    exact inf_le_inf (inf_le_inf (Scheme.basicOpen_le _ _) (Scheme.basicOpen_le _ _))
      (Scheme.basicOpen_le _ _)
  refine le_antisymm
    (le_inf (le_inf (le_inf hle (inf_le_left.trans inf_le_left))
      (le_inf hle (inf_le_left.trans inf_le_right))) (le_inf hle inf_le_right)) ?_
  exact le_inf
    (le_inf ((inf_le_left.trans inf_le_left).trans inf_le_right)
      ((inf_le_left.trans inf_le_right).trans inf_le_right))
    (inf_le_right.trans inf_le_right)

end BasicOpenCoverData

/-! ## Constructor congruence -/

/-- **Constructor congruence for the cocycle datum**: two data with the same cover data
and pointwise-equal transition units are equal (the cocycle laws are proofs). This is
the shape of the RE-5 descent certificate after the cover-data components have been
substituted. -/
lemma BasicOpenCocycleDatum.ext_units {cov : BasicOpenCoverData C R π}
    {u₁ u₂ : ∀ i j : cov.index, Γ(relCurve C R, cov.pieces i ⊓ cov.pieces j)ˣ}
    {c₁ : Scheme.IsGluingCocycle cov.pieces u₁} {c₂ : Scheme.IsGluingCocycle cov.pieces u₂}
    (h : ∀ i j, u₁ i j = u₂ i j) :
    (⟨cov, u₁, c₁⟩ : BasicOpenCocycleDatum C R π) = ⟨cov, u₂, c₂⟩ := by
  obtain rfl : u₁ = u₂ := funext fun i => funext fun j => h i j
  rfl

end Chart

end AlgebraicGeometry
