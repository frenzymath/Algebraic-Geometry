/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.SectionsBaseChange

/-!
# Two-factor product charts on `X ⊗ T` (deg-D4b, brick B2)

For two objects `X, T` of `Over (Spec k)` (`k` a field) and opens `U ⊆ X.left`,
`V ⊆ T.left`, this file builds the **product chart**

`𝔚 U V := (fst X T).left ⁻¹ᵁ U ⊓ (snd X T).left ⁻¹ᵁ V ⊆ (X ⊗ T).left`

and, for `U`, `V` affine, provides the D5 kit of `informal/deg-d4b-worksheet.md`:

* **(i)** `𝔚 U V` is an affine open (`Over.isAffineOpen_productChart`);
* **(ii)** the sections identification `Γ(U) ⊗[k] Γ(V) ≃+* Γ(𝔚 U V)`
  (`Over.productChartSections`, in `CommRingCat`: `Over.productChartSectionsIso`), sending a
  pure tensor `s ⊗ₜ t` to the product `fst^♯ s * snd^♯ t` of the two projection pullbacks
  (`productChartSections_tmul` and the two half-rules), compatible with restriction in BOTH
  factors (`productChartSections_naturality`) and with the `k`-algebra structures
  (`productChartSections_algebraMap`, packaged as `productChartSectionsAlgEquiv`);
* **(iii)** the **lift-app rule**: for any `q : Z ⟶ X ⊗ T` in `Over (Spec k)` with
  `q ≫ fst = a` and `q ≫ snd = b`, the pullback `q^♯` on the chart sends the identified
  `s ⊗ₜ t` to `a^♯ s * b^♯ t` (`Over.appLE_productChartSections_tmul`, specialized to
  `lift a b` in `Over.appLE_productChartSections_tmul_lift`), with the difference shape
  `s ⊗ₜ 1 - 1 ⊗ₜ t ↦ a^♯ s - b^♯ t` (`Over.appLE_productChartSections_sub`) — the exact
  input shape of the B1 regularity engine (`AlgebraicJacobian.Diagonal.diagGen`).

The B4-facing basic-open seam is packaged as
`Over.isLocalization_away_basicOpen_productChartSections`: for `x : Γ(U) ⊗[k] Γ(V)`, the
sections over the basic open of the identified section `productChartSections x` are a
localization of `Γ(U) ⊗[k] Γ(V)` away from `x` — the abstract `IsLocalization.Away` target
that `AlgebraicJacobian.Diagonal.ker_map_localization_eq` (B0, deliverable (c)) is stated
over, so the chart sections plug in directly.

## Main declarations

* `AlgebraicGeometry.Over.productChart` — the product chart `𝔚 U V`, with the access lemmas
  `productChart_def`, `productChart_le_fst_preimage`, `productChart_le_snd_preimage`,
  `mem_productChart`, `productChart_mono` and the two lift-preimage bounds
  `preimage_productChart_le_fst`, `preimage_productChart_le_snd`.
* `AlgebraicGeometry.Over.isAffineOpen_productChart` — (i).
* `AlgebraicGeometry.Over.isPushout_productChartSections`,
  `Over.isPushout_algebraMap_productChart` — the master pushout square of section rings and
  its re-cornering to `k`.
* `AlgebraicGeometry.Over.productChartSectionsIso`, `Over.productChartSections`,
  `Over.productChartSectionsAlgEquiv` — (ii), with computation rules
  `productChartSections_tmul_one`, `productChartSections_one_tmul`,
  `productChartSections_tmul`, `productChartSections_algebraMap` and the restriction seam
  `productChartSections_naturality`.
* `AlgebraicGeometry.Over.appLE_productChartSections_tmul`,
  `Over.appLE_productChartSections_tmul_lift`, `Over.appLE_productChartSections_sub` — (iii).
* `AlgebraicGeometry.Over.basicOpen_productChartSections_tmul`,
  `Over.isAffineOpen_basicOpen_productChartSections`,
  `Over.isLocalization_away_basicOpen_productChartSections` — the basic-open interface.

## Design notes

* **No flatness, no properness, no smoothness.** Everything rests on the affine case of
  mathlib's `pushoutSection` (`isIso_pushoutSection_of_isAffineOpen`), through the single
  bridge `Over.isPullback_left` between the cartesian-monoidal `⊗` of `Over (Spec k)` and
  scheme-level pullbacks; `tensorObj` is never unfolded.
* **The `k`-algebra structures on section rings** are `Over.sectionsAlgebra`
  (`Cohomology/SectionsBaseChange.lean`), a `local instance` reactivated here; the tensor
  products are formed with respect to them, and consumers (B4/B5 of the diagonal campaign)
  must reactivate the same instance for the statements to elaborate identically.
* Kernel discipline: `productChart` and the two isos are `def`s consumed only through the
  named lemmas of this file; nothing downstream should unfold them.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

namespace Over

variable {k : Type u} [Field k]
variable (X T : Over (Spec (.of k)))

-- The `k`-algebra structure on sections of objects over `Spec k`, by pullback along the
-- structure morphism (`Cohomology/SectionsBaseChange.lean`).
attribute [local instance] Over.sectionsAlgebra

/-! ## The product chart -/

/-- **The product chart.** For opens `U ⊆ X.left` and `V ⊆ T.left`, the open
`𝔚 U V := fst ⁻¹ U ⊓ snd ⁻¹ V` of the product `(X ⊗ T).left`. Consumed only through the
named lemmas below (`productChart_def`, the `≤`-access lemmas, `mem_productChart`). -/
noncomputable def productChart (U : X.left.Opens) (V : T.left.Opens) : (X ⊗ T).left.Opens :=
  (fst X T).left ⁻¹ᵁ U ⊓ (snd X T).left ⁻¹ᵁ V

/-- Unfolding lemma for `Over.productChart`. -/
lemma productChart_def (U : X.left.Opens) (V : T.left.Opens) :
    productChart X T U V = (fst X T).left ⁻¹ᵁ U ⊓ (snd X T).left ⁻¹ᵁ V :=
  rfl

/-- The product chart lies in the first-projection preimage of its first factor. -/
lemma productChart_le_fst_preimage (U : X.left.Opens) (V : T.left.Opens) :
    productChart X T U V ≤ (fst X T).left ⁻¹ᵁ U :=
  inf_le_left

/-- The product chart lies in the second-projection preimage of its second factor. -/
lemma productChart_le_snd_preimage (U : X.left.Opens) (V : T.left.Opens) :
    productChart X T U V ≤ (snd X T).left ⁻¹ᵁ V :=
  inf_le_right

/-- Membership in the product chart is membership of the two projections. -/
lemma mem_productChart {U : X.left.Opens} {V : T.left.Opens} {z : (X ⊗ T).left} :
    z ∈ productChart X T U V ↔
      (fst X T).left.base z ∈ U ∧ (snd X T).left.base z ∈ V :=
  Iff.rfl

/-- The product chart is monotone in both factors. -/
lemma productChart_mono {U U' : X.left.Opens} {V V' : T.left.Opens} (hU : U' ≤ U)
    (hV : V' ≤ V) : productChart X T U' V' ≤ productChart X T U V :=
  inf_le_inf ((fst X T).left.preimage_mono hU) ((snd X T).left.preimage_mono hV)

variable {X T} in
/-- For `q : Z ⟶ X ⊗ T` over `Spec k` with first component `a = q ≫ fst`, the `q`-preimage
of the product chart lies in the `a`-preimage of the first factor. -/
lemma preimage_productChart_le_fst {Z : Over (Spec (.of k))} {q : Z ⟶ X ⊗ T} {a : Z ⟶ X}
    (ha : q ≫ fst X T = a) (U : X.left.Opens) (V : T.left.Opens) :
    q.left ⁻¹ᵁ productChart X T U V ≤ a.left ⁻¹ᵁ U := by
  subst ha
  refine (q.left.preimage_mono (productChart_le_fst_preimage X T U V)).trans ?_
  rw [Over.comp_left, Scheme.Hom.comp_preimage]

variable {X T} in
/-- For `q : Z ⟶ X ⊗ T` over `Spec k` with second component `b = q ≫ snd`, the `q`-preimage
of the product chart lies in the `b`-preimage of the second factor. -/
lemma preimage_productChart_le_snd {Z : Over (Spec (.of k))} {q : Z ⟶ X ⊗ T} {b : Z ⟶ T}
    (hb : q ≫ snd X T = b) (U : X.left.Opens) (V : T.left.Opens) :
    q.left ⁻¹ᵁ productChart X T U V ≤ b.left ⁻¹ᵁ V := by
  subst hb
  refine (q.left.preimage_mono (productChart_le_snd_preimage X T U V)).trans ?_
  rw [Over.comp_left, Scheme.Hom.comp_preimage]

/-! ## Affineness of the product chart (D5 (i)) -/

/-- **The product chart of two affine opens is affine.** The restriction of the product to
`𝔚 U V` is the scheme pullback of the restrictions to `U` and `V` over the affine base
(`Scheme.Hom.isPullback_resLE` applied to the product square `Over.isPullback_left`), and a
pullback of affines over an affine is affine. -/
theorem isAffineOpen_productChart {U : X.left.Opens} {V : T.left.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : IsAffineOpen (productChart X T U V) := by
  haveI : IsAffine _ := hU
  haveI : IsAffine _ := hV
  haveI : IsAffine _ := isAffineOpen_top (Spec (.of k))
  exact IsAffine.of_isIso
    (Scheme.Hom.isPullback_resLE (Over.isPullback_left X T)
      (le_top.trans (Scheme.Hom.preimage_top T.hom).ge)
      (le_top.trans (Scheme.Hom.preimage_top X.hom).ge)
      (productChart_def X T U V)).isoPullback.hom

/-! ## The sections pushout square -/

/-- **The master pushout square on sections.** For affine opens `U ⊆ X.left`, `V ⊆ T.left`,
the square of section rings

```
Γ(Spec k, ⊤) ⟶ Γ(X.left, U)
     |               |
     ↓               ↓
Γ(T.left, V) ⟶ Γ((X ⊗ T).left, 𝔚 U V)
```

is a pushout of commutative rings — the affine case of mathlib's `pushoutSection` applied to
the product square `Over.isPullback_left`; no flatness is needed. -/
theorem isPushout_productChartSections {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsPushout (X.hom.appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top X.hom).ge))
      (T.hom.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top T.hom).ge))
      ((fst X T).left.appLE U (productChart X T U V) (productChart_le_fst_preimage X T U V))
      ((snd X T).left.appLE V (productChart X T U V)
        (productChart_le_snd_preimage X T U V)) := by
  have h := isIso_pushoutSection_of_isAffineOpen (Over.isPullback_left X T)
    (le_top.trans (Scheme.Hom.preimage_top T.hom).ge)
    (le_top.trans (Scheme.Hom.preimage_top X.hom).ge)
    (productChart_def X T U V) (isAffineOpen_top _) hV hU
  exact (isIso_pushoutSection_iff _ _ _ _).mp h

/-- The pushout square re-cornered to `k`: the `Γ(Spec k, ⊤)` corner is replaced by `k`
along `ΓSpecIso`, turning the two structure-map edges into the `Over.sectionsAlgebra`
algebra structure maps. -/
theorem isPushout_algebraMap_productChart {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsPushout (CommRingCat.ofHom (algebraMap k Γ(X.left, U)))
      (CommRingCat.ofHom (algebraMap k Γ(T.left, V)))
      ((fst X T).left.appLE U (productChart X T U V) (productChart_le_fst_preimage X T U V))
      ((snd X T).left.appLE V (productChart X T U V)
        (productChart_le_snd_preimage X T U V)) := by
  refine (isPushout_productChartSections X T hU hV).of_iso
    (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [Over.ofHom_algebraMap_sections, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [Over.ofHom_algebraMap_sections, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-! ## The sections identification (D5 (ii)) -/

/-- **The sections identification** (in `CommRingCat`): for affine opens `U ⊆ X.left`,
`V ⊆ T.left`, `Γ(U) ⊗[k] Γ(V) ≅ Γ((X ⊗ T).left, 𝔚 U V)`. The `k`-algebra structures on the
factors are `Over.sectionsAlgebra`. -/
noncomputable def productChartSectionsIso {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    CommRingCat.of (Γ(X.left, U) ⊗[k] Γ(T.left, V)) ≅
      Γ((X ⊗ T).left, productChart X T U V) :=
  (CommRingCat.isPushout_tensorProduct k Γ(X.left, U) Γ(T.left, V)).isoIsPushout _ _
    (isPushout_algebraMap_productChart X T hU hV)

/-- **The sections identification, as a ring equivalence**
`Γ(U) ⊗[k] Γ(V) ≃+* Γ((X ⊗ T).left, 𝔚 U V)`, sending `s ⊗ₜ t` to the product of the two
projection pullbacks (`productChartSections_tmul`). -/
noncomputable def productChartSections {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Γ(X.left, U) ⊗[k] Γ(T.left, V) ≃+* Γ((X ⊗ T).left, productChart X T U V) :=
  (productChartSectionsIso X T hU hV).commRingCatIsoToRingEquiv

/-- On `s ⊗ₜ 1` the identification is the first-projection pullback `fst^♯ s`. -/
theorem productChartSections_tmul_one {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (s : Γ(X.left, U)) :
    productChartSections X T hU hV (s ⊗ₜ 1)
      = (fst X T).left.appLE U (productChart X T U V)
          (productChart_le_fst_preimage X T U V) s :=
  congr($((CommRingCat.isPushout_tensorProduct k Γ(X.left, U)
    Γ(T.left, V)).inl_isoIsPushout_hom _ _
    (isPushout_algebraMap_productChart X T hU hV)).hom s)

/-- On `1 ⊗ₜ t` the identification is the second-projection pullback `snd^♯ t`. -/
theorem productChartSections_one_tmul {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (t : Γ(T.left, V)) :
    productChartSections X T hU hV (1 ⊗ₜ t)
      = (snd X T).left.appLE V (productChart X T U V)
          (productChart_le_snd_preimage X T U V) t :=
  congr($((CommRingCat.isPushout_tensorProduct k Γ(X.left, U)
    Γ(T.left, V)).inr_isoIsPushout_hom _ _
    (isPushout_algebraMap_productChart X T hU hV)).hom t)

/-- **The `tmul` computation rule** (D5 (ii)): on a pure tensor `s ⊗ₜ t`, the identification
is the product `fst^♯ s * snd^♯ t` of the two projection pullbacks. -/
theorem productChartSections_tmul {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (s : Γ(X.left, U)) (t : Γ(T.left, V)) :
    productChartSections X T hU hV (s ⊗ₜ t)
      = (fst X T).left.appLE U (productChart X T U V)
          (productChart_le_fst_preimage X T U V) s *
        (snd X T).left.appLE V (productChart X T U V)
          (productChart_le_snd_preimage X T U V) t := by
  have h : (s ⊗ₜ[k] t : Γ(X.left, U) ⊗[k] Γ(T.left, V)) = (s ⊗ₜ 1) * (1 ⊗ₜ t) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, productChartSections_tmul_one, productChartSections_one_tmul]

/-! ## The `k`-algebra face -/

private lemma appLE_congr_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (U : Z.Opens)
    (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

/-- The `Over.sectionsAlgebra` structure maps intertwine the first-projection pullback to
the product chart: `fst^♯ ∘ algebraMap = algebraMap` on sections. -/
theorem ofHom_algebraMap_sections_comp_appLE_fst (U : X.left.Opens) (V : T.left.Opens) :
    CommRingCat.ofHom (algebraMap k Γ(X.left, U)) ≫
        (fst X T).left.appLE U (productChart X T U V) (productChart_le_fst_preimage X T U V)
      = CommRingCat.ofHom (algebraMap k Γ((X ⊗ T).left, productChart X T U V)) := by
  rw [Over.ofHom_algebraMap_sections, Over.ofHom_algebraMap_sections, Category.assoc,
    Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (Over.w (fst X T))]

/-- The identification intertwines the `k`-algebra structure maps (the tensor algebra map
on the left, `Over.sectionsAlgebra` of the product on the right). -/
theorem productChartSections_algebraMap {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (r : k) :
    productChartSections X T hU hV (algebraMap k (Γ(X.left, U) ⊗[k] Γ(T.left, V)) r)
      = algebraMap k Γ((X ⊗ T).left, productChart X T U V) r := by
  rw [Algebra.TensorProduct.algebraMap_apply, productChartSections_tmul_one]
  exact congr($(ofHom_algebraMap_sections_comp_appLE_fst X T U V).hom r)

/-- **The sections identification as a `k`-algebra equivalence**
`Γ(U) ⊗[k] Γ(V) ≃ₐ[k] Γ((X ⊗ T).left, 𝔚 U V)` (all `k`-algebra structures are
`Over.sectionsAlgebra`) — the face through which the étale-coordinate `k[u]`-data of the
diagonal campaign transports. -/
noncomputable def productChartSectionsAlgEquiv {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (Γ(X.left, U) ⊗[k] Γ(T.left, V)) ≃ₐ[k] Γ((X ⊗ T).left, productChart X T U V) :=
  AlgEquiv.ofRingEquiv (f := productChartSections X T hU hV)
    (productChartSections_algebraMap X T hU hV)

@[simp]
lemma productChartSectionsAlgEquiv_apply {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (x : Γ(X.left, U) ⊗[k] Γ(T.left, V)) :
    productChartSectionsAlgEquiv X T hU hV x = productChartSections X T hU hV x :=
  rfl

/-! ## Restriction naturality (D5 (ii), the B4/B5 seam) -/

set_option backward.isDefEq.respectTransparency false in
/-- **Restriction naturality of the identification, in both factors**: for affine opens
`U' ≤ U` of `X.left` and `V' ≤ V` of `T.left`, restricting the identified section to
`𝔚 U' V'` is identifying the factorwise-restricted tensor. The map on tensor products is
`Algebra.TensorProduct.map` of the two restrictions `Over.resAlgHom`. -/
theorem productChartSections_naturality {U U' : X.left.Opens} {V V' : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hU' : IsAffineOpen U')
    (hV' : IsAffineOpen V') (hUU : U' ≤ U) (hVV : V' ≤ V)
    (x : Γ(X.left, U) ⊗[k] Γ(T.left, V)) :
    (X ⊗ T).left.presheaf.map (homOfLE (productChart_mono X T hUU hVV)).op
        (productChartSections X T hU hV x)
      = productChartSections X T hU' hV'
          (Algebra.TensorProduct.map (Over.resAlgHom X hUU) (Over.resAlgHom T hVV) x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s t =>
    rw [Algebra.TensorProduct.map_tmul, Over.resAlgHom_apply, Over.resAlgHom_apply,
      productChartSections_tmul, productChartSections_tmul, map_mul]
    congr 1
    · rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, ← CommRingCat.comp_apply,
        Scheme.Hom.map_appLE]
    · rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, ← CommRingCat.comp_apply,
        Scheme.Hom.map_appLE]

/-! ## The lift-app rule (D5 (iii)) -/

variable {X T} in
/-- **The lift-app rule.** For `q : Z ⟶ X ⊗ T` in `Over (Spec k)` with components
`a = q ≫ fst` and `b = q ≫ snd`, the pullback of sections along `q` from the product chart
to any open `W ≤ q⁻¹(𝔚 U V)` sends the identified pure tensor `s ⊗ₜ t` to `a^♯ s * b^♯ t`.
This subsumes the diagonal `δ C = lift (𝟙 C) (𝟙 C)` (where the app is the multiplication)
and the graph lifts `lift (fst C T) (snd C T ≫ t)` of deg-D4c. -/
theorem appLE_productChartSections_tmul {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) {Z : Over (Spec (.of k))} {q : Z ⟶ X ⊗ T}
    {a : Z ⟶ X} {b : Z ⟶ T} (ha : q ≫ fst X T = a) (hb : q ≫ snd X T = b)
    {W : Z.left.Opens} (hW : W ≤ q.left ⁻¹ᵁ productChart X T U V)
    (hWa : W ≤ a.left ⁻¹ᵁ U) (hWb : W ≤ b.left ⁻¹ᵁ V) (s : Γ(X.left, U))
    (t : Γ(T.left, V)) :
    q.left.appLE (productChart X T U V) W hW (productChartSections X T hU hV (s ⊗ₜ t))
      = a.left.appLE U W hWa s * b.left.appLE V W hWb t := by
  subst ha hb
  rw [productChartSections_tmul, map_mul, ← CommRingCat.comp_apply,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  rfl

variable {X T} in
/-- The lift-app rule for a cartesian-monoidal `lift a b : Z ⟶ X ⊗ T`: the app of
`lift a b` on the product chart sends the identified `s ⊗ₜ t` to `a^♯ s * b^♯ t`. -/
theorem appLE_productChartSections_tmul_lift {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) {Z : Over (Spec (.of k))} (a : Z ⟶ X)
    (b : Z ⟶ T) {W : Z.left.Opens} (hW : W ≤ (lift a b).left ⁻¹ᵁ productChart X T U V)
    (hWa : W ≤ a.left ⁻¹ᵁ U) (hWb : W ≤ b.left ⁻¹ᵁ V) (s : Γ(X.left, U))
    (t : Γ(T.left, V)) :
    (lift a b).left.appLE (productChart X T U V) W hW
        (productChartSections X T hU hV (s ⊗ₜ t))
      = a.left.appLE U W hWa s * b.left.appLE V W hWb t :=
  appLE_productChartSections_tmul hU hV (lift_fst a b) (lift_snd a b) hW hWa hWb s t

variable {X T} in
/-- **The difference shape of the lift-app rule** (the B1 regularity engine's exact input,
`AlgebraicJacobian.Diagonal.diagGen`-style): the app of `q` on the product chart sends the
identified `s ⊗ₜ 1 - 1 ⊗ₜ t` to the difference `a^♯ s - b^♯ t` of the two component
pullbacks. Specialized to the diagonal lift this is `u ⊗ 1 - 1 ⊗ u ↦ fst^♯ u - snd^♯ u`. -/
theorem appLE_productChartSections_sub {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) {Z : Over (Spec (.of k))} {q : Z ⟶ X ⊗ T}
    {a : Z ⟶ X} {b : Z ⟶ T} (ha : q ≫ fst X T = a) (hb : q ≫ snd X T = b)
    {W : Z.left.Opens} (hW : W ≤ q.left ⁻¹ᵁ productChart X T U V)
    (hWa : W ≤ a.left ⁻¹ᵁ U) (hWb : W ≤ b.left ⁻¹ᵁ V) (s : Γ(X.left, U))
    (t : Γ(T.left, V)) :
    q.left.appLE (productChart X T U V) W hW
        (productChartSections X T hU hV (s ⊗ₜ 1 - 1 ⊗ₜ t))
      = a.left.appLE U W hWa s - b.left.appLE V W hWb t := by
  rw [map_sub, map_sub, appLE_productChartSections_tmul hU hV ha hb hW hWa hWb,
    appLE_productChartSections_tmul hU hV ha hb hW hWa hWb, map_one, map_one, mul_one,
    one_mul]

/-! ## Basic opens of identified sections (the B4 seam) -/

/-- The basic open of an identified pure tensor is the product chart of the two factor
basic opens: `D(fst^♯ s * snd^♯ t) = 𝔚 (D s) (D t)`. -/
theorem basicOpen_productChartSections_tmul {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (s : Γ(X.left, U)) (t : Γ(T.left, V)) :
    (X ⊗ T).left.basicOpen (productChartSections X T hU hV (s ⊗ₜ t))
      = productChart X T (X.left.basicOpen s) (T.left.basicOpen t) := by
  have hc : (fst X T).left ⁻¹ᵁ X.left.basicOpen s ≤ (fst X T).left ⁻¹ᵁ U :=
    (fst X T).left.preimage_mono (X.left.basicOpen_le s)
  have hd : (snd X T).left ⁻¹ᵁ T.left.basicOpen t ≤ (snd X T).left ⁻¹ᵁ V :=
    (snd X T).left.preimage_mono (T.left.basicOpen_le t)
  rw [productChartSections_tmul, Scheme.basicOpen_mul, Scheme.basicOpen_appLE,
    Scheme.basicOpen_appLE, productChart_def, productChart_def]
  refine le_antisymm (inf_le_inf inf_le_right inf_le_right)
    (le_inf (le_inf (le_inf (inf_le_left.trans hc) (inf_le_right.trans hd)) inf_le_left)
      (le_inf (le_inf (inf_le_left.trans hc) (inf_le_right.trans hd)) inf_le_right))

/-- Basic opens of the product chart are affine (for affine factors). -/
theorem isAffineOpen_basicOpen_productChartSections {U : X.left.Opens} {V : T.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (x : Γ(X.left, U) ⊗[k] Γ(T.left, V)) :
    IsAffineOpen ((X ⊗ T).left.basicOpen (productChartSections X T hU hV x)) :=
  (isAffineOpen_productChart X T hU hV).basicOpen _

/-- **Sections over the basic open of an identified section are a localization of the
tensor ring** (the B4 splice): for `x : Γ(U) ⊗[k] Γ(V)`, the sections over
`D(productChartSections x) ⊆ 𝔚 U V`, as an algebra over `Γ(U) ⊗[k] Γ(V)` through the
identification followed by restriction, are `IsLocalization.Away x` — the abstract target
of the B0 statement `AlgebraicJacobian.Diagonal.ker_map_localization_eq`. -/
theorem isLocalization_away_basicOpen_productChartSections {U : X.left.Opens}
    {V : T.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (x : Γ(X.left, U) ⊗[k] Γ(T.left, V)) :
    letI : Algebra (Γ(X.left, U) ⊗[k] Γ(T.left, V))
        Γ((X ⊗ T).left, (X ⊗ T).left.basicOpen (productChartSections X T hU hV x)) :=
      ((algebraMap Γ((X ⊗ T).left, productChart X T U V)
          Γ((X ⊗ T).left, (X ⊗ T).left.basicOpen (productChartSections X T hU hV x))).comp
        (productChartSections X T hU hV).toRingHom).toAlgebra
    IsLocalization.Away x
      Γ((X ⊗ T).left, (X ⊗ T).left.basicOpen (productChartSections X T hU hV x)) := by
  letI : Algebra (Γ(X.left, U) ⊗[k] Γ(T.left, V))
      Γ((X ⊗ T).left, (X ⊗ T).left.basicOpen (productChartSections X T hU hV x)) :=
    ((algebraMap Γ((X ⊗ T).left, productChart X T U V)
        Γ((X ⊗ T).left, (X ⊗ T).left.basicOpen (productChartSections X T hU hV x))).comp
      (productChartSections X T hU hV).toRingHom).toAlgebra
  haveI := (isAffineOpen_productChart X T hU hV).isLocalization_basicOpen
    (productChartSections X T hU hV x)
  exact IsLocalization.of_ringEquiv_left (productChartSections X T hU hV)
    (Submonoid.map_powers _ x) (fun _ => rfl)

end Over

end AlgebraicGeometry
