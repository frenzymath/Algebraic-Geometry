/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.Sections

/-!
# The rigidity lemma

This file proves the **rigidity lemma** for schemes over an algebraically closed field
(Mumford, *Abelian Varieties*, §II.4 p. 43, "Form I"; Milne, *Abelian Varieties*, I Thm 1.1):
if `X` is proper and geometrically integral over `K`, the product `X ⊗ Y` (fibre product over
`Spec K`) is integral, `Z` is separated and locally of finite type over `K`, and a `K`-morphism
`f : X ⊗ Y ⟶ Z` contracts the slice `X × {y₀}` over a `K`-point `y₀ : 𝟙_ ⟶ Y` to a `K`-point
`z₀ : 𝟙_ ⟶ Z`, then `f` factors uniquely through the second projection `snd X Y`.

Its engine application (Milne, I Cor 1.2) is proved in
`AlgebraicJacobian.AbelianVariety.RigidityCorollaries`.

## Main results

* `AlgebraicGeometry.exists_eq_comp_of_isIso_appTop_of_range_subset`: a morphism from a scheme
  `V` all of whose global sections come from the base ring (`IsIso sV.appTop`, e.g. `V` proper
  and geometrically integral over a field) into a scheme `W`, with set-theoretic image inside an
  affine open of `W`, is *constant*: it factors through the base `Spec R`.
* `AlgebraicGeometry.exists_eq_toUnit_comp_of_isIso_appTop_of_range_subset`: the same statement
  in `Over (Spec R)`, producing a point `c : 𝟙_ (Over (Spec R)) ⟶ W` with `q = toUnit V ≫ c`.
* `AlgebraicGeometry.point_ext_of_apply_closedPoint_eq`: two `K`-points of a locally finite type
  scheme over `K = K̄` agree as soon as their underlying points agree.
* `AlgebraicGeometry.isIntegral_tensorObj_left`: over a field, a product of geometrically
  integral schemes locally of finite type is integral (instance form, keyed on `(X ⊗ Y).left`).
* `AlgebraicGeometry.exists_unique_eq_snd_comp_of_isProper_of_geometricallyIntegral`:
  **the rigidity lemma**.

## Proof sketch

Let `z` be the image point of `z₀` and `U` an affine open neighbourhood of `z`. Since `X` is
proper over `K`, the projection `snd X Y` is universally closed, so
`W := snd (f⁻¹(Z ∖ U))` is closed in `Y`. For any `K`-point `yPt` of `Y` avoiding `W`, the
slice `X × {yPt}` maps into `U`; since `Γ(X, 𝒪_X) = K`
(`bijective_appTop_of_isProper_of_geometricallyIntegral`, this project) a morphism from `X`
into an affine open is constant, so `f` is constant on the slice. The distinguished point `y₀`
avoids `W`: a point of `f⁻¹(Z ∖ U)` in the fibre over `y₀` would dominate a *closed* such point
(the fibre is closed and `X ⊗ Y` is Jacobson), which corresponds to a `K`-point of the slice
`X × {y₀}` — but `f` maps that slice to `z ∈ U` by hypothesis. Hence
`S := snd⁻¹(Y ∖ W)` is a nonempty open, dense because `X ⊗ Y` is irreducible. On closed points
of `S` the morphisms `f` and `snd ≫ g`, with `g := f(x₀, ·)` for a `K`-point `x₀` of `X`, agree
by the slice constancy; since `X ⊗ Y` is reduced and `Z` is separated, they agree
(`ext_of_apply_closedPoint_eq` machinery from `Mathlib.AlgebraicGeometry.AlgClosed.Basic`).
Uniqueness holds because `snd X Y` is split by `lift (toUnit Y ≫ x₀) (𝟙 Y)`.

Compared to Mumford's Form I (`X` a complete variety, `Y`, `Z` varieties over `K = K̄`), the
hypothesis set here is honest and slightly weaker: `Y` only needs to be locally of finite type
with `X ⊗ Y` integral, and `Z` only separated and locally of finite type (no properness,
reducedness or irreducibility of `Z` is used).
-/

set_option autoImplicit false

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory.CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A morphism `p : T ⟶ X ⊗ Y` whose second component is constant with value the point
`y : 𝟙_ C ⟶ Y` factors through the slice `lift (𝟙 X) (toUnit X ≫ y) : X ⟶ X ⊗ Y` over `y`. 






 * Provenance: CUSTOM.
-/
theorem eq_comp_lift_id_of_comp_snd_eq {T X Y : C} {p : T ⟶ X ⊗ Y} {y : 𝟙_ C ⟶ Y}
    (h : p ≫ snd X Y = toUnit T ≫ y) :
    p = (p ≫ fst X Y) ≫ lift (𝟙 X) (toUnit X ≫ y) := by
  rw [comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit, ← h, lift_comp_fst_snd]

/-- If `f : X ⊗ Y ⟶ Z` is constant on the slice over the point `y : 𝟙_ C ⟶ Y` (with value the
point `c : 𝟙_ C ⟶ Z`), then `f` composed with any morphism whose second component is constant
with value `y` is constant with value `c`. 






 * Provenance: CUSTOM.
-/
theorem comp_eq_toUnit_comp_of_comp_snd_eq {T X Y Z : C} {p : T ⟶ X ⊗ Y} {y : 𝟙_ C ⟶ Y}
    {f : X ⊗ Y ⟶ Z} {c : 𝟙_ C ⟶ Z} (h : p ≫ snd X Y = toUnit T ≫ y)
    (hf : lift (𝟙 X) (toUnit X ≫ y) ≫ f = toUnit X ≫ c) :
    p ≫ f = toUnit T ≫ c := by
  rw [eq_comp_lift_id_of_comp_snd_eq h, Category.assoc, hf, ← Category.assoc, comp_toUnit]

end CategoryTheory.CartesianMonoidalCategory

namespace AlgebraicGeometry

section Constancy

set_option backward.isDefEq.respectTransparency false in
/-- **Constancy of morphisms into affines.** A morphism `q : V ⟶ W` of schemes, where all global
sections of `V` come from a base ring `R` (`IsIso sV.appTop` for a structure morphism
`sV : V ⟶ Spec R`; e.g. `V` proper and geometrically integral over a field `R`) and the
set-theoretic image of `q` is contained in an affine open `U` of `W`, is *constant*: it factors
through the base as `q = sV ≫ z` for a point `z : Spec R ⟶ W`. 






 * Provenance: ADAPTED.
-/
theorem exists_eq_comp_of_isIso_appTop_of_range_subset {V W : Scheme.{u}} {R : CommRingCat.{u}}
    (sV : V ⟶ Spec R) [IsIso sV.appTop] (q : V ⟶ W) {U : W.Opens} (hU : IsAffineOpen U)
    (hq : Set.range ⇑q ⊆ (U : Set W)) :
    ∃ z : Spec R ⟶ W, q = sV ≫ z := by
  have : IsAffine U.toScheme := hU
  -- factor `q` through the open subscheme `U`
  have hfac : IsOpenImmersion.lift U.ι q (by rwa [Scheme.Opens.range_ι]) ≫ U.ι = q :=
    IsOpenImmersion.lift_fac _ _ _
  set q' : V ⟶ U.toScheme := IsOpenImmersion.lift U.ι q (by rwa [Scheme.Opens.range_ι])
  refine ⟨(Spec R).toSpecΓ ≫ inv (Spec.map sV.appTop) ≫ Spec.map q'.appTop ≫
    U.toScheme.isoSpec.inv ≫ U.ι, ?_⟩
  have h1 : sV ≫ (Spec R).toSpecΓ ≫ inv (Spec.map sV.appTop) = V.toSpecΓ := by
    rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have h2 : V.toSpecΓ ≫ Spec.map q'.appTop ≫ U.toScheme.isoSpec.inv = q' := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  rw [reassoc_of% h1, reassoc_of% h2, hfac]

set_option backward.isDefEq.respectTransparency false in
/-- `Over`-category form of the constancy lemma
`AlgebraicGeometry.exists_eq_comp_of_isIso_appTop_of_range_subset`: a morphism `q : V ⟶ W` of
schemes over `Spec R` with `Γ(V, 𝒪_V) = R` whose image lies in an affine open of `W` factors
through a point `c : 𝟙_ (Over (Spec R)) ⟶ W`. 






 * Provenance: CUSTOM.
-/
theorem exists_eq_toUnit_comp_of_isIso_appTop_of_range_subset {R : CommRingCat.{u}}
    {V W : Over (Spec R)} [IsIso V.hom.appTop] (q : V ⟶ W) {U : W.left.Opens}
    (hU : IsAffineOpen U) (hq : Set.range ⇑q.left ⊆ (U : Set W.left)) :
    ∃ c : 𝟙_ (Over (Spec R)) ⟶ W, q = toUnit V ≫ c := by
  obtain ⟨z, hz⟩ := exists_eq_comp_of_isIso_appTop_of_range_subset V.hom q.left hU hq
  -- `z` is a section of `W.hom`: cancel `V.hom` on global sections
  have h1 : V.hom ≫ z ≫ W.hom = V.hom := by
    rw [← Category.assoc, ← hz, Over.w q]
  have h2 : (z ≫ W.hom).appTop ≫ V.hom.appTop = 𝟙 Γ(Spec R, ⊤) ≫ V.hom.appTop := by
    rw [Category.id_comp, ← Scheme.Hom.comp_appTop, h1]
  have h3 : (z ≫ W.hom).appTop = 𝟙 Γ(Spec R, ⊤) := (cancel_mono V.hom.appTop).mp h2
  have hz' : z ≫ W.hom = 𝟙 (Spec R) := by
    have h4 : (z ≫ W.hom) ≫ (Spec R).toSpecΓ = (Spec R).toSpecΓ := by
      rw [Scheme.toSpecΓ_naturality, h3, Spec.map_id, Category.comp_id]
    calc z ≫ W.hom
        = ((z ≫ W.hom) ≫ (Spec R).toSpecΓ) ≫ Spec.map (Scheme.ΓSpecIso R).inv := by
          rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
      _ = 𝟙 (Spec R) := by rw [h4, toSpecΓ_SpecMap_ΓSpecIso_inv]
  refine ⟨Over.homMk z hz', Over.OverMorphism.ext ?_⟩
  simpa using hz

end Constancy

section Points

variable {K : Type u} [Field K]

set_option backward.isDefEq.respectTransparency false in
/-- Two `K`-points (in the `Over`-category sense) of a scheme locally of finite type over an
algebraically closed field `K` are equal as soon as their underlying points agree. 






 * Provenance: CUSTOM.
-/
theorem point_ext_of_apply_closedPoint_eq [IsAlgClosed K]
    {T : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType T.hom]
    {p q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ T}
    (h : p.left (IsLocalRing.closedPoint K) = q.left (IsLocalRing.closedPoint K)) : p = q :=
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq T.hom
    (by simp) (by simp) h)

/-- A product of geometrically integral schemes locally of finite type over a field is
integral. Instance form, keyed on the monoidal product of `Over (Spec K)`. 






 * Provenance: CUSTOM.
-/
instance isIntegral_tensorObj_left {X Y : Over (Spec (CommRingCat.of K))}
    [GeometricallyIntegral X.hom] [GeometricallyIntegral Y.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    IsIntegral (X ⊗ Y).left := by
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact inferInstanceAs (IsIntegral (pullback X.hom Y.hom))

end Points

section Rigidity

variable {K : Type u} [Field K] [IsAlgClosed K]

set_option backward.isDefEq.respectTransparency false in
/-- **The rigidity lemma** (Mumford, *Abelian Varieties*, §II.4 p. 43, Form I; Milne, *Abelian
Varieties*, I Thm 1.1). Let `K` be an algebraically closed field and `X`, `Y`, `Z` schemes
over `K` with `X` proper and geometrically integral, `X ⊗ Y` integral, `Y` locally of finite
type, and `Z` separated and locally of finite type. If a `K`-morphism `f : X ⊗ Y ⟶ Z` contracts
the slice `X × {y₀}` over a `K`-point `y₀` of `Y` to a `K`-point `z₀` of `Z`, then `f` factors
uniquely through the second projection.

The integrality of `X ⊗ Y` holds automatically when `Y` is also geometrically integral
(`AlgebraicGeometry.isIntegral_tensorObj_left`). 






 * Provenance: REFERENCE.
-/
theorem exists_unique_eq_snd_comp_of_isProper_of_geometricallyIntegral
    {X Y Z : Over (Spec (CommRingCat.of K))}
    [IsProper X.hom] [GeometricallyIntegral X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral (X ⊗ Y).left] [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⊗ Y ⟶ Z) (y₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Z)
    (hf : lift (𝟙 X) (toUnit X ≫ y₀) ≫ f = toUnit X ≫ z₀) :
    ∃! g : Y ⟶ Z, f = snd X Y ≫ g := by
  -- point-set bookkeeping for the base `Spec K`
  have instSub : Subsingleton ↥(Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have instSubU : Subsingleton ↥(𝟙_ (Over (Spec (CommRingCat.of K)))).left := instSub
  have instNeU : Nonempty ↥(𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    ⟨IsLocalRing.closedPoint K⟩
  -- standing consequences of the hypotheses
  have hIsoX : IsIso X.hom.appTop := isIso_appTop_of_isProper_of_geometricallyIntegral X.hom
  have hlftXY : LocallyOfFiniteType (X ⊗ Y).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst X.hom Y.hom ≫ X.hom))
  have hJacXY : JacobsonSpace ↥(X ⊗ Y).left := LocallyOfFiniteType.jacobsonSpace (X ⊗ Y).hom
  have hJacX : JacobsonSpace ↥X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hXint : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  have hsndUC : UniversallyClosed (snd X Y).left :=
    inferInstanceAs (UniversallyClosed (pullback.snd X.hom Y.hom))
  -- a `K`-point `x₀` of `X`
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := ↥X.left))
    isOpen_univ.isLocallyClosed
  set x₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom x hx) (by simp) with hx₀def
  set g : Y ⟶ Z := lift (toUnit Y ≫ x₀) (𝟙 Y) ≫ f with hgdef
  refine ⟨g, ?_, fun g' hg' ↦ by rw [hgdef, hg', lift_snd_assoc, Category.id_comp]⟩
  -- an affine open neighbourhood `U` of the image point of `z₀`
  obtain ⟨-, ⟨U, hU, rfl⟩, hzU, -⟩ := Z.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (z₀.left (IsLocalRing.closedPoint K))) isOpen_univ
  -- the bad locus `W ⊆ Y`: the image of `f⁻¹(Z ∖ U)` under the second projection
  set A : Set ↥(X ⊗ Y).left := ⇑f.left ⁻¹' ((U : Set ↥Z.left))ᶜ with hAdef
  have hAclosed : IsClosed A := U.isOpen.isClosed_compl.preimage f.left.continuous
  set W : Set ↥Y.left := ⇑(snd X Y).left '' A with hWdef
  have hWclosed : IsClosed W := (snd X Y).left.isClosedMap A hAclosed
  -- `f` is constant on slices over `K`-points avoiding `W`
  have sliceConst : ∀ yPt : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y,
      yPt.left (IsLocalRing.closedPoint K) ∉ W →
      ∃ c : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Z,
        lift (𝟙 X) (toUnit X ≫ yPt) ≫ f = toUnit X ≫ c := by
    intro yPt hyW
    apply exists_eq_toUnit_comp_of_isIso_appTop_of_range_subset _ hU
    rintro - ⟨v, rfl⟩
    by_contra hvU
    refine hyW ⟨(lift (𝟙 X) (toUnit X ≫ yPt)).left v, ?_, ?_⟩
    · rw [hAdef, Set.mem_preimage]
      simpa [Over.comp_left, Scheme.Hom.comp_apply] using hvU
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd, Over.comp_left,
        Scheme.Hom.comp_apply, Over.toUnit_left]
      exact congr(yPt.left $(Subsingleton.elim _ _))
  -- the distinguished point avoids `W`
  have hy₀W : y₀.left (IsLocalRing.closedPoint K) ∉ W := by
    rintro ⟨a, haA, ha⟩
    have hy₀c : IsClosed {y₀.left (IsLocalRing.closedPoint K)} := by
      have : IsClosedImmersion y₀.left :=
        isClosedImmersion_of_comp_eq_id Y.hom y₀.left (by simp)
      have hr := y₀.left.isClosedEmbedding.isClosed_range
      have hconst : ∀ a : ↥(𝟙_ (Over (Spec (CommRingCat.of K)))).left,
          y₀.left a = y₀.left (IsLocalRing.closedPoint K) :=
        fun a ↦ congr(y₀.left $(Subsingleton.elim a (IsLocalRing.closedPoint K)))
      rwa [Set.range_eq_singleton hconst] at hr
    obtain ⟨p, ⟨hpA, hpsnd⟩, hp⟩ := nonempty_inter_closedPoints
      (Z := A ∩ ⇑(snd X Y).left ⁻¹' {y₀.left (IsLocalRing.closedPoint K)}) ⟨a, haA, ha⟩
      (hAclosed.inter (hy₀c.preimage (snd X Y).left.continuous)).isLocallyClosed
    set pPt : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X ⊗ Y :=
      Over.homMk (pointOfClosedPoint (X ⊗ Y).hom p hp) (by simp) with hpPtdef
    have hpPt : pPt.left (IsLocalRing.closedPoint K) = p := by simp [hpPtdef]
    have hsnd : pPt ≫ snd X Y = toUnit _ ≫ y₀ := by
      rw [toUnit_unit, Category.id_comp]
      refine point_ext_of_apply_closedPoint_eq ?_
      rw [Over.comp_left, Scheme.Hom.comp_apply, hpPt]
      exact Set.mem_singleton_iff.mp hpsnd
    have hcomp : pPt ≫ f = toUnit _ ≫ z₀ := comp_eq_toUnit_comp_of_comp_snd_eq hsnd hf
    -- evaluating at the point contradicts `p ∈ A`
    have : f.left p ∈ (U : Set ↥Z.left) := by
      have h5 : (pPt ≫ f).left (IsLocalRing.closedPoint K) = f.left p := by
        rw [Over.comp_left, Scheme.Hom.comp_apply, hpPt]
      rw [← h5, hcomp, Over.comp_left, Scheme.Hom.comp_apply]
      simpa using hzU
    exact hpA this
  -- the two sides agree on the dense open `snd⁻¹(Y ∖ W)`
  have hflft : LocallyOfFiniteType (f.left ≫ Z.hom) := by rw [Over.w f]; exact hlftXY
  have hmain : f.left = (snd X Y ≫ g).left := by
    refine ext_of_apply_eq Z.hom (⇑(snd X Y).left ⁻¹' Wᶜ)
      ((hWclosed.isOpen_compl.preimage (snd X Y).left.continuous).isLocallyClosed) ?_ ?_ ?_
    · -- density: nonempty open in an irreducible space
      refine (hWclosed.isOpen_compl.preimage (snd X Y).left.continuous).dense ?_
      refine ⟨(lift x₀ y₀).left (IsLocalRing.closedPoint K), ?_⟩
      change (snd X Y).left ((lift x₀ y₀).left (IsLocalRing.closedPoint K)) ∉ W
      have h6 : (lift x₀ y₀ ≫ snd X Y).left (IsLocalRing.closedPoint K) =
          y₀.left (IsLocalRing.closedPoint K) := by rw [lift_snd]
      rw [Over.comp_left, Scheme.Hom.comp_apply] at h6
      rwa [h6]
    · -- agreement on closed points of the dense open
      intro p hpS hp
      -- the image `y` of `p` is a closed point of `Y` avoiding `W`
      have hyc : IsClosed {(snd X Y).left p} := by
        simpa using (snd X Y).left.isClosedMap _ hp
      set yPt : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y :=
        Over.homMk (pointOfClosedPoint Y.hom _ hyc) (by simp) with hyPtdef
      have hyPt : yPt.left (IsLocalRing.closedPoint K) = (snd X Y).left p := by
        simp [hyPtdef]
      obtain ⟨c, hc⟩ := sliceConst yPt (by rw [hyPt]; exact hpS)
      -- the `K`-point over `p`
      set pPt : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X ⊗ Y :=
        Over.homMk (pointOfClosedPoint (X ⊗ Y).hom p hp) (by simp) with hpPtdef
      have hpPt : pPt.left (IsLocalRing.closedPoint K) = p := by simp [hpPtdef]
      have hsnd : pPt ≫ snd X Y = toUnit _ ≫ yPt := by
        rw [toUnit_unit, Category.id_comp]
        refine point_ext_of_apply_closedPoint_eq ?_
        rw [Over.comp_left, Scheme.Hom.comp_apply, hpPt, hyPt]
      -- `f` at `p`
      have h7 : pPt ≫ f = toUnit _ ≫ c := comp_eq_toUnit_comp_of_comp_snd_eq hsnd hc
      -- `snd ≫ g` at `p`
      have hp2 : (pPt ≫ snd X Y ≫ lift (toUnit Y ≫ x₀) (𝟙 Y)) ≫ snd X Y =
          toUnit _ ≫ yPt := by
        simp only [Category.assoc, lift_snd, Category.comp_id]
        exact hsnd
      have h8 : pPt ≫ snd X Y ≫ g = toUnit _ ≫ c := by
        have h8' := comp_eq_toUnit_comp_of_comp_snd_eq hp2 hc
        simpa only [hgdef, Category.assoc] using h8'
      -- compare underlying points
      have h9 := congrArg
        (fun q : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Z ↦ q.left (IsLocalRing.closedPoint K))
        (h7.trans h8.symm)
      simp only [Over.comp_left, Scheme.Hom.comp_apply, hpPt] at h9
      simpa only [Over.comp_left, Scheme.Hom.comp_apply] using h9
    · rw [Over.w, Over.w]
  exact Over.OverMorphism.ext hmain

end Rigidity

end AlgebraicGeometry
