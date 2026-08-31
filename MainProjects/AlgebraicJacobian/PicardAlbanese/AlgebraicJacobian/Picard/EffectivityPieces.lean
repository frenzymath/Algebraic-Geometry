/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SectionsDescent
import AlgebraicJacobian.Picard.AffineTwoCover

/-!
# `cg`-saturated affine pieces of the curve product (C2 effectivity, brick E0)

For a tower of `k`-algebras `k → A → B` and any `C` over `Spec k`, the base-change morphism
`cg : (C ⊗ Spec B).left ⟶ (C ⊗ Spec A).left` (`C ◁ Spec (ofId A B)`) — the cover inclusion
on the curve product, whose Čech-Picard pullback the (C2) effectivity brick must invert — is
an **affine** morphism (the base change of the affine `Spec B → Spec A` along the projection
`pA`), and over every **affine** open `V ⊆ (C ⊗ Spec A).left` its section ring is the base
change of `Γ(V)` along `A → B`:

`Γ((C ⊗ Spec B).left, cg⁻¹ V) ≃ₐ[Γ(V)] Γ(V) ⊗[A] B`,

faithfully flat over `Γ(V)` whenever `A → B` is.  This is the affine-open generalization of
the landed `⊤`-case `Over.sectionsTopAlgEquiv` (`Γ((C ⊗ Spec B).left, ⊤) ≃ₐ[A] B`,
`Picard/WitnessAssembly.lean`); its ring engine is the pushout-of-sections calculus of
`Picard/SectionsDescent.lean` (the private `sectionsPushoutIso`, here re-derived publicly and
packaged with the `Γ(V)`-algebra face, faithful flatness, and restriction naturality).

These are the geometric pieces the downstream (C2) effectivity bricks consume: E1/E2 build a
per-piece `Module.IsDescentCocycle` over `Γ(V) → Γ(V) ⊗[A] B` (faithful flatness is exactly
`faithfullyFlat_pieceCover`), transported through `pieceEquiv`; E3 restricts the descent data
to overlaps `W ≤ V`, which commutes with the identification by `pieceRingEquiv_naturality`.

## Main declarations

* `AlgebraicGeometry.Over.isAffineHom_cg` — `cg` is an affine morphism.
* `AlgebraicGeometry.Over.isAffineOpen_cgPreimage` — `cg⁻¹ V` is affine for affine `V`.
* `AlgebraicGeometry.Over.pieceTensorIso`, `pieceRingEquiv` — the section-ring identification
  `Γ(V) ⊗[A] B ≅ Γ((C ⊗ Spec B).left, cg⁻¹ V)` (in `CommRingCat`, resp. as a ring
  equivalence), with the computation rules `pieceRingEquiv_tmul_one`, `pieceRingEquiv_one_tmul`,
  `pieceRingEquiv_tmul`.
* `AlgebraicGeometry.Over.pieceCoverAlgebra` — the `Γ(V)`-algebra structure on `Γ(cg⁻¹ V)`
  by pullback along `cg` (a `local instance`, reactivated by consumers).
* `AlgebraicGeometry.Over.pieceEquiv` — the identification as a `Γ(V)`-algebra equivalence
  `Γ(cg⁻¹ V) ≃ₐ[Γ(V)] Γ(V) ⊗[A] B`.
* `AlgebraicGeometry.Over.faithfullyFlat_pieceCover` — `Γ(cg⁻¹ V)` is faithfully flat over
  `Γ(V)` when `A → B` is faithfully flat.
* `AlgebraicGeometry.Over.pieceRingEquiv_naturality` — the restriction seam: the
  identification commutes with restriction along `W ≤ V` (through `Over.resAlgHomA`).
* `AlgebraicGeometry.Over.exists_isAffineOpen_cg_le` — the affine basis packaging: every
  neighbourhood of a point contains a `cg`-saturated affine open.
* `AlgebraicGeometry.Over.isSeparated_left`, `AlgebraicGeometry.Over.isAffineOpen_inf` — for
  `C` proper, `C ⊗ Spec A` is separated, so the affine family is closed under the intersections
  (overlaps) the E3 reassembly forms.

## Design notes

* **No properness or flatness in the geometry.** The identification rests only on the affine
  case of mathlib's `pushoutSection` (`isIso_pushoutSection_of_isAffineOpen`), which needs no
  flatness; `[IsProper C.hom]`, geometric irreducibility/reducedness and even
  `[Module.FaithfullyFlat A B]` are absent from everything except the faithful-flatness
  conclusion `faithfullyFlat_pieceCover`.
* **The `A`-algebra structure on `Γ(V)`** is `Over.sectionsAlgebraA` (pullback along `pA`
  through `ΓSpecIso`), a `local instance` of `Picard/SectionsDescent.lean` reactivated here;
  the tensor `Γ(V) ⊗[A] B` is taken with respect to it, so `Γ(V) ⊗[A] B` is faithfully flat
  over `Γ(V)` by mathlib's base-change instance for faithful flatness.
* **The `Γ(V)`-algebra structure on `Γ(cg⁻¹ V)`** is `Over.pieceCoverAlgebra`, pullback along
  `cg`; the identification `pieceEquiv` is `Γ(V)`-linear on the nose because `pieceRingEquiv`
  sends `s ⊗ₜ 1` to `cg^♯ s` (`pieceRingEquiv_tmul_one`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]
variable (C : Over (Spec (.of k)))

set_option quotPrecheck false in
local notation "XA" => (C ⊗ overSpec k A).left
set_option quotPrecheck false in
local notation "XB" => (C ⊗ overSpec k B).left
set_option quotPrecheck false in
local notation "gA" => Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)
set_option quotPrecheck false in
local notation "cg" => (C ◁ (gA)).left
set_option quotPrecheck false in
local notation "gS" => (gA).left
set_option quotPrecheck false in
local notation "pA" => (snd C (overSpec k A)).left
set_option quotPrecheck false in
local notation "pB" => (snd C (overSpec k B)).left

namespace Over

-- The `A`-algebra structure on sections of the curve product, by pullback along `pA`.
attribute [local instance] Over.sectionsAlgebraA

/-! ## Affineness of the cover inclusion -/

/-- **The cover inclusion `cg` is an affine morphism.** `cg` is the base change of the affine
`gS = Spec (ofId A B) : Spec B ⟶ Spec A` along the projection `pA`, via the base-change
pullback square `Over.isPullback_whiskerLeft_snd`; affineness is stable under base change. -/
instance isAffineHom_cg : IsAffineHom (cg) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (Over.isPullback_whiskerLeft_snd C gA).flip inferInstance

/-- **The `cg`-preimage of an affine open is affine.** Preimages of affine opens under the
affine morphism `cg` are affine (`IsAffineOpen.preimage`). -/
theorem isAffineOpen_cgPreimage {U : (XA).Opens} (hU : IsAffineOpen U) :
    IsAffineOpen ((cg) ⁻¹ᵁ U) :=
  hU.preimage (cg)

/-! ## The section-ring pushout square, re-cornered to `A` and `B` -/

/-- The mathlib pushout-of-sections square for the base-change square of the tower `A → B`,
with the `Spec B`-side at `⊤` and an affine open `U` on the product side.  No flatness is
needed (the affine case of `pushoutSection`). -/
theorem isPushout_cgSections {U : (XA).Opens} (hU : IsAffineOpen U) :
    IsPushout
      ((pA).appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top (pA)).ge))
      ((gS).appLE ⊤ ⊤ (Scheme.Hom.preimage_top (gS)).ge)
      ((cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl)
      ((pB).appLE ⊤ ((cg) ⁻¹ᵁ U)
        (le_top.trans (Scheme.Hom.preimage_top (pB)).ge)) := by
  have H := Over.isPullback_whiskerLeft_snd C gA
  have hUY : (cg) ⁻¹ᵁ U
      = (cg) ⁻¹ᵁ U ⊓ (pB) ⁻¹ᵁ (⊤ : ((overSpec k B).left).Opens) := by
    rw [Scheme.Hom.preimage_top, inf_top_eq]
  have h := isIso_pushoutSection_of_isAffineOpen H
    (le_top.trans (Scheme.Hom.preimage_top (gS)).ge)
    (le_top.trans (Scheme.Hom.preimage_top (pA)).ge) hUY
    (isAffineOpen_top_overSpec k A) (isAffineOpen_top_overSpec k B) hU
  exact (isIso_pushoutSection_iff _ _ _ _).mp h

/-- The pushout square re-cornered to `A` and `B`: the `Γ(Spec A, ⊤)` and `Γ(Spec B, ⊤)`
corners are replaced by `A` and `B` along `ΓSpecIso`. -/
theorem isPushout_cgAlgebraMap {U : (XA).Opens} (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (algebraMap A Γ(XA, U)))
      (CommRingCat.ofHom (algebraMap A B))
      ((cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl)
      ((Scheme.ΓSpecIso (.of B)).inv
        ≫ (pB).appLE ⊤ ((cg) ⁻¹ᵁ U)
          (le_top.trans (Scheme.Hom.preimage_top (pB)).ge)) := by
  refine (isPushout_cgSections C hU).of_iso
    (Scheme.ΓSpecIso (.of A)) (Iso.refl _) (Scheme.ΓSpecIso (.of B)) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [Over.ofHom_algebraMap_sectionsA]
    exact (Iso.hom_inv_id_assoc _ _).symm
  · have h : (gS).appLE ⊤ ⊤ (Scheme.Hom.preimage_top (gS)).ge = (gS).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [h, Over.overSpecMap_left]
    have hφ : CommRingCat.ofHom ((Algebra.ofId A B).restrictScalars k).toRingHom
        = CommRingCat.ofHom (algebraMap A B) := rfl
    rw [hφ]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id]
    exact (Iso.hom_inv_id_assoc _ _).symm

/-! ## The section-ring identification -/

/-- **The section-ring identification** (in `CommRingCat`): for an affine open `U` of the
curve product `C ⊗ Spec A`, `Γ(U) ⊗[A] B ≅ Γ((C ⊗ Spec B).left, cg⁻¹ U)`.  This is the
affine-open generalization of the landed `⊤`-case `Over.sectionsTopAlgEquiv`. -/
noncomputable def pieceTensorIso {U : (XA).Opens} (hU : IsAffineOpen U) :
    CommRingCat.of (Γ(XA, U) ⊗[A] B) ≅ Γ(XB, (cg) ⁻¹ᵁ U) :=
  (CommRingCat.isPushout_tensorProduct A Γ(XA, U) B).isoIsPushout _ _
    (isPushout_cgAlgebraMap C hU)

/-- **The section-ring identification, as a ring equivalence** `Γ(U) ⊗[A] B ≃+* Γ(cg⁻¹ U)`,
sending `s ⊗ b` to the product of the two pullbacks (`pieceRingEquiv_tmul`). -/
noncomputable def pieceRingEquiv {U : (XA).Opens} (hU : IsAffineOpen U) :
    Γ(XA, U) ⊗[A] B ≃+* Γ(XB, (cg) ⁻¹ᵁ U) :=
  (pieceTensorIso C hU).commRingCatIsoToRingEquiv

/-- On `s ⊗ 1` the identification is the pullback `cg^♯ s` of `s`. -/
theorem pieceRingEquiv_tmul_one {U : (XA).Opens} (hU : IsAffineOpen U) (s : Γ(XA, U)) :
    pieceRingEquiv C hU (s ⊗ₜ 1)
      = (cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl s :=
  congr($((CommRingCat.isPushout_tensorProduct A Γ(XA, U) B).inl_isoIsPushout_hom _ _
    (isPushout_cgAlgebraMap C hU)).hom s)

/-- On `1 ⊗ b` the identification is the pullback of `b` along the second projection `pB`. -/
theorem pieceRingEquiv_one_tmul {U : (XA).Opens} (hU : IsAffineOpen U) (b : B) :
    pieceRingEquiv C hU (1 ⊗ₜ b)
      = ((Scheme.ΓSpecIso (.of B)).inv
          ≫ (pB).appLE ⊤ ((cg) ⁻¹ᵁ U)
            (le_top.trans (Scheme.Hom.preimage_top (pB)).ge)) b :=
  congr($((CommRingCat.isPushout_tensorProduct A Γ(XA, U) B).inr_isoIsPushout_hom _ _
    (isPushout_cgAlgebraMap C hU)).hom b)

/-- On a pure tensor `s ⊗ b`, the identification is the product of the pullback of `s` along
`cg` and the pullback of `b` along the second projection. -/
theorem pieceRingEquiv_tmul {U : (XA).Opens} (hU : IsAffineOpen U) (s : Γ(XA, U)) (b : B) :
    pieceRingEquiv C hU (s ⊗ₜ b)
      = (cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl s *
        ((Scheme.ΓSpecIso (.of B)).inv
          ≫ (pB).appLE ⊤ ((cg) ⁻¹ᵁ U)
            (le_top.trans (Scheme.Hom.preimage_top (pB)).ge)) b := by
  have h : (s ⊗ₜ[A] b : Γ(XA, U) ⊗[A] B) = (s ⊗ₜ 1) * (1 ⊗ₜ b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, pieceRingEquiv_tmul_one, pieceRingEquiv_one_tmul]

/-! ## The `Γ(V)`-algebra face and faithful flatness -/

/-- The `Γ(V)`-algebra structure on the cover-piece ring `Γ(cg⁻¹ V)`, by pullback along `cg`.
A `local instance`; consumers reactivate it with `attribute [local instance]
Over.pieceCoverAlgebra`. -/
@[reducible] noncomputable def pieceCoverAlgebra (U : (XA).Opens) :
    Algebra Γ(XA, U) Γ(XB, (cg) ⁻¹ᵁ U) :=
  ((cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl).hom.toAlgebra

attribute [local instance] pieceCoverAlgebra

/-- Unfolding lemma for `Over.pieceCoverAlgebra`: the algebra structure map is `cg^♯`. -/
lemma algebraMap_pieceCover (U : (XA).Opens) (s : Γ(XA, U)) :
    algebraMap Γ(XA, U) Γ(XB, (cg) ⁻¹ᵁ U) s
      = (cg).appLE U ((cg) ⁻¹ᵁ U) le_rfl s :=
  rfl

/-- **The section-ring identification as a `Γ(V)`-algebra equivalence**, tensor side:
`Γ(V) ⊗[A] B ≃ₐ[Γ(V)] Γ(cg⁻¹ V)`.  It is `Γ(V)`-linear on the nose: `pieceRingEquiv` carries
`s ⊗ₜ 1` to `cg^♯ s`, which is the `Γ(V)`-algebra structure map of `Γ(cg⁻¹ V)`. -/
noncomputable def pieceTensorAlgEquiv {U : (XA).Opens} (hU : IsAffineOpen U) :
    Γ(XA, U) ⊗[A] B ≃ₐ[Γ(XA, U)] Γ(XB, (cg) ⁻¹ᵁ U) :=
  AlgEquiv.ofRingEquiv (f := pieceRingEquiv C hU)
    (fun s => by
      rw [show algebraMap Γ(XA, U) (Γ(XA, U) ⊗[A] B) s = s ⊗ₜ 1 from rfl,
        pieceRingEquiv_tmul_one, algebraMap_pieceCover])

/-- **The section-ring identification as a `Γ(V)`-algebra equivalence**
`Γ(cg⁻¹ V) ≃ₐ[Γ(V)] Γ(V) ⊗[A] B` (the shape the (C2) effectivity spec names). -/
noncomputable def pieceEquiv {U : (XA).Opens} (hU : IsAffineOpen U) :
    Γ(XB, (cg) ⁻¹ᵁ U) ≃ₐ[Γ(XA, U)] Γ(XA, U) ⊗[A] B :=
  (pieceTensorAlgEquiv C hU).symm

/-- **Faithful flatness of the cover piece over the base piece.** When `A → B` is faithfully
flat, so is `Γ(V) → Γ(cg⁻¹ V)`: `Γ(V) ⊗[A] B` is faithfully flat over `Γ(V)` by mathlib's
base-change instance, transported along `pieceEquiv`. -/
theorem faithfullyFlat_pieceCover [Module.FaithfullyFlat A B] {U : (XA).Opens}
    (hU : IsAffineOpen U) :
    Module.FaithfullyFlat Γ(XA, U) Γ(XB, (cg) ⁻¹ᵁ U) :=
  Module.FaithfullyFlat.of_linearEquiv _ _ (pieceEquiv C hU).toLinearEquiv

/-! ## Restriction compatibility (the E2/E3 seam) -/

/-- The `A`-algebra structure maps of `Over.sectionsAlgebraA` intertwine restriction. -/
lemma algebraMap_sectionsA_comp_res {V W : (XA).Opens} (h : W ≤ V) :
    CommRingCat.ofHom (algebraMap A Γ(XA, V)) ≫ (XA).presheaf.map (homOfLE h).op
      = CommRingCat.ofHom (algebraMap A Γ(XA, W)) := by
  rw [Over.ofHom_algebraMap_sectionsA, Over.ofHom_algebraMap_sectionsA, Category.assoc]
  congr 1
  exact Scheme.Hom.appLE_map _ _ _

/-- Restriction of base-piece sections along `W ≤ V` as an `A`-algebra homomorphism (with the
`Over.sectionsAlgebraA` structures). -/
noncomputable def resAlgHomA {V W : (XA).Opens} (h : W ≤ V) :
    Γ(XA, V) →ₐ[A] Γ(XA, W) where
  __ := ((XA).presheaf.map (homOfLE h).op).hom
  commutes' r := congr($(algebraMap_sectionsA_comp_res C h).hom r)

@[simp]
lemma resAlgHomA_apply {V W : (XA).Opens} (h : W ≤ V) (s : Γ(XA, V)) :
    resAlgHomA C h s = (XA).presheaf.map (homOfLE h).op s :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The restriction seam** (the E3 consumer): for affine opens `W ≤ V`, restricting the
identified cover section is identifying the restricted base section.  The map on tensor
products is `Algebra.TensorProduct.map` of the restriction `resAlgHomA` and the identity of
`B`.  This is what lets the per-piece descent data of E2 be compared on overlaps. -/
theorem pieceRingEquiv_naturality {V W : (XA).Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (hWV : W ≤ V) (x : Γ(XA, V) ⊗[A] B) :
    (XB).presheaf.map
        (homOfLE (show (cg) ⁻¹ᵁ W ≤ (cg) ⁻¹ᵁ V from (cg).preimage_mono hWV)).op
        (pieceRingEquiv C hV x)
      = pieceRingEquiv C hW
          (Algebra.TensorProduct.map (resAlgHomA C hWV) (AlgHom.id A B) x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s b =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, resAlgHomA_apply,
      pieceRingEquiv_tmul, pieceRingEquiv_tmul, map_mul]
    congr 1
    · rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, ← CommRingCat.comp_apply,
        Scheme.Hom.map_appLE]
    · rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]

/-! ## The affine basis packaging -/

/-- **`cg`-saturated affine opens form a basis.** Every neighbourhood `V` of a point `x` of
the curve product `C ⊗ Spec A` contains an affine open `W` with `x ∈ W` whose `cg`-preimage
is again affine — the affine opens form a basis (`isBasis_affineOpens`) and `cg` is affine.
This packages the geometric pieces for the downstream covering arguments of E3. -/
theorem exists_isAffineOpen_cg_le (x : XA) {V : (XA).Opens} (hx : x ∈ V) :
    ∃ W : (XA).Opens, IsAffineOpen W ∧ IsAffineOpen ((cg) ⁻¹ᵁ W) ∧ x ∈ W ∧ W ≤ V := by
  obtain ⟨W, hWaff, hxW, hWV⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (XA).isBasis_affineOpens hx
  exact ⟨W, hWaff, isAffineOpen_cgPreimage C hWaff, hxW, hWV⟩

section Separated

variable [IsProper C.hom]

/-- **The curve product over a proper `C` is a separated scheme.** `C.hom` is separated (`C`
proper over the field `k`), hence so is its base change `pA = snd`; composing with the affine
`Spec A ⟶ Spec k` and `Spec k ⟶ ⊤` gives a separated structure morphism, so `C ⊗ Spec A` is
separated.  This supplies the affine-diagonal instance the intersection lemma needs. -/
instance isSeparated_left : Scheme.IsSeparated (XA) := by
  constructor
  haveI : IsSeparated (snd C (overSpec k A)).left :=
    MorphismProperty.of_isPullback (Over.isPullback_left C (overSpec k A)) inferInstance
  haveI : IsSeparated ((C ⊗ overSpec k A).hom) := by
    rw [← Over.w (snd C (overSpec k A))]
    infer_instance
  rw [← Limits.terminal.comp_from ((C ⊗ overSpec k A).hom)]
  infer_instance

/-- **The affine opens of the curve product are closed under intersection** (for `C` proper
over the field `k`).  The intersection of two affine opens of the separated scheme
`C ⊗ Spec A` is affine (`IsAffineOpen.inf`, via the affine diagonal of a separated scheme), so
the `cg`-saturated affine family of `exists_isAffineOpen_cg_le` carries the overlaps
`W = V ⊓ V'` that the descent-cocycle reassembly of E3 forms. -/
theorem isAffineOpen_inf {V W : (XA).Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    IsAffineOpen (V ⊓ W) :=
  hV.inf hW

end Separated

end Over

end AlgebraicGeometry
