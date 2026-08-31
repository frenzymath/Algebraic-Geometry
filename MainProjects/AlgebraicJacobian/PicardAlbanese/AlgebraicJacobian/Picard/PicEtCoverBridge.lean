/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ZariskiSheaf

/-!
# The open-immersion evaluation bridge (DAT-6, stage 1)

The Zariski sheaf property of `picEt`/`pic0` landed by DAT-2
(`AlgebraicJacobian.Picard.Pic0ZariskiSheaf`) speaks *topological* covers of the test:
open sets `O i ⊆ T.left` and local data valued at affine opens subordinate to them.
The 01JJ packaging (DAT-6 stages 2–3) speaks *morphism-form* covers: families
`f i : T' i ⟶ T` of test morphisms with open-immersion left legs, jointly surjective,
carrying sections `x i : picEt C (T' i)` compatible on all common refinements.  This
file is the bridge: it evaluates a morphism-form family into DAT-2's `picEt.LocalData`
on the ranges `O i := (f i).left.opensRange` and exports the sheaf property of `picEt`
and of its degree-zero subfunctor in morphism-cover form.

* `AlgebraicGeometry.Over.appLEAlgEquiv`: the section-ring isomorphism of an open
  immersion of tests, `Γ(T.left, V) ≃ₐ[k] Γ(T'.left, f.left ⁻¹ᵁ V)` for
  `V ≤ opensRange`, upgrading `Over.appLEAlgHom` (bijectivity:
  `Over.bijective_appLEAlgHom`, from `Scheme.Hom.isIso_app`).
* `AlgebraicGeometry.picEt.coverValue`: the value at an affine open `W` subordinate to
  a cover member of the section carried by that member — evaluate at the preimage
  affine open and transport back along `appLEAlgEquiv`.  It is local data:
  `coverValue_res` (restriction within a member, pure `appLE`/`res` calculus) and
  `coverValue_glue` (agreement across members at a shared affine open, through the
  mediating test `picEt.overlapTest` — the open subscheme of the target at `W` — and
  `IsOpenImmersion.lift`).
* `AlgebraicGeometry.picEt.ext_of_cover` / `picEt.existsUnique_of_cover`: **the sheaf
  property of `picEt` in morphism-cover form** — separation and unique gluing for a
  compatible family on an abstract open-immersion cover of the test.
* `AlgebraicGeometry.pic0Subgroup_ext_of_cover` /
  `pic0Subgroup_existsUnique_of_cover`: the same for the degree-zero subfunctor;
  membership of the glued section is DAT-2's S-lemma (`mem_pic0Subgroup_of_cover`).

The compatibility hypothesis is the morphism form (`Presieve.Arrows.Compatible`
transported to the slice): for every pair of members and every test `Z` mapping to
both compatibly, the two restrictions of the family agree.  Stage 3 instantiates it
from a compatible family of elements of the Σ-extension on a scheme-level open cover.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k]

/-! ## The section-ring isomorphism of an open immersion of tests -/

namespace Over

/-- `appLEAlgHom` respects equality of test morphisms. -/
lemma appLEAlgHom_congr_hom {T T' : Over (Spec (.of k))} {f f' : T' ⟶ T} (h : f = f')
    (V : T.left.Opens) (U : T'.left.Opens) (e : U ≤ f.left ⁻¹ᵁ V)
    (e' : U ≤ f'.left ⁻¹ᵁ V) :
    appLEAlgHom f V U e = appLEAlgHom f' V U e' := by
  subst h
  rfl

/-- The pullback of sections along a test morphism with open-immersion left leg, from
an open `V` inside the range onto its preimage, is bijective: the underlying map is
`f.app V` (an isomorphism on opens inside the range) composed with restriction along
an equality of opens. -/
theorem bijective_appLEAlgHom {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    [IsOpenImmersion f.left] (V : T.left.Opens) (U : T'.left.Opens)
    (e : U ≤ f.left ⁻¹ᵁ V) (hV : V ≤ f.left.opensRange) (hU : f.left ⁻¹ᵁ V ≤ U) :
    Function.Bijective (appLEAlgHom f V U e) := by
  obtain rfl : U = f.left ⁻¹ᵁ V := le_antisymm e hU
  haveI : IsIso (f.left.app V) := Scheme.Hom.isIso_app f.left V hV
  haveI : IsIso (f.left.appLE V (f.left ⁻¹ᵁ V) e) := by
    have happ : f.left.appLE V (f.left ⁻¹ᵁ V) e = f.left.app V := by
      rw [Scheme.Hom.appLE, show homOfLE e = 𝟙 (f.left ⁻¹ᵁ V) from rfl, op_id,
        CategoryTheory.Functor.map_id, Category.comp_id]
    rw [happ]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (f.left.appLE V (f.left ⁻¹ᵁ V) e)

/-- The section-ring isomorphism of an open immersion of tests: pullback of sections
from an open inside the range onto its preimage, as a `k`-algebra isomorphism. -/
noncomputable def appLEAlgEquiv {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    [IsOpenImmersion f.left] (V : T.left.Opens) (hV : V ≤ f.left.opensRange) :
    Γ(T.left, V) ≃ₐ[k] Γ(T'.left, f.left ⁻¹ᵁ V) :=
  AlgEquiv.ofBijective (appLEAlgHom f V (f.left ⁻¹ᵁ V) le_rfl)
    (bijective_appLEAlgHom f V (f.left ⁻¹ᵁ V) le_rfl hV le_rfl)

/-- The forward pullback undoes the inverse transport of `appLEAlgEquiv`. -/
lemma appLEAlgHom_comp_appLEAlgEquiv_symm {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    [IsOpenImmersion f.left] (V : T.left.Opens) (hV : V ≤ f.left.opensRange) :
    (appLEAlgHom f V (f.left ⁻¹ᵁ V) le_rfl).comp
        (appLEAlgEquiv f V hV).symm.toAlgHom
      = AlgHom.id k Γ(T'.left, f.left ⁻¹ᵁ V) :=
  AlgHom.ext fun a => (appLEAlgEquiv f V hV).apply_symm_apply a

end Over

variable (C : Over (Spec (.of k)))

/-! ## `mapAlg` along bijective algebra maps -/

/-- Transport of plus classes along a bijective algebra map of test algebras is
injective. -/
theorem PicEtAff.mapAlg_injective {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (φ : A →ₐ[k] B) (hφ : Function.Bijective φ) :
    Function.Injective (PicEtAff.mapAlg C φ) := by
  intro y z hyz
  have h := congrArg (PicEtAff.mapAlg C (AlgEquiv.ofBijective φ hφ).symm.toAlgHom) hyz
  rwa [← PicEtAff.mapAlg_comp, ← PicEtAff.mapAlg_comp,
    show (AlgEquiv.ofBijective φ hφ).symm.toAlgHom.comp φ = AlgHom.id k A from
      AlgHom.ext fun a => (AlgEquiv.ofBijective φ hφ).symm_apply_apply a,
    PicEtAff.mapAlg_id, PicEtAff.mapAlg_id] at h

namespace picEt

variable {C}
variable {T : Over (Spec (.of k))} {ι : Type*} {T' : ι → Over (Spec (.of k))}
variable (f : ∀ i, T' i ⟶ T) [∀ i, IsOpenImmersion (f i).left]
variable (x : ∀ i, picEt C (T' i))

/-! ## The local data of a morphism-form cover -/

/-- The value at an affine open subordinate to a cover member of the section carried by
that member: evaluate at the preimage affine open and transport back along the
section-ring isomorphism of the open immersion. -/
noncomputable def coverValue (i : ι) (W : T.left.affineOpens)
    (hW : W.1 ≤ (f i).left.opensRange) : PicEtAff C Γ(T.left, W.1) :=
  PicEtAff.mapAlg C (Over.appLEAlgEquiv (f i) W.1 hW).symm.toAlgHom
    ((x i).1 ⟨(f i).left ⁻¹ᵁ W.1, W.2.preimage_of_isOpenImmersion (f i).left hW⟩)

/-- The defining property of `coverValue`, forward form: its pullback to the preimage
affine open recovers the value of the local section there. -/
theorem mapAlg_coverValue (i : ι) (W : T.left.affineOpens)
    (hW : W.1 ≤ (f i).left.opensRange) :
    PicEtAff.mapAlg C (Over.appLEAlgHom (f i) W.1 ((f i).left ⁻¹ᵁ W.1) le_rfl)
        (coverValue f x i W hW)
      = (x i).1 ⟨(f i).left ⁻¹ᵁ W.1, W.2.preimage_of_isOpenImmersion (f i).left hW⟩ := by
  rw [coverValue, ← PicEtAff.mapAlg_comp,
    Over.appLEAlgHom_comp_appLEAlgEquiv_symm (f i) W.1 hW, PicEtAff.mapAlg_id]

/-- `coverValue` restricts correctly within a member: the `res` field of the local
data, by the `appLE`/`res` calculus and the compatibility of the member's section. -/
theorem coverValue_res (i : ι) (W W' : T.left.affineOpens)
    (hW : W.1 ≤ (f i).left.opensRange) (hW' : W'.1 ≤ (f i).left.opensRange)
    (h : W.1 ≤ W'.1) :
    PicEtAff.mapAlg C (Over.resAlgHom T h) (coverValue f x i W' hW')
      = coverValue f x i W hW := by
  have hpre : (f i).left ⁻¹ᵁ W.1 ≤ (f i).left ⁻¹ᵁ W'.1 := (f i).left.preimage_mono h
  apply PicEtAff.mapAlg_injective C
    (Over.appLEAlgHom (f i) W.1 ((f i).left ⁻¹ᵁ W.1) le_rfl)
    (Over.bijective_appLEAlgHom (f i) W.1 ((f i).left ⁻¹ᵁ W.1) le_rfl hW le_rfl)
  rw [mapAlg_coverValue f x i W hW, ← PicEtAff.mapAlg_comp,
    Over.appLEAlgHom_comp_resAlgHom (f i) ((f i).left ⁻¹ᵁ W.1) h le_rfl
      (hpre.trans le_rfl),
    ← Over.resAlgHom_comp_appLEAlgHom (f i) W'.1 le_rfl hpre,
    PicEtAff.mapAlg_comp, mapAlg_coverValue f x i W' hW']
  exact (x i).compat
    ⟨(f i).left ⁻¹ᵁ W.1, W.2.preimage_of_isOpenImmersion (f i).left hW⟩
    ⟨(f i).left ⁻¹ᵁ W'.1, W'.2.preimage_of_isOpenImmersion (f i).left hW'⟩ hpre

/-! ## The mediating test at a shared affine open -/

variable (T) in
/-- The mediating test of the cross-member gluing: the open subscheme of the target at
an affine open `W`, over the base through the inclusion. -/
noncomputable def overlapTest (W : T.left.affineOpens) : Over (Spec (.of k)) :=
  Over.mk (W.1.ι ≫ T.hom)

variable (T) in
/-- The inclusion of the mediating test into the target. -/
noncomputable def overlapInclusion (W : T.left.affineOpens) : overlapTest T W ⟶ T :=
  Over.homMk W.1.ι rfl

instance (W : T.left.affineOpens) : IsOpenImmersion (overlapInclusion T W).left :=
  inferInstanceAs (IsOpenImmersion W.1.ι)

variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

/-- `coverValue` of a compatible family agrees across members at a shared affine open:
the `glue` field of the local data.  The inclusion of the mediating test lifts through
both members (`IsOpenImmersion.lift`), where the compatibility hypothesis identifies
the two restricted sections, and the common evaluation map
`appLEAlgHom (overlapInclusion T W) W ⊤` is injective. -/
theorem coverValue_glue
    (hx : ∀ (i j : ι) (Z : Over (Spec (.of k))) (gi : Z ⟶ T' i) (gj : Z ⟶ T' j),
      gi ≫ f i = gj ≫ f j → picEtMap C gi (x i) = picEtMap C gj (x j))
    (i j : ι) (W : T.left.affineOpens) (hi : W.1 ≤ (f i).left.opensRange)
    (hj : W.1 ≤ (f j).left.opensRange) :
    coverValue f x i W hi = coverValue f x j W hj := by
  haveI : IsAffine (overlapTest T W).left := W.2
  have hiWrange : W.1 ≤ Scheme.Hom.opensRange (overlapInclusion T W).left :=
    le_of_eq (W.1.opensRange_ι).symm
  have eW : (⊤ : (overlapTest T W).left.Opens)
      ≤ (overlapInclusion T W).left ⁻¹ᵁ W.1 := (W.1.ι_preimage_self).ge
  -- the common evaluation identity at each member
  have main : ∀ (l : ι) (hl : W.1 ≤ (f l).left.opensRange) (g : overlapTest T W ⟶ T' l),
      g ≫ f l = overlapInclusion T W →
      PicEtAff.mapAlg C (Over.appLEAlgHom (overlapInclusion T W) W.1 ⊤ eW)
          (coverValue f x l W hl)
        = (picEtMap C g (x l)).1 ⟨⊤, isAffineOpen_top _⟩ := by
    intro l hl g hg
    have hgleft : g.left ≫ (f l).left = W.1.ι := congrArg Over.Hom.left hg
    have e₃ : (⊤ : (overlapTest T W).left.Opens) ≤ (g ≫ f l).left ⁻¹ᵁ W.1 := by
      rw [hg]
      exact eW
    have hpre : (⊤ : (overlapTest T W).left.Opens)
        ≤ g.left ⁻¹ᵁ ((f l).left ⁻¹ᵁ W.1) := by
      refine le_of_eq ?_
      rw [← Scheme.Hom.comp_preimage, hgleft]
      exact (Scheme.Opens.ι_preimage_self W.1).symm
    rw [picEtMap_val, picEtMapVal_eq_mapAlg C g (x l)
        (W := ⟨⊤, isAffineOpen_top _⟩)
        (V := ⟨(f l).left ⁻¹ᵁ W.1, W.2.preimage_of_isOpenImmersion (f l).left hl⟩) hpre,
      ← mapAlg_coverValue f x l W hl, ← PicEtAff.mapAlg_comp,
      Over.appLEAlgHom_comp (f l) g W.1 ((f l).left ⁻¹ᵁ W.1) ⊤ le_rfl hpre e₃,
      Over.appLEAlgHom_congr_hom hg W.1 ⊤ e₃ eW]
  -- the lifts of the inclusion through the members
  have hrange : ∀ (l : ι), W.1 ≤ (f l).left.opensRange →
      Set.range ⇑W.1.ι ⊆ Set.range ⇑(f l).left := by
    intro l hl
    rw [Scheme.Opens.range_ι]
    exact hl
  have hgiw : IsOpenImmersion.lift (f i).left W.1.ι (hrange i hi) ≫ (T' i).hom
      = (overlapTest T W).hom := by
    rw [← Over.w (f i), ← Category.assoc, IsOpenImmersion.lift_fac]
    rfl
  have hgjw : IsOpenImmersion.lift (f j).left W.1.ι (hrange j hj) ≫ (T' j).hom
      = (overlapTest T W).hom := by
    rw [← Over.w (f j), ← Category.assoc, IsOpenImmersion.lift_fac]
    rfl
  let gi : overlapTest T W ⟶ T' i :=
    Over.homMk (IsOpenImmersion.lift (f i).left W.1.ι (hrange i hi)) hgiw
  let gj : overlapTest T W ⟶ T' j :=
    Over.homMk (IsOpenImmersion.lift (f j).left W.1.ι (hrange j hj)) hgjw
  have hgi : gi ≫ f i = overlapInclusion T W := by
    ext : 1
    exact IsOpenImmersion.lift_fac (f i).left W.1.ι (hrange i hi)
  have hgj : gj ≫ f j = overlapInclusion T W := by
    ext : 1
    exact IsOpenImmersion.lift_fac (f j).left W.1.ι (hrange j hj)
  -- equate through the compatibility hypothesis and cancel the evaluation map
  apply PicEtAff.mapAlg_injective C
    (Over.appLEAlgHom (overlapInclusion T W) W.1 ⊤ eW)
    (Over.bijective_appLEAlgHom (overlapInclusion T W) W.1 ⊤ eW hiWrange le_top)
  rw [main i hi gi hgi, main j hj gj hgj,
    hx i j (overlapTest T W) gi gj (hgi.trans hgj.symm)]

/-! ## Separation and gluing in morphism-cover form -/

variable (hcov : ∀ p : T.left, ∃ i, p ∈ (f i).left.opensRange)

include hcov in
/-- **Separation of `picEt` in morphism-cover form**: two sections of the target
agreeing after restriction to every member of an open-immersion cover agree. -/
theorem ext_of_cover {s t : picEt C T}
    (h : ∀ i, picEtMap C (f i) s = picEtMap C (f i) t) : s = t := by
  refine picEt.ext_of_le_cover C (fun i => (f i).left.opensRange) hcov
    (fun U i hU => ?_)
  apply PicEtAff.mapAlg_injective C
    (Over.appLEAlgHom (f i) U.1 ((f i).left ⁻¹ᵁ U.1) le_rfl)
    (Over.bijective_appLEAlgHom (f i) U.1 ((f i).left ⁻¹ᵁ U.1) le_rfl hU le_rfl)
  rw [← picEtMapVal_eq_mapAlg C (f i) s
      (W := ⟨(f i).left ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion (f i).left hU⟩) le_rfl,
    ← picEtMapVal_eq_mapAlg C (f i) t
      (W := ⟨(f i).left ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion (f i).left hU⟩) le_rfl,
    ← picEtMap_val, ← picEtMap_val, h i]

include hcov in
/-- **The sheaf property of `picEt` in morphism-cover form** (the evaluation bridge,
headline): a family of sections on an abstract open-immersion cover of a test,
compatible on all common refinements, glues to a unique section of the target
restricting to each member's section. -/
theorem existsUnique_of_cover
    (hx : ∀ (i j : ι) (Z : Over (Spec (.of k))) (gi : Z ⟶ T' i) (gj : Z ⟶ T' j),
      gi ≫ f i = gj ≫ f j → picEtMap C gi (x i) = picEtMap C gj (x j)) :
    ∃! s : picEt C T, ∀ i, picEtMap C (f i) s = x i := by
  classical
  choose ip hip using fun p : T.left => hcov p
  -- the point-indexed local data
  have hv₀ : LocalData (fun p : T.left => (f (ip p)).left.opensRange)
      (fun p W hW => coverValue f x (ip p) W hW) :=
    ⟨fun p W W' hW hW' h => coverValue_res f x (ip p) W W' hW hW' h,
      fun p q W hp hq => coverValue_glue f x hx (ip p) (ip q) W hp hq⟩
  have hcov₀ : ∀ p : T.left, ∃ q : T.left, p ∈ (f (ip q)).left.opensRange :=
    fun p => ⟨p, hip p⟩
  obtain ⟨s, hs, -⟩ := existsUnique_glue_of_le_cover hcov₀ hv₀
  -- the glued section takes the bridge values at every member of the original cover
  have hval : ∀ (i : ι) (W : T.left.affineOpens) (hW : W.1 ≤ (f i).left.opensRange),
      s.1 W = coverValue f x i W hW := by
    intro i W hW
    refine glueValue_unique (v := fun p W hW => coverValue f x (ip p) W hW) hcov₀
      (fun W₀ hW₀ q hq => ?_) (fun W₀ hW₀ q hq => ?_)
    · rw [s.compat W₀ W hW₀]
      exact hs q W₀ hq
    · rw [coverValue_res f x i W₀ W (hW₀.trans hW) hW hW₀]
      exact coverValue_glue f x hx i (ip q) W₀ (hW₀.trans hW) hq
  -- the glued section restricts to the members' sections
  have hmain : ∀ i, picEtMap C (f i) s = x i := by
    intro i
    refine picEt.ext fun U' => ?_
    have himage : (f i).left ''ᵁ U'.1 ≤ (f i).left.opensRange :=
      (f i).left.image_le_opensRange U'.1
    have hres : U'.1 ≤ (f i).left ⁻¹ᵁ ((f i).left ''ᵁ U'.1) :=
      ((f i).left.preimage_image_eq U'.1).ge
    rw [picEtMap_val, picEtMapVal_eq_mapAlg C (f i) s
        (W := U') (V := ⟨(f i).left ''ᵁ U'.1, U'.2.image_of_isOpenImmersion _⟩) hres,
      hval i ⟨(f i).left ''ᵁ U'.1, U'.2.image_of_isOpenImmersion _⟩ himage,
      ← Over.resAlgHom_comp_appLEAlgHom (f i) ((f i).left ''ᵁ U'.1) le_rfl hres,
      PicEtAff.mapAlg_comp,
      mapAlg_coverValue f x i ⟨(f i).left ''ᵁ U'.1, U'.2.image_of_isOpenImmersion _⟩
        himage]
    exact (x i).compat U'
      ⟨(f i).left ⁻¹ᵁ ((f i).left ''ᵁ U'.1),
        (U'.2.image_of_isOpenImmersion _).preimage_of_isOpenImmersion (f i).left himage⟩
      hres
  exact ⟨s, hmain, fun s' hs' => ext_of_cover f hcov fun i => by rw [hs' i, hmain i]⟩

end picEt

/-! ## The degree-zero subfunctor in morphism-cover form -/

section Pic0

variable {C}
variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
variable [SmoothOfRelativeDimension 1 C.hom]
variable {T : Over (Spec (.of k))} {ι : Type*} {T' : ι → Over (Spec (.of k))}
variable (f : ∀ i, T' i ⟶ T) [∀ i, IsOpenImmersion (f i).left]
variable (hcov : ∀ p : T.left, ∃ i, p ∈ (f i).left.opensRange)

omit [GeometricallyReduced C.hom] in
include hcov in
/-- **Separation of `pic0` in morphism-cover form**: two degree-zero classes agreeing
after restriction to every member of an open-immersion cover agree. -/
theorem pic0Subgroup_ext_of_cover {s t : pic0Subgroup C T}
    (h : ∀ i, pic0Map C (f i) s = pic0Map C (f i) t) : s = t :=
  Subtype.ext (picEt.ext_of_cover f hcov fun i =>
    congrArg Subtype.val (h i))

include hcov in
/-- **The sheaf property of the degree-zero Picard functor in morphism-cover form**:
a compatible family of degree-zero classes on an abstract open-immersion cover of a
test glues to a unique degree-zero class of the target restricting to each — the
`picEt` bridge plus DAT-2's S-lemma for the membership of the glued class. -/
theorem pic0Subgroup_existsUnique_of_cover (x : ∀ i, pic0Subgroup C (T' i))
    (hx : ∀ (i j : ι) (Z : Over (Spec (.of k))) (gi : Z ⟶ T' i) (gj : Z ⟶ T' j),
      gi ≫ f i = gj ≫ f j → pic0Map C gi (x i) = pic0Map C gj (x j)) :
    ∃! s : pic0Subgroup C T, ∀ i, pic0Map C (f i) s = x i := by
  obtain ⟨s, hs, huniq⟩ := picEt.existsUnique_of_cover f
    (fun i => (x i : picEt C (T' i))) hcov
    (fun i j Z gi gj hgf => congrArg Subtype.val (hx i j Z gi gj hgf))
  have hmem : s ∈ pic0Subgroup C T :=
    mem_pic0Subgroup_of_cover C f hcov (fun i => by rw [hs i]; exact (x i).2)
  refine ⟨⟨s, hmem⟩, fun i => Subtype.ext (hs i), fun s' hs' => Subtype.ext ?_⟩
  exact huniq (s' : picEt C T) fun i => congrArg Subtype.val (hs' i)

end Pic0

end AlgebraicGeometry
