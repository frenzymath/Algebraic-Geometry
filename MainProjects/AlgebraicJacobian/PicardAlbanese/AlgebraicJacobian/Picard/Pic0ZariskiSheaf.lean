/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0Functor

/-!
# The degree-zero Picard functor is a Zariski sheaf on the slice (DAT-2)

The datum campaign feeds the degree-zero relative Picard functor `pic0Functor C`
(`AlgebraicJacobian.Picard.Pic0Functor`) to mathlib's local-representability engine
(01JJ, `AlgebraicGeometry.Scheme.LocalRepresentability.representableBy`) through the
slice trick.  That engine consumes an honest Zariski sheaf.  This file certifies the
sheaf condition of the affine-opens-limit vehicle `picEt` and of its degree-zero
subfunctor `pic0` for *arbitrary* Zariski open covers of *arbitrary* tests in
`Over (Spec k)` — the separation and gluing halves — together with the S-lemma that
makes `pic0` a *sub*sheaf: degree-zero membership is Zariski-local.

The affine basic-open halves are landed
(`AlgebraicJacobian.Picard.PicEtAffZariskiSep`, `PicEtAffZariskiGlue`); this file lifts
them from the affine test to an arbitrary test through the affine-opens limit.

## Separation

* `AlgebraicGeometry.picEt.ext_of_le_cover` (landed, `PicEtMap`): two sections of
  `picEt C T` agreeing on affine opens subordinate to an open cover of `T.left` agree.
* `AlgebraicGeometry.pic0.ext_of_le_cover`: the same for degree-zero classes.

## Gluing

* `AlgebraicGeometry.picEt.IsGlueValue`: the characterizing property of the value at an
  affine open of a section glued from a compatible family of local data on an open
  cover.  Values are unique (`glueValue_unique`) and exist (`exists_isGlueValue`).
* `AlgebraicGeometry.picEt.existsUnique_glue_of_le_cover`: **the gluing half** — a
  family of local sections on an open cover, compatible on the affine overlaps, glues
  to a unique section of `picEt C T`.

## The S-lemma (degree-zero is Zariski-local)

* `AlgebraicGeometry.mem_pic0Subgroup_of_forall_factor`: if a class restricts to a
  degree-zero class on each member of an open-immersion cover, it is degree-zero — a
  field point of `T` factors through some cover member, where its degree is read.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

namespace picEt

variable {C}
variable {T : Over (Spec (.of k))} {ι : Type u} (O : ι → T.left.Opens)

/-- The conversion between the abstract localization map of a basic-open inclusion and
the section restriction (local copy of the `PicEtMap` helper). -/
private lemma algHomOfDvd_eq_resAlgHom (W : T.left.affineOpens)
    (a b : Γ(T.left, W.1)) (hle : T.left.basicOpen b ≤ T.left.basicOpen a)
    (hdvd : a ∣ b) :
    haveI := W.2.isLocalization_basicOpen a
    haveI := W.2.isLocalization_basicOpen b
    (IsLocalization.Away.algHomOfDvd a b Γ(T.left, T.left.basicOpen a)
      Γ(T.left, T.left.basicOpen b) hdvd).restrictScalars k
      = Over.resAlgHom T hle := by
  haveI := W.2.isLocalization_basicOpen a
  haveI := W.2.isLocalization_basicOpen b
  haveI hsub : Subsingleton (Γ(T.left, T.left.basicOpen a)
      →ₐ[Γ(T.left, W.1)] Γ(T.left, T.left.basicOpen b)) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers a)
  rw [show IsLocalization.Away.algHomOfDvd a b Γ(T.left, T.left.basicOpen a)
      Γ(T.left, T.left.basicOpen b) hdvd = Over.resAwayAlgHom T hle from
    Subsingleton.elim _ _]
  exact Over.resAwayAlgHom_restrictScalars T hle

/-! ## Local data on an open cover -/

/-- **Compatible local data** on an open cover `O` of `T.left`: a plus class at every
affine open subordinate to a cover member, restricting correctly within a member
(`res`) and agreeing across members on shared affine opens (`glue`).  This is the input
of the gluing half — the vehicle-native spelling of a compatible family of sections of
`picEt` over the cover. -/
structure LocalData (v : ∀ (i : ι) (W : T.left.affineOpens), W.1 ≤ O i →
    PicEtAff C Γ(T.left, W.1)) : Prop where
  res : ∀ (i : ι) (W W' : T.left.affineOpens) (hW : W.1 ≤ O i) (hW' : W'.1 ≤ O i)
    (h : W.1 ≤ W'.1),
      PicEtAff.mapAlg C (Over.resAlgHom T h) (v i W' hW') = v i W hW
  glue : ∀ (i j : ι) (W : T.left.affineOpens) (hi : W.1 ≤ O i) (hj : W.1 ≤ O j),
      v i W hi = v j W hj

variable (v : ∀ (i : ι) (W : T.left.affineOpens), W.1 ≤ O i → PicEtAff C Γ(T.left, W.1))

/-- The characterizing property of the glued value at `W`: on every affine sub-open of
`W` contained in a cover member, it restricts to the local datum there. -/
def IsGlueValue (W : T.left.affineOpens) (z : PicEtAff C Γ(T.left, W.1)) : Prop :=
  ∀ (W₀ : T.left.affineOpens) (hW₀ : W₀.1 ≤ W.1) (i : ι) (hi : W₀.1 ≤ O i),
    PicEtAff.mapAlg C (Over.resAlgHom T hW₀) z = v i W₀ hi

variable {O v}

omit [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom] in
/-- Glued values are unique. -/
theorem glueValue_unique (hcov : ∀ p : T.left, ∃ i, p ∈ O i)
    {W : T.left.affineOpens} {z z' : PicEtAff C Γ(T.left, W.1)}
    (hz : IsGlueValue O v W z) (hz' : IsGlueValue O v W z') : z = z' := by
  classical
  obtain ⟨sub, hspan, hsub⟩ := Scheme.exists_basic_subcover W.2
    (fun U₀ => ∃ i, U₀ ≤ O i)
    (fun w _ => by obtain ⟨i, hi⟩ := hcov w; exact ⟨O i, hi, ⟨i, le_rfl⟩⟩)
  refine eq_of_basic_eq C W sub hspan (fun r hr => ?_)
  obtain ⟨U₀, ⟨i, hi⟩, hle⟩ := hsub r hr
  rw [hz ⟨_, W.2.basicOpen r⟩ (T.left.basicOpen_le r) i (hle.trans hi),
    hz' ⟨_, W.2.basicOpen r⟩ (T.left.basicOpen_le r) i (hle.trans hi)]

set_option maxHeartbeats 1600000 in
-- The instance towers over the section rings of the basic refinement exceed the
-- default elaboration budget (as in `PicEtMap.exists_isPullbackValue`).
/-- **Existence of the glued value**: compatible local data on an open cover has a value
at every affine open of `T.left`, glued over a finite basic-open refinement subordinate
to the cover. -/
theorem exists_isGlueValue (hcov : ∀ p : T.left, ∃ i, p ∈ O i)
    (hv : LocalData O v) (W : T.left.affineOpens) :
    ∃ z, IsGlueValue O v W z := by
  classical
  -- the basic refinement subordinate to the cover
  obtain ⟨sub, hspan, hsub⟩ := Scheme.exists_basic_subcover W.2
    (fun U₀ => ∃ i, U₀ ≤ O i)
    (fun w _ => by obtain ⟨i, hi⟩ := hcov w; exact ⟨O i, hi, ⟨i, le_rfl⟩⟩)
  have hsub' : ∀ r ∈ sub, ∃ i, T.left.basicOpen r ≤ O i := fun r hr => by
    obtain ⟨U₀, ⟨i, hi⟩, hle⟩ := hsub r hr
    exact ⟨i, hle.trans hi⟩
  choose ic hic using hsub'
  -- localization instances for the basic opens and their overlaps
  haveI hAway : ∀ r : ↥sub, IsLocalization.Away (r : Γ(T.left, W.1))
      Γ(T.left, T.left.basicOpen (r : Γ(T.left, W.1))) := fun r =>
    W.2.isLocalization_basicOpen (r : Γ(T.left, W.1))
  haveI hAwayT : ∀ r r' : ↥sub,
      IsLocalization.Away ((r : Γ(T.left, W.1)) * (r' : Γ(T.left, W.1)))
        Γ(T.left, T.left.basicOpen
          ((r : Γ(T.left, W.1)) * (r' : Γ(T.left, W.1)))) := fun r r' =>
    W.2.isLocalization_basicOpen _
  have hbmul : ∀ r r' : ↥sub,
      T.left.basicOpen ((r : Γ(T.left, W.1)) * (r' : Γ(T.left, W.1)))
        ≤ T.left.basicOpen (r : Γ(T.left, W.1)) := fun r r' => by
    rw [Scheme.basicOpen_mul]; exact inf_le_left
  have hbmul' : ∀ r r' : ↥sub,
      T.left.basicOpen ((r : Γ(T.left, W.1)) * (r' : Γ(T.left, W.1)))
        ≤ T.left.basicOpen (r' : Γ(T.left, W.1)) := fun r r' => by
    rw [Scheme.basicOpen_mul]; exact inf_le_right
  -- glue the local pieces
  obtain ⟨z, hz⟩ := PicEtAff.exists_mapAlg_eq_of_compat C
    (fun r : ↥sub => (r : Γ(T.left, W.1)))
    (fun r : ↥sub => Γ(T.left, T.left.basicOpen (r : Γ(T.left, W.1))))
    (fun r r' : ↥sub => Γ(T.left, T.left.basicOpen
      ((r : Γ(T.left, W.1)) * (r' : Γ(T.left, W.1)))))
    (by
      have hr : (Set.range fun r : ↥sub => (r : Γ(T.left, W.1)))
          = (↑sub : Set Γ(T.left, W.1)) := Subtype.range_coe
      rw [hr]; exact hspan)
    (fun r => v (ic r.1 r.2) ⟨_, W.2.basicOpen r.1⟩ (hic r.1 r.2))
    (fun r r' => by
      -- the overlap compatibility, from `res` and `glue`
      rw [algHomOfDvd_eq_resAlgHom ⟨_, W.2⟩ r.1 (r.1 * r'.1) (hbmul r r') (dvd_mul_right _ _),
        algHomOfDvd_eq_resAlgHom ⟨_, W.2⟩ r'.1 (r.1 * r'.1) (hbmul' r r') (dvd_mul_left _ _)]
      rw [hv.res (ic r.1 r.2) ⟨_, W.2.basicOpen (r.1 * r'.1)⟩ ⟨_, W.2.basicOpen r.1⟩
          ((hbmul r r').trans (hic r.1 r.2)) (hic r.1 r.2) (hbmul r r'),
        hv.res (ic r'.1 r'.2) ⟨_, W.2.basicOpen (r.1 * r'.1)⟩ ⟨_, W.2.basicOpen r'.1⟩
          ((hbmul' r r').trans (hic r'.1 r'.2)) (hic r'.1 r'.2) (hbmul' r r')]
      exact hv.glue (ic r.1 r.2) (ic r'.1 r'.2) ⟨_, W.2.basicOpen (r.1 * r'.1)⟩
        ((hbmul r r').trans (hic r.1 r.2)) ((hbmul' r r').trans (hic r'.1 r'.2)))
  -- the glued value has the characterizing property
  refine ⟨z, fun W₀ hW₀ i hi => ?_⟩
  obtain ⟨sub₀, hspan₀, hsub₀⟩ := Scheme.exists_basic_subcover W₀.2
    (fun U₀ => ∃ r ∈ sub, U₀ = T.left.basicOpen r)
    (fun w hw => by
      have hwW : w ∈ (⨆ r ∈ (↑sub : Set Γ(T.left, W.1)), T.left.basicOpen r) := by
        rw [iSup_basicOpen_of_span_eq_top _ _ hspan]; exact hW₀ hw
      obtain ⟨r, hr⟩ := Opens.mem_iSup.mp hwW
      obtain ⟨hrsub, hwr⟩ := Opens.mem_iSup.mp hr
      exact ⟨T.left.basicOpen r, hwr, ⟨r, hrsub, rfl⟩⟩)
  refine eq_of_basic_eq C W₀ sub₀ hspan₀ (fun q hq => ?_)
  obtain ⟨U₀, ⟨r, hr, rfl⟩, hqle⟩ := hsub₀ q hq
  -- the left side restricts through the glued datum
  have hzr := hz ⟨r, hr⟩
  rw [show IsScalarTower.toAlgHom k Γ(T.left, W.1)
      Γ(T.left, T.left.basicOpen r)
    = Over.resAlgHom T (T.left.basicOpen_le r) from AlgHom.ext fun _ => rfl] at hzr
  have hL : PicEtAff.mapAlg C (Over.resAlgHom T (T.left.basicOpen_le q))
      (PicEtAff.mapAlg C (Over.resAlgHom T hW₀) z)
      = v (ic r hr) ⟨_, W₀.2.basicOpen q⟩ (hqle.trans (hic r hr)) := by
    rw [← PicEtAff.mapAlg_comp, Over.resAlgHom_comp,
      show ((T.left.basicOpen_le q).trans hW₀ : T.left.basicOpen q ≤ W.1)
        = (hqle.trans (T.left.basicOpen_le r)) from rfl,
      ← Over.resAlgHom_comp T hqle (T.left.basicOpen_le r), PicEtAff.mapAlg_comp, hzr]
    exact hv.res (ic r hr) ⟨_, W₀.2.basicOpen q⟩ ⟨_, W.2.basicOpen r⟩
      (hqle.trans (hic r hr)) (hic r hr) hqle
  -- the right side restricts the local datum directly
  rw [hL, hv.res i ⟨_, W₀.2.basicOpen q⟩ W₀ ((T.left.basicOpen_le q).trans hi) hi
    (T.left.basicOpen_le q)]
  exact hv.glue (ic r hr) i ⟨_, W₀.2.basicOpen q⟩ (hqle.trans (hic r hr))
    ((T.left.basicOpen_le q).trans hi)

/-! ## Assembling the glued section -/

variable (hcov : ∀ p : T.left, ∃ i, p ∈ O i) (hv : LocalData O v)

/-- The glued value at an affine open of `T.left`. -/
noncomputable def glueValue (W : T.left.affineOpens) : PicEtAff C Γ(T.left, W.1) :=
  (exists_isGlueValue hcov hv W).choose

lemma glueValue_spec (W : T.left.affineOpens) : IsGlueValue O v W (glueValue hcov hv W) :=
  (exists_isGlueValue hcov hv W).choose_spec

lemma glueValue_eq_of {W : T.left.affineOpens} {z : PicEtAff C Γ(T.left, W.1)}
    (hz : IsGlueValue O v W z) : glueValue hcov hv W = z :=
  glueValue_unique hcov (glueValue_spec hcov hv W) hz

/-- **The glued section**: compatible local data on an open cover assembles to a section
of `picEt C T`. -/
noncomputable def glueSection : picEt C T :=
  ⟨fun W => glueValue hcov hv W, by
    intro U V h
    refine (glueValue_eq_of hcov hv ?_).symm
    intro W₀ hW₀ i hi
    rw [← PicEtAff.mapAlg_comp, Over.resAlgHom_comp]
    exact glueValue_spec hcov hv V W₀ (hW₀.trans h) i hi⟩

/-- The glued section restricts to the local datum on each cover member. -/
theorem glueSection_eq (i : ι) (W : T.left.affineOpens) (hW : W.1 ≤ O i) :
    (glueSection hcov hv).1 W = v i W hW := by
  have h := glueValue_spec hcov hv W W le_rfl i hW
  rwa [Over.resAlgHom_rfl, PicEtAff.mapAlg_id] at h

include hcov hv in
/-- **The gluing half of the Zariski sheaf property of `picEt`**: a family of local
sections on an open cover of `T.left`, compatible on the affine overlaps
(`LocalData`), glues to a unique section of `picEt C T` restricting to each. -/
theorem existsUnique_glue_of_le_cover :
    ∃! s : picEt C T, ∀ (i : ι) (W : T.left.affineOpens) (hW : W.1 ≤ O i),
      s.1 W = v i W hW := by
  refine ⟨glueSection hcov hv, fun i W hW => glueSection_eq hcov hv i W hW, fun s hs => ?_⟩
  refine picEt.ext_of_le_cover C O hcov (fun U i hU => ?_)
  rw [hs i U hU, glueSection_eq hcov hv i U hU]

end picEt

/-! ## Separation for the degree-zero subfunctor -/

variable [SmoothOfRelativeDimension 1 C.hom]

omit [GeometricallyReduced C.hom] in
/-- **Separation for `pic0`**: two degree-zero classes agreeing on the affine opens
subordinate to an open cover of `T.left` agree — immediate from the separation of
`picEt`, since `pic0Subgroup` is a subgroup. -/
theorem pic0Subgroup_ext_of_le_cover {T : Over (Spec (.of k))} {ι' : Type*}
    (O : ι' → T.left.Opens) (hcov : ∀ p : T.left, ∃ i, p ∈ O i)
    {s t : pic0Subgroup C T}
    (h : ∀ (U : T.left.affineOpens) (i : ι'), U.1 ≤ O i →
      (s : picEt C T).1 U = (t : picEt C T).1 U) : s = t :=
  Subtype.ext (picEt.ext_of_le_cover C O hcov h)

/-! ## The S-lemma: degree-zero membership is Zariski-local -/

/-- **The S-lemma** (degree-zero is Zariski-local): a class whose restriction to each
member of an open-immersion cover of the test is degree-zero is itself degree-zero.  A
field point of `T` factors through some cover member (its image is a single point,
contained in a member's range), where its degree is read; this is what makes the
degree-zero subfunctor a *sub*sheaf, not merely a subfunctor of the sheaf `picEt`. -/
theorem mem_pic0Subgroup_of_cover {T : Over (Spec (.of k))} {ι : Type*}
    {T' : ι → Over (Spec (.of k))} (f : ∀ i, T' i ⟶ T)
    [∀ i, IsOpenImmersion (f i).left]
    (hcov : ∀ p : T.left, ∃ i, p ∈ (f i).left.opensRange)
    {lam : picEt C T} (hloc : ∀ i, picEtMap C (f i) lam ∈ pic0Subgroup C (T' i)) :
    lam ∈ pic0Subgroup C T := by
  rw [mem_pic0Subgroup_iff]
  intro K _ _ t
  haveI : Nonempty ↥(overSpec k K).left := inferInstanceAs (Nonempty ↥(Spec (.of K)))
  haveI : Subsingleton ↥(overSpec k K).left :=
    inferInstanceAs (Subsingleton ↥(Spec (.of K)))
  -- the field point has a single-point image; pick a cover member containing it
  obtain ⟨i, hi⟩ := hcov (t.left.base (Classical.arbitrary _))
  have hrange : Set.range t.left.base ⊆ Set.range (f i).left.base := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (Classical.arbitrary _)]
    obtain ⟨x, hx⟩ := hi
    exact ⟨x, hx⟩
  -- factor `t` through the cover member `f i`
  set g := IsOpenImmersion.lift (f i).left t.left hrange with hg
  have hfac : g ≫ (f i).left = t.left := IsOpenImmersion.lift_fac _ _ hrange
  set t' : overSpec k K ⟶ T' i := Over.homMk g (by
    rw [← Over.w (f i), ← Category.assoc, hfac]; exact Over.w t) with ht'
  have htt : t = t' ≫ f i := by
    ext : 1
    rw [Over.comp_left]
    exact hfac.symm
  rw [htt, ← degAt_picEtMap (f i) lam t']
  exact (mem_pic0Subgroup_iff.mp (hloc i)) K t'

end AlgebraicGeometry
