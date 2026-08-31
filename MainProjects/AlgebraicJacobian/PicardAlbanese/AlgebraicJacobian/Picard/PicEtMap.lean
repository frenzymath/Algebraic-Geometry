/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtMapToolkit

/-!
# Functoriality of the étale-sheafified relative Picard functor

The Layer-2 functor `picEt` (`AlgebraicJacobian.Picard.PicEt`) is functorial along an
*arbitrary* morphism `f : T' ⟶ T` of test objects: the value of the restricted family at
an affine open `W ⊆ T'.left` — whose `f`-image need not lie in any affine open of
`T.left` — is *glued* over a finite basic-open refinement of `W` subordinate to the
preimages of affine opens, using the Zariski sheaf property of the affine étale Picard
functor (`AlgebraicJacobian.Picard.PicEtAffZariskiSep`, `PicEtAffZariskiGlue`) whose
gluing half is licensed by the (C1) étale separatedness.

* `AlgebraicGeometry.picEt.IsPullbackValue`: the characterizing property of the glued
  value — on every affine sub-open lying in the preimage of an affine open, it restricts
  to the pullback of the family value there.  Values with this property are unique
  (`pullbackValue_unique`, from Zariski separation) and exist
  (`exists_isPullbackValue`, from Zariski gluing).
* `AlgebraicGeometry.picEtMap C f : picEt C T →* picEt C T'` with the functor laws
  `picEtMap_id` and `picEtMap_comp`, and the functor
  `AlgebraicGeometry.picEtFunctor C : (Over (Spec k))ᵒᵖ ⥤ CommGrpCat`.
* `AlgebraicGeometry.picEtAffineEquiv_naturality`: the affine comparison
  (`AlgebraicJacobian.Picard.PicEt`) is natural in the test algebra.
* `AlgebraicGeometry.picEt.ext_of_le_cover`: **uniqueness of gluings** — two sections of
  `picEt C T` agreeing on every affine open subordinate to an open cover of `T.left`
  are equal (the separation half of the sheaf property of `picEt` itself).
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

namespace picEt

variable {T T' T'' : Over (Spec (.of k))}

/-! ## The characterizing property of the glued value -/

/-- The characterizing property of the value at `W` of the restriction of `s` along
`f`: on every affine sub-open of `W` contained in the preimage of an affine open `V` of
the target, it restricts to the pullback of the value of `s` at `V`. -/
def IsPullbackValue (f : T' ⟶ T) (s : picEt C T) (W : T'.left.affineOpens)
    (v : PicEtAff C Γ(T'.left, W.1)) : Prop :=
  ∀ (W₀ : T'.left.affineOpens) (hW₀ : W₀.1 ≤ W.1) (V : T.left.affineOpens)
    (hV : W₀.1 ≤ f.left ⁻¹ᵁ V.1),
    PicEtAff.mapAlg C (Over.resAlgHom T' hW₀) v
      = PicEtAff.mapAlg C (Over.appLEAlgHom f V.1 W₀.1 hV) (s.1 V)

/-- Values with the pullback property are unique. -/
theorem pullbackValue_unique {f : T' ⟶ T} {s : picEt C T} {W : T'.left.affineOpens}
    {v v' : PicEtAff C Γ(T'.left, W.1)} (hv : IsPullbackValue C f s W v)
    (hv' : IsPullbackValue C f s W v') : v = v' := by
  classical
  obtain ⟨sub, hspan, hsub⟩ := Scheme.exists_basic_subcover W.2
    (fun U₀ => ∃ V : T.left.affineOpens, U₀ = f.left ⁻¹ᵁ V.1)
    (fun w _ => by
      obtain ⟨V, hVaff, hfwV, -⟩ := Opens.isBasis_iff_nbhd.mp
        T.left.isBasis_affineOpens (show f.left.base w ∈ (⊤ : T.left.Opens) from trivial)
      exact ⟨f.left ⁻¹ᵁ V, hfwV, ⟨⟨V, hVaff⟩, rfl⟩⟩)
  refine eq_of_basic_eq C W sub hspan (fun r hr => ?_)
  obtain ⟨U₀, ⟨V, rfl⟩, hle⟩ := hsub r hr
  rw [hv ⟨_, W.2.basicOpen r⟩ (T'.left.basicOpen_le r) V hle,
    hv' ⟨_, W.2.basicOpen r⟩ (T'.left.basicOpen_le r) V hle]

variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

/-- The conversion between the abstract localization map of a basic-open inclusion and
the section restriction. -/
private lemma algHomOfDvd_eq_resAlgHom (W : T'.left.affineOpens)
    (a b : Γ(T'.left, W.1)) (hle : T'.left.basicOpen b ≤ T'.left.basicOpen a)
    (hdvd : a ∣ b) :
    haveI := W.2.isLocalization_basicOpen a
    haveI := W.2.isLocalization_basicOpen b
    (IsLocalization.Away.algHomOfDvd a b Γ(T'.left, T'.left.basicOpen a)
      Γ(T'.left, T'.left.basicOpen b) hdvd).restrictScalars k
      = Over.resAlgHom T' hle := by
  haveI := W.2.isLocalization_basicOpen a
  haveI := W.2.isLocalization_basicOpen b
  haveI hsub : Subsingleton (Γ(T'.left, T'.left.basicOpen a)
      →ₐ[Γ(T'.left, W.1)] Γ(T'.left, T'.left.basicOpen b)) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers a)
  rw [show IsLocalization.Away.algHomOfDvd a b Γ(T'.left, T'.left.basicOpen a)
      Γ(T'.left, T'.left.basicOpen b) hdvd = Over.resAwayAlgHom T' hle from
    Subsingleton.elim _ _]
  exact Over.resAwayAlgHom_restrictScalars T' hle

set_option maxHeartbeats 1600000 in
-- The instance towers over the section rings of the basic refinement exceed the
-- default elaboration budget.
/-- **Existence of the glued value**: the restriction of a compatible family along an
arbitrary morphism of test objects has a value at every affine open of the source,
glued over a finite basic-open refinement subordinate to the preimages of affine
opens. -/
theorem exists_isPullbackValue (f : T' ⟶ T) (s : picEt C T) (W : T'.left.affineOpens) :
    ∃ v, IsPullbackValue C f s W v := by
  classical
  -- the basic refinement subordinate to preimages of affine opens
  obtain ⟨sub, hspan, hsub⟩ := Scheme.exists_basic_subcover W.2
    (fun U₀ => ∃ V : T.left.affineOpens, U₀ = f.left ⁻¹ᵁ V.1)
    (fun w _ => by
      obtain ⟨V, hVaff, hfwV, -⟩ := Opens.isBasis_iff_nbhd.mp
        T.left.isBasis_affineOpens (show f.left.base w ∈ (⊤ : T.left.Opens) from trivial)
      exact ⟨f.left ⁻¹ᵁ V, hfwV, ⟨⟨V, hVaff⟩, rfl⟩⟩)
  have hsub' : ∀ r ∈ sub, ∃ V : T.left.affineOpens,
      T'.left.basicOpen r ≤ f.left ⁻¹ᵁ V.1 := fun r hr => by
    obtain ⟨U₀, ⟨V, rfl⟩, hle⟩ := hsub r hr
    exact ⟨V, hle⟩
  choose Vc hVc using hsub'
  -- the local values
  haveI hAway : ∀ r : ↥sub, IsLocalization.Away (r : Γ(T'.left, W.1))
      Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))) := fun r =>
    W.2.isLocalization_basicOpen (r : Γ(T'.left, W.1))
  haveI hAwayT : ∀ r r' : ↥sub,
      IsLocalization.Away ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))
        Γ(T'.left, T'.left.basicOpen
          ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))) := fun r r' =>
    W.2.isLocalization_basicOpen _
  have hbmul : ∀ r r' : ↥sub,
      T'.left.basicOpen ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))
        ≤ T'.left.basicOpen (r : Γ(T'.left, W.1)) := fun r r' => by
    rw [Scheme.basicOpen_mul]
    exact inf_le_left
  have hbmul' : ∀ r r' : ↥sub,
      T'.left.basicOpen ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))
        ≤ T'.left.basicOpen (r' : Γ(T'.left, W.1)) := fun r r' => by
    rw [Scheme.basicOpen_mul]
    exact inf_le_right
  -- glue
  obtain ⟨z, hz⟩ := PicEtAff.exists_mapAlg_eq_of_compat C
    (fun r : ↥sub => (r : Γ(T'.left, W.1)))
    (fun r : ↥sub => Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))))
    (fun r r' : ↥sub => Γ(T'.left, T'.left.basicOpen
      ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))))
    (by
      have hr : (Set.range fun r : ↥sub => (r : Γ(T'.left, W.1)))
          = (↑sub : Set Γ(T'.left, W.1)) := Subtype.range_coe
      rw [hr]
      exact hspan)
    (fun r => PicEtAff.mapAlg C
      (Over.appLEAlgHom f (Vc r.1 r.2).1 (T'.left.basicOpen r.1) (hVc r.1 r.2)) (s.1 (Vc r.1 r.2)))
    (fun r r' => by
      -- the overlap compatibility, from choice independence
      rw [algHomOfDvd_eq_resAlgHom W r.1 (r.1 * r'.1) (hbmul r r') (dvd_mul_right _ _),
        algHomOfDvd_eq_resAlgHom W r'.1 (r.1 * r'.1) (hbmul' r r') (dvd_mul_left _ _),
        ← PicEtAff.mapAlg_comp, ← PicEtAff.mapAlg_comp,
        Over.resAlgHom_comp_appLEAlgHom, Over.resAlgHom_comp_appLEAlgHom]
      exact mapAlg_appLE_eq C f s
        (W₀ := ⟨_, W.2.basicOpen (r.1 * r'.1)⟩) _ _)
  -- the glued value has the pullback property
  refine ⟨z, fun W₀ hW₀ V hV => ?_⟩
  obtain ⟨sub₀, hspan₀, hsub₀⟩ := Scheme.exists_basic_subcover W₀.2
    (fun U₀ => ∃ r ∈ sub, U₀ = T'.left.basicOpen r)
    (fun w hw => by
      have hwW : w ∈ (⨆ r ∈ (↑sub : Set Γ(T'.left, W.1)), T'.left.basicOpen r) := by
        rw [iSup_basicOpen_of_span_eq_top _ _ hspan]
        exact hW₀ hw
      obtain ⟨r, hr⟩ := Opens.mem_iSup.mp hwW
      obtain ⟨hrsub, hwr⟩ := Opens.mem_iSup.mp hr
      exact ⟨T'.left.basicOpen r, hwr, ⟨r, hrsub, rfl⟩⟩)
  refine eq_of_basic_eq C W₀ sub₀ hspan₀ (fun q hq => ?_)
  obtain ⟨U₀, ⟨r, hr, rfl⟩, hqle⟩ := hsub₀ q hq
  -- the left side restricts through the glued datum
  have hL : PicEtAff.mapAlg C (Over.resAlgHom T' (T'.left.basicOpen_le q))
      (PicEtAff.mapAlg C (Over.resAlgHom T' hW₀) z)
      = PicEtAff.mapAlg C (Over.appLEAlgHom f (Vc r hr).1 (T'.left.basicOpen q)
          (hqle.trans (hVc r hr))) (s.1 (Vc r hr)) := by
    have hzr := hz ⟨r, hr⟩
    rw [show IsScalarTower.toAlgHom k Γ(T'.left, W.1)
        Γ(T'.left, T'.left.basicOpen r)
      = Over.resAlgHom T' (T'.left.basicOpen_le r) from AlgHom.ext fun _ => rfl] at hzr
    rw [← PicEtAff.mapAlg_comp, Over.resAlgHom_comp,
      show ((T'.left.basicOpen_le q).trans hW₀ :
          T'.left.basicOpen q ≤ W.1)
        = (hqle.trans (T'.left.basicOpen_le r)) from rfl,
      ← Over.resAlgHom_comp T' hqle (T'.left.basicOpen_le r), PicEtAff.mapAlg_comp,
      hzr, ← PicEtAff.mapAlg_comp, Over.resAlgHom_comp_appLEAlgHom]
  -- the right side restricts directly
  rw [hL, ← PicEtAff.mapAlg_comp, Over.resAlgHom_comp_appLEAlgHom]
  exact mapAlg_appLE_eq C f s (W₀ := ⟨_, W₀.2.basicOpen q⟩) _ _

/-- Existence and uniqueness of the glued value. -/
theorem existsUnique_isPullbackValue (f : T' ⟶ T) (s : picEt C T)
    (W : T'.left.affineOpens) : ∃! v, IsPullbackValue C f s W v := by
  obtain ⟨v, hv⟩ := exists_isPullbackValue C f s W
  exact ⟨v, hv, fun v' hv' => pullbackValue_unique C hv' hv⟩

end picEt

/-! ## The functoriality -/

section Map

variable {T T' T'' : Over (Spec (.of k))}
variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

open picEt

/-- The value of the restricted family at an affine open of the source. -/
noncomputable def picEtMapVal (f : T' ⟶ T) (s : picEt C T) (W : T'.left.affineOpens) :
    PicEtAff C Γ(T'.left, W.1) :=
  (existsUnique_isPullbackValue C f s W).choose

lemma picEtMapVal_spec (f : T' ⟶ T) (s : picEt C T) (W : T'.left.affineOpens) :
    IsPullbackValue C f s W (picEtMapVal C f s W) :=
  (existsUnique_isPullbackValue C f s W).choose_spec.1

lemma picEtMapVal_eq_of (f : T' ⟶ T) (s : picEt C T) {W : T'.left.affineOpens}
    {v : PicEtAff C Γ(T'.left, W.1)} (hv : IsPullbackValue C f s W v) :
    picEtMapVal C f s W = v :=
  pullbackValue_unique C (picEtMapVal_spec C f s W) hv

/-- The value of the restricted family on an affine open lying in the preimage of an
affine open is the plain pullback. -/
lemma picEtMapVal_eq_mapAlg (f : T' ⟶ T) (s : picEt C T) {W : T'.left.affineOpens}
    {V : T.left.affineOpens} (hV : W.1 ≤ f.left ⁻¹ᵁ V.1) :
    picEtMapVal C f s W = PicEtAff.mapAlg C (Over.appLEAlgHom f V.1 W.1 hV) (s.1 V) := by
  have h := picEtMapVal_spec C f s W W le_rfl V hV
  rwa [Over.resAlgHom_rfl, PicEtAff.mapAlg_id] at h

/-- **Restriction of `picEt` along an arbitrary morphism of test objects.** -/
noncomputable def picEtMap (f : T' ⟶ T) : picEt C T →* picEt C T' where
  toFun s := ⟨fun W => picEtMapVal C f s W, by
    intro U V h
    refine (picEtMapVal_eq_of C f s (W := U) ?_).symm
    intro W₀ hW₀ V' hV'
    rw [← PicEtAff.mapAlg_comp, Over.resAlgHom_comp]
    exact picEtMapVal_spec C f s V W₀ (hW₀.trans h) V' hV'⟩
  map_one' := by
    refine picEt.ext fun W => ?_
    change picEtMapVal C f 1 W = 1
    refine picEtMapVal_eq_of C f 1 ?_
    intro W₀ hW₀ V hV
    rw [picEt.one_val, map_one, map_one]
  map_mul' s t := by
    refine picEt.ext fun W => ?_
    change picEtMapVal C f (s * t) W = picEtMapVal C f s W * picEtMapVal C f t W
    refine picEtMapVal_eq_of C f (s * t) ?_
    intro W₀ hW₀ V hV
    rw [picEt.mul_val, map_mul, map_mul,
      picEtMapVal_spec C f s W W₀ hW₀ V hV, picEtMapVal_spec C f t W W₀ hW₀ V hV]

@[simp]
lemma picEtMap_val (f : T' ⟶ T) (s : picEt C T) (W : T'.left.affineOpens) :
    (picEtMap C f s).1 W = picEtMapVal C f s W :=
  rfl

/-- The functor law: restriction along the identity is the identity. -/
theorem picEtMap_id (s : picEt C T) : picEtMap C (𝟙 T) s = s := by
  refine picEt.ext fun W => ?_
  rw [picEtMap_val]
  refine picEtMapVal_eq_of C (𝟙 T) s ?_
  intro W₀ hW₀ V hV
  have hV' : W₀.1 ≤ V.1 := by
    intro p hp
    have hmem := hV hp
    rw [Over.id_left] at hmem
    exact hmem
  rw [Over.appLEAlgHom_id T V.1 W₀.1 hV hV', s.compat W₀ W hW₀, s.compat W₀ V hV']

/-- The functor law: restriction along a composite is the composite of the
restrictions. -/
theorem picEtMap_comp (f : T' ⟶ T) (g : T'' ⟶ T') (s : picEt C T) :
    picEtMap C (g ≫ f) s = picEtMap C g (picEtMap C f s) := by
  classical
  refine picEt.ext fun W => ?_
  rw [picEtMap_val, picEtMap_val]
  refine (picEtMapVal_eq_of C (g ≫ f) s ?_)
  intro W₀ hW₀ V hV
  -- refine by basic opens whose `g`-image lies in an affine open inside `f⁻¹ V`
  obtain ⟨sub, hspan, hsub⟩ := Scheme.exists_basic_subcover W₀.2
    (fun U₀ => ∃ V'' : T'.left.affineOpens,
      V''.1 ≤ f.left ⁻¹ᵁ V.1 ∧ U₀ = g.left ⁻¹ᵁ V''.1)
    (fun w hw => by
      have hgw : g.left.base w ∈ f.left ⁻¹ᵁ V.1 := by
        have := hV hw
        rw [Over.comp_left] at this
        exact this
      obtain ⟨V'', hV''aff, hgwV'', hV''le⟩ := Opens.isBasis_iff_nbhd.mp
        T'.left.isBasis_affineOpens hgw
      exact ⟨g.left ⁻¹ᵁ V'', hgwV'', ⟨⟨V'', hV''aff⟩, hV''le, rfl⟩⟩)
  refine eq_of_basic_eq C W₀ sub hspan (fun q hq => ?_)
  obtain ⟨U₀, ⟨V'', hV''le, rfl⟩, hqle⟩ := hsub q hq
  -- the left side, through the two glued values
  have hL : PicEtAff.mapAlg C (Over.resAlgHom T'' (T''.left.basicOpen_le q))
      (PicEtAff.mapAlg C (Over.resAlgHom T'' hW₀)
        (picEtMapVal C g (picEtMap C f s) W))
      = PicEtAff.mapAlg C (Over.appLEAlgHom g V''.1 (T''.left.basicOpen q) hqle)
          (PicEtAff.mapAlg C (Over.appLEAlgHom f V.1 V''.1 hV''le) (s.1 V)) := by
    rw [← PicEtAff.mapAlg_comp, Over.resAlgHom_comp,
      picEtMapVal_spec C g (picEtMap C f s) W ⟨_, W₀.2.basicOpen q⟩
        ((T''.left.basicOpen_le q).trans hW₀) V'' hqle,
      picEtMap_val, picEtMapVal_eq_mapAlg C f s hV''le]
  rw [hL, ← PicEtAff.mapAlg_comp, ← PicEtAff.mapAlg_comp,
    Over.appLEAlgHom_comp f g V.1 V''.1 (T''.left.basicOpen q) hV''le hqle
      (hqle.trans ((g.left.preimage_mono hV''le).trans
        (le_of_eq (by rw [Over.comp_left, Scheme.Hom.comp_preimage])))),
    Over.resAlgHom_comp_appLEAlgHom]

/-- **The étale-sheafified relative Picard functor** of a proper, geometrically
irreducible and geometrically reduced curve, on all test objects. -/
noncomputable def picEtFunctor : (Over (Spec (.of k)))ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (picEt C T.unop)
  map g := CommGrpCat.ofHom (picEtMap C g.unop)
  map_id T := by
    ext s U
    exact congrArg (fun z : picEt C T.unop => z.1 U) (picEtMap_id C s)
  map_comp g h := by
    ext s U
    exact congrArg (fun z => z.1 U) (picEtMap_comp C g.unop h.unop s)

end Map

/-! ## Naturality of the affine comparison -/

section AffineNaturality

variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- The affine comparison intertwines the section-ring pullback along `Spec` of an
algebra map with the algebra map itself. -/
private lemma overSpecΓTop_appLE_comp (φ : A →ₐ[k] B) :
    (Over.overSpecΓTopAlgEquiv k B).toAlgHom.comp
      (Over.appLEAlgHom (Over.overSpecMap φ) (overSpecTopAffine A).1
        (overSpecTopAffine B).1 le_top)
      = φ.comp (Over.overSpecΓTopAlgEquiv k A).toAlgHom := by
  have key : (Over.overSpecMap φ).left.appLE (overSpecTopAffine A).1
        (overSpecTopAffine B).1 le_top ≫ (Scheme.ΓSpecIso (.of B)).hom
      = (Scheme.ΓSpecIso (.of A)).hom ≫ CommRingCat.ofHom φ.toRingHom := by
    have h₁ : (Over.overSpecMap φ).left.appLE (overSpecTopAffine A).1
          (overSpecTopAffine B).1 le_top
        = (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [h₁]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom)
  ext x
  exact congr($(key).hom x)

/-- **Naturality of the affine comparison**: over affine tests, `picEtMap` along `Spec`
of an algebra map corresponds to `PicEtAff.mapAlg` under the comparison isomorphisms. -/
theorem picEtAffineEquiv_naturality (φ : A →ₐ[k] B) (s : picEt C (overSpec k A)) :
    picEtAffineEquiv C B (picEtMap C (Over.overSpecMap φ) s)
      = PicEtAff.mapAlg C φ (picEtAffineEquiv C A s) := by
  rw [picEtAffineEquiv_apply, picEtAffineEquiv_apply, picEtMap_val]
  have hval := picEtMapVal_eq_mapAlg C (Over.overSpecMap φ) s
    (W := overSpecTopAffine B) (V := overSpecTopAffine A) le_top
  rw [hval]
  calc PicEtAff.mapAlg C (Over.overSpecΓTopAlgEquiv k B).toAlgHom
        (PicEtAff.mapAlg C (Over.appLEAlgHom (Over.overSpecMap φ)
          (overSpecTopAffine A).1 (overSpecTopAffine B).1 le_top)
          (s.1 (overSpecTopAffine A)))
      = PicEtAff.mapAlg C ((Over.overSpecΓTopAlgEquiv k B).toAlgHom.comp
          (Over.appLEAlgHom (Over.overSpecMap φ)
            (overSpecTopAffine A).1 (overSpecTopAffine B).1 le_top))
          (s.1 (overSpecTopAffine A)) := (PicEtAff.mapAlg_comp C _ _ _).symm
    _ = PicEtAff.mapAlg C (φ.comp (Over.overSpecΓTopAlgEquiv k A).toAlgHom)
          (s.1 (overSpecTopAffine A)) := by
        rw [overSpecΓTop_appLE_comp φ]
        exact rfl
    _ = PicEtAff.mapAlg C φ (PicEtAff.mapAlg C
          (Over.overSpecΓTopAlgEquiv k A).toAlgHom (s.1 (overSpecTopAffine A))) :=
        PicEtAff.mapAlg_comp C _ _ _

end AffineNaturality

/-! ## Uniqueness of gluings for `picEt` itself -/

/-- **Uniqueness of gluings**: two sections of `picEt C T` agreeing on every affine open
subordinate to an open cover of `T.left` are equal — the separation half of the sheaf
property of the Layer-2 functor, the binding input of the (C2) comparison and the
degree interface. -/
theorem picEt.ext_of_le_cover {T : Over (Spec (.of k))} {ι' : Type*}
    (O : ι' → T.left.Opens) (hcov : ∀ p : T.left, ∃ i, p ∈ O i) {s t : picEt C T}
    (h : ∀ (U : T.left.affineOpens) (i : ι'), U.1 ≤ O i → s.1 U = t.1 U) : s = t := by
  classical
  refine picEt.ext fun U => ?_
  obtain ⟨sub, hspan, hsub⟩ := Scheme.exists_basic_subcover U.2
    (fun U₀ => ∃ i, U₀ ≤ O i)
    (fun w _ => by
      obtain ⟨i, hi⟩ := hcov w
      exact ⟨O i, hi, ⟨i, le_rfl⟩⟩)
  refine picEt.eq_of_basic_eq C U sub hspan (fun r hr => ?_)
  obtain ⟨U₀, ⟨i, hle⟩, hrle⟩ := hsub r hr
  rw [s.compat ⟨_, U.2.basicOpen r⟩ U (T.left.basicOpen_le r),
    t.compat ⟨_, U.2.basicOpen r⟩ U (T.left.basicOpen_le r)]
  exact h ⟨T.left.basicOpen r, U.2.basicOpen r⟩ i (hrle.trans hle)

end AlgebraicGeometry
