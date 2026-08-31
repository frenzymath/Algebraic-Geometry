/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZarMapKit

/-!
# Functoriality of the locally certified divisor vehicle (DD-2 stage S6a)

The locally certified vehicle `divFamZar`
(`AlgebraicJacobian.Picard.DivisorFamilyZarVehicle`) is functorial along an
*arbitrary* morphism `f : T' ⟶ T` of test objects: the value of the restricted family
at an affine open `W ⊆ T'.left` — whose `f`-image need not lie in any affine open of
`T.left` — is *glued* over a finite basic-open refinement of `W` subordinate to the
preimages of affine opens, using the S5b Zariski keystones of `DivFamZar` through the
basic-open toolkit (`AlgebraicJacobian.Picard.DivisorFamilyZarMapKit`).  This is the
`picEtMap` pattern (`AlgebraicJacobian.Picard.PicEtMap`), clause for clause.

* `AlgebraicGeometry.divFamZar.IsPullbackValue`: the characterizing property of the
  glued value — on every affine sub-open lying in the preimage of an affine open, it
  restricts to the pullback of the family value there.  Values with this property are
  unique (`pullbackValue_unique`, from Zariski separation) and exist
  (`exists_isPullbackValue`, from Zariski gluing).
* `AlgebraicGeometry.divFamZar.map C π n f : divFamZar C π n T → divFamZar C π n T'`
  with the functor laws `divFamZar.map_id` and `divFamZar.map_comp`, and the
  no-gluing evaluation `divFamZar.mapVal_eq_mapAlgHom` on affine opens lying in a
  preimage.
* `AlgebraicGeometry.divFamZarAffineEquiv_naturality`: the affine comparison
  (`AlgebraicJacobian.Picard.DivisorFamilyZarVehicle`) is natural in the test algebra —
  over affine tests, `divFamZar.map` along `Spec` of an algebra map corresponds to the
  affine-level `DivFamZar.mapAlgHom` under the comparison equivalences.

The `divFunctor` packaging as a `CategoryTheory` functor is deliberately NOT frozen
here (`informal/spec-dd-2.md` §6: the exact functor spelling is co-signed with the
DD-R lane before freezing); everything up to it is delivered.
-/

set_option autoImplicit false
/- Statements mix the section rings `Γ(T.left, ·)` with the locally certified
divisor-functor values over them, which are stated on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}

namespace divFamZar

variable {T T' T'' : Over (Spec (.of k))}

/-! ## The characterizing property of the glued value -/

variable (C π n) in
/-- The characterizing property of the value at `W` of the restriction of `s` along
`f`: on every affine sub-open of `W` contained in the preimage of an affine open `V`
of the target, it restricts to the pullback of the value of `s` at `V`. -/
def IsPullbackValue (f : T' ⟶ T) (s : divFamZar C π n T) (W : T'.left.affineOpens)
    (v : DivFamZar C Γ(T'.left, W.1) π n) : Prop :=
  ∀ (W₀ : T'.left.affineOpens) (hW₀ : W₀.1 ≤ W.1) (V : T.left.affineOpens)
    (hV : W₀.1 ≤ f.left ⁻¹ᵁ V.1),
    DivFamZar.mapAlgHom (Over.resAlgHom T' hW₀) v
      = DivFamZar.mapAlgHom (Over.appLEAlgHom f V.1 W₀.1 hV) (s.1 V)

/-- Values with the pullback property are unique — from the Zariski separation of
`DivFamZar` over a basic refinement subordinate to the preimages of affine opens. -/
theorem pullbackValue_unique {f : T' ⟶ T} {s : divFamZar C π n T}
    {W : T'.left.affineOpens} {v v' : DivFamZar C Γ(T'.left, W.1) π n}
    (hv : IsPullbackValue C π n f s W v) (hv' : IsPullbackValue C π n f s W v') :
    v = v' := by
  classical
  obtain ⟨sub, hspan, hsub⟩ := Scheme.exists_basic_subcover W.2
    (fun U₀ => ∃ V : T.left.affineOpens, U₀ = f.left ⁻¹ᵁ V.1)
    (fun w _ => by
      obtain ⟨V, hVaff, hfwV, -⟩ := Opens.isBasis_iff_nbhd.mp
        T.left.isBasis_affineOpens (show f.left.base w ∈ (⊤ : T.left.Opens) from trivial)
      exact ⟨f.left ⁻¹ᵁ V, hfwV, ⟨⟨V, hVaff⟩, rfl⟩⟩)
  refine eq_of_basic_eq W sub hspan (fun r hr => ?_)
  obtain ⟨U₀, ⟨V, rfl⟩, hle⟩ := hsub r hr
  rw [hv ⟨_, W.2.basicOpen r⟩ (T'.left.basicOpen_le r) V hle,
    hv' ⟨_, W.2.basicOpen r⟩ (T'.left.basicOpen_le r) V hle]

set_option maxHeartbeats 1600000 in
-- The instance towers over the section rings of the basic refinement exceed the
-- default elaboration budget (as in `PicEtMap.exists_isPullbackValue`).
/-- **Existence of the glued value**: the restriction of a compatible family along an
arbitrary morphism of test objects has a value at every affine open of the source,
glued over a finite basic-open refinement subordinate to the preimages of affine
opens — the S5b gluing keystone through `divFamZar.exists_glue_of_basic_compat`. -/
theorem exists_isPullbackValue (f : T' ⟶ T) (s : divFamZar C π n T)
    (W : T'.left.affineOpens) : ∃ v, IsPullbackValue C π n f s W v := by
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
  -- glue the local pullbacks over the basic refinement
  obtain ⟨z, hz⟩ := exists_glue_of_basic_compat W sub hspan
    (fun r : ↥sub => DivFamZar.mapAlgHom
      (Over.appLEAlgHom f (Vc r.1 r.2).1 (T'.left.basicOpen r.1) (hVc r.1 r.2))
      (s.1 (Vc r.1 r.2)))
    hbmul hbmul'
    (fun r r' => by
      -- the overlap compatibility, from choice independence
      rw [← DivFamZar.mapAlgHom_comp, ← DivFamZar.mapAlgHom_comp,
        Over.resAlgHom_comp_appLEAlgHom, Over.resAlgHom_comp_appLEAlgHom]
      exact mapAlgHom_appLE_eq C π n f s (W₀ := ⟨_, W.2.basicOpen (r.1 * r'.1)⟩) _ _)
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
  refine eq_of_basic_eq W₀ sub₀ hspan₀ (fun q hq => ?_)
  obtain ⟨U₀, ⟨r, hr, rfl⟩, hqle⟩ := hsub₀ q hq
  -- the left side restricts through the glued datum
  have hzr : DivFamZar.mapAlgHom
        (Over.resAlgHom T' (T'.left.basicOpen_le r)) z
      = DivFamZar.mapAlgHom
          (Over.appLEAlgHom f (Vc r hr).1 (T'.left.basicOpen r) (hVc r hr))
          (s.1 (Vc r hr)) := hz ⟨r, hr⟩
  have hL : DivFamZar.mapAlgHom (Over.resAlgHom T' (T'.left.basicOpen_le q))
      (DivFamZar.mapAlgHom (Over.resAlgHom T' hW₀) z)
      = DivFamZar.mapAlgHom (Over.appLEAlgHom f (Vc r hr).1 (T'.left.basicOpen q)
          (hqle.trans (hVc r hr))) (s.1 (Vc r hr)) := by
    rw [← DivFamZar.mapAlgHom_comp, Over.resAlgHom_comp,
      show ((T'.left.basicOpen_le q).trans hW₀ :
          T'.left.basicOpen q ≤ W.1)
        = (hqle.trans (T'.left.basicOpen_le r)) from rfl,
      ← Over.resAlgHom_comp T' hqle (T'.left.basicOpen_le r),
      DivFamZar.mapAlgHom_comp, hzr, ← DivFamZar.mapAlgHom_comp,
      Over.resAlgHom_comp_appLEAlgHom]
  -- the right side restricts directly
  rw [hL, ← DivFamZar.mapAlgHom_comp, Over.resAlgHom_comp_appLEAlgHom]
  exact mapAlgHom_appLE_eq C π n f s (W₀ := ⟨_, W₀.2.basicOpen q⟩) _ _

/-- Existence and uniqueness of the glued value. -/
theorem existsUnique_isPullbackValue (f : T' ⟶ T) (s : divFamZar C π n T)
    (W : T'.left.affineOpens) : ∃! v, IsPullbackValue C π n f s W v := by
  obtain ⟨v, hv⟩ := exists_isPullbackValue f s W
  exact ⟨v, hv, fun v' hv' => pullbackValue_unique hv' hv⟩

/-! ## The functoriality -/

variable (C π n)

/-- The value of the restricted family at an affine open of the source. -/
noncomputable def mapVal (f : T' ⟶ T) (s : divFamZar C π n T)
    (W : T'.left.affineOpens) : DivFamZar C Γ(T'.left, W.1) π n :=
  (existsUnique_isPullbackValue f s W).choose

lemma mapVal_spec (f : T' ⟶ T) (s : divFamZar C π n T) (W : T'.left.affineOpens) :
    IsPullbackValue C π n f s W (mapVal C π n f s W) :=
  (existsUnique_isPullbackValue f s W).choose_spec.1

lemma mapVal_eq_of (f : T' ⟶ T) (s : divFamZar C π n T) {W : T'.left.affineOpens}
    {v : DivFamZar C Γ(T'.left, W.1) π n} (hv : IsPullbackValue C π n f s W v) :
    mapVal C π n f s W = v :=
  pullbackValue_unique (mapVal_spec C π n f s W) hv

/-- The value of the restricted family on an affine open lying in the preimage of an
affine open is the plain pullback — no gluing. -/
lemma mapVal_eq_mapAlgHom (f : T' ⟶ T) (s : divFamZar C π n T)
    {W : T'.left.affineOpens} {V : T.left.affineOpens} (hV : W.1 ≤ f.left ⁻¹ᵁ V.1) :
    mapVal C π n f s W
      = DivFamZar.mapAlgHom (Over.appLEAlgHom f V.1 W.1 hV) (s.1 V) := by
  have h := mapVal_spec C π n f s W W le_rfl V hV
  rwa [Over.resAlgHom_rfl, DivFamZar.mapAlgHom_id] at h

/-- **Restriction of the locally certified vehicle along an arbitrary morphism of test
objects** (`informal/spec-dd-2.md` §6 on the Addendum-2 carrier; the `picEtMap`
pattern): the value at each affine open of the source is the glued pullback value. -/
noncomputable def map (f : T' ⟶ T) : divFamZar C π n T → divFamZar C π n T' :=
  fun s =>
    ⟨fun W => mapVal C π n f s W, by
      intro U V h
      beta_reduce
      refine (mapVal_eq_of C π n f s (W := U) ?_).symm
      intro W₀ hW₀ V' hV'
      rw [← DivFamZar.mapAlgHom_comp, Over.resAlgHom_comp]
      exact mapVal_spec C π n f s V W₀ (hW₀.trans h) V' hV'⟩

@[simp]
lemma map_val (f : T' ⟶ T) (s : divFamZar C π n T) (W : T'.left.affineOpens) :
    (map C π n f s).1 W = mapVal C π n f s W :=
  rfl

/-- The functor law: restriction along the identity is the identity. -/
theorem map_id (s : divFamZar C π n T) : map C π n (𝟙 T) s = s := by
  refine ext fun W => ?_
  rw [map_val]
  refine mapVal_eq_of C π n (𝟙 T) s ?_
  intro W₀ hW₀ V hV
  have hV' : W₀.1 ≤ V.1 := by
    intro p hp
    have hmem := hV hp
    rw [Over.id_left] at hmem
    exact hmem
  rw [Over.appLEAlgHom_id T V.1 W₀.1 hV hV', s.compat W₀ W hW₀, s.compat W₀ V hV']

/-- The functor law: restriction along a composite is the composite of the
restrictions. -/
theorem map_comp (f : T' ⟶ T) (g : T'' ⟶ T') (s : divFamZar C π n T) :
    map C π n (g ≫ f) s = map C π n g (map C π n f s) := by
  classical
  refine ext fun W => ?_
  rw [map_val, map_val]
  refine (mapVal_eq_of C π n (g ≫ f) s ?_)
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
  refine eq_of_basic_eq W₀ sub hspan (fun q hq => ?_)
  obtain ⟨U₀, ⟨V'', hV''le, rfl⟩, hqle⟩ := hsub q hq
  -- the left side, through the two glued values
  have hL : DivFamZar.mapAlgHom (Over.resAlgHom T'' (T''.left.basicOpen_le q))
      (DivFamZar.mapAlgHom (Over.resAlgHom T'' hW₀)
        (mapVal C π n g (map C π n f s) W))
      = DivFamZar.mapAlgHom (Over.appLEAlgHom g V''.1 (T''.left.basicOpen q) hqle)
          (DivFamZar.mapAlgHom (Over.appLEAlgHom f V.1 V''.1 hV''le) (s.1 V)) := by
    rw [← DivFamZar.mapAlgHom_comp, Over.resAlgHom_comp,
      mapVal_spec C π n g (map C π n f s) W ⟨_, W₀.2.basicOpen q⟩
        ((T''.left.basicOpen_le q).trans hW₀) V'' hqle,
      map_val, mapVal_eq_mapAlgHom C π n f s hV''le]
  rw [hL, ← DivFamZar.mapAlgHom_comp, ← DivFamZar.mapAlgHom_comp,
    Over.appLEAlgHom_comp f g V.1 V''.1 (T''.left.basicOpen q) hV''le hqle
      (hqle.trans ((g.left.preimage_mono hV''le).trans
        (le_of_eq (by rw [Over.comp_left, Scheme.Hom.comp_preimage])))),
    Over.resAlgHom_comp_appLEAlgHom]

end divFamZar

/-! ## Naturality of the affine comparison -/

section AffineNaturality

variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- The affine comparison intertwines the section-ring pullback along `Spec` of an
algebra map with the algebra map itself (local copy of the `PicEtMap` helper). -/
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

/-- **Naturality of the affine comparison**: over affine tests, `divFamZar.map` along
`Spec` of an algebra map corresponds to the affine-level `DivFamZar.mapAlgHom` under
the comparison equivalences — the `picEtAffineEquiv_naturality` mirror, the agreement
of the glued general-test restriction with the S5b total base change. -/
theorem divFamZarAffineEquiv_naturality (φ : A →ₐ[k] B)
    (s : divFamZar C π n (overSpec k A)) :
    divFamZarAffineEquiv C π n B (divFamZar.map C π n (Over.overSpecMap φ) s)
      = DivFamZar.mapAlgHom φ (divFamZarAffineEquiv C π n A s) := by
  rw [divFamZarAffineEquiv_apply, divFamZarAffineEquiv_apply, divFamZar.map_val]
  have hval := divFamZar.mapVal_eq_mapAlgHom C π n (Over.overSpecMap φ) s
    (W := overSpecTopAffine B) (V := overSpecTopAffine A) le_top
  rw [hval]
  calc DivFamZar.mapAlgHom (Over.overSpecΓTopAlgEquiv k B).toAlgHom
        (DivFamZar.mapAlgHom (Over.appLEAlgHom (Over.overSpecMap φ)
          (overSpecTopAffine A).1 (overSpecTopAffine B).1 le_top)
          (s.1 (overSpecTopAffine A)))
      = DivFamZar.mapAlgHom ((Over.overSpecΓTopAlgEquiv k B).toAlgHom.comp
          (Over.appLEAlgHom (Over.overSpecMap φ)
            (overSpecTopAffine A).1 (overSpecTopAffine B).1 le_top))
          (s.1 (overSpecTopAffine A)) := (DivFamZar.mapAlgHom_comp _ _ _).symm
    _ = DivFamZar.mapAlgHom (φ.comp (Over.overSpecΓTopAlgEquiv k A).toAlgHom)
          (s.1 (overSpecTopAffine A)) := by
        rw [overSpecΓTop_appLE_comp φ]
    _ = DivFamZar.mapAlgHom φ (DivFamZar.mapAlgHom
          (Over.overSpecΓTopAlgEquiv k A).toAlgHom (s.1 (overSpecTopAffine A))) :=
        DivFamZar.mapAlgHom_comp _ _ _

end AffineNaturality

end AlgebraicGeometry
