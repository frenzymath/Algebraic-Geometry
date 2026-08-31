/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffMapKit

/-!
# Functoriality of the WIDENED vehicle along an arbitrary test morphism (R2, residue (b))

The widened vehicle `divFamZarAff` (`…AffVehicle.lean`) is functorial along an **arbitrary**
morphism `f : T' ⟶ T` of test objects: the value of the restricted family at an affine open
`W ⊆ T'.left` — whose `f`-image need not lie in any affine open of `T.left` — is *glued* over a
finite basic-open refinement of `W` subordinate to the preimages of affine opens, using the
widened S5b Zariski keystones through the basic-open toolkit (`…AffMapKit.lean`).

This is the last packaging layer of R2 residue (b): with it the widened carrier of protection
I-0492 is a functor on the whole slice over `Spec k`, which is the generality every DD-R
consumer (`DivRepGlobalData.pull_comp`) is stated at.

## Main declarations

* `AlgebraicGeometry.divFamZarAff.IsPullbackValue` — the characterizing property of the glued
  value, with `pullbackValue_unique` (Zariski separation) and `exists_isPullbackValue`
  (Zariski gluing).
* `AlgebraicGeometry.divFamZarAff.map C n f : divFamZarAff C n T → divFamZarAff C n T'`, with
  `map_id`, `map_comp`, and the no-gluing evaluation `mapVal_eq_mapAlgHom`.
* `AlgebraicGeometry.divFamZarAffAffineEquiv_naturality` — over affine tests, `map` along
  `Spec` of an algebra map is `DivFamZarAff.mapAlgHom` of that map under the widened affine
  collapse.

## What is and is not asserted

Everything here is about the Zariski topology of the **base**.  R2 widened the curve side, so
these are the chart-typed proofs of `DivisorFamilyZarMap.lean` with `DivFamZar` replaced by
`DivFamZarAff` — no new geometry, and in particular **no `|P¹(k)|` hypothesis** anywhere in the
statements or their route.  What the widened lane still owes is unchanged by this file: the
subordinate Stacks 0B8B input (residue (a), out of scope per I-0492 clause 2).
-/

set_option autoImplicit false
/- Statements mix the section rings `Γ(T.left, ·)` with the widened locally certified divisor
values over them, which are stated on the product spelling `(C ⊗ overSpec k R).left`; see
`AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom] {n : ℕ}

namespace divFamZarAff

variable {T T' T'' : Over (Spec (.of k))}

/-! ## The characterizing property of the glued value -/

variable (C n) in
/-- The characterizing property of the value at `W` of the restriction of `s` along `f`: on
every affine sub-open of `W` contained in the preimage of an affine open `V` of the target, it
restricts to the base change of the value of `s` at `V`. -/
def IsPullbackValue (f : T' ⟶ T) (s : divFamZarAff C n T) (W : T'.left.affineOpens)
    (v : DivFamZarAff C Γ(T'.left, W.1) n) : Prop :=
  ∀ (W₀ : T'.left.affineOpens) (hW₀ : W₀.1 ≤ W.1) (V : T.left.affineOpens)
    (hV : W₀.1 ≤ f.left ⁻¹ᵁ V.1),
    DivFamZarAff.mapAlgHom (Over.resAlgHom T' hW₀) v
      = DivFamZarAff.mapAlgHom (Over.appLEAlgHom f V.1 W₀.1 hV) (s.1 V)

/-- Values with the pullback property are unique — from the Zariski separation of
`DivFamZarAff` over a basic refinement subordinate to the preimages of affine opens. -/
theorem pullbackValue_unique {f : T' ⟶ T} {s : divFamZarAff C n T}
    {W : T'.left.affineOpens} {v v' : DivFamZarAff C Γ(T'.left, W.1) n}
    (hv : IsPullbackValue C n f s W v) (hv' : IsPullbackValue C n f s W v') :
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
-- The instance towers over the section rings of the basic refinement exceed the default
-- elaboration budget (as in the chart-typed `divFamZar.exists_isPullbackValue`).
/-- **Existence of the glued value**: the restriction of a compatible family of widened classes
along an arbitrary morphism of test objects has a value at every affine open of the source,
glued over a finite basic-open refinement subordinate to the preimages of affine opens — the
widened S5b gluing keystone through `divFamZarAff.exists_glue_of_basic_compat`. -/
theorem exists_isPullbackValue (f : T' ⟶ T) (s : divFamZarAff C n T)
    (W : T'.left.affineOpens) : ∃ v, IsPullbackValue C n f s W v := by
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
  -- glue the local base changes over the basic refinement
  obtain ⟨z, hz⟩ := exists_glue_of_basic_compat W sub hspan
    (fun r : ↥sub => DivFamZarAff.mapAlgHom
      (Over.appLEAlgHom f (Vc r.1 r.2).1 (T'.left.basicOpen r.1) (hVc r.1 r.2))
      (s.1 (Vc r.1 r.2)))
    hbmul hbmul'
    (fun r r' => by
      -- the overlap compatibility, from choice independence
      rw [← DivFamZarAff.mapAlgHom_comp, ← DivFamZarAff.mapAlgHom_comp,
        Over.resAlgHom_comp_appLEAlgHom, Over.resAlgHom_comp_appLEAlgHom]
      exact mapAlgHom_appLE_eq C n f s (W₀ := ⟨_, W.2.basicOpen (r.1 * r'.1)⟩) _ _)
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
  have hzr : DivFamZarAff.mapAlgHom
        (Over.resAlgHom T' (T'.left.basicOpen_le r)) z
      = DivFamZarAff.mapAlgHom
          (Over.appLEAlgHom f (Vc r hr).1 (T'.left.basicOpen r) (hVc r hr))
          (s.1 (Vc r hr)) := hz ⟨r, hr⟩
  have hL : DivFamZarAff.mapAlgHom (Over.resAlgHom T' (T'.left.basicOpen_le q))
      (DivFamZarAff.mapAlgHom (Over.resAlgHom T' hW₀) z)
      = DivFamZarAff.mapAlgHom (Over.appLEAlgHom f (Vc r hr).1 (T'.left.basicOpen q)
          (hqle.trans (hVc r hr))) (s.1 (Vc r hr)) := by
    rw [← DivFamZarAff.mapAlgHom_comp, Over.resAlgHom_comp,
      show ((T'.left.basicOpen_le q).trans hW₀ :
          T'.left.basicOpen q ≤ W.1)
        = (hqle.trans (T'.left.basicOpen_le r)) from rfl,
      ← Over.resAlgHom_comp T' hqle (T'.left.basicOpen_le r),
      DivFamZarAff.mapAlgHom_comp, hzr, ← DivFamZarAff.mapAlgHom_comp,
      Over.resAlgHom_comp_appLEAlgHom]
  -- the right side restricts directly
  rw [hL, ← DivFamZarAff.mapAlgHom_comp, Over.resAlgHom_comp_appLEAlgHom]
  exact mapAlgHom_appLE_eq C n f s (W₀ := ⟨_, W₀.2.basicOpen q⟩) _ _

/-- Existence and uniqueness of the glued value. -/
theorem existsUnique_isPullbackValue (f : T' ⟶ T) (s : divFamZarAff C n T)
    (W : T'.left.affineOpens) : ∃! v, IsPullbackValue C n f s W v := by
  obtain ⟨v, hv⟩ := exists_isPullbackValue f s W
  exact ⟨v, hv, fun v' hv' => pullbackValue_unique hv' hv⟩

/-! ## The functoriality -/

variable (C n)

/-- The value of the restricted widened family at an affine open of the source. -/
noncomputable def mapVal (f : T' ⟶ T) (s : divFamZarAff C n T)
    (W : T'.left.affineOpens) : DivFamZarAff C Γ(T'.left, W.1) n :=
  (existsUnique_isPullbackValue f s W).choose

lemma mapVal_spec (f : T' ⟶ T) (s : divFamZarAff C n T) (W : T'.left.affineOpens) :
    IsPullbackValue C n f s W (mapVal C n f s W) :=
  (existsUnique_isPullbackValue f s W).choose_spec.1

lemma mapVal_eq_of (f : T' ⟶ T) (s : divFamZarAff C n T) {W : T'.left.affineOpens}
    {v : DivFamZarAff C Γ(T'.left, W.1) n} (hv : IsPullbackValue C n f s W v) :
    mapVal C n f s W = v :=
  pullbackValue_unique (mapVal_spec C n f s W) hv

/-- The value of the restricted widened family on an affine open lying in the preimage of an
affine open is the plain base change — no gluing. -/
lemma mapVal_eq_mapAlgHom (f : T' ⟶ T) (s : divFamZarAff C n T)
    {W : T'.left.affineOpens} {V : T.left.affineOpens} (hV : W.1 ≤ f.left ⁻¹ᵁ V.1) :
    mapVal C n f s W
      = DivFamZarAff.mapAlgHom (Over.appLEAlgHom f V.1 W.1 hV) (s.1 V) := by
  have h := mapVal_spec C n f s W W le_rfl V hV
  rwa [Over.resAlgHom_rfl, DivFamZarAff.mapAlgHom_id] at h

/-- **Restriction of the widened vehicle along an arbitrary morphism of test objects** — the
last packaging layer of R2 residue (b): the value at each affine open of the source is the
glued pullback value. -/
noncomputable def map (f : T' ⟶ T) : divFamZarAff C n T → divFamZarAff C n T' :=
  fun s =>
    ⟨fun W => mapVal C n f s W, by
      intro U V h
      beta_reduce
      refine (mapVal_eq_of C n f s (W := U) ?_).symm
      intro W₀ hW₀ V' hV'
      rw [← DivFamZarAff.mapAlgHom_comp, Over.resAlgHom_comp]
      exact mapVal_spec C n f s V W₀ (hW₀.trans h) V' hV'⟩

@[simp]
lemma map_val (f : T' ⟶ T) (s : divFamZarAff C n T) (W : T'.left.affineOpens) :
    (map C n f s).1 W = mapVal C n f s W :=
  rfl

/-- The functor law: restriction along the identity is the identity. -/
theorem map_id (s : divFamZarAff C n T) : map C n (𝟙 T) s = s := by
  refine ext fun W => ?_
  rw [map_val]
  refine mapVal_eq_of C n (𝟙 T) s ?_
  intro W₀ hW₀ V hV
  have hV' : W₀.1 ≤ V.1 := by
    intro p hp
    have hmem := hV hp
    rw [Over.id_left] at hmem
    exact hmem
  rw [Over.appLEAlgHom_id T V.1 W₀.1 hV hV', s.compat W₀ W hW₀, s.compat W₀ V hV']

/-- The functor law: restriction along a composite is the composite of the restrictions. -/
theorem map_comp (f : T' ⟶ T) (g : T'' ⟶ T') (s : divFamZarAff C n T) :
    map C n (g ≫ f) s = map C n g (map C n f s) := by
  classical
  refine ext fun W => ?_
  rw [map_val, map_val]
  refine (mapVal_eq_of C n (g ≫ f) s ?_)
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
  have hL : DivFamZarAff.mapAlgHom (Over.resAlgHom T'' (T''.left.basicOpen_le q))
      (DivFamZarAff.mapAlgHom (Over.resAlgHom T'' hW₀)
        (mapVal C n g (map C n f s) W))
      = DivFamZarAff.mapAlgHom (Over.appLEAlgHom g V''.1 (T''.left.basicOpen q) hqle)
          (DivFamZarAff.mapAlgHom (Over.appLEAlgHom f V.1 V''.1 hV''le) (s.1 V)) := by
    rw [← DivFamZarAff.mapAlgHom_comp, Over.resAlgHom_comp,
      mapVal_spec C n g (map C n f s) W ⟨_, W₀.2.basicOpen q⟩
        ((T''.left.basicOpen_le q).trans hW₀) V'' hqle,
      map_val, mapVal_eq_mapAlgHom C n f s hV''le]
  rw [hL, ← DivFamZarAff.mapAlgHom_comp, ← DivFamZarAff.mapAlgHom_comp,
    Over.appLEAlgHom_comp f g V.1 V''.1 (T''.left.basicOpen q) hV''le hqle
      (hqle.trans ((g.left.preimage_mono hV''le).trans
        (le_of_eq (by rw [Over.comp_left, Scheme.Hom.comp_preimage])))),
    Over.resAlgHom_comp_appLEAlgHom]

end divFamZarAff

/-! ## The widened divisor functor -/

section Functor

/- `C` and `n` are file-level IMPLICIT variables; the `variable (C n)` that made them explicit
lived inside `namespace divFamZarAff` and ended with it.  Without re-declaring them here,
`divFunctorAff` takes them implicitly and the `simp` lemmas below — which apply it to `C` and
`n` — do not elaborate. -/
variable (C n)

/-- **The widened divisor functor**: the R2 carrier of protection I-0492 as a presheaf of types
on the slice over `Spec k`, with the glued restriction `divFamZarAff.map` along arbitrary test
morphisms.  The widened mirror of `divFunctor` (`DivisorFamilyZarFunctor.lean`), and the
generality `DivRepGlobalData.pull_comp` consumes. -/
noncomputable def divFunctorAff : (Over (Spec (.of k)))ᵒᵖ ⥤ Type u where
  obj T := divFamZarAff C n T.unop
  map g := ↾divFamZarAff.map C n g.unop
  map_id T := by
    ext s U
    exact congrArg (fun z : divFamZarAff C n T.unop => z.1 U) (divFamZarAff.map_id C n s)
  map_comp {T T' T''} g h := by
    ext s U
    exact congrArg (fun z : divFamZarAff C n T''.unop => z.1 U)
      (divFamZarAff.map_comp C n g.unop h.unop s)

@[simp]
lemma divFunctorAff_obj (T : (Over (Spec (.of k)))ᵒᵖ) :
    (divFunctorAff C n).obj T = divFamZarAff C n T.unop :=
  rfl

@[simp]
lemma divFunctorAff_map {T T' : (Over (Spec (.of k)))ᵒᵖ} (g : T ⟶ T')
    (s : divFamZarAff C n T.unop) :
    (divFunctorAff C n).map g s = divFamZarAff.map C n g.unop s :=
  rfl

end Functor

/-! ## Naturality of the widened affine comparison -/

section AffineNaturality

variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- The widened affine comparison intertwines the section-ring pullback along `Spec` of an
algebra map with the algebra map itself (local copy of the `PicEtMap` helper). -/
private lemma overSpecΓTop_appLE_comp_aff (φ : A →ₐ[k] B) :
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

/-- **Naturality of the widened affine comparison**: over affine tests, `divFamZarAff.map` along
`Spec` of an algebra map corresponds to `DivFamZarAff.mapAlgHom` of that map under the widened
collapse `divFamZarAffAffineEquiv`.

This is the coherence that carries the widened certificate lane's endpoint (which lands at an
affine test) into the functor: the glued general-test restriction agrees with the widened total
base change wherever both are defined. -/
theorem divFamZarAffAffineEquiv_naturality (φ : A →ₐ[k] B)
    (s : divFamZarAff C n (overSpec k A)) :
    divFamZarAffAffineEquiv C n B (divFamZarAff.map C n (Over.overSpecMap φ) s)
      = DivFamZarAff.mapAlgHom φ (divFamZarAffAffineEquiv C n A s) := by
  rw [divFamZarAffAffineEquiv_apply, divFamZarAffAffineEquiv_apply, divFamZarAff.map_val]
  have hval := divFamZarAff.mapVal_eq_mapAlgHom C n (Over.overSpecMap φ) s
    (W := overSpecTopAffine B) (V := overSpecTopAffine A) le_top
  rw [hval]
  calc DivFamZarAff.mapAlgHom (Over.overSpecΓTopAlgEquiv k B).toAlgHom
        (DivFamZarAff.mapAlgHom (Over.appLEAlgHom (Over.overSpecMap φ)
          (overSpecTopAffine A).1 (overSpecTopAffine B).1 le_top)
          (s.1 (overSpecTopAffine A)))
      = DivFamZarAff.mapAlgHom ((Over.overSpecΓTopAlgEquiv k B).toAlgHom.comp
          (Over.appLEAlgHom (Over.overSpecMap φ)
            (overSpecTopAffine A).1 (overSpecTopAffine B).1 le_top))
          (s.1 (overSpecTopAffine A)) := (DivFamZarAff.mapAlgHom_comp _ _ _).symm
    _ = DivFamZarAff.mapAlgHom (φ.comp (Over.overSpecΓTopAlgEquiv k A).toAlgHom)
          (s.1 (overSpecTopAffine A)) := by
        rw [overSpecΓTop_appLE_comp_aff φ]
    _ = DivFamZarAff.mapAlgHom φ (DivFamZarAff.mapAlgHom
          (Over.overSpecΓTopAlgEquiv k A).toAlgHom (s.1 (overSpecTopAffine A))) :=
        DivFamZarAff.mapAlgHom_comp _ _ _

end AffineNaturality

end AlgebraicGeometry
