/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyZarVehicle
import AlgebraicJacobian.Picard.DivisorFamilyZarGlue
import AlgebraicJacobian.Picard.PicEtMapToolkit

/-!
# The basic-open toolkit for the locally certified vehicle's functoriality (DD-2 S6a)

The general-test functoriality and sheaf statements of the locally certified vehicle
`divFamZar` (`AlgebraicJacobian.Picard.DivisorFamilyZarMap` / `…ZarSheaf`) evaluate
compatible families on finite basic-open refinements of affine opens — the `picEtMap`
pattern.  This file instantiates the S5b Zariski keystones of `DivFamZar` at the
section rings of a basic cover of an affine open, translated onto the explicit
`Over.resAlgHom` face through the face-change bridge `DivFamZar.mapAlgHom_eq_mapAlg`:

* `AlgebraicGeometry.divFamZar.eq_of_basic_eq`: **separation over a basic cover** —
  two locally certified classes over `Γ(U)` agreeing on every member of a spanning
  family of basic opens agree (`DivFamZar.eq_of_away_eq` at
  `IsAffineOpen.isLocalization_basicOpen` localizations, with the landed
  `Over.isScalarTower_sections_basicOpen` towers).
* `AlgebraicGeometry.divFamZar.exists_glue_of_basic_compat`: **gluing over a basic
  cover** — classes on the members of a spanning family of basic opens compatible on
  the multiplicative overlaps glue to a class on `Γ(U)`
  (`DivFamZar.exists_glue_of_away_compat`, with the overlap carriers
  `Γ(basicOpen (r·r'))` receiving the member section rings by restriction).
* `AlgebraicGeometry.divFamZar.mapAlgHom_appLE_eq`: **choice independence** — the
  restriction of a vehicle section through two different affine opens of the target
  agree; the well-definedness of the glued functoriality
  (`picEt.mapAlg_appLE_eq`, verbatim on the `DivFamZar` values).
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

/-! ## Separation over the section rings of a basic cover -/

/-- **Separation over a basic cover**: two locally certified divisor classes over the
sections of an affine open agreeing on every member of a finite spanning family of
basic opens agree — the S5b separation keystone `DivFamZar.eq_of_away_eq` instantiated
at the basic-open section-ring localizations, read on the explicit `Over.resAlgHom`
face through the face-change bridge. -/
theorem eq_of_basic_eq {T' : Over (Spec (.of k))} (W : T'.left.affineOpens)
    (sub : Finset Γ(T'.left, W.1))
    (hs : Ideal.span (↑sub : Set Γ(T'.left, W.1)) = ⊤)
    {x y : DivFamZar C Γ(T'.left, W.1) π n}
    (h : ∀ r ∈ sub,
      DivFamZar.mapAlgHom (Over.resAlgHom T' (T'.left.basicOpen_le r)) x
        = DivFamZar.mapAlgHom (Over.resAlgHom T' (T'.left.basicOpen_le r)) y) :
    x = y := by
  classical
  haveI hAway : ∀ r : ↥sub, IsLocalization.Away (r : Γ(T'.left, W.1))
      Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))) := fun r =>
    W.2.isLocalization_basicOpen (r : Γ(T'.left, W.1))
  haveI htow : ∀ r : ↥sub, IsScalarTower k Γ(T'.left, W.1)
      Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))) := fun r =>
    Over.isScalarTower_sections_basicOpen T' W.1 (r : Γ(T'.left, W.1))
  refine DivFamZar.eq_of_away_eq (fun r : ↥sub => (r : Γ(T'.left, W.1)))
    (fun r : ↥sub => Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1)))) ?_
    (fun r => ?_)
  · rw [show (Set.range fun r : ↥sub => (r : Γ(T'.left, W.1))) = (↑sub : Set _) from
      Subtype.range_coe]
    exact hs
  · rw [← DivFamZar.mapAlgHom_eq_mapAlg
        (Over.resAlgHom T' (T'.left.basicOpen_le (r : Γ(T'.left, W.1))))
        (fun _ => rfl) x,
      ← DivFamZar.mapAlgHom_eq_mapAlg
        (Over.resAlgHom T' (T'.left.basicOpen_le (r : Γ(T'.left, W.1))))
        (fun _ => rfl) y]
    exact h r r.2

/-! ## Gluing over the section rings of a basic cover -/

/-- **Gluing over a basic cover**: locally certified divisor classes on the members of
a finite spanning family of basic opens of an affine open, compatible on the
multiplicative overlaps, glue to a class over the ambient sections restricting to
each — the S5b gluing keystone `DivFamZar.exists_glue_of_away_compat` instantiated at
the basic-open section-ring localizations, with the overlap carriers
`Γ(basicOpen (r·r'))` receiving the member section rings by restriction, read on the
explicit `Over.resAlgHom` face through the face-change bridge.  (Uniqueness is
`divFamZar.eq_of_basic_eq`.) -/
theorem exists_glue_of_basic_compat {T' : Over (Spec (.of k))} (W : T'.left.affineOpens)
    (sub : Finset Γ(T'.left, W.1))
    (hspan : Ideal.span (↑sub : Set Γ(T'.left, W.1)) = ⊤)
    (v : ∀ r : ↥sub, DivFamZar C Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))) π n)
    (hmul : ∀ r r' : ↥sub,
      T'.left.basicOpen ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))
        ≤ T'.left.basicOpen (r : Γ(T'.left, W.1)))
    (hmul' : ∀ r r' : ↥sub,
      T'.left.basicOpen ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))
        ≤ T'.left.basicOpen (r' : Γ(T'.left, W.1)))
    (hcompat : ∀ r r' : ↥sub,
      DivFamZar.mapAlgHom (Over.resAlgHom T' (hmul r r')) (v r)
        = DivFamZar.mapAlgHom (Over.resAlgHom T' (hmul' r r')) (v r')) :
    ∃ z : DivFamZar C Γ(T'.left, W.1) π n, ∀ r : ↥sub,
      DivFamZar.mapAlgHom
          (Over.resAlgHom T' (T'.left.basicOpen_le (r : Γ(T'.left, W.1)))) z
        = v r := by
  classical
  -- the member localizations and their towers
  haveI hAway : ∀ r : ↥sub, IsLocalization.Away (r : Γ(T'.left, W.1))
      Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))) := fun r =>
    W.2.isLocalization_basicOpen (r : Γ(T'.left, W.1))
  haveI htow : ∀ r : ↥sub, IsScalarTower k Γ(T'.left, W.1)
      Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))) := fun r =>
    Over.isScalarTower_sections_basicOpen T' W.1 (r : Γ(T'.left, W.1))
  -- the overlap localizations and their towers
  haveI hAwayT : ∀ r r' : ↥sub,
      IsLocalization.Away ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))
        Γ(T'.left, T'.left.basicOpen
          ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))) := fun r r' =>
    W.2.isLocalization_basicOpen _
  haveI htowT : ∀ r r' : ↥sub, IsScalarTower k Γ(T'.left, W.1)
      Γ(T'.left, T'.left.basicOpen
        ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))) := fun r r' =>
    Over.isScalarTower_sections_basicOpen T' W.1 _
  -- the overlap carriers receive the member section rings by restriction
  letI algS : ∀ r r' : ↥sub,
      Algebra Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1)))
        Γ(T'.left, T'.left.basicOpen
          ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))) := fun r r' =>
    (Over.resAlgHom T' (hmul r r')).toRingHom.toAlgebra
  letI algS' : ∀ r r' : ↥sub,
      Algebra Γ(T'.left, T'.left.basicOpen (r' : Γ(T'.left, W.1)))
        Γ(T'.left, T'.left.basicOpen
          ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))) := fun r r' =>
    (Over.resAlgHom T' (hmul' r r')).toRingHom.toAlgebra
  haveI towkS : ∀ r r' : ↥sub,
      IsScalarTower k Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1)))
        Γ(T'.left, T'.left.basicOpen
          ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))) := fun r r' =>
    IsScalarTower.of_algebraMap_eq fun a =>
      ((Over.resAlgHom T' (hmul r r')).commutes a).symm
  haveI towkS' : ∀ r r' : ↥sub,
      IsScalarTower k Γ(T'.left, T'.left.basicOpen (r' : Γ(T'.left, W.1)))
        Γ(T'.left, T'.left.basicOpen
          ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))) := fun r r' =>
    IsScalarTower.of_algebraMap_eq fun a =>
      ((Over.resAlgHom T' (hmul' r r')).commutes a).symm
  haveI towRS : ∀ r r' : ↥sub,
      IsScalarTower Γ(T'.left, W.1)
        Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1)))
        Γ(T'.left, T'.left.basicOpen
          ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))) := fun r r' =>
    IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom
      (Over.resAlgHom_comp T' (hmul r r')
        (T'.left.basicOpen_le (r : Γ(T'.left, W.1)))).symm)
  haveI towRS' : ∀ r r' : ↥sub,
      IsScalarTower Γ(T'.left, W.1)
        Γ(T'.left, T'.left.basicOpen (r' : Γ(T'.left, W.1)))
        Γ(T'.left, T'.left.basicOpen
          ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))) := fun r r' =>
    IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom
      (Over.resAlgHom_comp T' (hmul' r r')
        (T'.left.basicOpen_le (r' : Γ(T'.left, W.1)))).symm)
  -- the S5b gluing keystone at the basic localizations
  obtain ⟨z, hz⟩ := DivFamZar.exists_glue_of_away_compat
    (fun r : ↥sub => (r : Γ(T'.left, W.1)))
    (fun r : ↥sub => Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))))
    (fun r r' : ↥sub => Γ(T'.left, T'.left.basicOpen
      ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))))
    (by
      rw [show (Set.range fun r : ↥sub => (r : Γ(T'.left, W.1))) = (↑sub : Set _) from
        Subtype.range_coe]
      exact hspan)
    v
    (fun r r' => by
      rw [← DivFamZar.mapAlgHom_eq_mapAlg (Over.resAlgHom T' (hmul r r'))
          (fun _ => rfl) (v r),
        ← DivFamZar.mapAlgHom_eq_mapAlg (Over.resAlgHom T' (hmul' r r'))
          (fun _ => rfl) (v r')]
      exact hcompat r r')
  refine ⟨z, fun r => ?_⟩
  rw [DivFamZar.mapAlgHom_eq_mapAlg
    (Over.resAlgHom T' (T'.left.basicOpen_le (r : Γ(T'.left, W.1)))) (fun _ => rfl) z]
  exact hz r

/-! ## Choice independence of the glued evaluation -/

variable (C π n) in
/-- **Choice independence**: restricting a vehicle section through two different affine
opens of the target gives the same locally certified class on any affine open of the
source contained in both preimages — the well-definedness of the glued functoriality
(`picEt.mapAlg_appLE_eq`, verbatim on the `DivFamZar` values). -/
theorem mapAlgHom_appLE_eq {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (s : divFamZar C π n T) {W₀ : T'.left.affineOpens}
    {V V' : T.left.affineOpens} (hV : W₀.1 ≤ f.left ⁻¹ᵁ V.1)
    (hV' : W₀.1 ≤ f.left ⁻¹ᵁ V'.1) :
    DivFamZar.mapAlgHom (Over.appLEAlgHom f V.1 W₀.1 hV) (s.1 V)
      = DivFamZar.mapAlgHom (Over.appLEAlgHom f V'.1 W₀.1 hV') (s.1 V') := by
  classical
  -- refine by basic opens whose image lies in an affine open inside `V ⊓ V'`
  obtain ⟨sub, hspan, hsub⟩ := Scheme.exists_basic_subcover W₀.2
    (fun U₀ => ∃ V'' : T.left.affineOpens,
      V''.1 ≤ V.1 ∧ V''.1 ≤ V'.1 ∧ U₀ = f.left ⁻¹ᵁ V''.1)
    (fun w hw => by
      have hfw : f.left.base w ∈ V.1 ⊓ V'.1 := ⟨hV hw, hV' hw⟩
      obtain ⟨V'', hV''aff, hwV'', hV''le⟩ := Opens.isBasis_iff_nbhd.mp
        T.left.isBasis_affineOpens hfw
      exact ⟨f.left ⁻¹ᵁ V'', hwV'', ⟨⟨V'', hV''aff⟩,
        hV''le.trans inf_le_left, hV''le.trans inf_le_right, rfl⟩⟩)
  choose V'' hV''₁ hV''₂ hU₀ using fun (r : Γ(T'.left, W₀.1)) (hr : r ∈ sub) =>
    (hsub r hr).choose_spec.1
  have hDle : ∀ (r : Γ(T'.left, W₀.1)) (hr : r ∈ sub),
      T'.left.basicOpen r ≤ f.left ⁻¹ᵁ (V'' r hr).1 := fun r hr => by
    have h1 := (hsub r hr).choose_spec.2
    rw [hU₀ r hr] at h1
    exact h1
  refine eq_of_basic_eq W₀ sub hspan (fun r hr => ?_)
  -- both sides restrict to the value at `V'' r hr` on the basic piece
  have hcalc : ∀ (Vb : T.left.affineOpens) (hVb : W₀.1 ≤ f.left ⁻¹ᵁ Vb.1)
      (hb₁ : (V'' r hr).1 ≤ Vb.1),
      DivFamZar.mapAlgHom (Over.resAlgHom T' (T'.left.basicOpen_le r))
        (DivFamZar.mapAlgHom (Over.appLEAlgHom f Vb.1 W₀.1 hVb) (s.1 Vb))
      = DivFamZar.mapAlgHom
          (Over.appLEAlgHom f (V'' r hr).1 (T'.left.basicOpen r) (hDle r hr))
          (s.1 (V'' r hr)) := by
    intro Vb hVb hb₁
    rw [← DivFamZar.mapAlgHom_comp, Over.resAlgHom_comp_appLEAlgHom,
      ← Over.appLEAlgHom_comp_resAlgHom f (T'.left.basicOpen r) hb₁
        (hDle r hr) ((T'.left.basicOpen_le r).trans hVb),
      DivFamZar.mapAlgHom_comp, s.compat (V'' r hr) Vb hb₁]
  rw [hcalc V hV (hV''₁ r hr), hcalc V' hV' (hV''₂ r hr)]

end divFamZar

end AlgebraicGeometry
