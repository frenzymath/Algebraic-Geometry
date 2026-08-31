/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffGlueZar
import AlgebraicJacobian.Picard.DivisorFamilyAffVehicle
import AlgebraicJacobian.Picard.PicEtMapToolkit

/-!
# The basic-open toolkit for the WIDENED vehicle's functoriality (R2, residue (b))

The widened vehicle `divFamZarAff` (`…AffVehicle.lean`) collapses correctly on affine tests,
but a DD-R consumer needs its restriction along an **arbitrary** morphism of test objects —
`DivRepGlobalData.pull_comp` is stated at that generality.  The value of a restricted family
at an affine open `W ⊆ T'.left` whose `f`-image lies in no single affine open of `T.left` has
to be *glued* over a finite basic-open refinement of `W` subordinate to the preimages of
affine opens.  This file instantiates the widened S5b Zariski keystones at the section rings
of such a refinement, exactly as `DivisorFamilyZarMapKit.lean` does for the chart-typed
carrier.

## Why this is a transcription and not new mathematics

R2 (protection I-0492) widened where the certificate's cover pieces live **on the curve**.
Every statement here is about the Zariski topology of the **base** `T'.left`: a basic cover of
an affine open, the localizations at its members, and the overlaps.  The widening is invisible
to that argument, which is why the chart-typed proofs transfer clause for clause with
`DivFamZar → DivFamZarAff`.  What is *not* free is the typing: the keystones are spelled at
localization instance packs and the vehicle's compatibility at `Over.resAlgHom`, a bare
`AlgHom`, so every use goes through the face-change bridge `DivFamZarAff.mapAlgHom_eq_mapAlg`
(`…AffFace.lean`) — the layer whose absence made the widened carrier unusable for four
sessions.

## Main declarations

* `AlgebraicGeometry.divFamZarAff.eq_of_basic_eq`: **separation over a basic cover** — two
  widened classes over `Γ(W)` agreeing on every member of a spanning family of basic opens
  agree (`DivFamZarAff.eq_of_away_eq` at `IsAffineOpen.isLocalization_basicOpen`).
* `AlgebraicGeometry.divFamZarAff.exists_glue_of_basic_compat`: **gluing over a basic cover**
  (`DivFamZarAff.exists_glue_of_away_compat`, with the overlap carriers `Γ(basicOpen (r·r'))`
  receiving the member section rings by restriction).
* `AlgebraicGeometry.divFamZarAff.mapAlgHom_appLE_eq`: **choice independence** — restricting a
  widened vehicle section through two different affine opens of the target agrees.

**A TRAP CARRIED FROM `…AffMapAlg.lean`, and it is why this file exists as a separate layer:**
`DivFamZarAff.eq_of_away_eq` takes `n` as an **explicit leading argument** where the
chart-typed `DivFamZar.eq_of_away_eq` has it implicit.  A port that copies the chart-typed
call site feeds the cover family where `n` belongs and the error surfaces as an unresolvable
`l.down` on a `ULift` binder, naming neither.  A sorry census scores such a file healthy.
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

/-! ## Separation over the section rings of a basic cover -/

/-- **Separation over a basic cover**: two widened locally certified divisor classes over the
sections of an affine open agreeing on every member of a finite spanning family of basic opens
agree — the widened S5b separation keystone `DivFamZarAff.eq_of_away_eq` instantiated at the
basic-open section-ring localizations, read on the explicit `Over.resAlgHom` face through the
face-change bridge. -/
theorem eq_of_basic_eq {T' : Over (Spec (.of k))} (W : T'.left.affineOpens)
    (sub : Finset Γ(T'.left, W.1))
    (hs : Ideal.span (↑sub : Set Γ(T'.left, W.1)) = ⊤)
    {x y : DivFamZarAff C Γ(T'.left, W.1) n}
    (h : ∀ r ∈ sub,
      DivFamZarAff.mapAlgHom (Over.resAlgHom T' (T'.left.basicOpen_le r)) x
        = DivFamZarAff.mapAlgHom (Over.resAlgHom T' (T'.left.basicOpen_le r)) y) :
    x = y := by
  classical
  haveI hAway : ∀ r : ↥sub, IsLocalization.Away (r : Γ(T'.left, W.1))
      Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))) := fun r =>
    W.2.isLocalization_basicOpen (r : Γ(T'.left, W.1))
  haveI htow : ∀ r : ↥sub, IsScalarTower k Γ(T'.left, W.1)
      Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))) := fun r =>
    Over.isScalarTower_sections_basicOpen T' W.1 (r : Γ(T'.left, W.1))
  -- `n` is EXPLICIT here; the chart-typed twin has it implicit (see the header trap).
  refine DivFamZarAff.eq_of_away_eq n (fun r : ↥sub => (r : Γ(T'.left, W.1)))
    (fun r : ↥sub => Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1)))) ?_
    (fun r => ?_)
  · rw [show (Set.range fun r : ↥sub => (r : Γ(T'.left, W.1))) = (↑sub : Set _) from
      Subtype.range_coe]
    exact hs
  · rw [← DivFamZarAff.mapAlgHom_eq_mapAlg
        (Over.resAlgHom T' (T'.left.basicOpen_le (r : Γ(T'.left, W.1))))
        (fun _ => rfl) x,
      ← DivFamZarAff.mapAlgHom_eq_mapAlg
        (Over.resAlgHom T' (T'.left.basicOpen_le (r : Γ(T'.left, W.1))))
        (fun _ => rfl) y]
    exact h r r.2

/-! ## Gluing over the section rings of a basic cover -/

/-- **Gluing over a basic cover**: widened locally certified divisor classes on the members of a
finite spanning family of basic opens of an affine open, compatible on the multiplicative
overlaps, glue to a class over the ambient sections restricting to each — the widened S5b gluing
keystone `DivFamZarAff.exists_glue_of_away_compat` instantiated at the basic-open section-ring
localizations, with the overlap carriers `Γ(basicOpen (r·r'))` receiving the member section rings
by restriction, read on the explicit `Over.resAlgHom` face.  (Uniqueness is
`divFamZarAff.eq_of_basic_eq`.) -/
theorem exists_glue_of_basic_compat {T' : Over (Spec (.of k))} (W : T'.left.affineOpens)
    (sub : Finset Γ(T'.left, W.1))
    (hspan : Ideal.span (↑sub : Set Γ(T'.left, W.1)) = ⊤)
    (v : ∀ r : ↥sub, DivFamZarAff C Γ(T'.left, T'.left.basicOpen (r : Γ(T'.left, W.1))) n)
    (hmul : ∀ r r' : ↥sub,
      T'.left.basicOpen ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))
        ≤ T'.left.basicOpen (r : Γ(T'.left, W.1)))
    (hmul' : ∀ r r' : ↥sub,
      T'.left.basicOpen ((r : Γ(T'.left, W.1)) * (r' : Γ(T'.left, W.1)))
        ≤ T'.left.basicOpen (r' : Γ(T'.left, W.1)))
    (hcompat : ∀ r r' : ↥sub,
      DivFamZarAff.mapAlgHom (Over.resAlgHom T' (hmul r r')) (v r)
        = DivFamZarAff.mapAlgHom (Over.resAlgHom T' (hmul' r r')) (v r')) :
    ∃ z : DivFamZarAff C Γ(T'.left, W.1) n, ∀ r : ↥sub,
      DivFamZarAff.mapAlgHom
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
  -- the widened S5b gluing keystone at the basic localizations
  obtain ⟨z, hz⟩ := DivFamZarAff.exists_glue_of_away_compat
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
      rw [← DivFamZarAff.mapAlgHom_eq_mapAlg (Over.resAlgHom T' (hmul r r'))
          (fun _ => rfl) (v r),
        ← DivFamZarAff.mapAlgHom_eq_mapAlg (Over.resAlgHom T' (hmul' r r'))
          (fun _ => rfl) (v r')]
      exact hcompat r r')
  refine ⟨z, fun r => ?_⟩
  rw [DivFamZarAff.mapAlgHom_eq_mapAlg
    (Over.resAlgHom T' (T'.left.basicOpen_le (r : Γ(T'.left, W.1)))) (fun _ => rfl) z]
  exact hz r

/-! ## Choice independence of the glued evaluation -/

variable (C n) in
/-- **Choice independence**: restricting a widened vehicle section through two different affine
opens of the target gives the same widened locally certified class on any affine open of the
source contained in both preimages — the well-definedness of the glued functoriality
(`divFamZar.mapAlgHom_appLE_eq`, verbatim on the `DivFamZarAff` values). -/
theorem mapAlgHom_appLE_eq {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (s : divFamZarAff C n T) {W₀ : T'.left.affineOpens}
    {V V' : T.left.affineOpens} (hV : W₀.1 ≤ f.left ⁻¹ᵁ V.1)
    (hV' : W₀.1 ≤ f.left ⁻¹ᵁ V'.1) :
    DivFamZarAff.mapAlgHom (Over.appLEAlgHom f V.1 W₀.1 hV) (s.1 V)
      = DivFamZarAff.mapAlgHom (Over.appLEAlgHom f V'.1 W₀.1 hV') (s.1 V') := by
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
      DivFamZarAff.mapAlgHom (Over.resAlgHom T' (T'.left.basicOpen_le r))
        (DivFamZarAff.mapAlgHom (Over.appLEAlgHom f Vb.1 W₀.1 hVb) (s.1 Vb))
      = DivFamZarAff.mapAlgHom
          (Over.appLEAlgHom f (V'' r hr).1 (T'.left.basicOpen r) (hDle r hr))
          (s.1 (V'' r hr)) := by
    intro Vb hVb hb₁
    rw [← DivFamZarAff.mapAlgHom_comp, Over.resAlgHom_comp_appLEAlgHom,
      ← Over.appLEAlgHom_comp_resAlgHom f (T'.left.basicOpen r) hb₁
        (hDle r hr) ((T'.left.basicOpen_le r).trans hVb),
      DivFamZarAff.mapAlgHom_comp, s.compat (V'' r hr) Vb hb₁]
  rw [hcalc V hV (hV''₁ r hr), hcalc V' hV' (hV''₂ r hr)]

end divFamZarAff

end AlgebraicGeometry
