/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GaloisDescent.InvariantQuotientOpen
import AlgebraicJacobian.Picard.GaloisDescent.GaloisQuotientUniqueness
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Restricting finite Galois quotients to stable opens

The universal property of a finite Galois quotient is local on the quotient
target.  This file proves the precise restriction theorem needed to glue the
invariant-ring quotients of stable affine charts.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicJacobian.GaloisDescent

universe u

set_option autoImplicit false

/-- The base-change map `Spec L ⟶ Spec K`. -/
noncomputable abbrev fieldBaseMap
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

namespace SemilinearGalAction

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
variable (ρ : SemilinearGalAction K L X f)

/-- The universal `T`-points property of a Galois quotient restricts to an open
whose inverse image is a stable open of the source. -/
theorem universalRestrict
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of K))
    {U V : X.Opens} (hU : ρ.IsStableOpen U) (hV : ρ.IsStableOpen V)
    (hVU : V ≤ U)
    (eU : pullback g (fieldBaseMap K L) ≅ U.toScheme)
    (hunivU : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K))
      (h : pullback t (fieldBaseMap K L) ⟶ U.toScheme),
      h ≫ (U.ι ≫ f) = pullback.snd t (fieldBaseMap K L) →
      (pullbackSemilinearGalAction K L t).IsEquivariant (ρ.restrict hU) h →
      ∃! u : {u : T ⟶ Y // u ≫ g = t},
        pullbackBaseChange K L g t u.1 u.2 ≫ eU.hom = h)
    (q : U.toScheme ⟶ Y)
    (hproj : eU.inv ≫ pullback.fst g (fieldBaseMap K L) = q)
    (W : Y.Opens)
    (hpre : q ⁻¹ᵁ W = U.ι ⁻¹ᵁ V)
    (eV : pullback (W.ι ≫ g) (fieldBaseMap K L) ≅ V.toScheme)
    (hcompare : eV.hom ≫ X.homOfLE hVU =
      pullbackBaseChange K L g (W.ι ≫ g) W.ι rfl ≫ eU.hom) :
    ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K))
      (h : pullback t (fieldBaseMap K L) ⟶ V.toScheme),
      h ≫ (V.ι ≫ f) = pullback.snd t (fieldBaseMap K L) →
      (pullbackSemilinearGalAction K L t).IsEquivariant (ρ.restrict hV) h →
      ∃! u : {u : T ⟶ W.toScheme // u ≫ (W.ι ≫ g) = t},
        pullbackBaseChange K L (W.ι ≫ g) t u.1 u.2 ≫ eV.hom = h := by
  intro T t h hover hequiv
  let j : V.toScheme ⟶ U.toScheme := X.homOfLE hVU
  have hj : j ≫ U.ι = V.ι := Scheme.homOfLE_ι X hVU
  have hjEquiv : (ρ.restrict hV).IsEquivariant (ρ.restrict hU) j := by
    intro γ
    rw [← cancel_mono U.ι]
    simp [j]
  have hover' : (h ≫ j) ≫ (U.ι ≫ f) =
      pullback.snd t (fieldBaseMap K L) := by
    calc
      (h ≫ j) ≫ (U.ι ≫ f) = h ≫ (V.ι ≫ f) := by
        simp only [Category.assoc]
        exact congrArg (fun z => h ≫ z ≫ f) hj
      _ = pullback.snd t (fieldBaseMap K L) := hover
  have hequiv' :
      (pullbackSemilinearGalAction K L t).IsEquivariant
        (ρ.restrict hU) (h ≫ j) := by
    intro γ
    calc
      ((pullbackSemilinearGalAction K L t).act γ).hom ≫ (h ≫ j) =
          (((pullbackSemilinearGalAction K L t).act γ).hom ≫ h) ≫ j :=
        (Category.assoc _ _ _).symm
      _ = (h ≫ ((ρ.restrict hV).act γ).hom) ≫ j :=
        congrArg (fun z => z ≫ j) (hequiv γ)
      _ = h ≫ (((ρ.restrict hV).act γ).hom ≫ j) := Category.assoc _ _ _
      _ = h ≫ (j ≫ ((ρ.restrict hU).act γ).hom) :=
        congrArg (fun z => h ≫ z) (hjEquiv γ)
      _ = (h ≫ j) ≫ ((ρ.restrict hU).act γ).hom :=
        (Category.assoc _ _ _).symm
  obtain ⟨u, hu, huniq⟩ := hunivU T t (h ≫ j) hover' hequiv'
  have hcomp : eU.hom ≫ q = pullback.fst g (fieldBaseMap K L) := by
    calc
      eU.hom ≫ q =
          eU.hom ≫ (eU.inv ≫ pullback.fst g (fieldBaseMap K L)) :=
        congrArg (fun z => eU.hom ≫ z) hproj.symm
      _ = pullback.fst g (fieldBaseMap K L) := by simp
  have hmap : pullback.fst t (fieldBaseMap K L) ≫ u.1 = h ≫ j ≫ q := by
    have hp := congrArg (fun z => z ≫ q) hu
    simpa only [Category.assoc, hcomp, pullbackBaseChange_fst] using hp
  letI : Surjective (fieldBaseMap K L) :=
    ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  have hsurj : Function.Surjective (pullback.fst t (fieldBaseMap K L)) :=
    (pullback.fst t (fieldBaseMap K L)).surjective
  have huW : Set.range u.1 ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hsurj x
    have hzmem : j (h z) ∈ q ⁻¹ᵁ W := by
      rw [hpre]
      change U.ι (j (h z)) ∈ V
      rw [← Scheme.Hom.comp_apply, hj]
      exact (h z).2
    change q (j (h z)) ∈ W at hzmem
    have hp := congrArg (fun m => m z) hmap
    have hp' : u.1 ((pullback.fst t (fieldBaseMap K L)) z) =
        q (j (h z)) := by
      simpa only [Scheme.Hom.comp_apply] using hp
    have hxW : u.1 x ∈ W := by
      rw [← hz, hp']
      exact hzmem
    exact ⟨⟨u.1 x, hxW⟩, rfl⟩
  let uw : T ⟶ W.toScheme := IsOpenImmersion.lift W.ι u.1 huW
  have huw_fac : uw ≫ W.ι = u.1 := IsOpenImmersion.lift_fac _ _ _
  have huw_over : uw ≫ (W.ι ≫ g) = t := by
    rw [← Category.assoc, huw_fac, u.2]
  let uw' : {u : T ⟶ W.toScheme // u ≫ (W.ι ≫ g) = t} :=
    ⟨uw, huw_over⟩
  have huw_eq :
      pullbackBaseChange K L (W.ι ≫ g) t uw huw_over ≫ eV.hom = h := by
    rw [← cancel_mono j]
    calc
      (pullbackBaseChange K L (W.ι ≫ g) t uw huw_over ≫ eV.hom) ≫ j =
          pullbackBaseChange K L (W.ι ≫ g) t uw huw_over ≫ (eV.hom ≫ j) :=
        Category.assoc _ _ _
      _ = pullbackBaseChange K L (W.ι ≫ g) t uw huw_over ≫
          (pullbackBaseChange K L g (W.ι ≫ g) W.ι rfl ≫ eU.hom) :=
        congrArg _ hcompare
      _ = (pullbackBaseChange K L (W.ι ≫ g) t uw huw_over ≫
          pullbackBaseChange K L g (W.ι ≫ g) W.ι rfl) ≫ eU.hom :=
        (Category.assoc _ _ _).symm
      _ = pullbackBaseChange K L g t (uw ≫ W.ι)
          (by rw [huw_fac, u.2]) ≫ eU.hom := by
        rw [pullbackBaseChange_comp K L g (W.ι ≫ g) t W.ι rfl uw huw_over]
      _ = pullbackBaseChange K L g t u.1 u.2 ≫ eU.hom := by
        rw [pullbackBaseChange_congr K L g t huw_fac]
      _ = h ≫ j := hu
  refine ⟨uw', huw_eq, ?_⟩
  intro y hy
  let yQ : {u : T ⟶ Y // u ≫ g = t} :=
    ⟨y.1 ≫ W.ι, by rw [Category.assoc, y.2]⟩
  have hyQ :
      pullbackBaseChange K L g t yQ.1 yQ.2 ≫ eU.hom = h ≫ j := by
    calc
      pullbackBaseChange K L g t yQ.1 yQ.2 ≫ eU.hom =
          (pullbackBaseChange K L (W.ι ≫ g) t y.1 y.2 ≫
            pullbackBaseChange K L g (W.ι ≫ g) W.ι rfl) ≫ eU.hom := by
        rw [← pullbackBaseChange_comp K L g (W.ι ≫ g) t W.ι rfl y.1 y.2]
      _ = pullbackBaseChange K L (W.ι ≫ g) t y.1 y.2 ≫
          (pullbackBaseChange K L g (W.ι ≫ g) W.ι rfl ≫ eU.hom) :=
        Category.assoc _ _ _
      _ = pullbackBaseChange K L (W.ι ≫ g) t y.1 y.2 ≫
          (eV.hom ≫ j) :=
        congrArg _ hcompare.symm
      _ = (pullbackBaseChange K L (W.ι ≫ g) t y.1 y.2 ≫ eV.hom) ≫ j :=
        (Category.assoc _ _ _).symm
      _ = h ≫ j := congrArg (fun z => z ≫ j) hy
  have hyu : yQ = u := huniq yQ hyQ
  apply Subtype.ext
  rw [← cancel_mono W.ι]
  calc
    y.1 ≫ W.ι = yQ.1 := rfl
    _ = u.1 := congrArg Subtype.val hyu
    _ = uw ≫ W.ι := huw_fac.symm

variable {U : X.Opens} (hU : ρ.IsStableOpen U)

/-- The quotient projection on a stable subopen, obtained by lifting the ambient
affine quotient map through the corresponding quotient-side open. -/
noncomputable def stableAffineQuotientMapRestrict [FiniteDimensional K L]
    (hUa : IsAffineOpen U) {V : X.Opens} (hVU : V ≤ U)
    (hV : ρ.IsStableOpen V) :
    letI := ρ.sectionsMulSemiringAction hU
    letI := sectionsAlgebra f U
    letI := sectionsAlgebraK (K := K) f U
    letI := sections_isScalarTower (K := K) f U
    letI := ρ.isSemilinear_sections hU
    let W := quotientOpenOfStableSubopen ρ hU V
    V.toScheme ⟶ W.toScheme := by
  letI := ρ.sectionsMulSemiringAction hU
  letI := sectionsAlgebra f U
  letI := sectionsAlgebraK (K := K) f U
  letI := sections_isScalarTower (K := K) f U
  letI := ρ.isSemilinear_sections hU
  let q := stableAffineQuotientMap ρ hU hUa
  let W := quotientOpenOfStableSubopen ρ hU V
  let j := X.homOfLE hVU
  have hpre : q ⁻¹ᵁ W = U.ι ⁻¹ᵁ V :=
    stableAffineQuotientMap_preimage_quotientOpen ρ hU hUa hVU hV
  have hland : Set.range (j ≫ q) ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    have hx : j x ∈ q ⁻¹ᵁ W := by
      rw [hpre]
      change U.ι (j x) ∈ V
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      exact x.2
    change q (j x) ∈ W at hx
    exact ⟨⟨q (j x), hx⟩, rfl⟩
  exact IsOpenImmersion.lift W.ι (j ≫ q) hland

@[reassoc]
theorem stableAffineQuotientMapRestrict_fac [FiniteDimensional K L]
    (hUa : IsAffineOpen U) {V : X.Opens} (hVU : V ≤ U)
    (hV : ρ.IsStableOpen V) :
    letI := ρ.sectionsMulSemiringAction hU
    letI := sectionsAlgebra f U
    letI := sectionsAlgebraK (K := K) f U
    letI := sections_isScalarTower (K := K) f U
    letI := ρ.isSemilinear_sections hU
    let W := quotientOpenOfStableSubopen ρ hU V
    stableAffineQuotientMapRestrict ρ hU hUa hVU hV ≫ W.ι =
      X.homOfLE hVU ≫ stableAffineQuotientMap ρ hU hUa := by
  letI := ρ.sectionsMulSemiringAction hU
  letI := sectionsAlgebra f U
  letI := sectionsAlgebraK (K := K) f U
  letI := sections_isScalarTower (K := K) f U
  letI := ρ.isSemilinear_sections hU
  exact IsOpenImmersion.lift_fac _ _ _

/-- The pinned quotient witness obtained by restricting an affine invariant-ring
quotient to a stable subopen.  Keeping this data in `Type` preserves the chosen
base-change isomorphism needed for coherent overlap gluing. -/
noncomputable def galoisQuotientWitness_quotientOpenOfStableSubopen
    [FiniteDimensional K L] [IsGalois K L]
    (hUa : IsAffineOpen U) {V : X.Opens} (hVU : V ≤ U)
    (hV : ρ.IsStableOpen V) :
    letI := ρ.sectionsMulSemiringAction hU
    letI := sectionsAlgebra f U
    letI := sectionsAlgebraK (K := K) f U
    letI := sections_isScalarTower (K := K) f U
    letI := ρ.isSemilinear_sections hU
    let W := quotientOpenOfStableSubopen ρ hU V
    GaloisQuotientWitnessWithProjection (ρ.restrict hV) W.toScheme
      (W.ι ≫ Spec.map (CommRingCat.ofHom
        (algebraMap K
          (SemilinearAction.invariantsSubalgebra K L Γ(X, U)))))
      (stableAffineQuotientMapRestrict ρ hU hUa hVU hV) := by
  letI := ρ.sectionsMulSemiringAction hU
  letI := sectionsAlgebra f U
  letI := sectionsAlgebraK (K := K) f U
  letI := sections_isScalarTower (K := K) f U
  letI := ρ.isSemilinear_sections hU
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap K (SemilinearAction.invariantsSubalgebra K L Γ(X, U))))
  let q := stableAffineQuotientMap ρ hU hUa
  let W := quotientOpenOfStableSubopen ρ hU V
  let eA := affineQuotientPullbackIso K L Γ(X, U)
  let eU := eA ≪≫ hUa.isoSpec.symm
  have hstruct : hUa.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap L Γ(X, U))) = U.ι ≫ f := by
    suffices h : hUa.isoSpec.hom ≫ Spec.map (f.appLE ⊤ U le_top)
          ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv = U.ι ≫ f by
      simpa [sectionsAlgebraMapHom, Scheme.Hom.appLE,
        RingHom.algebraMap_toAlgebra] using h
    rw [hUa.isoSpec_hom]
    have hn := Scheme.Opens.toSpecΓ_SpecMap_appLE f ⊤ U le_top
    calc
      U.toSpecΓ ≫ Spec.map (f.appLE ⊤ U le_top) ≫
            Spec.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv =
          (f.resLE ⊤ U le_top ≫ (⊤ : (Spec (CommRingCat.of L)).Opens).toSpecΓ) ≫
            Spec.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv :=
        congrArg (fun z => z ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv) hn
      _ = U.ι ≫ f := by rw [Category.assoc]; simp
  have hoverU : eU.hom ≫ (U.ι ≫ f) =
      pullback.snd g (fieldBaseMap K L) := by
    dsimp only [eU, eA, g, fieldBaseMap]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← hstruct, Iso.inv_hom_id_assoc,
      affineQuotientPullbackIso_hom_specMap]
  have hequivIso :
      (specSemilinearGalAction K L Γ(X, U)).IsEquivariant
        (ρ.restrict hU) hUa.isoSpec.inv := by
    intro γ
    rw [← cancel_mono hUa.isoSpec.hom]
    simp only [Category.assoc]
    rw [ρ.actRes_isoSpec_hom_toSpecAut hU hUa γ]
    simp
  have hequivU :
      (pullbackSemilinearGalAction K L g).IsEquivariant
        (ρ.restrict hU) eU.hom := by
    intro γ
    dsimp only [eU, eA]
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc,
      isEquivariant_affineQuotientPullbackIso_hom K L Γ(X, U) γ,
      Category.assoc]
    exact congrArg (fun z => (affineQuotientPullbackIso K L Γ(X, U)).hom ≫ z)
      (hequivIso γ)
  have hunivU : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K))
      (h : pullback t (fieldBaseMap K L) ⟶ U.toScheme),
      h ≫ (U.ι ≫ f) = pullback.snd t (fieldBaseMap K L) →
      (pullbackSemilinearGalAction K L t).IsEquivariant (ρ.restrict hU) h →
      ∃! u : {u : T ⟶ Spec (CommRingCat.of
          (SemilinearAction.invariantsSubalgebra K L Γ(X, U))) // u ≫ g = t},
        pullbackBaseChange K L g t u.1 u.2 ≫ eU.hom = h := by
    intro T t h hover hequiv
    have hoverA : (h ≫ hUa.isoSpec.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L Γ(X, U))) =
        pullback.snd t (fieldBaseMap K L) := by
      rw [Category.assoc, hstruct, hover]
    have hequivA :
        (pullbackSemilinearGalAction K L t).IsEquivariant
          (specSemilinearGalAction K L Γ(X, U))
          (h ≫ hUa.isoSpec.hom) := by
      intro γ
      calc
        ((pullbackSemilinearGalAction K L t).act γ).hom ≫
              (h ≫ hUa.isoSpec.hom) =
            (((pullbackSemilinearGalAction K L t).act γ).hom ≫ h) ≫
              hUa.isoSpec.hom := (Category.assoc _ _ _).symm
        _ = (h ≫ ((ρ.restrict hU).act γ).hom) ≫ hUa.isoSpec.hom :=
          congrArg (fun z => z ≫ hUa.isoSpec.hom) (hequiv γ)
        _ = h ≫ (((ρ.restrict hU).act γ).hom ≫ hUa.isoSpec.hom) :=
          Category.assoc _ _ _
        _ = h ≫ (hUa.isoSpec.hom ≫
              ((specSemilinearGalAction K L Γ(X, U)).act γ).hom) := by
          rw [specSemilinearGalAction_act]
          exact congrArg (fun z => h ≫ z)
            (ρ.actRes_isoSpec_hom_toSpecAut hU hUa γ)
        _ = (h ≫ hUa.isoSpec.hom) ≫
              ((specSemilinearGalAction K L Γ(X, U)).act γ).hom :=
          (Category.assoc _ _ _).symm
    obtain ⟨u, hu, huniq⟩ :=
      affineQuotient_existsUnique K L Γ(X, U) T t
        (h ≫ hUa.isoSpec.hom) hoverA hequivA
    refine ⟨u, ?_, ?_⟩
    · dsimp only [eU, eA]
      simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
      rw [hu, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · intro y hy
      apply huniq y
      have hy' := congrArg (fun z => z ≫ hUa.isoSpec.hom) hy
      dsimp only [eU, eA] at hy'
      simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id] using hy'
  have hproj : eU.inv ≫ pullback.fst g (fieldBaseMap K L) = q := by
    dsimp only [eU, eA, g, q]
    simp only [Iso.trans_inv, stableAffineQuotientMap, Category.assoc]
    rw [affineQuotientPullbackIso_inv_fst]
    rfl
  have hpre : q ⁻¹ᵁ W = U.ι ⁻¹ᵁ V := by
    dsimp only [q, W]
    exact stableAffineQuotientMap_preimage_quotientOpen ρ hU hUa hVU hV
  let bc := pullbackBaseChange K L g (W.ι ≫ g) W.ι rfl
  let s := bc ≫ eU.hom ≫ U.ι
  have hcomp : eU.hom ≫ q = pullback.fst g (fieldBaseMap K L) := by
    calc
      eU.hom ≫ q = eU.hom ≫
          (eU.inv ≫ pullback.fst g (fieldBaseMap K L)) :=
        congrArg (fun z => eU.hom ≫ z) hproj.symm
      _ = pullback.fst g (fieldBaseMap K L) := by simp
  have heq : eU.hom ⁻¹ᵁ (q ⁻¹ᵁ W) =
      pullback.fst g (fieldBaseMap K L) ⁻¹ᵁ W := by
    calc
      eU.hom ⁻¹ᵁ (q ⁻¹ᵁ W) = (eU.hom ≫ q) ⁻¹ᵁ W :=
        (Scheme.Hom.comp_preimage eU.hom q W).symm
      _ = pullback.fst g (fieldBaseMap K L) ⁻¹ᵁ W :=
        congrArg (fun z => z ⁻¹ᵁ W) hcomp
  have hbc : bc.opensRange =
      pullback.fst g (fieldBaseMap K L) ⁻¹ᵁ W := by
    apply Opens.ext
    rw [Scheme.Hom.coe_opensRange]
    change Set.range bc =
      (pullback.fst g (fieldBaseMap K L)).base ⁻¹' (W : Set _)
    dsimp only [bc, pullbackBaseChange]
    rw [Scheme.Pullback.range_map]
    rw [Scheme.Opens.range_ι]
    have hid : Function.Surjective
        (𝟙 (Spec (CommRingCat.of L)) :
          Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L)) :=
      fun x => ⟨x, rfl⟩
    rw [Set.range_eq_univ.mpr hid, Set.preimage_univ, Set.inter_univ]
  have hsopen : s.opensRange = V := by
    dsimp only [s]
    rw [Scheme.Hom.opensRange_comp]
    rw [Scheme.Hom.comp_image]
    rw [hbc]
    rw [← heq]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_of_isIso]
    rw [inf_eq_right.mpr le_top]
    rw [hpre]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVU
  have hsrange : Set.range s = Set.range V.ι := by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, hsopen,
      Scheme.Opens.opensRange_ι]
  haveI : IsOpenImmersion s := by
    dsimp only [s, bc]
    infer_instance
  let eV : pullback (W.ι ≫ g) (fieldBaseMap K L) ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq s V.ι hsrange
  have heV : eV.hom ≫ V.ι = s :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let j : V.toScheme ⟶ U.toScheme := X.homOfLE hVU
  have heVj : eV.hom ≫ j = bc ≫ eU.hom := by
    rw [← cancel_mono U.ι]
    rw [Category.assoc, Scheme.homOfLE_ι, heV]
    rfl
  have hbridge : eV.inv ≫ bc ≫ eU.hom = j := by
    calc
      eV.inv ≫ bc ≫ eU.hom = eV.inv ≫ (eV.hom ≫ j) := by rw [heVj]
      _ = j := by simp
  have hjEquiv : (ρ.restrict hV).IsEquivariant (ρ.restrict hU) j := by
    intro γ
    rw [← cancel_mono U.ι]
    simp [j]
  have hequivBC :
      (pullbackSemilinearGalAction K L (W.ι ≫ g)).IsEquivariant
        (ρ.restrict hU) (bc ≫ eU.hom) :=
    SemilinearGalAction.isEquivariant_pullbackBaseChange_comp g (W.ι ≫ g)
      (ρ.restrict hU) hequivU W.ι rfl
  refine ⟨⟨eV, ?_, ?_, ?_⟩, ?_⟩
  · calc
      eV.hom ≫ (V.ι ≫ f) = eV.hom ≫ ((j ≫ U.ι) ≫ f) :=
        congrArg (fun z => eV.hom ≫ (z ≫ f))
          (Scheme.homOfLE_ι X hVU).symm
      _ = (eV.hom ≫ j) ≫ (U.ι ≫ f) := by simp only [Category.assoc]
      _ = (bc ≫ eU.hom) ≫ (U.ι ≫ f) :=
        congrArg (fun z => z ≫ (U.ι ≫ f)) heVj
      _ = bc ≫ (eU.hom ≫ (U.ι ≫ f)) := Category.assoc _ _ _
      _ = bc ≫ pullback.snd g (fieldBaseMap K L) :=
        congrArg (fun z => bc ≫ z) hoverU
      _ = pullback.snd (W.ι ≫ g) (fieldBaseMap K L) :=
        pullbackBaseChange_snd K L g (W.ι ≫ g) W.ι rfl
  · intro γ
    rw [← cancel_mono j]
    calc
      (((pullbackSemilinearGalAction K L (W.ι ≫ g)).act γ).hom ≫ eV.hom) ≫ j =
          ((pullbackSemilinearGalAction K L (W.ι ≫ g)).act γ).hom ≫
            (bc ≫ eU.hom) := by rw [Category.assoc, heVj]
      _ = (bc ≫ eU.hom) ≫ ((ρ.restrict hU).act γ).hom := hequivBC γ
      _ = (eV.hom ≫ j) ≫ ((ρ.restrict hU).act γ).hom := by rw [heVj]
      _ = eV.hom ≫ (j ≫ ((ρ.restrict hU).act γ).hom) :=
        Category.assoc _ _ _
      _ = eV.hom ≫ (((ρ.restrict hV).act γ).hom ≫ j) :=
        congrArg (fun z => eV.hom ≫ z) (hjEquiv γ).symm
      _ = (eV.hom ≫ ((ρ.restrict hV).act γ).hom) ≫ j :=
        (Category.assoc _ _ _).symm
  · exact ρ.universalRestrict g hU hV hVU eU hunivU q hproj W hpre eV heVj
  · rw [← cancel_mono W.ι]
    calc
      (eV.inv ≫ pullback.fst (W.ι ≫ g) (fieldBaseMap K L)) ≫ W.ι =
          eV.inv ≫ (bc ≫ pullback.fst g (fieldBaseMap K L)) := by
        rw [pullbackBaseChange_fst]
        simp only [Category.assoc]
      _ = eV.inv ≫ (bc ≫ (eU.hom ≫ q)) :=
        congrArg (fun z => eV.inv ≫ (bc ≫ z)) hcomp.symm
      _ = (eV.inv ≫ bc ≫ eU.hom) ≫ q := by
        simp only [Category.assoc]
      _ = j ≫ q := congrArg (fun z => z ≫ q) hbridge
      _ = stableAffineQuotientMapRestrict ρ hU hUa hVU hV ≫ W.ι :=
        (stableAffineQuotientMapRestrict_fac ρ hU hUa hVU hV).symm

/-- **The invariant-ring quotient of a stable affine chart restricts to every
stable subopen.**  The quotient-side open is the one constructed from invariant
basic opens, and the conclusion contains the full universal `T`-points clause.
-/
theorem isGaloisQuotient_quotientOpenOfStableSubopen
    [FiniteDimensional K L] [IsGalois K L]
    (hUa : IsAffineOpen U) {V : X.Opens} (hVU : V ≤ U)
    (hV : ρ.IsStableOpen V) :
    letI := ρ.sectionsMulSemiringAction hU
    letI := sectionsAlgebra f U
    letI := sectionsAlgebraK (K := K) f U
    letI := sections_isScalarTower (K := K) f U
    letI := ρ.isSemilinear_sections hU
    let W := quotientOpenOfStableSubopen ρ hU V
    IsGaloisQuotient (ρ.restrict hV)
      (W.ι ≫ Spec.map (CommRingCat.ofHom
        (algebraMap K
          (SemilinearAction.invariantsSubalgebra K L Γ(X, U))))) := by
  letI := ρ.sectionsMulSemiringAction hU
  letI := sectionsAlgebra f U
  letI := sectionsAlgebraK (K := K) f U
  letI := sections_isScalarTower (K := K) f U
  letI := ρ.isSemilinear_sections hU
  let w := galoisQuotientWitness_quotientOpenOfStableSubopen
    ρ hU hUa hVU hV
  exact ⟨w.e, w.over, w.equivariant, w.universal⟩

end SemilinearGalAction

end AlgebraicJacobian.GaloisDescent
