/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SectionsToDivisorsClass
import AlgebraicJacobian.Picard.DivisorFamily
import AlgebraicJacobian.Picard.Pic0RankOneFibrePresentedProducerSectionDivEq

/-!
# T3 — datum-section extraction from a class-matched divisor

The converse of the DAT-A class law (`sectionLocalEquations_picClass`): a
`Scheme.LocalEquations` divisor datum `d` whose Picard class is the Čech class of a pinned
basic-open cocycle datum `D` is itself cut — up to `DivEq` — by a germ-regular global
section of `D`'s glued sheaf.

The construction is the α-corrected gluing: class equality unquotients (on a common
refinement of `d.cover` and `D`'s canonical piece cover) to a `0`-cochain of units `α`
conjugating `d`'s ratio-unit cocycle into `D`'s subordinated transition cocycle
(`OneCocycle.class_eq_iff` + `isCohomologous_iff_evInf`).  The corrected local sections
`α x · d.eqn x` then form a matching family for `D`'s transition units, i.e. a compatible
family of sections of `D`'s glued sheaf through the piece trivializations (`gluedTriv`);
the glued sheaf's own sheaf property (`gluedSheaf`, `TopCat.Sheaf.existsUnique_gluing'`)
glues them to a global section.  Its components are unit multiples of `d`'s equations near
every point, giving germ-regularity, and the divisor it cuts on any subordinated pointed
cover is `DivEq` to `d` (`sectionLocalEquations_divEq_of_same_section` transports between
covers).

No Noetherian or finiteness hypothesis beyond the datum's own appears: the statement holds
over an arbitrary test algebra `B`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

namespace BasicOpenCocycleDatum

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable (D : BasicOpenCocycleDatum C B π) (d : (relCurve C B).LocalEquations)

/-- The underlying section of a restricted unit is the restriction of its underlying
section. -/
private lemma coe_unitsRestrict {X : Scheme.{u}} {W U : X.Opens} (h : W ≤ U)
    (u : Γ(X, U)ˣ) :
    ((X.unitsRestrict h u : Γ(X, W)ˣ) : Γ(X, W)) = X.resHom h (u : Γ(X, U)) :=
  rfl

/-! ## The α-corrected local sections and their matching law -/

/-- The α-corrected local section over a member of the common refinement: the correcting
unit times the restricted equation of `d`. -/
private noncomputable def corrSection (𝒲₀ : (relCurve C B).PointedCover)
    (hWd : 𝒲₀ ≤ d.cover) (α : ∀ x : relCurve C B, Γ(relCurve C B, 𝒲₀.opens x)ˣ)
    (x : relCurve C B) : Γ(relCurve C B, 𝒲₀.opens x) :=
  (α x : Γ(relCurve C B, 𝒲₀.opens x)) * (relCurve C B).resHom (hWd x) (d.eqn x)

/-- **The matching law of the corrected sections**: on the overlap of two refinement
members, the corrected sections differ by the restricted transition unit of the datum —
the coboundary law for `α` composed with the ratio law of `d`'s equations. -/
private lemma corrSection_matching (𝒲₀ : (relCurve C B).PointedCover)
    (hWd : 𝒲₀ ≤ d.cover)
    (hσ₀ : ∀ x : relCurve C B, 𝒲₀.opens x ≤ D.pieces (D.pieceIndex x))
    (α : ∀ x : relCurve C B, Γ(relCurve C B, 𝒲₀.opens x)ˣ)
    (hα : ∀ x y : relCurve C B,
      (relCurve C B).unitsRestrict inf_le_left (α x)
          * (relCurve C B).unitsRestrict (inf_le_inf (hWd x) (hWd y)) (d.ratioUnit x y)
        = gluedSubordUnit D.unit 𝒲₀ D.pieceIndex hσ₀ x y
          * (relCurve C B).unitsRestrict inf_le_right (α y))
    (x y : relCurve C B) :
    (relCurve C B).resHom (inf_le_left : 𝒲₀.opens x ⊓ 𝒲₀.opens y ≤ 𝒲₀.opens x)
        (corrSection d 𝒲₀ hWd α x)
      = (relCurve C B).resHom
          (le_inf (inf_le_left.trans (hσ₀ x)) (inf_le_right.trans (hσ₀ y)) :
            𝒲₀.opens x ⊓ 𝒲₀.opens y
              ≤ D.pieces (D.pieceIndex x) ⊓ D.pieces (D.pieceIndex y))
          (D.unit (D.pieceIndex x) (D.pieceIndex y) :
            Γ(relCurve C B, D.pieces (D.pieceIndex x) ⊓ D.pieces (D.pieceIndex y)))
        * (relCurve C B).resHom (inf_le_right : 𝒲₀.opens x ⊓ 𝒲₀.opens y ≤ 𝒲₀.opens y)
            (corrSection d 𝒲₀ hWd α y) := by
  -- the ratio law of `d`, retyped in `resHom` form and restricted to the overlap
  have hbase : (relCurve C B).resHom
      (inf_le_left : d.cover.opens x ⊓ d.cover.opens y ≤ d.cover.opens x) (d.eqn x)
      = (d.ratioUnit x y : Γ(relCurve C B, d.cover.opens x ⊓ d.cover.opens y))
        * (relCurve C B).resHom inf_le_right (d.eqn y) := d.eqn_restrict_eq x y
  have hratio := congrArg
    ((relCurve C B).resHom (inf_le_inf (hWd x) (hWd y) :
      𝒲₀.opens x ⊓ 𝒲₀.opens y ≤ d.cover.opens x ⊓ d.cover.opens y)) hbase
  rw [map_mul] at hratio
  simp only [Scheme.resHom_resHom] at hratio
  -- the value form of the coboundary law
  have hval := congrArg Units.val (hα x y)
  rw [Units.val_mul, Units.val_mul, gluedSubordUnit] at hval
  simp only [coe_unitsRestrict] at hval
  -- assemble
  simp only [corrSection, map_mul, Scheme.resHom_resHom]
  rw [hratio, ← mul_assoc, hval, mul_assoc]

/-! ## The main extraction theorem -/

/-- **Datum-section extraction from a class-matched divisor** (T3, the heart of the
rank-one uniqueness discharge): a `LocalEquations` divisor datum whose Picard class is the
Čech class of the pinned cocycle datum is cut, up to `DivEq` on every subordinated pointed
cover, by a germ-regular global section of the datum's glued sheaf. -/
theorem exists_gluedSection_sectionLocalEquations_divEq
    (h : d.picClass = D.cechPicClass) :
    ∃ (s : ↥(gluedSubmodule B D.pieces D.unit ⊤))
      (hreg : ∀ (j : D.index) (y : relCurve C B) (hy : y ∈ D.pieces j),
        ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom (D.component s j)
          ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk y)),
      ∀ (𝒲 : (relCurve C B).PointedCover) (σ : relCurve C B → D.index)
        (hσ : ∀ x : relCurve C B, 𝒲.opens x ≤ D.pieces (σ x)),
        Scheme.LocalEquations.DivEq (D.sectionLocalEquations s 𝒲 σ hσ hreg) d := by
  classical
  -- Step 1: common refinement of the two covers computing the classes
  have h' : Scheme.CechPic.mk d.cover d.unitsCocycle.class
      = Scheme.CechPic.mk D.pointedCover
          (gluedSubordCocycle D.isGluingCocycle D.pointedCover D.pieceIndex
            fun _ => le_rfl).class := h
  obtain ⟨𝒲₀, hWd, hWD, e⟩ := Scheme.CechPic.mk_eq_mk_iff.mp h'
  have hσ₀ : ∀ x : relCurve C B, 𝒲₀.opens x ≤ D.pieces (D.pieceIndex x) :=
    fun x => hWD x
  -- Step 2: the restricted cocycles are cohomologous
  have e' : (d.unitsCocycle.res fun p => homOfLE (hWd p)).IsCohomologous
      (gluedSubordCocycle D.isGluingCocycle 𝒲₀ D.pieceIndex hσ₀) := by
    rw [← OneCocycle.class_eq_iff]
    calc (d.unitsCocycle.res fun p => homOfLE (hWd p)).class
        = Scheme.unitsRes hWd d.unitsCocycle.class := rfl
      _ = Scheme.unitsRes hWD (gluedSubordCocycle D.isGluingCocycle D.pointedCover
            D.pieceIndex fun _ => le_rfl).class := e
      _ = ((gluedSubordCocycle D.isGluingCocycle D.pointedCover D.pieceIndex
            fun _ => le_rfl).res fun p => homOfLE (hWD p)).class := rfl
      _ = (gluedSubordCocycle D.isGluingCocycle 𝒲₀ D.pieceIndex hσ₀).class := by
            rw [gluedSubordCocycle_res]
  -- Step 3: extract the correcting 0-cochain of units
  obtain ⟨α, hα₀⟩ := (OneCocycle.isCohomologous_iff_evInf _ _).mp e'
  have hα : ∀ x y : relCurve C B,
      (relCurve C B).unitsRestrict inf_le_left (α x)
          * (relCurve C B).unitsRestrict (inf_le_inf (hWd x) (hWd y)) (d.ratioUnit x y)
        = gluedSubordUnit D.unit 𝒲₀ D.pieceIndex hσ₀ x y
          * (relCurve C B).unitsRestrict inf_le_right (α y) := by
    intro x y
    have key : (relCurve C B).unitsRestrict inf_le_left (α x)
        * Scheme.unitsEvInf (d.unitsCocycle.res fun p => homOfLE (hWd p)) x y
      = Scheme.unitsEvInf
          (gluedSubordCocycle D.isGluingCocycle 𝒲₀ D.pieceIndex hσ₀) x y
        * (relCurve C B).unitsRestrict inf_le_right (α y) := hα₀ x y
    rwa [Scheme.res_unitsEvInf, d.unitsCocycle_evInf, gluedSubordCocycle_evInf] at key
  -- Step 4: the corrected sections are a compatible family of glued-sheaf sections
  set sf : ∀ x : relCurve C B, ↥(gluedSubmodule B D.pieces D.unit (𝒲₀.opens x)) :=
    fun x => (gluedTriv B D.isGluingCocycle (D.pieceIndex x) (hσ₀ x)).symm
      (corrSection d 𝒲₀ hWd α x) with hsf
  have hcompat : ∀ x y : relCurve C B,
      gluedRes B D.pieces D.unit
          (inf_le_left : 𝒲₀.opens x ⊓ 𝒲₀.opens y ≤ 𝒲₀.opens x) (sf x)
        = gluedRes B D.pieces D.unit inf_le_right (sf y) := by
    intro x y
    apply (gluedTriv B D.isGluingCocycle (D.pieceIndex x)
      (inf_le_left.trans (hσ₀ x))).injective
    rw [gluedTriv_res B D.isGluingCocycle (D.pieceIndex x) inf_le_left (hσ₀ x) (sf x),
      hsf]
    simp only [LinearEquiv.apply_symm_apply]
    rw [gluedTriv_eq_unit_mul B D.isGluingCocycle (D.pieceIndex x) (D.pieceIndex y)
        (inf_le_left.trans (hσ₀ x)) (inf_le_right.trans (hσ₀ y)),
      gluedTriv_res B D.isGluingCocycle (D.pieceIndex y) inf_le_right (hσ₀ y)]
    simp only [LinearEquiv.apply_symm_apply]
    exact D.corrSection_matching d 𝒲₀ hWd hσ₀ α hα x y
  -- Step 5: glue by the sheaf property of the glued sheaf
  have hcov : (⊤ : (relCurve C B).Opens) ≤ ⨆ x : relCurve C B, 𝒲₀.opens x :=
    fun p _ => Opens.mem_iSup.mpr ⟨p, 𝒲₀.mem_opens p⟩
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (gluedSheaf B D.pieces D.unit) (fun x => 𝒲₀.opens x) ⊤
    (fun x => homOfLE le_top) hcov sf (fun x y => hcompat x y)
  have hs' : ∀ x : relCurve C B,
      gluedRes B D.pieces D.unit (le_top : 𝒲₀.opens x ≤ ⊤) s = sf x :=
    fun x => hs x
  -- Step 6: the component over each refinement member is the corrected section
  have heqn : ∀ x : relCurve C B,
      (relCurve C B).resHom (hσ₀ x) (D.component s (D.pieceIndex x))
        = corrSection d 𝒲₀ hWd α x := by
    intro x
    have h2 := congrArg
      (gluedTriv B D.isGluingCocycle (D.pieceIndex x) (hσ₀ x)) (hs' x)
    rw [hsf] at h2
    simp only [LinearEquiv.apply_symm_apply] at h2
    calc (relCurve C B).resHom (hσ₀ x) (D.component s (D.pieceIndex x))
        = (relCurve C B).resHom (hσ₀ x)
            ((relCurve C B).resHom (le_inf le_top le_rfl)
              (s.val (D.pieceIndex x))) := rfl
      _ = gluedTriv B D.isGluingCocycle (D.pieceIndex x) (hσ₀ x)
            (gluedRes B D.pieces D.unit le_top s) := by
          rw [gluedTriv_apply, gluedRes_coe]
          simp only [Scheme.resHom_resHom]
      _ = corrSection d 𝒲₀ hWd α x := h2
  -- Step 7: germ-regularity of the glued section's components
  have hreg : ∀ (j : D.index) (y : relCurve C B) (hy : y ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom (D.component s j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk y) := by
    intro j y hy
    have hyO : y ∈ D.pieces j ⊓ 𝒲₀.opens y := ⟨hy, 𝒲₀.mem_opens y⟩
    -- the component near `y`, through the matching relation and the corrected section
    have hO : D.pieces j ⊓ 𝒲₀.opens y
        ≤ ⊤ ⊓ D.pieces j ⊓ D.pieces (D.pieceIndex y) :=
      le_inf (le_inf le_top inf_le_left) (inf_le_right.trans (hσ₀ y))
    have hmatch := congrArg ((relCurve C B).resHom hO) (s.property j (D.pieceIndex y))
    rw [map_mul] at hmatch
    simp only [Scheme.resHom_resHom] at hmatch
    have hcomp1 : D.component s j
        = (relCurve C B).resHom (le_inf le_top le_rfl) (s.val j) := rfl
    have hcomp2 : D.component s (D.pieceIndex y)
        = (relCurve C B).resHom (le_inf le_top le_rfl) (s.val (D.pieceIndex y)) := rfl
    have h2 := congrArg ((relCurve C B).resHom
      (inf_le_right : D.pieces j ⊓ 𝒲₀.opens y ≤ 𝒲₀.opens y)) (heqn y)
    rw [hcomp2] at h2
    simp only [Scheme.resHom_resHom] at h2
    have hkey : (relCurve C B).resHom
        (inf_le_left : D.pieces j ⊓ 𝒲₀.opens y ≤ D.pieces j) (D.component s j)
        = (relCurve C B).resHom (hO.trans (gluedInclCoc D.pieces ⊤ j (D.pieceIndex y)))
            (D.unit j (D.pieceIndex y) :
              Γ(relCurve C B, D.pieces j ⊓ D.pieces (D.pieceIndex y)))
          * (relCurve C B).resHom inf_le_right (corrSection d 𝒲₀ hWd α y) := by
      rw [hcomp1]
      simp only [Scheme.resHom_resHom]
      rw [← h2]
      exact hmatch
    have hgerm : ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom (D.component s j)
        = ((relCurve C B).presheaf.germ (D.pieces j ⊓ 𝒲₀.opens y) y hyO).hom
            ((relCurve C B).resHom
              (inf_le_left : D.pieces j ⊓ 𝒲₀.opens y ≤ D.pieces j)
              (D.component s j)) := by
      rw [Scheme.resHom, TopCat.Presheaf.germ_res_apply]
    rw [hgerm, hkey, map_mul]
    refine mul_mem ?_ ?_
    · exact (((relCurve C B).unitsRestrict
        (hO.trans (gluedInclCoc D.pieces ⊤ j (D.pieceIndex y)))
        (D.unit j (D.pieceIndex y))).isUnit.map
          ((relCurve C B).presheaf.germ (D.pieces j ⊓ 𝒲₀.opens y) y
            hyO).hom).mem_nonZeroDivisors
    · rw [corrSection, map_mul, map_mul]
      simp only [Scheme.resHom_resHom]
      refine mul_mem ?_ ?_
      · exact (((relCurve C B).unitsRestrict
          (inf_le_right : D.pieces j ⊓ 𝒲₀.opens y ≤ 𝒲₀.opens y) (α y)).isUnit.map
            ((relCurve C B).presheaf.germ (D.pieces j ⊓ 𝒲₀.opens y) y
              hyO).hom).mem_nonZeroDivisors
      · have hmem : ((relCurve C B).presheaf.germ (D.pieces j ⊓ 𝒲₀.opens y) y
            hyO).hom ((relCurve C B).resHom
              ((inf_le_right : D.pieces j ⊓ 𝒲₀.opens y ≤ 𝒲₀.opens y).trans (hWd y))
              (d.eqn y))
            = ((relCurve C B).presheaf.germ (d.cover.opens y) y
                ((hWd y) (𝒲₀.mem_opens y))).hom (d.eqn y) := by
          rw [Scheme.resHom, TopCat.Presheaf.germ_res_apply]
        rw [hmem]
        exact d.regular y y ((hWd y) (𝒲₀.mem_opens y))
  -- Step 8: the divisor cut on the refinement cover is `DivEq` to `d`
  have hdiv0 : Scheme.LocalEquations.DivEq
      (D.sectionLocalEquations s 𝒲₀ D.pieceIndex hσ₀ hreg) d := by
    refine ⟨𝒲₀, fun x => le_rfl, hWd, fun x => ⟨α x, ?_⟩⟩
    have hL : ((relCurve C B).presheaf.map (homOfLE
        (le_rfl : 𝒲₀.opens x ≤ 𝒲₀.opens x)).op).hom
          ((D.sectionLocalEquations s 𝒲₀ D.pieceIndex hσ₀ hreg).eqn x)
        = (relCurve C B).resHom (hσ₀ x) (D.component s (D.pieceIndex x)) := by
      rw [sectionLocalEquations_eqn]
      exact Scheme.resHom_self _ _
    exact hL.trans (heqn x)
  -- Conclusion: transport to every subordinated cover
  exact ⟨s, hreg, fun 𝒲 σ hσ =>
    (D.sectionLocalEquations_divEq_of_same_section s 𝒲 𝒲₀ σ D.pieceIndex hσ hσ₀
      hreg).trans hdiv0⟩

/-! ## Unit rescaling of the glued section -/

/-- The `j`-th component of a scalar multiple of a glued section is the scalar multiple
of the component. -/
lemma component_smul (v : B) (s : ↥(gluedSubmodule B D.pieces D.unit ⊤))
    (j : D.index) :
    D.component (v • s) j = v • D.component s j := by
  unfold BasicOpenCocycleDatum.component
  change (relCurve C B).resHom (le_inf le_top le_rfl) (v • s.val j)
    = v • (relCurve C B).resHom (le_inf le_top le_rfl) (s.val j)
  rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
  congr 1
  exact (relCurve C B).overAlgebraMap_apply_res B (homOfLE (le_inf le_top le_rfl)).op v

/-- Germ-regularity of the components transfers to unit multiples of a glued section. -/
lemma germ_component_smul_mem_nonZeroDivisors (v : Bˣ)
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤))
    (hreg : ∀ (j : D.index) (y : relCurve C B) (hy : y ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom (D.component s j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk y))
    (j : D.index) (y : relCurve C B) (hy : y ∈ D.pieces j) :
    ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom
        (D.component ((v : B) • s) j)
      ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk y) := by
  rw [D.component_smul, Scheme.overModule_smul_def, map_mul]
  exact mul_mem
    ((v.isUnit.map ((relCurve C B).overAlgebraMap B (D.pieces j))).map
      ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom).mem_nonZeroDivisors
    (hreg j y hy)

/-- **Unit rescaling of the glued section does not change the cut divisor** (up to
`DivEq`, on any subordinated pointed cover, over an arbitrary test algebra): scaling the
glued section by a global unit of `B` multiplies each local equation by the image of the
unit in the section ring — a unit rescaling of the local-equation system. -/
theorem sectionLocalEquations_smul_divEq (v : Bˣ)
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤))
    (𝒲 : (relCurve C B).PointedCover) (σ : relCurve C B → D.index)
    (hσ : ∀ x : relCurve C B, 𝒲.opens x ≤ D.pieces (σ x))
    (hreg : ∀ (j : D.index) (y : relCurve C B) (hy : y ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom (D.component s j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk y))
    (hreg' : ∀ (j : D.index) (y : relCurve C B) (hy : y ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom
          (D.component ((v : B) • s) j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk y)) :
    Scheme.LocalEquations.DivEq
      (D.sectionLocalEquations ((v : B) • s) 𝒲 σ hσ hreg')
      (D.sectionLocalEquations s 𝒲 σ hσ hreg) := by
  refine ⟨𝒲, fun x => le_rfl, fun x => le_rfl, fun x => ?_⟩
  refine ⟨Units.map ((relCurve C B).overAlgebraMap B (𝒲.opens x)).toMonoidHom v, ?_⟩
  have hL : ((relCurve C B).presheaf.map (homOfLE
      (le_rfl : 𝒲.opens x ≤ 𝒲.opens x)).op).hom
        ((D.sectionLocalEquations ((v : B) • s) 𝒲 σ hσ hreg').eqn x)
      = (relCurve C B).resHom (hσ x) (D.component ((v : B) • s) (σ x)) := by
    rw [sectionLocalEquations_eqn]
    exact Scheme.resHom_self _ _
  have hR : ((relCurve C B).presheaf.map (homOfLE
      (le_rfl : 𝒲.opens x ≤ 𝒲.opens x)).op).hom
        ((D.sectionLocalEquations s 𝒲 σ hσ hreg).eqn x)
      = (relCurve C B).resHom (hσ x) (D.component s (σ x)) := by
    rw [sectionLocalEquations_eqn]
    exact Scheme.resHom_self _ _
  have hmain : (relCurve C B).resHom (hσ x) (D.component ((v : B) • s) (σ x))
      = ((Units.map ((relCurve C B).overAlgebraMap B (𝒲.opens x)).toMonoidHom v :
            Γ(relCurve C B, 𝒲.opens x)ˣ) : Γ(relCurve C B, 𝒲.opens x))
        * (relCurve C B).resHom (hσ x) (D.component s (σ x)) := by
    rw [D.component_smul, Scheme.overModule_smul_def, map_mul]
    congr 1
    exact (relCurve C B).overAlgebraMap_apply_res B (homOfLE (hσ x)).op (v : B)
  exact hL.trans (hmain.trans (congrArg
    (((Units.map ((relCurve C B).overAlgebraMap B (𝒲.opens x)).toMonoidHom v :
        Γ(relCurve C B, 𝒲.opens x)ˣ) : Γ(relCurve C B, 𝒲.opens x)) * ·) hR.symm))

end BasicOpenCocycleDatum

end AlgebraicGeometry
