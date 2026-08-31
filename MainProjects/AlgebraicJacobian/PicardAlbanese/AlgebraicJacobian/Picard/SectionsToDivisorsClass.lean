/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SectionsToDivisors
import AlgebraicJacobian.Cohomology.GluedSheafClass

/-!
# Sections to divisors — the LocalEquations construction and the class law (DAT-A)

Worksheet §2.2 step 2, made literal (`informal/spec-dat-a.md` §3): a global section of
the DAT-1 glued sheaf **is** a matching family `(s_j)` with `s_i = g_{ij}·s_j`, so once
its components are germ-regular (DAT-A2, `AlgebraicJacobian.Picard.SectionsToDivisors`)
it is a `Scheme.LocalEquations` datum on the nose. The (1e) class law
(`Cohomology/GluedSheafClass.lean`, landed while this brick was in flight) is consumed
directly — the spec's `cocycleClassOn` seam is CLOSED, no interim class carrier exists:

* `BasicOpenCocycleDatum.sectionLocalEquations` — the LocalEquations datum of a
  germ-regular global section on **any** pointed cover subordinated to the pieces
  (the (1e) subordination interface `𝒲, σ, hσ`): equations the restricted components
  `D.component s (σ y)`, ratio witnesses the subordinated transition units
  `gluedSubordUnit`;
* `sectionLocalEquations_ratioUnit` — the ratio units are **exactly** the (restricted)
  transition units of the cocycle (`ratioUnit_unique`); on the piece cover the
  restriction is along `≤`-reflexivity, i.e. the units themselves;
* `sectionLocalEquations_unitsCocycle` — the units cocycle of the constructed datum is
  the (1e) subordinated cocycle `gluedSubordCocycle`;
* **the class law** `sectionLocalEquations_picClass`:
  `(D.sectionLocalEquations …).picClass = D.cechPicClass` — the divisor datum cut out
  by a germ-regular section presents THE class of the datum's cocycle (the Abel
  correspondence), through the landed `cechPicClass_eq_mk`. Naturality under
  refinement/subordination-choice is the landed `gluedSubordCocycle_class_eq`; unit
  rescalings and cover refinements of the constructed datum keep the class by the
  landed `LocalEquations.picClass_rescale`/`picClass_restrict`;
* `sectionLocalEquations_picClass_congr` — any two germ-regular sections on any two
  subordinated covers cut divisors of the same class;
* `sectionLocalEquationsOfFibrewiseRegular` — the A2-bundled wrapper on the canonical
  pointed cover (`D.pointedCover`): a fibrewise-regular global section yields the
  divisor datum outright, with class `D.cechPicClass` (`[IsNoetherianRing B]`).
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

namespace BasicOpenCocycleDatum

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]

/-- The value of a restricted unit section is the restriction of its value. -/
private lemma val_unitsRestrict {X : Scheme.{u}} {W U : X.Opens} (h : W ≤ U)
    (u : Γ(X, U)ˣ) :
    ((X.unitsRestrict h u : Γ(X, W)ˣ) : Γ(X, W)) = X.resHom h (u : Γ(X, U)) :=
  rfl

section AffineHom

variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable (D : BasicOpenCocycleDatum C B π)
variable (s : ↥(gluedSubmodule B D.pieces D.unit ⊤))
variable (𝒲 : (relCurve C B).PointedCover) (σ : relCurve C B → D.index)
variable (hσ : ∀ y : relCurve C B, 𝒲.opens y ≤ D.pieces (σ y))

/-- The defining ratio equation of the section's restricted components on the overlaps
of a subordinated pointed cover: the matching relation of the glued family, restricted
from `⊤ ⊓ Uᵢ ⊓ Uⱼ`. -/
private lemma component_ratio_eq (y y' : relCurve C B) :
    ((relCurve C B).presheaf.map (homOfLE (inf_le_left :
        𝒲.opens y ⊓ 𝒲.opens y' ≤ 𝒲.opens y)).op).hom
        ((relCurve C B).resHom (hσ y) (D.component s (σ y)))
      = (gluedSubordUnit D.unit 𝒲 σ hσ y y' :
            Γ(relCurve C B, 𝒲.opens y ⊓ 𝒲.opens y'))
        * ((relCurve C B).presheaf.map (homOfLE (inf_le_right :
            𝒲.opens y ⊓ 𝒲.opens y' ≤ 𝒲.opens y')).op).hom
            ((relCurve C B).resHom (hσ y') (D.component s (σ y'))) := by
  have hle : 𝒲.opens y ⊓ 𝒲.opens y'
      ≤ ⊤ ⊓ D.pieces (σ y) ⊓ D.pieces (σ y') :=
    le_inf (le_inf le_top (inf_le_left.trans (hσ y))) (inf_le_right.trans (hσ y'))
  have key := congrArg ((relCurve C B).resHom hle) (s.property (σ y) (σ y'))
  rw [map_mul] at key
  simp only [Scheme.resHom_resHom] at key
  change (relCurve C B).resHom inf_le_left
      ((relCurve C B).resHom (hσ y) (D.component s (σ y)))
    = (gluedSubordUnit D.unit 𝒲 σ hσ y y' :
        Γ(relCurve C B, 𝒲.opens y ⊓ 𝒲.opens y'))
      * (relCurve C B).resHom inf_le_right
          ((relCurve C B).resHom (hσ y') (D.component s (σ y')))
  rw [gluedSubordUnit, val_unitsRestrict, component, component]
  simp only [Scheme.resHom_resHom]
  exact key

/-- **Sections ↦ divisor families** (DAT-A, worksheet §2.2 step 2): a germ-regular
global section of the DAT-1 glued sheaf is a `Scheme.LocalEquations` datum on any
pointed cover subordinated to the pieces — the equations are the (restricted)
components, the ratio witnesses the subordinated transition units. Germ-regularity
(`hreg`) is DAT-A2's output (`germ_component_mem_nonZeroDivisors` relatively;
`Scheme.germ_mem_nonZeroDivisors_of_ne_zero` on an integral field-level curve). -/
noncomputable def sectionLocalEquations
    (hreg : ∀ (j : D.index) (y : relCurve C B) (hy : y ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom (D.component s j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk y)) :
    (relCurve C B).LocalEquations where
  cover := 𝒲
  eqn y := (relCurve C B).resHom (hσ y) (D.component s (σ y))
  regular y z hz := by
    rw [Scheme.resHom, TopCat.Presheaf.germ_res_apply]
    exact hreg (σ y) z (hσ y hz)
  ratio_isUnit y y' :=
    ⟨gluedSubordUnit D.unit 𝒲 σ hσ y y', D.component_ratio_eq s 𝒲 σ hσ y y'⟩

variable (hreg : ∀ (j : D.index) (y : relCurve C B) (hy : y ∈ D.pieces j),
  ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom (D.component s j)
    ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk y))

@[simp]
lemma sectionLocalEquations_cover :
    (D.sectionLocalEquations s 𝒲 σ hσ hreg).cover = 𝒲 :=
  rfl

@[simp]
lemma sectionLocalEquations_eqn (y : relCurve C B) :
    (D.sectionLocalEquations s 𝒲 σ hσ hreg).eqn y
      = (relCurve C B).resHom (hσ y) (D.component s (σ y)) :=
  rfl

/-- **The ratio units are exactly the cocycle's transition units** (worksheet §2.2 step
2's "ratio units EXACTLY the cocycle"), in subordinated form: by uniqueness of ratio
witnesses against a regular equation. On the piece cover the subordination is
`≤`-reflexivity and `gluedSubordUnit` is the transition unit restricted along it. -/
lemma sectionLocalEquations_ratioUnit (y y' : relCurve C B) :
    (D.sectionLocalEquations s 𝒲 σ hσ hreg).ratioUnit y y'
      = gluedSubordUnit D.unit 𝒲 σ hσ y y' :=
  ((D.sectionLocalEquations s 𝒲 σ hσ hreg).ratioUnit_unique y y'
    (gluedSubordUnit D.unit 𝒲 σ hσ y y')
    (D.component_ratio_eq s 𝒲 σ hσ y y')).symm

/-- The units cocycle of the constructed LocalEquations datum is the (1e) subordinated
cocycle of the datum. -/
lemma sectionLocalEquations_unitsCocycle :
    (D.sectionLocalEquations s 𝒲 σ hσ hreg).unitsCocycle
      = gluedSubordCocycle D.isGluingCocycle 𝒲 σ hσ :=
  Scheme.unitsCocycle_ext fun y y' =>
    ((D.sectionLocalEquations s 𝒲 σ hσ hreg).unitsCocycle_evInf y y').trans
      ((D.sectionLocalEquations_ratioUnit s 𝒲 σ hσ hreg y y').trans
        (gluedSubordCocycle_evInf D.isGluingCocycle 𝒲 σ hσ y y').symm)

/-- **THE CLASS LAW** (DAT-A keystone; the Abel correspondence of worksheet §2.2 step
2): the Picard class of the divisor datum cut out by a germ-regular global section of
the DAT-1 glued sheaf is THE Čech Picard class of the datum's cocycle (stage (1e),
consumed on the nose through `cechPicClass_eq_mk`). -/
theorem sectionLocalEquations_picClass :
    (D.sectionLocalEquations s 𝒲 σ hσ hreg).picClass = D.cechPicClass := by
  change Scheme.CechPic.mk 𝒲
    (D.sectionLocalEquations s 𝒲 σ hσ hreg).unitsCocycle.class = D.cechPicClass
  rw [D.sectionLocalEquations_unitsCocycle s 𝒲 σ hσ hreg]
  exact D.cechPicClass_eq_mk 𝒲 σ hσ

end AffineHom

/-- **Independence of the section and the cover** (refinement/rescaling naturality,
subsumed): the class of the divisor datum cut by ANY germ-regular section of the datum,
on ANY subordinated pointed cover, is the same — both are `D.cechPicClass`. Unit
rescalings and cover refinements of the constructed datum keep the class by the landed
`LocalEquations.picClass_rescale`/`picClass_restrict`. -/
theorem sectionLocalEquations_picClass_congr
    {π : C.left ⟶ P1 k} [IsAffineHom π] (D : BasicOpenCocycleDatum C B π)
    (s s' : ↥(gluedSubmodule B D.pieces D.unit ⊤))
    (𝒲 𝒲' : (relCurve C B).PointedCover) (σ σ' : relCurve C B → D.index)
    (hσ : ∀ y : relCurve C B, 𝒲.opens y ≤ D.pieces (σ y))
    (hσ' : ∀ y : relCurve C B, 𝒲'.opens y ≤ D.pieces (σ' y))
    (hreg : ∀ (j : D.index) (y : relCurve C B) (hy : y ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom (D.component s j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk y))
    (hreg' : ∀ (j : D.index) (y : relCurve C B) (hy : y ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) y hy).hom (D.component s' j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk y)) :
    (D.sectionLocalEquations s 𝒲 σ hσ hreg).picClass
      = (D.sectionLocalEquations s' 𝒲' σ' hσ' hreg').picClass := by
  rw [D.sectionLocalEquations_picClass s 𝒲 σ hσ hreg,
    D.sectionLocalEquations_picClass s' 𝒲' σ' hσ' hreg']

/-! ## The A2-bundled wrapper, on the canonical pointed cover -/

section Bundled

variable {π : C.left ⟶ P1 k} [IsFinite π]
variable (D : BasicOpenCocycleDatum C B π)

/-- **Fibrewise-nonzero sections cut divisors** (DAT-A + DAT-A2, bundled): over a
Noetherian test ring, a fibrewise-regular global section of the DAT-1 glued sheaf
yields a `LocalEquations` divisor datum on the canonical pointed cover by pieces; its
class is `D.cechPicClass` (`sectionLocalEquationsOfFibrewiseRegular_picClass`). -/
noncomputable def sectionLocalEquationsOfFibrewiseRegular
    [IsNoetherianRing B]
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤))
    (hfib : ∀ (j : D.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField)) :
    (relCurve C B).LocalEquations :=
  D.sectionLocalEquations s D.pointedCover D.pieceIndex (fun _ => le_rfl)
    (fun j y hy => D.germ_component_mem_nonZeroDivisors s j (hfib j) y hy)

/-- The class law for the A2-bundled wrapper: the fibrewise-regular section cuts a
divisor of class exactly the datum's (1e) class. -/
theorem sectionLocalEquationsOfFibrewiseRegular_picClass
    [IsNoetherianRing B]
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤))
    (hfib : ∀ (j : D.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField)) :
    (D.sectionLocalEquationsOfFibrewiseRegular s hfib).picClass = D.cechPicClass :=
  D.sectionLocalEquations_picClass s D.pointedCover D.pieceIndex (fun _ => le_rfl) _

end Bundled

end BasicOpenCocycleDatum

end AlgebraicGeometry
