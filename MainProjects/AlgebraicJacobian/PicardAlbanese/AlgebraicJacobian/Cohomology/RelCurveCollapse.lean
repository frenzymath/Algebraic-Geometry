/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafClass
import AlgebraicJacobian.Cohomology.GluedSheafFibre
import AlgebraicJacobian.Cohomology.RelThetaTransport
import AlgebraicJacobian.Picard.LocalEquationsPullback
import AlgebraicJacobian.Picard.UniversalSections
import AlgebraicJacobian.RiemannRoch.ClassDegMapIso

/-!
# The base-field collapse brick: the theta twist as a cocycle datum (I-0175's M–L sub-brick)

The reusable seam between the twist world (`relThetaTwistSheaf`, where the ledger `H¹`
inputs land through `subsingleton_relThetaPairH1`) and the datum world
(`BasicOpenCocycleDatum`, which owns base change, the presentation bridge, and the Čech
Picard class law).  For any test ring `B` this file packages the relative theta cocycle
`t₀ᵃ` as a pinned cocycle datum on the **two whole pinned charts** (each chart is the
basic open of `1` in itself):

* `AlgebraicGeometry.thetaChartDatum` — the datum `(V₀ᴮ, V₁ᴮ; t₀ᵃ)` presenting `𝒪(Θᵃ)`
  on `relCurve C B`;
* `AlgebraicGeometry.thetaChartDatumSheafIso` — **the collapse of the sheaves**:
  the datum's glued sheaf is the relative theta twist sheaf,
  `(thetaChartDatum C B π a).sheaf ≅ relThetaTwistSheaf C B π a`;
* `AlgebraicGeometry.subsingleton_datumPair_h1_thetaChartDatum` — the `H¹` seam: the
  ledger-transported vanishing of the relative theta pair (`subsingleton_relThetaPairH1`,
  the landed I-0175 collapse of the two-lattice pairs) discharges the datum engine's
  `H¹`-input at `B = k`;
* `AlgebraicGeometry.cechPicClass_thetaChartDatum` — **the class law**: the datum's Čech
  Picard class is the pullback of the fiber twist `Θᵃ = fiberTwist π a` along the
  base-field collapse `relCurve C k ⟶ C.left` (the first projection, an isomorphism at
  test ring `k`);
* `AlgebraicGeometry.classDeg_cechPicClass_thetaChartDatum` — the degree of the datum
  class at `k` is `a · δ` (`windowδ`), through W7-B3's `classDeg_cechPicMap_of_isIso`.

Downstream (`RiemannRoch/WindowFieldTransport.lean`) base-changes the datum to a field
extension `K/k` and extracts the abstract fibre window divisor `N` of DDR-2's pinch from
its meromorphic presentation.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C B, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k B).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

section Datum

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (B : Type u) [CommRing B] [Algebra k B]
variable (π : C.left ⟶ P1 k) [IsFinite π]

/-- **The whole-chart cover data**: the two pinned charts themselves, each presented as
the basic open of `1` (partition of unity `1 · 1 = 1`). -/
noncomputable def thetaChartCover : BasicOpenCoverData C B π where
  J₀ := PUnit
  J₁ := PUnit
  fintype₀ := inferInstance
  fintype₁ := inferInstance
  h₀ _ := 1
  h₁ _ := 1
  a₀ _ := 1
  a₁ _ := 1
  partition₀ := by simp
  partition₁ := by simp

/-- The chart-0 piece is the whole first pinned chart. -/
lemma thetaChartCover_pieces_inl (j : (thetaChartCover C B π).J₀) :
    (thetaChartCover C B π).pieces (Sum.inl j) = (relCover C B (fiberTwoCover π)).V₀ :=
  (relCurve C B).basicOpen_of_isUnit isUnit_one

/-- The chart-1 piece is the whole second pinned chart. -/
lemma thetaChartCover_pieces_inr (j : (thetaChartCover C B π).J₁) :
    (thetaChartCover C B π).pieces (Sum.inr j) = (relCover C B (fiberTwoCover π)).V₁ :=
  (relCurve C B).basicOpen_of_isUnit isUnit_one

/-- Every piece is contained in its pinned chart, chart-0 side. -/
lemma thetaChartCover_pieces_le_inl (j : (thetaChartCover C B π).J₀) :
    (thetaChartCover C B π).pieces (Sum.inl j) ≤ (relCover C B (fiberTwoCover π)).V₀ :=
  (thetaChartCover_pieces_inl C B π j).le

/-- Every piece is contained in its pinned chart, chart-1 side. -/
lemma thetaChartCover_pieces_le_inr (j : (thetaChartCover C B π).J₁) :
    (thetaChartCover C B π).pieces (Sum.inr j) ≤ (relCover C B (fiberTwoCover π)).V₁ :=
  (thetaChartCover_pieces_inr C B π j).le

variable (a : ℕ)

/-- **The whole-chart theta transition units**: `1` on the diagonal blocks, the relative
theta cocycle `t₀ᵃ` (resp. its inverse) on the cross-chart blocks, restricted to the
piece overlaps. -/
noncomputable def thetaChartUnit :
    ∀ i j : (thetaChartCover C B π).index,
      Γ(relCurve C B,
        (thetaChartCover C B π).pieces i ⊓ (thetaChartCover C B π).pieces j)ˣ
  | Sum.inl _, Sum.inl _ => 1
  | Sum.inl j, Sum.inr j' =>
      (relCurve C B).unitsRestrict
        (inf_le_inf (thetaChartCover_pieces_le_inl C B π j)
          (thetaChartCover_pieces_le_inr C B π j'))
        (relThetaCocycle C B π a)
  | Sum.inr j, Sum.inl j' =>
      (relCurve C B).unitsRestrict
        (le_inf (inf_le_right.trans (thetaChartCover_pieces_le_inl C B π j'))
          (inf_le_left.trans (thetaChartCover_pieces_le_inr C B π j)))
        (relThetaCocycle C B π a)⁻¹
  | Sum.inr _, Sum.inr _ => 1

/-- The whole-chart theta units satisfy the gluing cocycle law. -/
lemma isGluingCocycle_thetaChartUnit :
    Scheme.IsGluingCocycle (thetaChartCover C B π).pieces (thetaChartUnit C B π a) where
  unit_self i := by
    rcases i with j | j <;> rfl
  mul_res i j l := by
    have hval : ∀ {U W : (relCurve C B).Opens} (h : W ≤ U) (u : Γ(relCurve C B, U)ˣ),
        ((relCurve C B).unitsRestrict h u : Γ(relCurve C B, W))
          = (relCurve C B).resHom h (u : Γ(relCurve C B, U)) := fun _ _ => rfl
    rcases i with i | i <;> rcases j with j | j <;> rcases l with l | l <;>
      simp only [thetaChartUnit, Units.val_one, map_one, one_mul, mul_one, hval,
        Scheme.resHom_resHom]
    · rw [← map_mul, Units.mul_inv, map_one]
    · rw [← map_mul, Units.inv_mul, map_one]

/-- **The whole-chart theta datum** `(V₀ᴮ, V₁ᴮ; t₀ᵃ)`: the relative theta cocycle as a
pinned basic-open cocycle datum whose pieces are the two whole pinned charts. -/
noncomputable def thetaChartDatum : BasicOpenCocycleDatum C B π :=
  { thetaChartCover C B π with
    unit := thetaChartUnit C B π a
    isGluingCocycle := isGluingCocycle_thetaChartUnit C B π a }

@[simp]
lemma thetaChartDatum_pieces :
    (thetaChartDatum C B π a).pieces = (thetaChartCover C B π).pieces := rfl

@[simp]
lemma thetaChartDatum_unit :
    (thetaChartDatum C B π a).unit = thetaChartUnit C B π a := rfl

/-! ## The collapse of the sheaves: the datum's glued sheaf is the theta twist sheaf -/

section SheafIso

/-- **The glued-to-twist membership**: the two components of a glued family for the
whole-chart theta datum, restricted along the piece identifications, form a twisted
pair for the relative theta cocycle. -/
private lemma mem_twist_of_glued {W : (relCurve C B).Opens}
    {s : ∀ j : (thetaChartCover C B π).index,
      Γ(relCurve C B, W ⊓ (thetaChartCover C B π).pieces j)}
    (hs : s ∈ gluedSubmodule B (thetaChartCover C B π).pieces (thetaChartUnit C B π a) W) :
    ((relCurve C B).resHom
        (inf_le_inf_left W (thetaChartCover_pieces_inl C B π PUnit.unit).ge)
        (s (Sum.inl PUnit.unit)),
      (relCurve C B).resHom
        (inf_le_inf_left W (thetaChartCover_pieces_inr C B π PUnit.unit).ge)
        (s (Sum.inr PUnit.unit)))
      ∈ twistSubmodule B (relCover C B (fiberTwoCover π)).V₀
        (relCover C B (fiberTwoCover π)).V₁ (relThetaCocycle C B π a) W := by
  rw [mem_twistSubmodule_iff]
  have hval : (thetaChartUnit C B π a (Sum.inl PUnit.unit) (Sum.inr PUnit.unit)
        : Γ(relCurve C B, (thetaChartCover C B π).pieces (Sum.inl PUnit.unit)
            ⊓ (thetaChartCover C B π).pieces (Sum.inr PUnit.unit)))
      = (relCurve C B).resHom
          (inf_le_inf (thetaChartCover_pieces_le_inl C B π PUnit.unit)
            (thetaChartCover_pieces_le_inr C B π PUnit.unit))
          (relThetaCocycle C B π a
            : Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₀
                ⊓ (relCover C B (fiberTwoCover π)).V₁)) := rfl
  have key := congrArg ((relCurve C B).resHom (le_of_eq (by
      rw [thetaChartCover_pieces_inl, thetaChartCover_pieces_inr] :
        W ⊓ (relCover C B (fiberTwoCover π)).V₀ ⊓ (relCover C B (fiberTwoCover π)).V₁
          = W ⊓ (thetaChartCover C B π).pieces (Sum.inl PUnit.unit)
            ⊓ (thetaChartCover C B π).pieces (Sum.inr PUnit.unit))))
    (hs (Sum.inl PUnit.unit) (Sum.inr PUnit.unit))
  rw [map_mul, hval] at key
  simp only [Scheme.resHom_resHom] at key ⊢
  exact key

/-- **The twist-to-glued membership**: the componentwise restrictions of a twisted pair
form a glued family for the whole-chart theta datum (all four matchings from the one
twist relation). -/
private lemma mem_glued_of_twist {W : (relCurve C B).Opens}
    {p : Γ(relCurve C B, W ⊓ (relCover C B (fiberTwoCover π)).V₀)
        × Γ(relCurve C B, W ⊓ (relCover C B (fiberTwoCover π)).V₁)}
    (hmem : p ∈ twistSubmodule B (relCover C B (fiberTwoCover π)).V₀
      (relCover C B (fiberTwoCover π)).V₁ (relThetaCocycle C B π a) W) :
    (fun j : (thetaChartCover C B π).index => Sum.rec
        (fun j' => (relCurve C B).resHom
          (inf_le_inf_left W (thetaChartCover_pieces_le_inl C B π j')) p.1)
        (fun j' => (relCurve C B).resHom
          (inf_le_inf_left W (thetaChartCover_pieces_le_inr C B π j')) p.2) j)
      ∈ gluedSubmodule B (thetaChartCover C B π).pieces (thetaChartUnit C B π a) W := by
  have hp := (mem_twistSubmodule_iff B _ _ _ p).mp hmem
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · -- diagonal `(0,0)`: the unit is `1`
    have hu : (thetaChartUnit C B π a (Sum.inl i) (Sum.inl j)) = 1 := rfl
    rw [hu, Units.val_one, map_one, one_mul]
    simp only [Scheme.resHom_resHom]
  · -- cross `(0,1)`: the twist relation itself
    have hu : (thetaChartUnit C B π a (Sum.inl i) (Sum.inr j)
          : Γ(relCurve C B, (thetaChartCover C B π).pieces (Sum.inl i)
              ⊓ (thetaChartCover C B π).pieces (Sum.inr j)))
        = (relCurve C B).resHom
            (inf_le_inf (thetaChartCover_pieces_le_inl C B π i)
              (thetaChartCover_pieces_le_inr C B π j))
            (relThetaCocycle C B π a
              : Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₀
                  ⊓ (relCover C B (fiberTwoCover π)).V₁)) := rfl
    rw [hu]
    have key := congrArg ((relCurve C B).resHom
      (le_inf (le_inf (inf_le_left.trans inf_le_left)
          ((inf_le_left.trans inf_le_right).trans
            (thetaChartCover_pieces_le_inl C B π i)))
        (inf_le_right.trans (thetaChartCover_pieces_le_inr C B π j)) :
        W ⊓ (thetaChartCover C B π).pieces (Sum.inl i)
            ⊓ (thetaChartCover C B π).pieces (Sum.inr j)
          ≤ W ⊓ (relCover C B (fiberTwoCover π)).V₀
            ⊓ (relCover C B (fiberTwoCover π)).V₁)) hp
    rw [map_mul] at key
    simp only [Scheme.resHom_resHom] at key ⊢
    exact key
  · -- cross `(1,0)`: the inverse twist relation
    have hu : (thetaChartUnit C B π a (Sum.inr i) (Sum.inl j)
          : Γ(relCurve C B, (thetaChartCover C B π).pieces (Sum.inr i)
              ⊓ (thetaChartCover C B π).pieces (Sum.inl j)))
        = (relCurve C B).resHom
            (le_inf (inf_le_right.trans (thetaChartCover_pieces_le_inl C B π j))
              (inf_le_left.trans (thetaChartCover_pieces_le_inr C B π i)))
            (((relThetaCocycle C B π a)⁻¹
                : Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₀
                    ⊓ (relCover C B (fiberTwoCover π)).V₁)ˣ)
              : Γ(relCurve C B, (relCover C B (fiberTwoCover π)).V₀
                  ⊓ (relCover C B (fiberTwoCover π)).V₁)) := rfl
    rw [hu]
    have key := congrArg ((relCurve C B).resHom
      (le_inf (le_inf (inf_le_left.trans inf_le_left)
          (inf_le_right.trans (thetaChartCover_pieces_le_inl C B π j)))
        ((inf_le_left.trans inf_le_right).trans
          (thetaChartCover_pieces_le_inr C B π i)) :
        W ⊓ (thetaChartCover C B π).pieces (Sum.inr i)
            ⊓ (thetaChartCover C B π).pieces (Sum.inl j)
          ≤ W ⊓ (relCover C B (fiberTwoCover π)).V₀
            ⊓ (relCover C B (fiberTwoCover π)).V₁)) hp
    rw [map_mul] at key
    simp only [Scheme.resHom_resHom] at key ⊢
    rw [key, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  · -- diagonal `(1,1)`: the unit is `1`
    have hu : (thetaChartUnit C B π a (Sum.inr i) (Sum.inr j)) = 1 := rfl
    rw [hu, Units.val_one, map_one, one_mul]
    simp only [Scheme.resHom_resHom]

/-- **Forward: a glued family reads as a twisted pair** — the two components,
restricted along the piece identifications. -/
noncomputable def gluedToTwistApp (W : (relCurve C B).Opens) :
    ↥(gluedSubmodule B (thetaChartDatum C B π a).pieces (thetaChartDatum C B π a).unit W)
      →ₗ[B] ↥(twistSubmodule B (relCover C B (fiberTwoCover π)).V₀
        (relCover C B (fiberTwoCover π)).V₁ (relThetaCocycle C B π a) W) where
  toFun s := ⟨(secRes ((relCurve C B).moduleKSheaf B)
        (inf_le_inf_left W (thetaChartCover_pieces_inl C B π PUnit.unit).ge)
        (s.val (Sum.inl PUnit.unit)),
      secRes ((relCurve C B).moduleKSheaf B)
        (inf_le_inf_left W (thetaChartCover_pieces_inr C B π PUnit.unit).ge)
        (s.val (Sum.inr PUnit.unit))),
    mem_twist_of_glued C B π a s.property⟩
  map_add' _ _ := Subtype.ext (Prod.ext
    (map_add (secRes ((relCurve C B).moduleKSheaf B) _) _ _)
    (map_add (secRes ((relCurve C B).moduleKSheaf B) _) _ _))
  map_smul' r _ := Subtype.ext (Prod.ext
    (map_smul (secRes ((relCurve C B).moduleKSheaf B) _) r _)
    (map_smul (secRes ((relCurve C B).moduleKSheaf B) _) r _))

/-- **Backward: a twisted pair assembles to a glued family**. -/
noncomputable def twistToGluedApp (W : (relCurve C B).Opens) :
    ↥(twistSubmodule B (relCover C B (fiberTwoCover π)).V₀
        (relCover C B (fiberTwoCover π)).V₁ (relThetaCocycle C B π a) W)
      →ₗ[B] ↥(gluedSubmodule B (thetaChartDatum C B π a).pieces
        (thetaChartDatum C B π a).unit W) where
  toFun p := ⟨fun j => Sum.rec
      (fun j' => secRes ((relCurve C B).moduleKSheaf B)
        (inf_le_inf_left W (thetaChartCover_pieces_le_inl C B π j')) p.val.1)
      (fun j' => secRes ((relCurve C B).moduleKSheaf B)
        (inf_le_inf_left W (thetaChartCover_pieces_le_inr C B π j')) p.val.2) j,
    by exact mem_glued_of_twist C B π a p.property⟩
  map_add' p q := Subtype.ext (funext fun j => by
    rcases j with j | j <;>
      exact map_add (secRes ((relCurve C B).moduleKSheaf B) _) _ _)
  map_smul' r p := Subtype.ext (funext fun j => by
    rcases j with j | j <;>
      exact map_smul (secRes ((relCurve C B).moduleKSheaf B) _) r _)

/-- **The glued–twist section equivalence** over every open. -/
noncomputable def gluedTwistEquiv (W : (relCurve C B).Opens) :
    ↥(gluedSubmodule B (thetaChartDatum C B π a).pieces (thetaChartDatum C B π a).unit W)
      ≃ₗ[B] ↥(twistSubmodule B (relCover C B (fiberTwoCover π)).V₀
        (relCover C B (fiberTwoCover π)).V₁ (relThetaCocycle C B π a) W) :=
  LinearEquiv.ofLinear (gluedToTwistApp C B π a W) (twistToGluedApp C B π a W)
    (LinearMap.ext fun p => Subtype.ext (Prod.ext
      ((Scheme.resHom_resHom _ _ _).trans (Scheme.resHom_self _ _))
      ((Scheme.resHom_resHom _ _ _).trans (Scheme.resHom_self _ _))))
    (LinearMap.ext fun s => Subtype.ext (funext fun j => by
      rcases j with j | j <;> cases j <;>
        exact (Scheme.resHom_resHom _ _ _).trans (Scheme.resHom_self _ _)))

/-- The section equivalence commutes with restriction. -/
lemma gluedToTwistApp_res {W' W : (relCurve C B).Opens} (h : W' ≤ W)
    (s : ↥(gluedSubmodule B (thetaChartDatum C B π a).pieces
      (thetaChartDatum C B π a).unit W)) :
    gluedToTwistApp C B π a W'
        (gluedRes B (thetaChartDatum C B π a).pieces (thetaChartDatum C B π a).unit h s)
      = twistRes B (relCover C B (fiberTwoCover π)).V₀
          (relCover C B (fiberTwoCover π)).V₁ (relThetaCocycle C B π a) h
          (gluedToTwistApp C B π a W s) :=
  Subtype.ext (Prod.ext
    ((Scheme.resHom_resHom _ _ _).trans (Scheme.resHom_resHom _ _ _).symm)
    ((Scheme.resHom_resHom _ _ _).trans (Scheme.resHom_resHom _ _ _).symm))

/-- The inverse section equivalence commutes with restriction. -/
lemma gluedTwistEquiv_symm_res {W' W : (relCurve C B).Opens} (h : W' ≤ W)
    (p : ↥(twistSubmodule B (relCover C B (fiberTwoCover π)).V₀
      (relCover C B (fiberTwoCover π)).V₁ (relThetaCocycle C B π a) W)) :
    gluedRes B (thetaChartDatum C B π a).pieces (thetaChartDatum C B π a).unit h
        ((gluedTwistEquiv C B π a W).symm p)
      = (gluedTwistEquiv C B π a W').symm
          (twistRes B (relCover C B (fiberTwoCover π)).V₀
            (relCover C B (fiberTwoCover π)).V₁ (relThetaCocycle C B π a) h p) := by
  apply (gluedTwistEquiv C B π a W').injective
  change gluedToTwistApp C B π a W'
      (gluedRes B (thetaChartDatum C B π a).pieces
        (thetaChartDatum C B π a).unit h ((gluedTwistEquiv C B π a W).symm p)) =
    gluedToTwistApp C B π a W'
      ((gluedTwistEquiv C B π a W').symm
        (twistRes B (relCover C B (fiberTwoCover π)).V₀
          (relCover C B (fiberTwoCover π)).V₁ (relThetaCocycle C B π a) h p))
  rw [gluedToTwistApp_res]
  change twistRes B (relCover C B (fiberTwoCover π)).V₀
      (relCover C B (fiberTwoCover π)).V₁ (relThetaCocycle C B π a) h
        ((gluedTwistEquiv C B π a W) ((gluedTwistEquiv C B π a W).symm p)) =
    (gluedTwistEquiv C B π a W')
      ((gluedTwistEquiv C B π a W').symm
        (twistRes B (relCover C B (fiberTwoCover π)).V₀
          (relCover C B (fiberTwoCover π)).V₁ (relThetaCocycle C B π a) h p))
  simp

/-- **The collapse of the sheaves**: the glued sheaf of the whole-chart theta datum is
the relative theta twist sheaf, as sheaves of `B`-modules on `relCurve C B`. -/
noncomputable def thetaChartDatumSheafIso :
    (thetaChartDatum C B π a).sheaf ≅ relThetaTwistSheaf C B π a :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents
      (fun W => (gluedTwistEquiv C B π a W.unop).toModuleIso)
      (fun {W₁ W₂} i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact gluedToTwistApp_res C B π a i.unop.le s))

/-- Cohomology-vanishing transport across the collapse, in every degree. -/
theorem subsingleton_hModule_thetaChartDatum_iff (n : ℕ) :
    Subsingleton (Sheaf.HModule (thetaChartDatum C B π a).sheaf n) ↔
      Subsingleton (Sheaf.HModule (relThetaTwistSheaf C B π a) n) :=
  (Sheaf.HModule.mapEquiv (thetaChartDatumSheafIso C B π a) n).toEquiv.subsingleton_congr

end SheafIso

/-! ## The `H¹` seam at the base field -/

/-- **The `H¹` seam at `B = k`**: the ledger-transported vanishing of the relative theta
pair (`subsingleton_relThetaPairH1`, discharged by `relThetaPairH1_windowM` and friends)
kills `H¹` of the two-lattice pair of the whole-chart theta datum — the datum engine's
`H¹` input at the base field, ready for `datum_subsingleton_h1_baseChange`. -/
theorem subsingleton_datumPair_h1_thetaChartDatum
    (h : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    Subsingleton (datumPair (thetaChartDatum C k π a)).H1 :=
  (subsingleton_datumPair_h1_iff _).mpr
    ((subsingleton_hModule_thetaChartDatum_iff C k π a 1).mpr
      ((relThetaH1PairEquiv C π a).toEquiv.subsingleton_congr.mpr h))

end Datum

/-! ## The transition units of the fiber divisor are the theta units -/

section RatioUnits

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  (π : Y ⟶ P1 K) [IsDominant π] (a : ℕ)

omit [IsIntegral Y] [IsDominant π] in
/-- `fiberEqn` in `resHom` normal form on the chart-0 members. -/
private lemma fiberEqn_of_mem' {z : Y} (h : z ∈ fiberChart₀ π) :
    fiberEqn π a z
      = Y.resHom (le_of_eq (fiberCover_opens_of_mem π h)) ((fiberCoord π) ^ a) :=
  fiberEqn_of_mem π a h

omit [IsIntegral Y] [IsDominant π] in
/-- The theta unit power in `resHom` normal form: `(θᵃ).val = res (t₀ᵃ)`. -/
private lemma thetaUnit_pow_val :
    ((thetaUnit π ^ a : Γ(Y, fiberChart₀ π ⊓ fiberChart₁ π)ˣ)
        : Γ(Y, fiberChart₀ π ⊓ fiberChart₁ π))
      = Y.resHom (inf_le_left : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₀ π)
          ((fiberCoord π) ^ a) := by
  rw [Units.val_pow_eq_pow_val, thetaUnit_val, ← map_pow]
  rfl

/-- **Same-chart transition units are `1`** (both points on the chart-0 member). -/
lemma fiberDivisor_ratioUnit_mem_mem {x y : Y} (hx : x ∈ fiberChart₀ π)
    (hy : y ∈ fiberChart₀ π) :
    (fiberDivisor π a).ratioUnit x y = 1 := by
  refine ((fiberDivisor π a).ratioUnit_unique x y 1 ?_).symm
  rw [Units.val_one, one_mul]
  change Y.resHom inf_le_left (fiberEqn π a x) = Y.resHom inf_le_right (fiberEqn π a y)
  rw [fiberEqn_of_mem' π a hx, fiberEqn_of_mem' π a hy, Scheme.resHom_resHom,
    Scheme.resHom_resHom]

/-- **Same-chart transition units are `1`** (both points on the chart-1 member). -/
lemma fiberDivisor_ratioUnit_notMem_notMem {x y : Y} (hx : x ∉ fiberChart₀ π)
    (hy : y ∉ fiberChart₀ π) :
    (fiberDivisor π a).ratioUnit x y = 1 := by
  refine ((fiberDivisor π a).ratioUnit_unique x y 1 ?_).symm
  rw [Units.val_one, one_mul]
  change Y.resHom inf_le_left (fiberEqn π a x) = Y.resHom inf_le_right (fiberEqn π a y)
  rw [fiberEqn_of_notMem π a hx, fiberEqn_of_notMem π a hy, map_one, map_one]

omit [IsIntegral Y] [IsDominant π] in
/-- The cross-chart overlap sits inside the pinned two-cover overlap (chart-0 first). -/
private lemma opens_inf_le_of_mem_of_notMem {x y : Y} (hx : x ∈ fiberChart₀ π)
    (hy : y ∉ fiberChart₀ π) :
    (fiberCover π).opens x ⊓ (fiberCover π).opens y
      ≤ fiberChart₀ π ⊓ fiberChart₁ π :=
  le_of_eq (by rw [fiberCover_opens_of_mem π hx, fiberCover_opens_of_notMem π hy])

omit [IsIntegral Y] [IsDominant π] in
/-- The cross-chart overlap sits inside the pinned two-cover overlap (chart-1 first). -/
private lemma opens_inf_le_of_notMem_of_mem {x y : Y} (hx : x ∉ fiberChart₀ π)
    (hy : y ∈ fiberChart₀ π) :
    (fiberCover π).opens x ⊓ (fiberCover π).opens y
      ≤ fiberChart₀ π ⊓ fiberChart₁ π :=
  le_inf (inf_le_right.trans (le_of_eq (fiberCover_opens_of_mem π hy)))
    (inf_le_left.trans (le_of_eq (fiberCover_opens_of_notMem π hx)))

/-- **Cross-chart transition units are the theta power** `θᵃ` (chart-0 to chart-1). -/
lemma fiberDivisor_ratioUnit_mem_notMem {x y : Y} (hx : x ∈ fiberChart₀ π)
    (hy : y ∉ fiberChart₀ π) :
    (fiberDivisor π a).ratioUnit x y
      = Y.unitsRestrict (opens_inf_le_of_mem_of_notMem π hx hy)
          (thetaUnit π ^ a) := by
  refine ((fiberDivisor π a).ratioUnit_unique x y _ ?_).symm
  change Y.resHom inf_le_left (fiberEqn π a x)
    = (Y.unitsRestrict (opens_inf_le_of_mem_of_notMem π hx hy) (thetaUnit π ^ a)
        : Γ(Y, _))
      * Y.resHom inf_le_right (fiberEqn π a y)
  have hval : (Y.unitsRestrict (opens_inf_le_of_mem_of_notMem π hx hy)
        (thetaUnit π ^ a) : Γ(Y, (fiberCover π).opens x ⊓ (fiberCover π).opens y))
      = Y.resHom (opens_inf_le_of_mem_of_notMem π hx hy)
          ((thetaUnit π ^ a : Γ(Y, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) : Γ(Y, _)) := rfl
  rw [fiberEqn_of_mem' π a hx, fiberEqn_of_notMem π a hy, map_one, mul_one, hval,
    thetaUnit_pow_val, Scheme.resHom_resHom, Scheme.resHom_resHom]

/-- **Cross-chart transition units are the inverse theta power** `θ⁻ᵃ` (chart-1 to
chart-0). -/
lemma fiberDivisor_ratioUnit_notMem_mem {x y : Y} (hx : x ∉ fiberChart₀ π)
    (hy : y ∈ fiberChart₀ π) :
    (fiberDivisor π a).ratioUnit x y
      = Y.unitsRestrict (opens_inf_le_of_notMem_of_mem π hx hy)
          (thetaUnit π ^ a)⁻¹ := by
  refine ((fiberDivisor π a).ratioUnit_unique x y _ ?_).symm
  change Y.resHom inf_le_left (fiberEqn π a x)
    = (Y.unitsRestrict (opens_inf_le_of_notMem_of_mem π hx hy) (thetaUnit π ^ a)⁻¹
        : Γ(Y, _))
      * Y.resHom inf_le_right (fiberEqn π a y)
  have hval : (Y.unitsRestrict (opens_inf_le_of_notMem_of_mem π hx hy)
        (thetaUnit π ^ a)⁻¹ : Γ(Y, (fiberCover π).opens x ⊓ (fiberCover π).opens y))
      = Y.resHom (opens_inf_le_of_notMem_of_mem π hx hy)
          (((thetaUnit π ^ a)⁻¹ : Γ(Y, fiberChart₀ π ⊓ fiberChart₁ π)ˣ)
            : Γ(Y, _)) := rfl
  rw [fiberEqn_of_notMem π a hx, fiberEqn_of_mem' π a hy, map_one, hval]
  have hy' : Y.resHom (inf_le_right :
        (fiberCover π).opens x ⊓ (fiberCover π).opens y ≤ (fiberCover π).opens y)
      (Y.resHom (le_of_eq (fiberCover_opens_of_mem π hy)) ((fiberCoord π) ^ a))
      = Y.resHom (opens_inf_le_of_notMem_of_mem π hx hy)
          ((thetaUnit π ^ a : Γ(Y, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) : Γ(Y, _)) := by
    rw [thetaUnit_pow_val, Scheme.resHom_resHom, Scheme.resHom_resHom]
  rw [hy', ← map_mul, Units.inv_mul, map_one]

end RatioUnits

/-! ## The class law: the datum class is the pulled fiber twist -/

section ClassLaw

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (π : C.left ⟶ P1 k) [IsFinite π] [IsDominant π]
variable [IsIntegral C.left] [IsIntegral (relCurve C k)]
variable (a : ℕ)

omit [IsFinite π] [IsDominant π] in
/-- The base-field collapse maps the generic point to the generic point. -/
lemma fst_left_self_genericPoint :
    ((fst C (overSpec k k)).left).base (genericPoint (relCurve C k))
      = genericPoint C.left := by
  haveI : IrreducibleSpace (↥(C ⊗ overSpec k k).left) :=
    (inferInstance : IrreducibleSpace (↥(relCurve C k)))
  exact genericPoint_eq_of_surjective _

/-- **The pulled fiber system**: the local-equation system of `a · F` on `C.left`,
pulled back along the base-field collapse — regularity for free from integrality. -/
noncomputable def thetaFiberPullback : (relCurve C k).LocalEquations :=
  haveI : IsIntegral (C ⊗ overSpec k k).left := ‹IsIntegral (relCurve C k)›
  (fiberDivisor π a).pullback (fst C (overSpec k k)).left
    (fun y z hz => Scheme.LocalEquations.pullbackEqn_germ_mem_nonZeroDivisors
      (fst C (overSpec k k)).left (fst_left_self_genericPoint C) (fiberDivisor π a) y z hz)

omit [IsFinite π] in
/-- The pulled fiber system presents the pulled fiber twist `Θᵃ`. -/
lemma thetaFiberPullback_picClass :
    (thetaFiberPullback C π a).picClass
      = Scheme.CechPic.map (fst C (overSpec k k)).left (fiberTwist π a) :=
  Scheme.LocalEquations.picClass_pullback _ _ _

omit [IsFinite π] in
/-- The transition units of the pulled fiber system are the pulled transition units. -/
lemma thetaFiberPullback_ratioUnit (z w : relCurve C k) :
    (thetaFiberPullback C π a).ratioUnit z w
      = (fst C (overSpec k k)).left.unitsAppLE
          ((fiberCover π).opens (((fst C (overSpec k k)).left).base z)
            ⊓ (fiberCover π).opens (((fst C (overSpec k k)).left).base w))
          (((fiberCover π).pullback (fst C (overSpec k k)).left).opens z
            ⊓ ((fiberCover π).pullback (fst C (overSpec k k)).left).opens w)
          ((fst C (overSpec k k)).left.le_preimage_inf inf_le_left inf_le_right)
          ((fiberDivisor π a).ratioUnit (((fst C (overSpec k k)).left).base z)
            (((fst C (overSpec k k)).left).base w)) :=
  Scheme.LocalEquations.pullback_ratioUnit _ _ _ z w

omit [IsFinite π] in
/-- The pulled-system pair values in ratio-unit form. -/
lemma thetaFiberPullback_evInf (z w : relCurve C k) :
    Scheme.unitsEvInf (thetaFiberPullback C π a).unitsCocycle z w
      = (thetaFiberPullback C π a).ratioUnit z w :=
  (thetaFiberPullback C π a).unitsCocycle_evInf z w

/-! ### The chart classification -/

open Classical in
/-- The chart classification of a point of the relative curve: chart 0 if its image
lies in the first pinned chart, chart 1 otherwise. -/
noncomputable def thetaChartIndex (z : relCurve C k) : (thetaChartCover C k π).index :=
  if ((fst C (overSpec k k)).left).base z ∈ fiberChart₀ π then Sum.inl PUnit.unit
  else Sum.inr PUnit.unit

omit [IsDominant π] [IsIntegral C.left] [IsIntegral (relCurve C k)] in
lemma thetaChartIndex_of_mem {z : relCurve C k}
    (h : ((fst C (overSpec k k)).left).base z ∈ fiberChart₀ π) :
    thetaChartIndex C π z = Sum.inl PUnit.unit := if_pos h

omit [IsDominant π] [IsIntegral C.left] [IsIntegral (relCurve C k)] in
lemma thetaChartIndex_of_notMem {z : relCurve C k}
    (h : ((fst C (overSpec k k)).left).base z ∉ fiberChart₀ π) :
    thetaChartIndex C π z = Sum.inr PUnit.unit := if_neg h

omit [IsDominant π] [IsIntegral C.left] [IsIntegral (relCurve C k)] in
/-- The pulled fiber cover is subordinated to the whole-chart pieces along the chart
classification. -/
lemma pullback_fiberCover_le_pieces (z : relCurve C k) :
    ((fiberCover π).pullback (fst C (overSpec k k)).left).opens z
      ≤ (thetaChartCover C k π).pieces (thetaChartIndex C π z) := by
  by_cases h : ((fst C (overSpec k k)).left).base z ∈ fiberChart₀ π
  · rw [thetaChartIndex_of_mem C π h, thetaChartCover_pieces_inl,
      Scheme.PointedCover.pullback_opens, fiberCover_opens_of_mem π h]
    exact le_rfl
  · rw [thetaChartIndex_of_notMem C π h, thetaChartCover_pieces_inr,
      Scheme.PointedCover.pullback_opens, fiberCover_opens_of_notMem π h]
    exact le_rfl

/-! ### Value normal forms -/

omit [IsDominant π] [IsIntegral C.left] [IsIntegral (relCurve C k)] in
/-- The subordinated pair value at known chart indices, in `resHom` normal form. -/
private lemma gluedSubordUnit_val_of_eq {z w : relCurve C k}
    {i j : (thetaChartCover C k π).index} (hi : thetaChartIndex C π z = i)
    (hj : thetaChartIndex C π w = j)
    (hle : ((fiberCover π).pullback (fst C (overSpec k k)).left).opens z
        ⊓ ((fiberCover π).pullback (fst C (overSpec k k)).left).opens w
      ≤ (thetaChartCover C k π).pieces i ⊓ (thetaChartCover C k π).pieces j) :
    (gluedSubordUnit (thetaChartDatum C k π a).unit
        ((fiberCover π).pullback (fst C (overSpec k k)).left) (thetaChartIndex C π)
        (pullback_fiberCover_le_pieces C π) z w
      : Γ(relCurve C k, ((fiberCover π).pullback (fst C (overSpec k k)).left).opens z
          ⊓ ((fiberCover π).pullback (fst C (overSpec k k)).left).opens w))
      = (relCurve C k).resHom hle
          (thetaChartUnit C k π a i j
            : Γ(relCurve C k, (thetaChartCover C k π).pieces i
                ⊓ (thetaChartCover C k π).pieces j)) := by
  subst hi
  subst hj
  rfl

omit [IsFinite π] [IsDominant π] [IsIntegral C.left] [IsIntegral (relCurve C k)] in
/-- Restriction after `appLE` composes to a single `appLE` (elementwise). -/
private lemma resHom_appLE_apply {U : C.left.Opens} {V V' : (relCurve C k).Opens}
    (e : V ≤ (fst C (overSpec k k)).left ⁻¹ᵁ U) (h : V' ≤ V) (s : Γ(C.left, U)) :
    (relCurve C k).resHom h (((fst C (overSpec k k)).left.appLE U V e).hom s)
      = ((fst C (overSpec k k)).left.appLE U V' (h.trans e)).hom s := by
  have hcomp : (fst C (overSpec k k)).left.appLE U V e
        ≫ (relCurve C k).presheaf.map (homOfLE h).op
      = (fst C (overSpec k k)).left.appLE U V' (h.trans e) :=
    Scheme.Hom.appLE_map (fst C (overSpec k k)).left e (homOfLE h).op
  exact congr($(hcomp).hom s)

omit [IsFinite π] [IsDominant π] [IsIntegral C.left] [IsIntegral (relCurve C k)] in
/-- `appLE` after restriction composes to a single `appLE` (elementwise). -/
private lemma appLE_resHom_apply {U' U : C.left.Opens} {V : (relCurve C k).Opens}
    (h : U' ≤ U) (e : V ≤ (fst C (overSpec k k)).left ⁻¹ᵁ U') (s : Γ(C.left, U)) :
    ((fst C (overSpec k k)).left.appLE U' V e).hom (C.left.resHom h s)
      = ((fst C (overSpec k k)).left.appLE U V
          (e.trans (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left h))).hom s := by
  have hcomp : C.left.presheaf.map (homOfLE h).op
        ≫ (fst C (overSpec k k)).left.appLE U' V e
      = (fst C (overSpec k k)).left.appLE U V
          (e.trans (Scheme.Hom.preimage_mono (fst C (overSpec k k)).left h)) :=
    Scheme.Hom.map_appLE (fst C (overSpec k k)).left e (homOfLE h).op
  exact congr($(hcomp).hom s)

omit [IsDominant π] [IsIntegral C.left] [IsIntegral (relCurve C k)] in
/-- The relative theta cocycle value is the collapse image of the theta power. -/
private lemma relThetaCocycle_val' :
    ((relThetaCocycle C k π a
        : Γ(relCurve C k, (relCover C k (fiberTwoCover π)).V₀
            ⊓ (relCover C k (fiberTwoCover π)).V₁)ˣ)
      : Γ(relCurve C k, (relCover C k (fiberTwoCover π)).V₀
          ⊓ (relCover C k (fiberTwoCover π)).V₁))
      = ((fst C (overSpec k k)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
          ((relCover C k (fiberTwoCover π)).V₀ ⊓ (relCover C k (fiberTwoCover π)).V₁)
          (le_of_eq (relCover_inf C k (fiberTwoCover π)))).hom
        ((thetaUnit π ^ a : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ)
          : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)) := rfl

omit [IsDominant π] [IsIntegral C.left] [IsIntegral (relCurve C k)] in
/-- The inverse relative theta cocycle value is the collapse image of the inverse. -/
private lemma relThetaCocycle_inv_val' :
    (((relThetaCocycle C k π a)⁻¹
        : Γ(relCurve C k, (relCover C k (fiberTwoCover π)).V₀
            ⊓ (relCover C k (fiberTwoCover π)).V₁)ˣ)
      : Γ(relCurve C k, (relCover C k (fiberTwoCover π)).V₀
          ⊓ (relCover C k (fiberTwoCover π)).V₁))
      = ((fst C (overSpec k k)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
          ((relCover C k (fiberTwoCover π)).V₀ ⊓ (relCover C k (fiberTwoCover π)).V₁)
          (le_of_eq (relCover_inf C k (fiberTwoCover π)))).hom
        (((thetaUnit π ^ a)⁻¹ : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ)
          : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)) := rfl

/-! ### The class law -/

set_option maxHeartbeats 800000 in
-- (The four-branch unit comparison crosses the `relCurve`/product spelling seam
-- repeatedly; the defeq checks exceed the default limit.)
/-- **The class law**: the Čech Picard class of the whole-chart theta datum is the
pullback of the fiber twist `Θᵃ` along the base-field collapse. -/
theorem cechPicClass_thetaChartDatum :
    (thetaChartDatum C k π a).cechPicClass
      = Scheme.CechPic.map (fst C (overSpec k k)).left (fiberTwist π a) := by
  rw [← thetaFiberPullback_picClass C π a,
    ← (thetaChartDatum C k π a).cechPicClass_eq_mk
      ((fiberCover π).pullback (fst C (overSpec k k)).left) (thetaChartIndex C π)
      (pullback_fiberCover_le_pieces C π)]
  have hR : (thetaFiberPullback C π a).picClass
      = Scheme.CechPic.mk ((fiberCover π).pullback (fst C (overSpec k k)).left)
          (thetaFiberPullback C π a).unitsCocycle.class := rfl
  rw [hR]
  refine congrArg (fun γ : (relCurve C k).unitsCocycle _ =>
    Scheme.CechPic.mk ((fiberCover π).pullback (fst C (overSpec k k)).left) γ.class)
    (Scheme.unitsCocycle_ext fun z w => ?_)
  rw [gluedSubordCocycle_evInf, thetaFiberPullback_evInf,
    thetaFiberPullback_ratioUnit]
  by_cases hz : ((fst C (overSpec k k)).left).base z ∈ fiberChart₀ π <;>
    by_cases hw : ((fst C (overSpec k k)).left).base w ∈ fiberChart₀ π
  · -- both chart 0: both units are `1`
    rw [fiberDivisor_ratioUnit_mem_mem π a hz hw, map_one]
    refine Units.ext ?_
    rw [gluedSubordUnit_val_of_eq C π a (thetaChartIndex_of_mem C π hz)
      (thetaChartIndex_of_mem C π hw)
      (inf_le_inf ((thetaChartIndex_of_mem C π hz) ▸ pullback_fiberCover_le_pieces C π z)
        ((thetaChartIndex_of_mem C π hw) ▸ pullback_fiberCover_le_pieces C π w))]
    have hu : thetaChartUnit C k π a (Sum.inl PUnit.unit) (Sum.inl PUnit.unit) = 1 := rfl
    rw [hu, Units.val_one, map_one, Units.val_one]
  · -- chart 0 to chart 1: the theta power
    rw [fiberDivisor_ratioUnit_mem_notMem π a hz hw]
    refine Units.ext ?_
    rw [gluedSubordUnit_val_of_eq C π a (thetaChartIndex_of_mem C π hz)
      (thetaChartIndex_of_notMem C π hw)
      (inf_le_inf ((thetaChartIndex_of_mem C π hz) ▸ pullback_fiberCover_le_pieces C π z)
        ((thetaChartIndex_of_notMem C π hw) ▸ pullback_fiberCover_le_pieces C π w))]
    have hval : (thetaChartUnit C k π a (Sum.inl PUnit.unit) (Sum.inr PUnit.unit)
          : Γ(relCurve C k, (thetaChartCover C k π).pieces (Sum.inl PUnit.unit)
              ⊓ (thetaChartCover C k π).pieces (Sum.inr PUnit.unit)))
        = (relCurve C k).resHom
            (inf_le_inf (thetaChartCover_pieces_le_inl C k π PUnit.unit)
              (thetaChartCover_pieces_le_inr C k π PUnit.unit))
            ((relThetaCocycle C k π a
                : Γ(relCurve C k, (relCover C k (fiberTwoCover π)).V₀
                    ⊓ (relCover C k (fiberTwoCover π)).V₁)ˣ)
              : Γ(relCurve C k, _)) := rfl
    rw [hval, Scheme.resHom_resHom, relThetaCocycle_val', resHom_appLE_apply]
    have hRval : ((fst C (overSpec k k)).left.unitsAppLE
          ((fiberCover π).opens (((fst C (overSpec k k)).left).base z)
              ⊓ (fiberCover π).opens (((fst C (overSpec k k)).left).base w))
          (((fiberCover π).pullback (fst C (overSpec k k)).left).opens z
              ⊓ ((fiberCover π).pullback (fst C (overSpec k k)).left).opens w)
          ((fst C (overSpec k k)).left.le_preimage_inf inf_le_left inf_le_right)
          (C.left.unitsRestrict (opens_inf_le_of_mem_of_notMem π hz hw)
            (thetaUnit π ^ a))).val
        = ((fst C (overSpec k k)).left.appLE
            ((fiberCover π).opens (((fst C (overSpec k k)).left).base z)
              ⊓ (fiberCover π).opens (((fst C (overSpec k k)).left).base w))
            (((fiberCover π).pullback (fst C (overSpec k k)).left).opens z
              ⊓ ((fiberCover π).pullback (fst C (overSpec k k)).left).opens w)
            ((fst C (overSpec k k)).left.le_preimage_inf inf_le_left inf_le_right)).hom
          (C.left.resHom (opens_inf_le_of_mem_of_notMem π hz hw)
            ((thetaUnit π ^ a : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ)
              : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π))) := rfl
    rw [hRval, appLE_resHom_apply]
  · -- chart 1 to chart 0: the inverse theta power
    rw [fiberDivisor_ratioUnit_notMem_mem π a hz hw]
    refine Units.ext ?_
    rw [gluedSubordUnit_val_of_eq C π a (thetaChartIndex_of_notMem C π hz)
      (thetaChartIndex_of_mem C π hw)
      (inf_le_inf ((thetaChartIndex_of_notMem C π hz) ▸ pullback_fiberCover_le_pieces C π z)
        ((thetaChartIndex_of_mem C π hw) ▸ pullback_fiberCover_le_pieces C π w))]
    have hval : (thetaChartUnit C k π a (Sum.inr PUnit.unit) (Sum.inl PUnit.unit)
          : Γ(relCurve C k, (thetaChartCover C k π).pieces (Sum.inr PUnit.unit)
              ⊓ (thetaChartCover C k π).pieces (Sum.inl PUnit.unit)))
        = (relCurve C k).resHom
            (le_inf (inf_le_right.trans (thetaChartCover_pieces_le_inl C k π PUnit.unit))
              (inf_le_left.trans (thetaChartCover_pieces_le_inr C k π PUnit.unit)))
            (((relThetaCocycle C k π a)⁻¹
                : Γ(relCurve C k, (relCover C k (fiberTwoCover π)).V₀
                    ⊓ (relCover C k (fiberTwoCover π)).V₁)ˣ)
              : Γ(relCurve C k, _)) := rfl
    rw [hval, Scheme.resHom_resHom, relThetaCocycle_inv_val', resHom_appLE_apply]
    have hRval : ((fst C (overSpec k k)).left.unitsAppLE
          ((fiberCover π).opens (((fst C (overSpec k k)).left).base z)
              ⊓ (fiberCover π).opens (((fst C (overSpec k k)).left).base w))
          (((fiberCover π).pullback (fst C (overSpec k k)).left).opens z
              ⊓ ((fiberCover π).pullback (fst C (overSpec k k)).left).opens w)
          ((fst C (overSpec k k)).left.le_preimage_inf inf_le_left inf_le_right)
          (C.left.unitsRestrict (opens_inf_le_of_notMem_of_mem π hz hw)
            (thetaUnit π ^ a)⁻¹)).val
        = ((fst C (overSpec k k)).left.appLE
            ((fiberCover π).opens (((fst C (overSpec k k)).left).base z)
              ⊓ (fiberCover π).opens (((fst C (overSpec k k)).left).base w))
            (((fiberCover π).pullback (fst C (overSpec k k)).left).opens z
              ⊓ ((fiberCover π).pullback (fst C (overSpec k k)).left).opens w)
            ((fst C (overSpec k k)).left.le_preimage_inf inf_le_left inf_le_right)).hom
          (C.left.resHom (opens_inf_le_of_notMem_of_mem π hz hw)
            (((thetaUnit π ^ a)⁻¹ : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ)
              : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π))) := rfl
    rw [hRval, appLE_resHom_apply]
  · -- both chart 1: both units are `1`
    rw [fiberDivisor_ratioUnit_notMem_notMem π a hz hw, map_one]
    refine Units.ext ?_
    rw [gluedSubordUnit_val_of_eq C π a (thetaChartIndex_of_notMem C π hz)
      (thetaChartIndex_of_notMem C π hw)
      (inf_le_inf ((thetaChartIndex_of_notMem C π hz) ▸ pullback_fiberCover_le_pieces C π z)
        ((thetaChartIndex_of_notMem C π hw) ▸ pullback_fiberCover_le_pieces C π w))]
    have hu : thetaChartUnit C k π a (Sum.inr PUnit.unit) (Sum.inr PUnit.unit) = 1 := rfl
    rw [hu, Units.val_one, map_one, Units.val_one]

end ClassLaw

end AlgebraicGeometry
