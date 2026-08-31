/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepClassifyZar
import AlgebraicJacobian.Picard.DivSchemeAtlasFactor
import AlgebraicJacobian.Picard.DivisorFamilyZarVehicle

/-!
# Conditional assembly kit for affine divisor representability

This file isolates the formal tail between a chart-wise universal certified family and
the affine equivalence of DDR-9.F6.  It deliberately makes the remaining F5 hypotheses
explicit:

* `divRepPullAt` pulls a supplied chart family of Zariski-local classes (`DivFamZar`, not
  globally certified families) along a map out of a carve-chart ring;
* `DivRepChartFamily.IsCompatible` is the exact choice-independence statement needed to
  glue those local pullbacks;
* `DivRepAffinePullback` packages the output of that glue together with the two laws and
  naturality;
* `DivRepAffinePullback.equiv` turns those data into the affine equivalence, using the
  already-landed uniqueness theorem for `divRepClassifyZar` for the hom-side law.

No universal family, compatibility, inverse law, or representability theorem is asserted
here.  The future F5 construction must supply the fields of these interfaces.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Grassmannian Scheme

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftDivRepAffKit :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant pi]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g : ℕ)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
variable (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
variable (r1 r2 : ℕ)
variable (b1 : Module.Basis (Fin r1) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

local notation "DivOver" =>
  divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm)

local notation "ChartRing" => fun i j =>
  DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

local notation "ChartMap" => fun i j =>
  divCarveChartToDivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

/-! ## F5: pullback from one supplied universal chart family -/

/-- Pull a supplied Zariski-locally certified **class** on one carve chart to a test
algebra.  This is the choice-free per-chart operation from which F5's affine forward map
is glued.

The supplied datum is a `DivFamZar` class, not a globally certified family: the forward
map only ever transports a class along `DivFamZar.mapAlgHom`, so a global degree-`g`
certificate over the chart ring is never consumed.  A caller that does hold a
`CertifiedDivisorFamily G` on a chart passes `(DivFam.mk G).toZar`, so no expressive
power is lost, while the Zariski-local production rules (`IsLocallyCertified`) become
usable here. -/
noncomputable def divRepPullAt
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    {S : Type u} [CommRing S] [Algebra k S]
    (i : (glueData k g r1).J) (j : (glueData k g r2).J)
    (omega : ChartRing i j →ₐ[k] S) : DivFamZar C S pi g :=
  DivFamZar.mapAlgHom omega (U i j)

set_option linter.unusedSectionVars false in
@[simp]
theorem divRepPullAt_id
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (i : (glueData k g r1).J) (j : (glueData k g r2).J) :
    divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U i j (AlgHom.id k (ChartRing i j))
      = U i j :=
  DivFamZar.mapAlgHom_id _

set_option linter.unusedSectionVars false in
/-- Pulling a chart class through two algebra maps is the same as pulling it through
their composite.  This is the algebraic part of F5 naturality. -/
theorem divRepPullAt_comp
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    {S T : Type u} [CommRing S] [Algebra k S] [CommRing T] [Algebra k T]
    (i : (glueData k g r1).J) (j : (glueData k g r2).J)
    (omega : ChartRing i j →ₐ[k] S) (phi : S →ₐ[k] T) :
    DivFamZar.mapAlgHom phi (divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U i j omega)
      = divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U i j (phi.comp omega) :=
  (DivFamZar.mapAlgHom_comp omega phi (U i j)).symm

namespace DivRepChartFamily

/-- The precise F5 overlap obligation for a supplied family of classes on every carve
chart: two chart points inducing the same morphism to `DivScheme` have equal pulled
locally certified divisor classes.  The future universal-family construction proves this
from its epsilon identity and the total mono theorem. -/
def IsCompatible
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g) : Prop :=
  ∀ {S : Type u} [CommRing S] [Algebra k S]
    (i : (glueData k g r1).J) (j : (glueData k g r2).J)
    (i' : (glueData k g r1).J) (j' : (glueData k g r2).J)
    (omega : ChartRing i j →ₐ[k] S) (omega' : ChartRing i' j' →ₐ[k] S),
    Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j
        = Spec.map (CommRingCat.ofHom omega'.toRingHom) ≫ ChartMap i' j' →
      divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U i j omega
        = divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U i' j' omega'

set_option linter.unusedSectionVars false in
/-- Compatibility may be applied when both chart presentations are identified with a
common morphism.  This is the form used on overlaps of an atlas factorization. -/
theorem pullAt_eq_of_eq_common
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g)
    (hU : IsCompatible (hpi := hpi) g r1 r2 b1 b2 U)
    {S : Type u} [CommRing S] [Algebra k S]
    (i : (glueData k g r1).J) (j : (glueData k g r2).J)
    (i' : (glueData k g r1).J) (j' : (glueData k g r2).J)
    (omega : ChartRing i j →ₐ[k] S) (omega' : ChartRing i' j' →ₐ[k] S)
    (q : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
        (b2.map (windowShiftEquiv hpi g).symm))
    (homega : Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j = q)
    (homega' : Spec.map (CommRingCat.ofHom omega'.toRingHom) ≫ ChartMap i' j' = q) :
    divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U i j omega
      = divRepPullAt (hpi := hpi) g r1 r2 b1 b2 U i' j' omega' :=
  hU i j i' j' omega omega' (homega.trans homega'.symm)

end DivRepChartFamily

/-! ## F6: package a completed affine pullback as an equivalence -/

/-- The exact output expected from F5 before the affine equivalence is packaged.
`isDivRepClassify_pull` is the hom-side law in the refinement-stable clause spelling;
classifier uniqueness turns it into the second inverse law automatically. -/
structure DivRepAffinePullback where
  pull : ∀ (S : Type u) [CommRing S] [Algebra k S],
    (overSpec k S ⟶ DivOver) → DivFamZar C S pi g
  pull_classify : ∀ (S : Type u) [CommRing S] [Algebra k S]
    (F : DivFamZar C S pi g),
    pull S (divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 S F) = F
  isDivRepClassify_pull : ∀ (S : Type u) [CommRing S] [Algebra k S]
    (v : overSpec k S ⟶ DivOver),
    IsDivRepClassify hpi g r1 r2 b1 b2 (pull S v) v.left
  pull_naturality : ∀ {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (phi : A →ₐ[k] B) (v : overSpec k A ⟶ DivOver),
    pull B (Over.overSpecMap phi ≫ v) = DivFamZar.mapAlgHom phi (pull A v)

namespace DivRepAffinePullback

/-- The affine representability equivalence assembled from an F5 pullback package.
The inverse is the landed backward classifier; its hom-side inverse law follows from
`divRepClassifyZar_eq_of_isDivRepClassify`. -/
noncomputable def equiv
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    (S : Type u) [CommRing S] [Algebra k S] :
    (overSpec k S ⟶ DivOver) ≃ DivFamZar C S pi g where
  toFun := D.pull S
  invFun := divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 S
  left_inv v :=
    (divRepClassifyZar_eq_of_isDivRepClassify hpi g hO hchi r1 r2 b1 b2
      (D.pull S v) v (D.isDivRepClassify_pull S v)).symm
  right_inv := D.pull_classify S

@[simp]
theorem equiv_apply
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    equiv (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) D S v = D.pull S v :=
  rfl

@[simp]
theorem equiv_symm_apply
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    (S : Type u) [CommRing S] [Algebra k S] (F : DivFamZar C S pi g) :
    (equiv (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) D S).symm F
      = divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 S F :=
  rfl

/-- Naturality of the assembled affine equivalence, in the frozen DDR-9 spelling. -/
theorem equiv_naturality
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (phi : A →ₐ[k] B)
    (v : overSpec k A ⟶ DivOver) :
    equiv (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) D B (Over.overSpecMap phi ≫ v)
      = DivFamZar.mapAlgHom phi
          (equiv (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
            (b1 := b1) (b2 := b2) D A v) :=
  D.pull_naturality phi v

end DivRepAffinePullback

end Curve

end AlgebraicGeometry
