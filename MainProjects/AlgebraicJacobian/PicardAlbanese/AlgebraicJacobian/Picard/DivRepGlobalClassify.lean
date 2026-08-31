/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepGlobalLift

/-!
# DDR-9.F7 — the affine-to-general lift, completed

`Picard/DivRepGlobalLift.lean` builds the general-test pullback `pullGlobal` of an
affine divisor package `DivRepAffinePullback` together with its naturality in the
test object.  This file supplies the other half — the general-test classifier — and
assembles the `DivRepGlobalData` of `Picard/DivRepKit.lean`, hence the divisor
representability of `divFunctor C π g` by `DivScheme`.

The classifier is obtained by gluing the landed affine classifiers `divRepClassifyZar`
over the affine opens of the test.  Two observations make the gluing cheap:

* The affine opens of a scheme form a **locally directed** open cover
  (`Scheme.directedAffineCover`), so a morphism glues from compatibility with the
  transition maps alone (`Scheme.OpenCover.glueMorphismsOverOfLocallyDirected`); no
  condition on the — in general non-affine — overlaps is needed.
* The required compatibility is naturality of `divRepClassifyZar` in the test algebra.
  That naturality is not proved from the characterizing clause: it is *forced* by the
  affine package, since `D.pull` is injective (`DivRepAffinePullback.equiv`) and natural
  (`D.pull_naturality`), so the classifier — its inverse — is natural as well.

The results:

* `AlgebraicGeometry.DivRepAffinePullback.classifyGlobal` — the general-test classifier,
  restricting at every affine open `W ⊆ T.left` to the affine classifier of the value
  `F.1 W` (`fromSpecAffine_classifyGlobal`).
* `AlgebraicGeometry.DivRepAffinePullback.toGlobalData` — the `DivRepGlobalData` of the
  affine package: `pullGlobal` and `classifyGlobal` are mutually inverse on every test.
* `AlgebraicGeometry.DivRepAffinePullback.representableBy` — **the divisor
  representability theorem in its conditional form**: an affine divisor package
  represents `divFunctor C π g` by `DivScheme`.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Grassmannian Scheme

attribute [local instance] Over.sectionsAlgebra

/-! ## Separation over the affine opens of a test object -/

section Separation

variable {k : Type u} [Field k]

/-- The comparison isomorphism of an affine open with the spectrum of its section ring
carries `IsAffineOpen.fromSpec` to the open immersion of the open. -/
private theorem isoSpec_hom_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
  rw [← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc]

/-- **Separation of test objects over their affine-open test objects**: two morphisms
out of a test object `T` agreeing on every affine-open test object `Over.fromSpecAffine T U`
are equal.  The affine opens cover `T.left`, and `fromSpecAffine T U` differs from the
open immersion of `U` by the comparison isomorphism of `U`. -/
private theorem hom_ext_fromSpecAffine {T Y : Over (Spec (CommRingCat.of k))} (a b : T ⟶ Y)
    (h : ∀ U : T.left.affineOpens,
      Over.fromSpecAffine T U ≫ a = Over.fromSpecAffine T U ≫ b) :
    a = b := by
  refine Over.OverMorphism.ext ?_
  refine Scheme.Cover.hom_ext T.left.directedAffineCover _ _ fun U => ?_
  have hU : U.2.fromSpec ≫ a.left = U.2.fromSpec ≫ b.left :=
    congrArg CategoryTheory.Over.Hom.left (h U)
  change U.1.ι ≫ a.left = U.1.ι ≫ b.left
  rw [← isoSpec_hom_fromSpec U.2, Category.assoc, Category.assoc, hU]

end Separation

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftDivRepGlobalClassify :
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

namespace DivRepAffinePullback

/-! ## Naturality of the affine classifier -/

/-- **The affine backward classifier is natural in the test algebra.**  This is not
proved from the characterizing clause: it is forced by the affine package, whose forward
map `D.pull` is injective and natural, so its inverse is natural too — concretely, the
base change of a classifier classifies the base-changed class, by
`D.isDivRepClassify_pull` at the base-changed morphism. -/
private theorem overSpecMap_comp_divRepClassifyZar
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (phi : A →ₐ[k] B) (F : DivFamZar C A pi g) :
    Over.overSpecMap phi ≫ divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 A F
      = divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 B (DivFamZar.mapAlgHom phi F) := by
  have hpull : D.pull B
      (Over.overSpecMap phi ≫ divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 A F)
      = DivFamZar.mapAlgHom phi F := by
    rw [D.pull_naturality phi (divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 A F),
      D.pull_classify A F]
  refine divRepClassifyZar_eq_of_isDivRepClassify hpi g hO hchi r1 r2 b1 b2 _ _ ?_
  rw [← hpull]
  exact D.isDivRepClassify_pull B _

/-! ## The general-test classifier -/

/-- The affine classifiers of the values of `F`, transported to the open subschemes of
the affine opens of `T.left` — the family glued by `classifyGlobal`. -/
private noncomputable def classifyPiece
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZar C pi g T)
    (U : T.left.affineOpens) : U.1.toScheme ⟶ (DivOver).left :=
  U.2.isoSpec.hom ≫
    (divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 Γ(T.left, U.1) (F.1 U)).left

set_option maxHeartbeats 1600000 in
-- The rewrite chain unifies through the section-ring algebra towers over both affine
-- opens at once, so it exceeds the default elaboration budget (as in
-- `divFamZar.exists_isGlueValue`).
/-- The gluing datum: the family `classifyPiece` is compatible with the transition maps
of the directed cover of `T.left` by its affine opens.  This is naturality of the affine
classifier along the section restriction, applied to the coherence of `F`. -/
private theorem homOfLE_classifyPiece
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZar C pi g T)
    {U V : T.left.affineOpens} (hle : U.1 ≤ V.1) :
    T.left.homOfLE hle ≫ classifyPiece hpi g hO hchi r1 r2 b1 b2 F V
      = classifyPiece hpi g hO hchi r1 r2 b1 b2 F U := by
  have hres : (Over.overSpecMap (Over.resAlgHom T hle)).left ≫ V.2.fromSpec
      = U.2.fromSpec :=
    congrArg CategoryTheory.Over.Hom.left (Over.fromSpecAffine_resAlgHom (T := T) hle)
  have hkey : U.2.isoSpec.hom ≫ (Over.overSpecMap (Over.resAlgHom T hle)).left
      = T.left.homOfLE hle ≫ V.2.isoSpec.hom := by
    rw [← cancel_mono V.2.fromSpec, Category.assoc, Category.assoc, hres,
      isoSpec_hom_fromSpec, isoSpec_hom_fromSpec, Scheme.homOfLE_ι]
  have hcl : (Over.overSpecMap (Over.resAlgHom T hle)).left
        ≫ (divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 Γ(T.left, V.1) (F.1 V)).left
      = (divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 Γ(T.left, U.1) (F.1 U)).left := by
    rw [← CategoryTheory.Over.comp_left,
      overSpecMap_comp_divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 D, F.compat U V hle]
  rw [classifyPiece, classifyPiece, ← Category.assoc, ← hkey, Category.assoc, hcl]

/-- The gluing datum: each piece lies over `Spec k` compatibly with the test `T`. -/
private theorem classifyPiece_over
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZar C pi g T)
    (U : T.left.affineOpens) :
    classifyPiece hpi g hO hchi r1 r2 b1 b2 F U ≫ (DivOver).hom = U.1.ι ≫ T.hom := by
  rw [classifyPiece, Category.assoc, CategoryTheory.Over.w,
    ← CategoryTheory.Over.w (Over.fromSpecAffine T U), ← Category.assoc]
  exact congrArg (· ≫ T.hom) (isoSpec_hom_fromSpec U.2)

private theorem classifyPiece_trans
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZar C pi g T)
    {U V : T.left.directedAffineCover.I₀} (hij : U ⟶ V) :
    Scheme.Cover.trans T.left.directedAffineCover hij
        ≫ classifyPiece hpi g hO hchi r1 r2 b1 b2 F V
      = classifyPiece hpi g hO hchi r1 r2 b1 b2 F U := by
  rw [Subsingleton.elim hij (homOfLE (leOfHom hij)),
    Scheme.directedAffineCover_trans (leOfHom hij)]
  exact homOfLE_classifyPiece hpi g hO hchi r1 r2 b1 b2 D F (leOfHom hij)

/-- **The general-test classifier of the affine package**: the affine classifiers of the
values of `F` at the affine opens of `T.left`, glued over the locally directed cover of
`T.left` by its affine opens.  The gluing datum is the compatibility with the transition
maps `T.left.homOfLE`, which is naturality of `divRepClassifyZar`
(`overSpecMap_comp_divRepClassifyZar`) applied to the coherence of `F`. -/
noncomputable def classifyGlobal
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZar C pi g T) : T ⟶ DivOver :=
  Scheme.OpenCover.glueMorphismsOverOfLocallyDirected (X := T) (Y := DivOver)
    T.left.directedAffineCover (classifyPiece hpi g hO hchi r1 r2 b1 b2 F)
    (fun {_U _V} hij => classifyPiece_trans hpi g hO hchi r1 r2 b1 b2 D F hij)
    (classifyPiece_over hpi g hO hchi r1 r2 b1 b2 F)

set_option linter.unusedSectionVars false in
/-- The general-test classifier restricts on the open subscheme of an affine open to the
transported affine classifier there. -/
private theorem ι_classifyGlobal
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZar C pi g T)
    (W : T.left.affineOpens) :
    W.1.ι ≫ (classifyGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) D F).left
      = classifyPiece hpi g hO hchi r1 r2 b1 b2 F W :=
  Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left
    (X := T) (Y := DivOver) T.left.directedAffineCover
    (classifyPiece hpi g hO hchi r1 r2 b1 b2 F)
    (fun {_U _V} hij => classifyPiece_trans hpi g hO hchi r1 r2 b1 b2 D F hij)
    (classifyPiece_over hpi g hO hchi r1 r2 b1 b2 F) W

set_option linter.unusedSectionVars false in
/-- **The characterizing property of the general-test classifier**: its restriction to
the affine-open test object presented by `W` is the affine classifier of the value of `F`
at `W`. -/
theorem fromSpecAffine_classifyGlobal
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZar C pi g T)
    (W : T.left.affineOpens) :
    Over.fromSpecAffine T W ≫ classifyGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) D F
      = divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 Γ(T.left, W.1) (F.1 W) := by
  refine Over.OverMorphism.ext ?_
  change W.2.fromSpec ≫ _ = _
  rw [← IsAffineOpen.isoSpec_inv_ι, Category.assoc,
    ι_classifyGlobal hpi g hO hchi r1 r2 b1 b2 D F W, classifyPiece,
    Iso.inv_hom_id_assoc]

/-! ## The two inverse laws -/

set_option linter.unusedSectionVars false in
/-- **The `pull_classify` law at an arbitrary test**: the general-test pullback of the
general-test classifier of `F` is `F`.  Both sides are sections of the Zariski vehicle,
so it suffices to compare at an affine open, where the characterizing property of the
classifier reduces the statement to the affine law `D.pull_classify`. -/
theorem pullGlobal_classifyGlobal
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZar C pi g T) :
    pullGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) D
        (classifyGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1)
          (r2 := r2) (b1 := b1) (b2 := b2) D F)
      = F := by
  refine divFamZar.ext fun W => ?_
  rw [pullGlobal_val, fromSpecAffine_classifyGlobal, D.pull_classify]

set_option linter.unusedSectionVars false in
/-- **The `classify_pull` law at an arbitrary test**: the general-test classifier of the
general-test pullback of `v` is `v`.  Morphisms out of a test are separated by the
affine-open test objects, and at each of those the uniqueness theorem
`divRepClassifyZar_eq_of_isDivRepClassify`, applied to `D.isDivRepClassify_pull`,
identifies the affine classifier with the restriction of `v`. -/
theorem classifyGlobal_pullGlobal
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ DivOver) :
    classifyGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) D
        (pullGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
          (b1 := b1) (b2 := b2) D v)
      = v := by
  refine hom_ext_fromSpecAffine _ _ fun W => ?_
  rw [fromSpecAffine_classifyGlobal, pullGlobal_val]
  exact (divRepClassifyZar_eq_of_isDivRepClassify hpi g hO hchi r1 r2 b1 b2 _ _
    (D.isDivRepClassify_pull _ (Over.fromSpecAffine T W ≫ v))).symm

/-! ## The affine-to-general lift -/

/-- **The affine-to-general lift of DDR-9.F7**: an affine divisor package determines the
general-test data of `DivRepGlobalData` — the pullback is `pullGlobal`, the classifier is
`classifyGlobal`, the two inverse laws are `classifyGlobal_pullGlobal` and
`pullGlobal_classifyGlobal`, and naturality in the test object is `pullGlobal_comp`. -/
noncomputable def toGlobalData
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2) :
    DivRepGlobalData hpi g r1 r2 b1 b2 where
  pull {_T} v := pullGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1)
    (r2 := r2) (b1 := b1) (b2 := b2) D v
  classify {_T} F := classifyGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi)
    (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) D F
  classify_pull {_T} v := classifyGlobal_pullGlobal (hpi := hpi) (g := g) (hO := hO)
    (hchi := hchi) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) D v
  pull_classify {_T} F := pullGlobal_classifyGlobal (hpi := hpi) (g := g) (hO := hO)
    (hchi := hchi) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) D F
  pull_comp {_T _T'} f v := pullGlobal_comp (hpi := hpi) (g := g) (hO := hO) (hchi := hchi)
    (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) D f v

/-- **Divisor representability from an affine package** (DDR-9.F7): an affine divisor
package represents the locally certified divisor functor `divFunctor C π g` by
`DivScheme`.  This is the composite of the affine-to-general lift with the categorical
packaging `DivRepGlobalData.representableBy`. -/
noncomputable def representableBy
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2) :
    (divFunctor C pi g).RepresentableBy DivOver :=
  DivRepGlobalData.representableBy (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1)
    (b2 := b2)
    (toGlobalData (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) D)

end DivRepAffinePullback

end Curve

end AlgebraicGeometry
