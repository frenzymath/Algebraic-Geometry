/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepClassifyZarAffNaturality
import AlgebraicJacobian.Picard.DivRepClassifyZarAffSep
import AlgebraicJacobian.Picard.DivisorFamilyAffMap

/-!
# The widened affine-to-global divisor representability endpoint

The widened classifier already supplies the inverse, its naturality, and both uniqueness
directions.  Thus the forward affine construction needs only three pieces of data: a pullback
of a `DivScheme` point, the classifier clause for that pullback, and naturality in the test
algebra.  `DivRepAffinePullbackAff` records exactly those data.

The rest of the file lifts this affine package through the affine-open vehicle
`divFamZarAff`, exactly as the chart-typed DDR-9 endpoint does.  In particular, no pinned
curve chart, comparison from `DivFamZar`, or extra representability hypothesis occurs.

## Main declarations

* `AlgebraicGeometry.DivRepAffinePullbackAff` -- the three-field widened affine package.
* `AlgebraicGeometry.DivRepAffinePullbackAff.toGlobalEquiv` -- its equivalence on any test.
* `AlgebraicGeometry.DivRepAffinePullbackAff.representableBy` -- the widened endpoint
  `(divFunctorAff C g).RepresentableBy DivOver`.
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

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftDivRepGlobalClassifyAff :
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

/-! ## The widened affine package -/

/-- The exact widened affine data needed by the representability endpoint.

The classifier inverse laws are omitted: `eq_of_isDivRepClassifyAff` and
`divRepClassifyZarAff_eq_of_isDivRepClassifyAff` derive them from
`isDivRepClassify_pull`. -/
structure DivRepAffinePullbackAff where
  pull : ∀ (S : Type u) [CommRing S] [Algebra k S],
    (overSpec k S ⟶ DivOver) → DivFamZarAff C S g
  isDivRepClassify_pull : ∀ (S : Type u) [CommRing S] [Algebra k S]
    (v : overSpec k S ⟶ DivOver),
    IsDivRepClassifyAff hpi g r1 r2 b1 b2 (pull S v) v.left
  pull_naturality : ∀ {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (phi : A →ₐ[k] B) (v : overSpec k A ⟶ DivOver),
    pull B (Over.overSpecMap phi ≫ v) = DivFamZarAff.mapAlgHom phi (pull A v)

namespace DivRepAffinePullbackAff

include hO hchi in
/-- A chosen preimage under the widened affine classifier. -/
noncomputable def pullOfClassifierSurjective
    (hsurj : ∀ (S : Type u) [CommRing S] [Algebra k S],
      Function.Surjective
        (divRepClassifyZarAff (C := C) (pi := pi) hpi g hO hchi r1 r2 b1 b2 S))
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    DivFamZarAff C S g :=
  (hsurj S v).choose

include hO hchi in
/-- The chosen preimage classifies to the original point. -/
theorem classify_pullOfClassifierSurjective
    (hsurj : ∀ (S : Type u) [CommRing S] [Algebra k S],
      Function.Surjective
        (divRepClassifyZarAff (C := C) (pi := pi) hpi g hO hchi r1 r2 b1 b2 S))
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 S
        (pullOfClassifierSurjective hpi g hO hchi r1 r2 b1 b2 hsurj S v)
      = v :=
  (hsurj S v).choose_spec

include hO hchi in
/-- Build the widened affine package from surjectivity of the canonical classifier.

The chosen preimage is automatically natural: after applying the injective classifier, the
claim is exactly `overSpecMap_comp_divRepClassifyZarAff`. -/
noncomputable def ofClassifierSurjective
    (hsurj : ∀ (S : Type u) [CommRing S] [Algebra k S],
      Function.Surjective
        (divRepClassifyZarAff (C := C) (pi := pi) hpi g hO hchi r1 r2 b1 b2 S)) :
    DivRepAffinePullbackAff hpi g r1 r2 b1 b2 where
  pull S _ _ v :=
    pullOfClassifierSurjective hpi g hO hchi r1 r2 b1 b2 hsurj S v
  isDivRepClassify_pull S _ _ v := by
    have hv := congrArg CategoryTheory.Over.Hom.left
      (classify_pullOfClassifierSurjective hpi g hO hchi r1 r2 b1 b2 hsurj S v)
    rw [← hv]
    exact divRepClassifyZarAff_isDivRepClassifyAff hpi g hO hchi r1 r2 b1 b2
      (pullOfClassifierSurjective hpi g hO hchi r1 r2 b1 b2 hsurj S v)
  pull_naturality {A B} _ _ _ _ phi v := by
    apply divRepClassifyZarAff_injective (C := C) (π := pi) (S := B)
      hpi g hO hchi r1 r2 b1 b2
    calc
      divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 B
          (pullOfClassifierSurjective hpi g hO hchi r1 r2 b1 b2 hsurj B
            (Over.overSpecMap phi ≫ v))
        = Over.overSpecMap phi ≫ v :=
          classify_pullOfClassifierSurjective hpi g hO hchi r1 r2 b1 b2 hsurj B _
      _ = Over.overSpecMap phi ≫
          divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 A
            (pullOfClassifierSurjective hpi g hO hchi r1 r2 b1 b2 hsurj A v) := by
        rw [classify_pullOfClassifierSurjective hpi g hO hchi r1 r2 b1 b2 hsurj A v]
      _ = divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 B
          (DivFamZarAff.mapAlgHom phi
            (pullOfClassifierSurjective hpi g hO hchi r1 r2 b1 b2 hsurj A v)) :=
        overSpecMap_comp_divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 phi _

include hO hchi in
/-- Pulling the canonical classifier recovers the widened class. -/
theorem pull_classify
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    (S : Type u) [CommRing S] [Algebra k S] (F : DivFamZarAff C S g) :
    D.pull S (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 S F) = F := by
  exact eq_of_isDivRepClassifyAff hpi g hO hchi r1 r2 b1 b2 _ _
    (D.isDivRepClassify_pull S _)
    (divRepClassifyZarAff_isDivRepClassifyAff hpi g hO hchi r1 r2 b1 b2 F)

include hO hchi in
/-- Classifying a pulled `DivScheme` point recovers that point. -/
theorem classify_pull
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 S (D.pull S v) = v := by
  exact (divRepClassifyZarAff_eq_of_isDivRepClassifyAff hpi g hO hchi r1 r2 b1 b2
    (D.pull S v) v (D.isDivRepClassify_pull S v)).symm

include hO hchi in
/-- The affine equivalence supplied by a widened affine package. -/
noncomputable def equiv
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    (S : Type u) [CommRing S] [Algebra k S] :
    (overSpec k S ⟶ DivOver) ≃ DivFamZarAff C S g where
  toFun := D.pull S
  invFun := divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 S
  left_inv := classify_pull hpi g hO hchi r1 r2 b1 b2 D S
  right_inv := pull_classify hpi g hO hchi r1 r2 b1 b2 D S

/-! ## The widened general-test pullback -/

/-- The general-test pullback obtained by evaluating the affine pull on every affine open. -/
noncomputable def pullGlobal
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ DivOver) : divFamZarAff C g T :=
  ⟨fun W => D.pull Γ(T.left, W.1) (Over.fromSpecAffine T W ≫ v), by
    intro U V h
    beta_reduce
    rw [← D.pull_naturality (Over.resAlgHom T h) (Over.fromSpecAffine T V ≫ v),
      ← Category.assoc, Over.fromSpecAffine_resAlgHom h]⟩

set_option linter.unusedSectionVars false in
@[simp]
theorem pullGlobal_val
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ DivOver)
    (W : T.left.affineOpens) :
    (pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) D v).1 W
      = D.pull Γ(T.left, W.1) (Over.fromSpecAffine T W ≫ v) :=
  rfl

/-- The widened general-test pullback is natural in the test object. -/
theorem pullGlobal_comp
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    {T T' : Over (Spec (CommRingCat.of k))} (f : T' ⟶ T) (v : T ⟶ DivOver) :
    pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) D (f ≫ v)
      = divFamZarAff.map C g f
          (pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
            (b1 := b1) (b2 := b2) D v) := by
  refine divFamZarAff.ext fun W => ?_
  rw [divFamZarAff.map_val]
  refine (divFamZarAff.mapVal_eq_of C g f _ ?_).symm
  intro W0 hW0 V hV
  rw [pullGlobal_val, pullGlobal_val,
    ← D.pull_naturality (Over.resAlgHom T' hW0) (Over.fromSpecAffine T' W ≫ f ≫ v),
    ← D.pull_naturality (Over.appLEAlgHom f V.1 W0.1 hV) (Over.fromSpecAffine T V ≫ v),
    ← Category.assoc (Over.overSpecMap (Over.resAlgHom T' hW0)),
    Over.fromSpecAffine_resAlgHom hW0,
    ← Category.assoc (Over.overSpecMap (Over.appLEAlgHom f V.1 W0.1 hV)),
    Over.fromSpecAffine_naturality f V W0 hV, Category.assoc]

/-! ## The widened general-test classifier -/

private theorem isoSpec_hom_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
  rw [← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc]

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

private noncomputable def classifyPiece
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T)
    (U : T.left.affineOpens) : U.1.toScheme ⟶ (DivOver).left :=
  U.2.isoSpec.hom ≫
    (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 Γ(T.left, U.1) (F.1 U)).left

set_option maxHeartbeats 1600000 in
-- The restriction map and both affine classifiers expose two section-ring algebra towers.
private theorem homOfLE_classifyPiece
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T)
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
        ≫ (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 Γ(T.left, V.1) (F.1 V)).left
      = (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 Γ(T.left, U.1) (F.1 U)).left := by
    rw [← CategoryTheory.Over.comp_left,
      overSpecMap_comp_divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2,
      F.compat U V hle]
  rw [classifyPiece, classifyPiece, ← Category.assoc, ← hkey, Category.assoc, hcl]

private theorem classifyPiece_over
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T)
    (U : T.left.affineOpens) :
    classifyPiece hpi g hO hchi r1 r2 b1 b2 F U ≫ (DivOver).hom = U.1.ι ≫ T.hom := by
  rw [classifyPiece, Category.assoc, CategoryTheory.Over.w,
    ← CategoryTheory.Over.w (Over.fromSpecAffine T U), ← Category.assoc]
  exact congrArg (· ≫ T.hom) (isoSpec_hom_fromSpec U.2)

private theorem classifyPiece_trans
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T)
    {U V : T.left.directedAffineCover.I₀} (hUV : U ⟶ V) :
    Scheme.Cover.trans T.left.directedAffineCover hUV
        ≫ classifyPiece hpi g hO hchi r1 r2 b1 b2 F V
      = classifyPiece hpi g hO hchi r1 r2 b1 b2 F U := by
  rw [Subsingleton.elim hUV (homOfLE (leOfHom hUV)),
    Scheme.directedAffineCover_trans (leOfHom hUV)]
  exact homOfLE_classifyPiece hpi g hO hchi r1 r2 b1 b2 F (leOfHom hUV)

/-- The general-test classifier obtained by gluing the widened affine classifiers. -/
noncomputable def classifyGlobal
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T) : T ⟶ DivOver :=
  Scheme.OpenCover.glueMorphismsOverOfLocallyDirected (X := T) (Y := DivOver)
    T.left.directedAffineCover (classifyPiece hpi g hO hchi r1 r2 b1 b2 F)
    (fun {_U _V} hUV => classifyPiece_trans hpi g hO hchi r1 r2 b1 b2 F hUV)
    (classifyPiece_over hpi g hO hchi r1 r2 b1 b2 F)

private theorem iota_classifyGlobal
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T)
    (W : T.left.affineOpens) :
    W.1.ι ≫ (classifyGlobal hpi g hO hchi r1 r2 b1 b2 F).left
      = classifyPiece hpi g hO hchi r1 r2 b1 b2 F W :=
  Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left
    (X := T) (Y := DivOver) T.left.directedAffineCover
    (classifyPiece hpi g hO hchi r1 r2 b1 b2 F)
    (fun {_U _V} hUV => classifyPiece_trans hpi g hO hchi r1 r2 b1 b2 F hUV)
    (classifyPiece_over hpi g hO hchi r1 r2 b1 b2 F) W

/-- The global classifier restricts to the affine classifier on every affine open. -/
theorem fromSpecAffine_classifyGlobal
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T)
    (W : T.left.affineOpens) :
    Over.fromSpecAffine T W ≫ classifyGlobal hpi g hO hchi r1 r2 b1 b2 F
      = divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 Γ(T.left, W.1) (F.1 W) := by
  refine Over.OverMorphism.ext ?_
  change W.2.fromSpec ≫ _ = _
  rw [← IsAffineOpen.isoSpec_inv_ι, Category.assoc,
    iota_classifyGlobal hpi g hO hchi r1 r2 b1 b2 F W,
    classifyPiece, Iso.inv_hom_id_assoc]

include hO hchi in
/-- The general-test pull and classifier are inverse on widened sections. -/
theorem pullGlobal_classifyGlobal
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T) :
    pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) D
        (classifyGlobal hpi g hO hchi r1 r2 b1 b2 F)
      = F := by
  refine divFamZarAff.ext fun W => ?_
  rw [pullGlobal_val, fromSpecAffine_classifyGlobal,
    pull_classify hpi g hO hchi r1 r2 b1 b2]

include hO hchi in
/-- The general-test classifier and pull are inverse on `DivScheme` points. -/
theorem classifyGlobal_pullGlobal
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ DivOver) :
    classifyGlobal hpi g hO hchi r1 r2 b1 b2
        (pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
          (b1 := b1) (b2 := b2) D v)
      = v := by
  refine hom_ext_fromSpecAffine _ _ fun W => ?_
  rw [fromSpecAffine_classifyGlobal, pullGlobal_val,
    classify_pull hpi g hO hchi r1 r2 b1 b2]

include hO hchi in
/-- The equivalence on an arbitrary test object underlying widened representability. -/
noncomputable def toGlobalEquiv
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ DivOver) ≃ divFamZarAff C g T where
  toFun := pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
    (b1 := b1) (b2 := b2) D
  invFun := classifyGlobal hpi g hO hchi r1 r2 b1 b2
  left_inv := classifyGlobal_pullGlobal hpi g hO hchi r1 r2 b1 b2 D
  right_inv := pullGlobal_classifyGlobal hpi g hO hchi r1 r2 b1 b2 D

include hO hchi in
/-- A widened affine pullback package represents `divFunctorAff C g` by `DivScheme`. -/
noncomputable def representableBy
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2) :
    (divFunctorAff C g).RepresentableBy DivOver where
  homEquiv {T} := toGlobalEquiv hpi g hO hchi r1 r2 b1 b2 D T
  homEquiv_comp {T T'} f v := by
    change pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) D (f ≫ v)
      = divFamZarAff.map C g f
          (pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
            (b1 := b1) (b2 := b2) D v)
    exact pullGlobal_comp hpi g r1 r2 b1 b2 D f v

/-! ## Off-diagonal classifier packaging -/

/-- A chosen preimage under the classifier at an independent curve parameter. -/
noncomputable def pullOfClassifierSurjective_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hsurj : ∀ (S : Type u) [CommRing S] [Algebra k S],
      Function.Surjective
        (divRepClassifyZarAff_at (C := C) (pi := pi) (S := S)
          (gamma := gamma) hpi g r1 r2 b1 b2 hgamma hchiGamma))
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    DivFamZarAff C S g :=
  (hsurj S v).choose

/-- The off-diagonal chosen preimage classifies to the original point. -/
theorem classify_pullOfClassifierSurjective_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hsurj : ∀ (S : Type u) [CommRing S] [Algebra k S],
      Function.Surjective
        (divRepClassifyZarAff_at (C := C) (pi := pi) (S := S)
          (gamma := gamma) hpi g r1 r2 b1 b2 hgamma hchiGamma))
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    divRepClassifyZarAff_at (S := S) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma
        (pullOfClassifierSurjective_at
          (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
          (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) hsurj S v) = v :=
  (hsurj S v).choose_spec

/-- Build the affine pullback package from off-diagonal classifier surjectivity. -/
noncomputable def ofClassifierSurjective_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hsurj : ∀ (S : Type u) [CommRing S] [Algebra k S],
      Function.Surjective
        (divRepClassifyZarAff_at (C := C) (pi := pi) (S := S)
          (gamma := gamma) hpi g r1 r2 b1 b2 hgamma hchiGamma)) :
    DivRepAffinePullbackAff hpi g r1 r2 b1 b2 where
  pull S _ _ v :=
    pullOfClassifierSurjective_at
      (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
      (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) hsurj S v
  isDivRepClassify_pull S _ _ v := by
    have hv := congrArg CategoryTheory.Over.Hom.left
      (classify_pullOfClassifierSurjective_at
        (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
        (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) hsurj S v)
    rw [← hv]
    exact divRepClassifyZarAff_isDivRepClassifyAff_at (gamma := gamma)
      hpi g r1 r2 b1 b2 hgamma hchiGamma
      (pullOfClassifierSurjective_at
        (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
        (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) hsurj S v)
  pull_naturality {A B} _ _ _ _ phi v := by
    apply divRepClassifyZarAff_injective_at
      (C := C) (π := pi) (S := B) (hπ := hpi) (g := g)
      (r₁ := r1) (r₂ := r2) (b₁ := b1) (b₂ := b2)
      (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma) (hχgamma := hchiGamma)
    calc
      divRepClassifyZarAff_at (S := B) (gamma := gamma)
          hpi g r1 r2 b1 b2 hgamma hchiGamma
          (pullOfClassifierSurjective_at
            (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
            (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma)
            hsurj B (Over.overSpecMap phi ≫ v))
        = Over.overSpecMap phi ≫ v :=
          classify_pullOfClassifierSurjective_at
            (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
            (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) hsurj B _
      _ = Over.overSpecMap phi ≫
          divRepClassifyZarAff_at (S := A) (gamma := gamma)
            hpi g r1 r2 b1 b2 hgamma hchiGamma
            (pullOfClassifierSurjective_at
              (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
              (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma)
              hsurj A v) := by
        rw [classify_pullOfClassifierSurjective_at
          (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
          (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) hsurj A v]
      _ = divRepClassifyZarAff_at (S := B) (gamma := gamma)
          hpi g r1 r2 b1 b2 hgamma hchiGamma
          (DivFamZarAff.mapAlgHom phi
            (pullOfClassifierSurjective_at
              (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
              (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma)
              hsurj A v)) :=
        overSpecMap_comp_divRepClassifyZarAff_at (gamma := gamma)
          hpi g r1 r2 b1 b2 hgamma hchiGamma phi _

/-- Pulling the off-diagonal canonical classifier recovers the widened class. -/
theorem pull_classify_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    (S : Type u) [CommRing S] [Algebra k S] (F : DivFamZarAff C S g) :
    D.pull S (divRepClassifyZarAff_at (S := S) (gamma := gamma)
      hpi g r1 r2 b1 b2 hgamma hchiGamma F) = F := by
  exact eq_of_isDivRepClassifyAff_at
    (hπ := hpi) (g := g) (r₁ := r1) (r₂ := r2) (b₁ := b1) (b₂ := b2)
    (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma) (hχgamma := hchiGamma)
    _ _ (D.isDivRepClassify_pull S _)
    (divRepClassifyZarAff_isDivRepClassifyAff_at (gamma := gamma)
      hpi g r1 r2 b1 b2 hgamma hchiGamma F)

/-- Classifying a pulled point with the off-diagonal classifier recovers that point. -/
theorem classify_pull_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    divRepClassifyZarAff_at (S := S) (gamma := gamma)
      hpi g r1 r2 b1 b2 hgamma hchiGamma (D.pull S v) = v := by
  exact (divRepClassifyZarAff_eq_of_isDivRepClassifyAff_at (gamma := gamma)
    hpi g r1 r2 b1 b2 hgamma hchiGamma
    (D.pull S v) v (D.isDivRepClassify_pull S v)).symm

private noncomputable def classifyPiece_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T)
    (U : T.left.affineOpens) : U.1.toScheme ⟶ (DivOver).left :=
  U.2.isoSpec.hom ≫
    (divRepClassifyZarAff_at (S := Γ(T.left, U.1)) (gamma := gamma)
      hpi g r1 r2 b1 b2 hgamma hchiGamma (F.1 U)).left

set_option maxHeartbeats 1600000 in
-- Restriction exposes the two off-diagonal affine classifiers and their algebra towers.
private theorem homOfLE_classifyPiece_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T)
    {U V : T.left.affineOpens} (hle : U.1 ≤ V.1) :
    T.left.homOfLE hle ≫
        classifyPiece_at (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
          (b1 := b1) (b2 := b2) (gamma := gamma)
          (hgamma := hgamma) (hchiGamma := hchiGamma) F V
      = classifyPiece_at (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
          (b1 := b1) (b2 := b2) (gamma := gamma)
          (hgamma := hgamma) (hchiGamma := hchiGamma) F U := by
  have hres : (Over.overSpecMap (Over.resAlgHom T hle)).left ≫ V.2.fromSpec
      = U.2.fromSpec :=
    congrArg CategoryTheory.Over.Hom.left (Over.fromSpecAffine_resAlgHom (T := T) hle)
  have hkey : U.2.isoSpec.hom ≫ (Over.overSpecMap (Over.resAlgHom T hle)).left
      = T.left.homOfLE hle ≫ V.2.isoSpec.hom := by
    rw [← cancel_mono V.2.fromSpec, Category.assoc, Category.assoc, hres,
      isoSpec_hom_fromSpec, isoSpec_hom_fromSpec, Scheme.homOfLE_ι]
  have hcl : (Over.overSpecMap (Over.resAlgHom T hle)).left ≫
        (divRepClassifyZarAff_at (S := Γ(T.left, V.1)) (gamma := gamma)
          hpi g r1 r2 b1 b2 hgamma hchiGamma (F.1 V)).left =
      (divRepClassifyZarAff_at (S := Γ(T.left, U.1)) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma (F.1 U)).left := by
    rw [← CategoryTheory.Over.comp_left,
      overSpecMap_comp_divRepClassifyZarAff_at (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma,
      F.compat U V hle]
  rw [classifyPiece_at, classifyPiece_at, ← Category.assoc, ← hkey, Category.assoc, hcl]

private theorem classifyPiece_over_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T)
    (U : T.left.affineOpens) :
    classifyPiece_at (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) (gamma := gamma)
        (hgamma := hgamma) (hchiGamma := hchiGamma) F U ≫ (DivOver).hom =
      U.1.ι ≫ T.hom := by
  rw [classifyPiece_at, Category.assoc, CategoryTheory.Over.w,
    ← CategoryTheory.Over.w (Over.fromSpecAffine T U), ← Category.assoc]
  exact congrArg (· ≫ T.hom) (isoSpec_hom_fromSpec U.2)

private theorem classifyPiece_trans_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T)
    {U V : T.left.directedAffineCover.I₀} (hUV : U ⟶ V) :
    Scheme.Cover.trans T.left.directedAffineCover hUV ≫
        classifyPiece_at (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
          (b1 := b1) (b2 := b2) (gamma := gamma)
          (hgamma := hgamma) (hchiGamma := hchiGamma) F V
      = classifyPiece_at (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
          (b1 := b1) (b2 := b2) (gamma := gamma)
          (hgamma := hgamma) (hchiGamma := hchiGamma) F U := by
  rw [Subsingleton.elim hUV (homOfLE (leOfHom hUV)),
    Scheme.directedAffineCover_trans (leOfHom hUV)]
  exact homOfLE_classifyPiece_at
    (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
    (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) F (leOfHom hUV)

/-- The global classifier obtained from the off-diagonal affine classifiers. -/
noncomputable def classifyGlobal_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T) : T ⟶ DivOver :=
  Scheme.OpenCover.glueMorphismsOverOfLocallyDirected (X := T) (Y := DivOver)
    T.left.directedAffineCover
    (classifyPiece_at (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) (gamma := gamma)
      (hgamma := hgamma) (hchiGamma := hchiGamma) F)
    (fun {_U _V} hUV =>
      classifyPiece_trans_at
        (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
        (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) F hUV)
    (classifyPiece_over_at
      (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
      (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) F)

private theorem iota_classifyGlobal_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T)
    (W : T.left.affineOpens) :
    W.1.ι ≫ (classifyGlobal_at
        (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
        (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) F).left =
      classifyPiece_at (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) (gamma := gamma)
        (hgamma := hgamma) (hchiGamma := hchiGamma) F W :=
  Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left
    (X := T) (Y := DivOver) T.left.directedAffineCover
    (classifyPiece_at (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) (gamma := gamma)
      (hgamma := hgamma) (hchiGamma := hchiGamma) F)
    (fun {_U _V} hUV =>
      classifyPiece_trans_at
        (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
        (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) F hUV)
    (classifyPiece_over_at
      (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
      (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) F) W

/-- The off-diagonal global classifier restricts to its affine classifier. -/
theorem fromSpecAffine_classifyGlobal_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T)
    (W : T.left.affineOpens) :
    Over.fromSpecAffine T W ≫
        classifyGlobal_at
          (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
          (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) F =
      divRepClassifyZarAff_at (S := Γ(T.left, W.1)) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma (F.1 W) := by
  refine Over.OverMorphism.ext ?_
  change W.2.fromSpec ≫ _ = _
  rw [← IsAffineOpen.isoSpec_inv_ι, Category.assoc,
    iota_classifyGlobal_at
      (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
      (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) F W,
    classifyPiece_at, Iso.inv_hom_id_assoc]

/-- The global pull and off-diagonal classifier are inverse on widened sections. -/
theorem pullGlobal_classifyGlobal_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (F : divFamZarAff C g T) :
    pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) D
        (classifyGlobal_at
          (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
          (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) F) = F := by
  refine divFamZarAff.ext fun W => ?_
  rw [pullGlobal_val, fromSpecAffine_classifyGlobal_at,
    pull_classify_at
      (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
      (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma)
      (hchiGamma := hchiGamma)]

/-- The off-diagonal global classifier and pull are inverse on `DivScheme` points. -/
theorem classifyGlobal_pullGlobal_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ DivOver) :
    classifyGlobal_at
        (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
        (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma)
        (pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
          (b1 := b1) (b2 := b2) D v) = v := by
  refine hom_ext_fromSpecAffine _ _ fun W => ?_
  rw [fromSpecAffine_classifyGlobal_at, pullGlobal_val,
    classify_pull_at
      (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
      (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma)]

/-- The off-diagonal equivalence on an arbitrary test object. -/
noncomputable def toGlobalEquiv_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2)
    (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ DivOver) ≃ divFamZarAff C g T where
  toFun := pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
    (b1 := b1) (b2 := b2) D
  invFun := classifyGlobal_at
    (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
    (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma)
  left_inv := classifyGlobal_pullGlobal_at
    (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
    (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) D
  right_inv := pullGlobal_classifyGlobal_at
    (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
    (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma)
    (hchiGamma := hchiGamma) D

/-- An affine pullback package represents the degree-`g` divisor functor when the curve
parameter is any `gamma ≤ g`. -/
noncomputable def representableBy_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (D : DivRepAffinePullbackAff hpi g r1 r2 b1 b2) :
    (divFunctorAff C g).RepresentableBy DivOver where
  homEquiv {T} :=
    toGlobalEquiv_at
      (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
      (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma)
      (hchiGamma := hchiGamma) D T
  homEquiv_comp {T T'} f v := by
    change pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) D (f ≫ v) =
      divFamZarAff.map C g f
        (pullGlobal (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
          (b1 := b1) (b2 := b2) D v)
    exact pullGlobal_comp hpi g r1 r2 b1 b2 D f v

end DivRepAffinePullbackAff

end Curve

end AlgebraicGeometry
