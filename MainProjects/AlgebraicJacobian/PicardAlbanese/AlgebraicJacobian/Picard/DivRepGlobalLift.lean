/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepKit
import AlgebraicJacobian.Picard.PicEtUnit

/-!
# DDR-9.F7 — the affine-to-general lift

`Picard/DivRepKit.lean` packages a `DivRepGlobalData` (general-test pullback,
classification, the two inverse laws, naturality) as the divisor representability
datum `(divFunctor C π g).RepresentableBy DivOver`.  It deliberately does **not**
construct one.  This file constructs the general-test pullback of such a datum from
the affine package `DivRepAffinePullback` (`Picard/DivRepAffKit.lean`) — the first
half of the lift.

The mechanism is the affine-open test objects `Over.fromSpecAffine T W`
(`Picard/PicEtUnit.lean`): every affine open `W ⊆ T.left` presents the affine test
`overSpec k Γ(T.left, W)` over `T`, coherently under restriction
(`Over.fromSpecAffine_resAlgHom`) and along arbitrary test morphisms
(`Over.fromSpecAffine_naturality`).  Since the vehicle `divFamZar C π g T` is by
definition the family of its values on affine opens, the affine forward maps assemble
with **no gluing at all**:

* `AlgebraicGeometry.DivRepAffinePullback.pullGlobal` — the general-test pullback,
  with value `D.pull Γ(T.left, W) (Over.fromSpecAffine T W ≫ v)` at every affine open
  (`pullGlobal_val`).  Compatibility under restriction is `D.pull_naturality` plus the
  restriction coherence of `fromSpecAffine`.
* `AlgebraicGeometry.DivRepAffinePullback.pullGlobal_comp` — the `divFamZar.map`
  naturality of `pullGlobal` in the test object, i.e. the `pull_comp` field of
  `DivRepGlobalData`: the characterizing `∃!`-property `divFamZar.IsPullbackValue` of
  the glued restriction is verified from `D.pull_naturality` and
  `Over.fromSpecAffine_naturality`.
* `AlgebraicGeometry.DivRepAffinePullback.divFamZarAffineEquiv_pullGlobal` — affine
  consistency: on an affine test the general-test pullback collapses through the
  affine comparison to `D.pull` itself.

The remaining half of DDR-9.F7 — the general-test classifier, obtained by gluing the
affine classifiers `divRepClassifyZar` over an affine open cover — is not in this
file; see the module docstring of `Picard/DivRepKit.lean`.
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

noncomputable local instance instOverCleftDivRepGlobalLift :
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

/-! ## The general-test pullback -/

/-- **The general-test pullback of the affine package**: the value at an affine open
`W ⊆ T.left` is the affine pullback of the restriction of `v` to the affine test
`overSpec k Γ(T.left, W)` presented by `W`.  Compatibility under restriction of
affine opens is exactly `D.pull_naturality` along `Over.resAlgHom`, transported by the
restriction coherence `Over.fromSpecAffine_resAlgHom`. -/
noncomputable def pullGlobal
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ DivOver) : divFamZar C pi g T :=
  ⟨fun W => D.pull Γ(T.left, W.1) (Over.fromSpecAffine T W ≫ v), by
    intro U V h
    beta_reduce
    rw [← D.pull_naturality (Over.resAlgHom T h) (Over.fromSpecAffine T V ≫ v),
      ← Category.assoc, Over.fromSpecAffine_resAlgHom h]⟩

set_option linter.unusedSectionVars false in
/-- The characterizing property of `pullGlobal`: its value at an affine open is the
affine pullback along the affine-open test object. -/
@[simp]
theorem pullGlobal_val
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ DivOver)
    (W : T.left.affineOpens) :
    (pullGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) D v).1 W
      = D.pull Γ(T.left, W.1) (Over.fromSpecAffine T W ≫ v) :=
  rfl

/-! ## Naturality in the test object -/

set_option linter.unusedSectionVars false in
/-- **The `pull_comp` field of `DivRepGlobalData` for `pullGlobal`**: the general-test
pullback is natural in the test object.  The value of the glued restriction
`divFamZar.map` is characterized by `divFamZar.IsPullbackValue`, and that property of
`pullGlobal (f ≫ v)` is `D.pull_naturality` along `Over.appLEAlgHom f` combined with
the naturality of the affine-open test objects `Over.fromSpecAffine_naturality`. -/
theorem pullGlobal_comp
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T T' : Over (Spec (CommRingCat.of k))} (f : T' ⟶ T) (v : T ⟶ DivOver) :
    pullGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) D (f ≫ v)
      = divFamZar.map C pi g f
          (pullGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1)
            (r2 := r2) (b1 := b1) (b2 := b2) D v) := by
  refine divFamZar.ext fun W => ?_
  rw [divFamZar.map_val]
  refine (divFamZar.mapVal_eq_of C pi g f _ ?_).symm
  intro W₀ hW₀ V hV
  rw [pullGlobal_val, pullGlobal_val,
    ← D.pull_naturality (Over.resAlgHom T' hW₀) (Over.fromSpecAffine T' W ≫ f ≫ v),
    ← D.pull_naturality (Over.appLEAlgHom f V.1 W₀.1 hV) (Over.fromSpecAffine T V ≫ v),
    ← Category.assoc (Over.overSpecMap (Over.resAlgHom T' hW₀)),
    Over.fromSpecAffine_resAlgHom hW₀,
    ← Category.assoc (Over.overSpecMap (Over.appLEAlgHom f V.1 W₀.1 hV)),
    Over.fromSpecAffine_naturality f V W₀ hV, Category.assoc]

set_option linter.unusedSectionVars false in
/-- **Affine consistency**: on an affine test the general-test pullback collapses
through the affine comparison `divFamZarAffineEquiv` to the affine pullback `D.pull`
of the package. -/
theorem divFamZarAffineEquiv_pullGlobal
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    (A : Type u) [CommRing A] [Algebra k A] (v : overSpec k A ⟶ DivOver) :
    divFamZarAffineEquiv C pi g A
        (pullGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1)
          (r2 := r2) (b1 := b1) (b2 := b2) D v)
      = D.pull A v := by
  have h := D.pull_naturality (Over.overSpecΓTopAlgEquiv k A).toAlgHom
    (Over.fromSpecAffine (overSpec k A) (overSpecTopAffine A) ≫ v)
  rw [← Category.assoc, Over.overSpecMap_ΓTop_fromSpecAffine_top A, Category.id_comp] at h
  rw [divFamZarAffineEquiv_apply]
  exact h.symm

end DivRepAffinePullback

end Curve

end AlgebraicGeometry
