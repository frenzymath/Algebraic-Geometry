/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepGlobalLift
import AlgebraicJacobian.Picard.DivisorFamilyAffFunctorCompare

/-!
# A DD-R CONSUMER ON THE WIDENED FUNCTOR (R2): `pullGlobal` read at `divFunctorAff`

The widened carrier of protection I-0492 acquired a base-change face (ADDENDUM 8), a Zariski
gluing keystone (§8.6), and finally a functor `divFunctorAff` with a natural transformation
`divFunctorToAff` out of the chart-typed one (ADDENDUM 9).  What it did **not** have, at every
one of those milestones, is a **consumer**: measured at HEAD, the widened names appeared in zero
files outside the `Picard/DivisorFamilyAff*.lean` family.

That is the gap this file closes.  It restates the DD-R general-test pullback
(`DivRepAffinePullback.pullGlobal`, `Picard/DivRepGlobalLift.lean`) on the widened functor and
proves the `pull_comp` law there — the one field of `DivRepGlobalData` that is *about* the
functor rather than about a single test.

## What the restatement costs, and why that is the point

Nothing but a push-forward.  `pullGlobalAff` is `divFamZarToAffVehicle ∘ pullGlobal`, and its
naturality is the chart-typed `pullGlobal_comp` transported along `divFamZarToAffVehicle_map`.
No gluing is redone and no certificate is re-derived over a widened cover.

That cheapness is the substantive claim: it says the widened layer is *usable* by the existing
DD-R stack, not merely well-formed.  A functor nothing consumes and a functor everything can
consume look identical to a sorry census and to a job count.

## Direction, once more

Old → new.  A consumer that already produces a chart-typed section gets its widened counterpart
for free.  The converse does not exist and cannot: by `informal/spec-dd-r.md` ADDENDUM 3 §2 /
ADDENDUM 4 §4.3 a straddling divisor at genus `≥ 2` is confined by no fixed pair of `P¹` charts.
So this file does **not** claim the widened functor is representable by `DivOver`; it claims the
chart-typed representability datum pushes forward to a compatible family of widened values.

## Main declarations

* `AlgebraicGeometry.DivRepAffinePullback.pullGlobalAff` — the widened general-test pullback.
* `…pullGlobalAff_val` — its value at an affine open, `toAff` of the chart-typed one.
* `…pullGlobalAff_comp` — the `pull_comp` law at `divFamZarAff.map`.
* `…divFamZarAffAffineEquiv_pullGlobalAff` — affine consistency, through the widened collapse.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Grassmannian Scheme

attribute [local instance] Over.sectionsAlgebra

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftDivRepGlobalAffLift :
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

/-! ## The widened general-test pullback -/

-- No `[IsAffineHom pi]` binder here: the file-level `[IsFinite pi]` already implies it, and
-- carrying both made every declaration below report an overlapping-instance warning.

/-- **The widened general-test pullback**: the chart-typed `pullGlobal` pushed forward along the
vehicle comparison of R2.  Its value at an affine open is the widened value of the chart-typed
one, so a consumer that already has the affine package gets the widened section with no extra
input. -/
noncomputable def pullGlobalAff
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ DivOver) : divFamZarAff C g T :=
  divFamZarToAffVehicle C g pi
    (pullGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) D v)

set_option linter.unusedSectionVars false in
/-- The value of the widened general-test pullback at an affine open. -/
@[simp]
theorem pullGlobalAff_val
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T : Over (Spec (CommRingCat.of k))} (v : T ⟶ DivOver)
    (W : T.left.affineOpens) :
    (pullGlobalAff (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) D v).1 W
      = (D.pull Γ(T.left, W.1) (Over.fromSpecAffine T W ≫ v)).toAff :=
  rfl

/-! ## Naturality in the test object, at the WIDENED functor -/

set_option linter.unusedSectionVars false in
/-- **The `pull_comp` law on the widened functor**: the widened general-test pullback is natural
in the test object, with the *widened* glued restriction `divFamZarAff.map`.

This is the field of `DivRepGlobalData` that is about the functor rather than about one test, and
it is the statement that makes the widened layer consumable.  The proof is the chart-typed
`pullGlobal_comp` transported along the naturality of the vehicle comparison
(`divFamZarToAffVehicle_map`) — no gluing is redone. -/
theorem pullGlobalAff_comp
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    {T T' : Over (Spec (CommRingCat.of k))} (f : T' ⟶ T) (v : T ⟶ DivOver) :
    pullGlobalAff (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
        (b1 := b1) (b2 := b2) D (f ≫ v)
      = divFamZarAff.map C g f
          (pullGlobalAff (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1)
            (r2 := r2) (b1 := b1) (b2 := b2) D v) := by
  show divFamZarToAffVehicle C g pi _ = _
  rw [pullGlobal_comp (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) D f v,
    divFamZarToAffVehicle_map f]
  -- Both sides are now `divFamZarAff.map C g f` applied to the same term, but the right-hand one
  -- still wears the folded name `pullGlobalAff`.  That unfolding is definitional and `rw`'s
  -- terminal `rfl` runs at reducible transparency only, so it must be discharged explicitly.
  rfl

set_option linter.unusedSectionVars false in
/-- **Affine consistency of the widened pullback**: on an affine test it collapses through the
widened comparison `divFamZarAffAffineEquiv` to the widened value of the affine pullback. -/
theorem divFamZarAffAffineEquiv_pullGlobalAff
    (D : DivRepAffinePullback hpi g hO hchi r1 r2 b1 b2)
    (A : Type u) [CommRing A] [Algebra k A] (v : overSpec k A ⟶ DivOver) :
    divFamZarAffAffineEquiv C g A
        (pullGlobalAff (hpi := hpi) (g := g) (hO := hO) (hchi := hchi) (r1 := r1) (r2 := r2)
          (b1 := b1) (b2 := b2) D v)
      = (D.pull A v).toAff := by
  rw [pullGlobalAff, divFamZarAffAffineEquiv_toAffVehicle,
    divFamZarAffineEquiv_pullGlobal (hpi := hpi) (g := g) (hO := hO) (hchi := hchi)
      (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) D A v]

end DivRepAffinePullback

end Curve

end AlgebraicGeometry
