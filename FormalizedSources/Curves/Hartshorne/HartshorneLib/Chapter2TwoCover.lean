/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# The canonical two-open Mayer--Vietoris square

For two opens of a scheme whose union is the whole space, this file records the
canonical Mayer--Vietoris square and transports the generic objectwise `H¹'`
calculation to cohomology of the small Zariski site.  Vanishing on the two
pieces is intentionally exposed as `Subsingleton` hypotheses; the geometric
affine-vanishing theorem belongs to a later chapter.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open CategoryTheory.GrothendieckTopology

section Square

variable (X : Scheme.{u}) (U₀ U₁ : X.Opens)

/-! The square `(U₀ ⊓ U₁, U₀, U₁, ⊤)` associated with a two-open cover. -/
noncomputable def Scheme.twoCoverSquare (hcov : U₀ ⊔ U₁ = ⊤) :
    (Opens.grothendieckTopology (X : TopCat)).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := U₀ ⊓ U₁
      X₂ := U₀
      X₃ := U₁
      X₄ := ⊤
      f₁₂ := homOfLE inf_le_left
      f₁₃ := homOfLE inf_le_right
      f₂₄ := homOfLE le_top
      f₃₄ := homOfLE le_top
      fac := Subsingleton.elim _ _ } hcov.symm rfl

end Square

section HOne

variable (R : Type u) [CommRing R] (X : Scheme.{u})
variable (U₀ U₁ : X.Opens)

/-!
The general-coefficient two-cover calculation.  The two local degree-one
cohomology groups are supplied as subsingleton instances, so this statement is
usable for any sheaf of `R`-modules and does not claim affine vanishing.
-/
noncomputable def Scheme.twoCoverH1LinearEquiv
    (F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} R))
    (hcov : U₀ ⊔ U₁ = ⊤)
    [Subsingleton (Sheaf.HModule' F U₀ 1)]
    [Subsingleton (Sheaf.HModule' F U₁ 1)] :
    Sheaf.HModule (Opens.grothendieckTopology (X : TopCat)) R F 1 ≃ₗ[R]
      (F.obj.obj (op (U₀ ⊓ U₁)) ⧸
        LinearMap.range ((X.twoCoverSquare U₀ U₁ hcov).moduleDiff F)) :=
  letI : Subsingleton
      (Sheaf.HModule' F (X.twoCoverSquare U₀ U₁ hcov).X₂ 1) :=
    inferInstanceAs (Subsingleton (Sheaf.HModule' F U₀ 1))
  letI : Subsingleton
      (Sheaf.HModule' F (X.twoCoverSquare U₀ U₁ hcov).X₃ 1) :=
    inferInstanceAs (Subsingleton (Sheaf.HModule' F U₁ 1))
  (Sheaf.HModule.linearEquivHModule'
      (isTerminalTop : IsTerminal (⊤ : X.Opens)) F 1).trans
    ((X.twoCoverSquare U₀ U₁ hcov).h1LinearEquiv F).symm

/-- The canonical two-cover `H¹` equivalence under explicit section-surjectivity
hypotheses for the two injective cokernel maps. -/
noncomputable def Scheme.twoCoverH1LinearEquiv_of_cokernel_app_surjective
    (F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} R))
    (hcov : U₀ ⊔ U₁ = ⊤)
    (hsurj₀ : Function.Surjective
      ((cokernel.π (Injective.ι F)).hom.app (op U₀)).hom)
    (hsurj₁ : Function.Surjective
      ((cokernel.π (Injective.ι F)).hom.app (op U₁)).hom) :
    Sheaf.HModule (Opens.grothendieckTopology (X : TopCat)) R F 1 ≃ₗ[R]
      (F.obj.obj (op (U₀ ⊓ U₁)) ⧸
        LinearMap.range ((X.twoCoverSquare U₀ U₁ hcov).moduleDiff F)) := by
  letI : Subsingleton (Sheaf.HModule' F U₀ 1) :=
    Sheaf.HModule'.subsingleton_one_of_cokernel_app_surjective F U₀ hsurj₀
  letI : Subsingleton (Sheaf.HModule' F U₁ 1) :=
    Sheaf.HModule'.subsingleton_one_of_cokernel_app_surjective F U₁ hsurj₁
  exact Scheme.twoCoverH1LinearEquiv R X U₀ U₁ F hcov

end HOne

end AlgebraicGeometry
