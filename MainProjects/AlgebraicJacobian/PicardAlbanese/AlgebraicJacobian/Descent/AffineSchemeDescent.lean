/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.AlgebraDescent
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Effective descent for affine schemes

This file applies `Spec` to the equalizer algebra constructed by
`Algebra.DescentDatum`.  It packages affine algebra effectivity as an
isomorphism in the category of schemes over the faithfully flat chart.

## Main declarations

* `Algebra.DescentDatum.baseScheme`: the spectrum of the descended algebra.
* `Algebra.DescentDatum.schemeBaseChangeIso`: its underlying scheme-level
  base-change isomorphism.
* `Algebra.DescentDatum.baseChangeIso`: the same isomorphism in the relevant
  over-category.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct
open AlgebraicGeometry

namespace Algebra.DescentDatum

variable {A B R : Type u} [CommRing A] [CommRing B] [CommRing R]
  [Algebra A B] [Algebra A R] [Algebra B R] [IsScalarTower A B R]

/-- The affine scheme over `Spec A` obtained from the equalizer algebra of a
commutative-algebra descent datum. -/
noncomputable def baseScheme (D : Algebra.DescentDatum A B R) :
    Over (Spec (CommRingCat.of A)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A D.descended)))

/-- The original affine `B`-scheme encoded by a commutative-algebra descent
datum. -/
noncomputable def affineScheme (_D : Algebra.DescentDatum A B R) :
    Over (Spec (CommRingCat.of B)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap B R)))

/-- The affine base map along which the descent datum is given. -/
noncomputable def coverMap (_D : Algebra.DescentDatum A B R) :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The spectrum of the descended algebra becomes the original affine scheme
after base change to `B`. -/
noncomputable def schemeBaseChangeIso (D : Algebra.DescentDatum A B R)
    [Module.Flat A B] :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A D.descended)))
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≅
      Spec (CommRingCat.of R) :=
  (pullbackSymmetry _ _).trans
    ((pullbackSpecIso A B D.descended).trans
      (asIso (Spec.map D.descentEquiv.symm.toRingEquiv.toCommRingCatIso.hom)))

/-- The affine base-change isomorphism commutes with the structure maps to
`Spec B`. -/
@[reassoc]
theorem schemeBaseChangeIso_hom_structureMap
    (D : Algebra.DescentDatum A B R) [Module.Flat A B] :
    D.schemeBaseChangeIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap B R)) =
      pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap A D.descended)))
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  rw [schemeBaseChangeIso, Iso.trans_hom, Iso.trans_hom, Category.assoc,
    Category.assoc, asIso_hom, ← Spec.map_comp]
  have hring :
      CommRingCat.ofHom (algebraMap B R) ≫
          D.descentEquiv.symm.toRingEquiv.toCommRingCatIso.hom =
        CommRingCat.ofHom (algebraMap B (B ⊗[A] D.descended)) := by
    ext b
    exact D.descentEquiv.symm.commutes b
  rw [hring, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]

/-- Effective affine-scheme descent, bundled in the over-category: pulling the
descended scheme back along `Spec B ⟶ Spec A` recovers the original affine
`B`-scheme. -/
noncomputable def baseChangeIso (D : Algebra.DescentDatum A B R)
    [Module.Flat A B] :
    (Over.pullback D.coverMap).obj D.baseScheme ≅ D.affineScheme :=
  Over.isoMk D.schemeBaseChangeIso D.schemeBaseChangeIso_hom_structureMap

end Algebra.DescentDatum
