/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.EulerCechComparison
import AlgebraicJacobian.Picard.HilbertPolynomial
import AlgebraicJacobian.Picard.LineBundlePullback

/-!
# Fibrewise truncated Euler indices for line bundles

For a morphism `f : X ⟶ S`, a point `s : S`, and a sheaf of modules `M` on
`X`, this file defines the degree-at-most-one Euler index of the restricted
module `M_s` over the residue field `kappa(s)`.  For a line bundle `L` on a
relative product, it also defines the signed difference

`chi(L_t) - chi(O_{(C x_S T)_t})`.

The definitions deliberately use the name *index*, not geometric degree.
`CategoryTheory.Sheaf.chi` is totalized: without finite-dimensional `H0` and
`H1`, `Module.finrank` can read an infinite-dimensional space as zero.  The
line-bundle difference becomes the usual fibre degree only after the relevant
cohomological finiteness and Riemann--Roch comparison are supplied.

This file proves invariance under isomorphism of the underlying modules by
using `Scheme.toModuleKSheafOfModulesFunctor` and the existing
`CategoryTheory.Sheaf.chi_congr`.  It does not yet descend the difference
through the relative Picard or etale equivalence relation, prove pullback
naturality in the test scheme, or prove local constancy on that test scheme.

## Main declarations

* `Scheme.Hom.fiberEulerIndex`: the totalized truncated Euler index of a module
  on a scheme-theoretic fibre.
* `Scheme.Hom.fiberEulerIndex_eq_cech`: computation of that index by any
  two-affine cover of a quasicoherent fibre module.
* `Scheme.LineBundle.OnProduct.fiberEulerIndexDifference`: the signed
  line-bundle index relative to the literal structure sheaf of the fibre.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- The totalized degree-at-most-one Euler index of the restriction of `M` to
the scheme-theoretic fibre of `f` at `s`, computed over `s`'s residue field.

No properness, dimension, or cohomological finiteness hypothesis is imposed,
so this is not asserted to be the genuine Euler characteristic. -/
noncomputable def Hom.fiberEulerIndex (f : X ⟶ S) (s : S)
    (M : X.Modules) : ℤ :=
  CategoryTheory.Sheaf.chi
    (toModuleKSheafOfModules
      (Over.mk (f.fiberToSpecResidueField s))
      (f.fiberModule s M))

/-- A two-affine cover of the fibre computes `fiberEulerIndex` for a
quasicoherent module.  This is an equality with the concrete signed
kernel/quotient-by-range index; it does not assert finite-dimensionality. -/
theorem Hom.fiberEulerIndex_eq_cech (f : X ⟶ S) (s : S)
    (M : X.Modules) [M.IsQuasicoherent]
    (V : (f.fiber s).AffineCoverMVSquare) :
    f.fiberEulerIndex s M =
      V.chi (Over.mk (f.fiberToSpecResidueField s)) (f.fiberModule s M) := by
  haveI : (f.fiberModule s M).IsQuasicoherent := f.fiberModule_isQuasicoherent s M
  unfold Hom.fiberEulerIndex
  exact @AffineCoverMVSquare.chi_toModuleKSheafOfModules_eq _ _
    (Over.mk (f.fiberToSpecResidueField s)) V (f.fiberModule s M) this

/-- `fiberEulerIndex` is invariant under an isomorphism of modules on the
total space.  The isomorphism is pulled back to the fibre, restricted to the
residue field, and passed to `Sheaf.chi_congr`. -/
theorem Hom.fiberEulerIndex_congr (f : X ⟶ S) (s : S)
    {M N : X.Modules} (e : M ≅ N) :
    f.fiberEulerIndex s M = f.fiberEulerIndex s N :=
  chi_toModuleKSheafOfModules_congr
    (Over.mk (f.fiberToSpecResidueField s))
    ((Modules.pullback (f.fiberι s)).mapIso e)

namespace LineBundle.OnProduct

/-- The signed, normalized fibre index of a line bundle on `C x_k T`:
`chi(L_t) - chi(O_{(C x_k T)_t})`.

The second term uses the literal unit module on the fibre, rather than a
definitionally different pullback of the unit module on the total space.  This
is the cohomological expression that Riemann--Roch identifies with degree once
finiteness and the curve comparison are available.  At this stage it is only
a totalized truncated index and has not descended to the relative Picard
functor. -/
noncomputable def fiberEulerIndexDifference {k : Type u} [Field k]
    {C T : Scheme.{u}} (piC : C ⟶ Spec (CommRingCat.of k))
    (piT : T ⟶ Spec (CommRingCat.of k))
    (L : LineBundle.OnProduct piC piT) (t : T) : ℤ :=
  let q := pullback.snd piC piT
  q.fiberEulerIndex t L.carrier -
    CategoryTheory.Sheaf.chi
      (toModuleKSheafOfModules
        (Over.mk (q.fiberToSpecResidueField t))
        (SheafOfModules.unit (q.fiber t).ringCatSheaf))

/-- The normalized fibre index is invariant under an isomorphism of the
underlying line-bundle modules.  This is the iso-invariance needed before a
later descent to line-bundle isomorphism classes; it does not prove invariance
under tensoring by a bundle pulled back from `T`. -/
theorem fiberEulerIndexDifference_congr {k : Type u} [Field k]
    {C T : Scheme.{u}} (piC : C ⟶ Spec (CommRingCat.of k))
    (piT : T ⟶ Spec (CommRingCat.of k))
    {L L' : LineBundle.OnProduct piC piT}
    (e : L.carrier ≅ L'.carrier) (t : T) :
    fiberEulerIndexDifference piC piT L t =
      fiberEulerIndexDifference piC piT L' t := by
  dsimp [fiberEulerIndexDifference]
  rw [Hom.fiberEulerIndex_congr _ _ e]

end LineBundle.OnProduct

end AlgebraicGeometry.Scheme
