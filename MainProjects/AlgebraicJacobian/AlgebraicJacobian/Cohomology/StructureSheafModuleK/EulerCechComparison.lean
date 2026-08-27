/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.ModulesFunctor
import AlgebraicJacobian.RiemannRoch.CohomologyKit

/-!
# Comparing the derived and two-chart Euler indices

For a quasicoherent module `M` on a scheme over a field, every two-affine cover
computes the degree-at-most-one derived cohomology of the underlying sheaf of
modules over the field.  This file records the comparison in the dialect used
by the Picard finite-replacement machinery:

* `AffineCoverMVSquare.hModuleZeroEquivH0ₗ` identifies derived `H⁰` with the
  kernel of the two-chart difference map.
* `AffineCoverMVSquare.hModuleOneEquivH1Cokₗ` identifies derived `H¹` with its
  cokernel.
* `AffineCoverMVSquare.chi_toModuleKSheafOfModules_eq` identifies the derived
  truncated Euler characteristic with the signed two-chart index.

The `H¹` comparison uses the existing affine quasicoherent vanishing theorem on
both charts.  No properness, noetherianity, curve hypothesis, or finiteness
hypothesis is required.  Consequently the result compares the two definitions
even in the infinite-dimensional case; it does not assert that their common
`Module.finrank` values are geometrically meaningful there.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Degree-zero derived cohomology of the underlying sheaf of `k`-modules is
the kernel of the difference-of-restrictions map on a two-affine cover.

The first equivalence is the degree-zero Ext/sections comparison at the
terminal open.  The second is sheaf gluing on the two charts. -/
noncomputable def AffineCoverMVSquare.hModuleZeroEquivH0ₗ
    {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    (S : C.left.AffineCoverMVSquare) (M : C.left.Modules) :
    CategoryTheory.Sheaf.HModule (toModuleKSheafOfModules C M) 0 ≃ₗ[k]
      S.H0ₗ C M :=
  (CategoryTheory.Sheaf.HModule.linearEquiv₀
    (Opens.grothendieckTopology C.left.toTopCat)
    (isTerminalTop : IsTerminal (⊤ : C.left.Opens))
    (toModuleKSheafOfModules C M)).trans
      (S.globalSectionsEquivH0ₗ C M)

/-- The sheaf-of-`k`-modules and sheaf-of-`𝒪`-modules spellings of the
two-chart degree-one cokernel agree.  Their section modules, scalar actions,
and difference maps are definitionally the same. -/
noncomputable def AffineCoverMVSquare.h1CokEquivH1Cokₗ
    {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    (S : C.left.AffineCoverMVSquare) (M : C.left.Modules) :
    S.H1Cok (toModuleKSheafOfModules C M) ≃ₗ[k] S.H1Cokₗ C M :=
  LinearEquiv.refl k _

/-- Degree-one derived cohomology of a quasicoherent module is the cokernel of
the difference-of-restrictions map on any two-affine cover.

`CategoryTheory.Sheaf.HModule` uses the lower Ext universe, while the existing
Mayer--Vietoris comparison uses `Scheme.HModule` in the next universe.  The
first factor is precisely the canonical Ext universe-change equivalence. -/
noncomputable def AffineCoverMVSquare.hModuleOneEquivH1Cokₗ
    {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    (S : C.left.AffineCoverMVSquare) (M : C.left.Modules) [M.IsQuasicoherent] :
    CategoryTheory.Sheaf.HModule (toModuleKSheafOfModules C M) 1 ≃ₗ[k]
      S.H1Cokₗ C M :=
  (Abelian.Ext.chgUnivLinearEquiv (R := k)).trans
    ((S.hModuleOneEquivH1CokOfSubsingleton (toModuleKSheafOfModules C M)
      (subsingleton_hModule'_one_of_isAffineOpen_of_isQuasicoherent
        k M S.isAffineOpen_U₁)
      (subsingleton_hModule'_one_of_isAffineOpen_of_isQuasicoherent
        k M S.isAffineOpen_U₂)).trans
      (S.h1CokEquivH1Cokₗ C M))

/-- The derived truncated Euler characteristic of a quasicoherent module is
the signed kernel/cokernel index of its two-chart Cech complex.

This is the first comparison needed toward connecting scheme-theoretic fibre
Euler indices to the finite two-term replacement substrate.  It reaches the
two-chart index only; it neither constructs a finite replacement nor proves
cohomological finiteness. -/
theorem AffineCoverMVSquare.chi_toModuleKSheafOfModules_eq
    {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    (S : C.left.AffineCoverMVSquare) (M : C.left.Modules) [M.IsQuasicoherent] :
    CategoryTheory.Sheaf.chi (toModuleKSheafOfModules C M) = S.chi C M := by
  rw [CategoryTheory.Sheaf.chi, S.chi_def]
  unfold CategoryTheory.Sheaf.h0 CategoryTheory.Sheaf.h1
    AffineCoverMVSquare.h0 AffineCoverMVSquare.h1
  rw [LinearEquiv.finrank_eq (S.hModuleZeroEquivH0ₗ C M),
    LinearEquiv.finrank_eq (S.hModuleOneEquivH1Cokₗ C M)]

end AlgebraicGeometry.Scheme
