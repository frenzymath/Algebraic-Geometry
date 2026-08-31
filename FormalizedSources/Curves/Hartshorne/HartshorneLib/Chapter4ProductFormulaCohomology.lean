/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorDevissageExact
import HartshorneLib.Chapter4DivisorDegreeStep
import HartshorneLib.Chapter4DegreeClass
import HartshorneLib.Chapter4DivisorSheafMul
import HartshorneLib.Chapter4SkyscraperCohomology
import HartshorneLib.Chapter2ChiSlice

/-!
# A cohomological route to the curve product formula

The one-point divisor dévissage and the skyscraper `H¹` vanishing imply that
the truncated Euler characteristic changes by one when a closed point is
removed.  This file keeps the finiteness of the divisor-sheaf cohomology as an
explicit hypothesis and derives the principal-divisor degree-zero statement
from that hypothesis.  No geometric finiteness theorem is hidden in an
instance or an axiom.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
attribute [local instance] Scheme.overModule

/-! ## The one-point Euler-characteristic increment -/

theorem chi_skyModule_jump_eq_one {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    CategoryTheory.Sheaf.chi
        (skyModule (X := X) x (jumpModule hx D)) = 1 := by
  letI : SmoothOfRelativeDimension 1
      (X.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  letI : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  rw [CategoryTheory.Sheaf.chi_eq_h0
    (skyModule_subsingleton_hModule_one (X := X) x (jumpModule hx D))]
  rw [h0_skyModule, finrank_jumpModule]
  rw [AlgebraicGeometry.Scheme.residueDeg_eq_one_of_isAlgClosed
    (K := k) (X := X.left) hx]
  norm_num

/-! ## The explicit finiteness input -/

/-- Global sections of an integral scheme proper over `Spec k` are finite over `k`.

The properness theorem gives finiteness over the global sections of `Spec k`.
The displayed compatibility calculation transports that result across
`Scheme.ΓSpecIso`, using the scalar map already built into `moduleKSheaf`.
-/
theorem moduleFinite_globalSections_of_isProper
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    [IsIntegral X.left] [IsProper X.hom] :
    Module.Finite k
      (X.left.presheaf.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens X.left.toTopCat))) := by
  letI : Algebra k
      (X.left.presheaf.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens X.left.toTopCat))) :=
    (X.left.overAlgebraMap k (⊤ : X.left.Opens)).toAlgebra
  have hf : (X.hom.appTop.hom).Finite :=
    AlgebraicGeometry.finite_appTop_of_universallyClosed k X.hom
  letI alg2 : Algebra
      ((Spec (CommRingCat.of k)).presheaf.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens
          (Spec (CommRingCat.of k)).toTopCat)))
      (X.left.presheaf.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens X.left.toTopCat))) :=
    RingHom.toAlgebra X.hom.appTop.hom
  have hM_inter :
      Module.Finite
        ((Spec (CommRingCat.of k)).presheaf.obj
          (Opposite.op (⊤ : TopologicalSpace.Opens
            (Spec (CommRingCat.of k)).toTopCat)))
        (X.left.presheaf.obj
          (Opposite.op (⊤ : TopologicalSpace.Opens X.left.toTopCat))) := by
    rw [← RingHom.finite_algebraMap]
    exact hf
  letI : Module.Finite
      ((Spec (CommRingCat.of k)).presheaf.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens
          (Spec (CommRingCat.of k)).toTopCat)))
      (X.left.presheaf.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens X.left.toTopCat))) := hM_inter
  refine Module.Finite.of_equiv_equiv
    (A₁ := (Spec (CommRingCat.of k)).presheaf.obj
      (Opposite.op (⊤ : TopologicalSpace.Opens
        (Spec (CommRingCat.of k)).toTopCat)))
    (B₁ := X.left.presheaf.obj
      (Opposite.op (⊤ : TopologicalSpace.Opens X.left.toTopCat)))
    (A₂ := k)
    (B₂ := X.left.presheaf.obj
      (Opposite.op (⊤ : TopologicalSpace.Opens X.left.toTopCat)))
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
    (RingEquiv.refl
      (X.left.presheaf.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens X.left.toTopCat)))) ?_
  ext x
  simp only [RingHom.coe_comp, RingEquiv.coe_toRingHom, RingEquiv.refl_apply,
    Function.comp_apply, RingHom.algebraMap_toAlgebra]
  have h_kts :
      (X.left.overAlgebraMap k (⊤ : X.left.Opens)) =
        (X.hom.appTop.hom).comp
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := by
    ext y
    simp only [Scheme.overAlgebraMap, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply]
    exact congrFun (congrArg (fun f => f.hom)
      (X.left.presheaf.map_id (Opposite.op (⊤ :
        TopologicalSpace.Opens X.left.toTopCat)))) _
  calc
    X.left.overAlgebraMap k (⊤ : X.left.Opens)
        ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv x)
      = (X.hom.appTop.hom).comp
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
          ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv x) := by
            exact congrFun (congrArg DFunLike.coe h_kts) _
    _ = X.hom.appTop.hom x := by
      simp only [RingHom.coe_comp, Function.comp_apply]
      congr 1
      change ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
          (Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom x = x
      rw [Iso.hom_inv_id]
      rfl

/-- The degree-zero cohomology of the structure sheaf is finite on a proper
integral `k`-scheme. -/
theorem moduleFinite_moduleKSheaf_zero_of_isProper
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    [IsIntegral X.left] [IsProper X.hom] :
    Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 0) := by
  have hM_top : Module.Finite k
      (X.left.presheaf.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens X.left.toTopCat))) :=
    moduleFinite_globalSections_of_isProper k X
  letI : Module.Finite k
      ((X.left.moduleKSheaf k).obj.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens X.left.toTopCat))) := by
    change Module.Finite k
      (X.left.presheaf.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens X.left.toTopCat)))
    exact hM_top
  exact Module.Finite.equiv
    (CategoryTheory.Sheaf.HModule.linearEquiv₀
      (J := Opens.grothendieckTopology (X.left : TopCat))
      (R := k)
      (T := (⊤ : TopologicalSpace.Opens X.left.toTopCat))
      (Preorder.isTerminalTop (TopologicalSpace.Opens X.left.toTopCat))
      (X.left.moduleKSheaf k)).symm

/-- The degree-zero and degree-one cohomology of one divisor sheaf are finite. -/
def HasFiniteDivisorSheafCohomology (D : CurveDivisor k X) : Prop :=
  Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 0) ∧
    Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf D) 1)

/-- Every divisor sheaf has finite degree-zero and degree-one cohomology.

This is a predicate rather than an instance so that the geometric finiteness
theorem needed by the product formula remains visible at each use site. -/
def HasFiniteDivisorCohomology : Prop :=
  ∀ D : CurveDivisor k X, HasFiniteDivisorSheafCohomology D

/-! ## Finiteness dévissage -/

/-- The skyscraper term in the dévissage sequence has finite cohomology in the
two degrees used by `chi`.  Degree zero is transported from the jump module,
while degree one is finite because it is subsingleton. -/
theorem hasFiniteSkyModuleCohomology {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    Module.Finite k
        (CategoryTheory.Sheaf.HModule
          (Opens.grothendieckTopology (X.left : TopCat)) k
          (skyModule (X := X) x (jumpModule hx D)) 0) ∧
      Module.Finite k
        (CategoryTheory.Sheaf.HModule
          (Opens.grothendieckTopology (X.left : TopCat)) k
          (skyModule (X := X) x (jumpModule hx D)) 1) := by
  letI : Module.Finite k (jumpModule hx D) := moduleFinite_jumpModule hx D
  constructor
  · exact Module.Finite.equiv
      (skyModuleGammaEquiv (X := X) x (jumpModule hx D)).symm
  · letI : Subsingleton
        (CategoryTheory.Sheaf.HModule
          (Opens.grothendieckTopology (X.left : TopCat)) k
          (skyModule (X := X) x (jumpModule hx D)) 1) :=
      skyModule_subsingleton_hModule_one (X := X) x (jumpModule hx D)
    letI : Finite
        (CategoryTheory.Sheaf.HModule
          (Opens.grothendieckTopology (X.left : TopCat)) k
          (skyModule (X := X) x (jumpModule hx D)) 1) := Finite.of_subsingleton
    exact Module.Finite.of_finite

/-- Finiteness of the structure-sheaf cohomology propagates to every divisor
sheaf through the one-point dévissage exact sequence. -/
theorem hasFiniteDivisorCohomology_of_zero
    (hzero : HasFiniteDivisorSheafCohomology (k := k) (X := X)
      (0 : CurveDivisor k X)) :
    HasFiniteDivisorCohomology (k := k) (X := X) := by
  intro D
  refine CurveDivisor.induction_devissage
    (P := fun E : CurveDivisor k X =>
      HasFiniteDivisorSheafCohomology (k := k) (X := X) E)
    hzero (fun {x} hx E => ?_) D
  have hS := devissageSES_shortExact hx E
  have hsky := hasFiniteSkyModuleCohomology hx E
  haveI hsky0 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx E).X₃ 0) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (skyModule (X := X) x (jumpModule hx E)) 0)
    exact hsky.1
  haveI hsky1 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx E).X₃ 1) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (skyModule (X := X) x (jumpModule hx E)) 1)
    exact hsky.2
  haveI hskysub : Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx E).X₃ 1) := by
    change Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (skyModule (X := X) x (jumpModule hx E)) 1)
    exact skyModule_subsingleton_hModule_one (X := X) x (jumpModule hx E)
  constructor
  · rintro ⟨h0E, h1E⟩
    haveI hX₂0 : Module.Finite k
        (CategoryTheory.Sheaf.HModule
          (Opens.grothendieckTopology (X.left : TopCat)) k
          (devissageSES hx E).X₂ 0) := h0E
    haveI hX₂1 : Module.Finite k
        (CategoryTheory.Sheaf.HModule
          (Opens.grothendieckTopology (X.left : TopCat)) k
          (devissageSES hx E).X₂ 1) := h1E
    exact ⟨CategoryTheory.Sheaf.HModule.moduleFinite_left_zero hS,
      CategoryTheory.Sheaf.HModule.moduleFinite_left_succ hS
        (show 0 + 1 = 1 from rfl)⟩
  · rintro ⟨h0E', h1E'⟩
    haveI hX₁0 : Module.Finite k
        (CategoryTheory.Sheaf.HModule
          (Opens.grothendieckTopology (X.left : TopCat)) k
          (devissageSES hx E).X₁ 0) := h0E'
    haveI hX₁1 : Module.Finite k
        (CategoryTheory.Sheaf.HModule
          (Opens.grothendieckTopology (X.left : TopCat)) k
          (devissageSES hx E).X₁ 1) := h1E'
    exact ⟨CategoryTheory.Sheaf.HModule.moduleFinite_middle hS 0,
      CategoryTheory.Sheaf.HModule.moduleFinite_middle hS 1⟩

/-! ## The one-point increment -/

theorem chi_divisorSheaf_devissage
    (hfin : HasFiniteDivisorCohomology (k := k) (X := X))
    {x : X.left} (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X) :
    CategoryTheory.Sheaf.chi (divisorSheaf D) =
      CategoryTheory.Sheaf.chi
          (divisorSheaf (CurveDivisor.devissageDivisor hx D)) + 1 := by
  let D' : CurveDivisor k X := CurveDivisor.devissageDivisor hx D
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D') 0) :=
    (hfin D').1
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D') 1) :=
    (hfin D').2
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D) 0) :=
    (hfin D).1
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D) 1) :=
    (hfin D).2
  letI : Module.Finite k (jumpModule hx D) :=
    moduleFinite_jumpModule hx D
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (skyModule (X := X) x (jumpModule hx D)) 0) :=
    Module.Finite.equiv
      (skyModuleGammaEquiv (X := X) x (jumpModule hx D)).symm
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₁ 0) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D') 0)
    exact (hfin D').1
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₁ 1) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D') 1)
    exact (hfin D').2
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₂ 0) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D) 0)
    exact (hfin D).1
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₂ 1) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k (divisorSheaf D) 1)
    exact (hfin D).2
  letI : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₃ 0) := by
    change Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (skyModule (X := X) x (jumpModule hx D)) 0)
    infer_instance
  letI : Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (devissageSES hx D).X₃ 1) := by
    change Subsingleton
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (skyModule (X := X) x (jumpModule hx D)) 1)
    infer_instance
  have hshort := devissageSES_shortExact hx D
  have hchi := CategoryTheory.Sheaf.chi_eq_add_of_shortExact hshort
  change CategoryTheory.Sheaf.chi (divisorSheaf D) =
    CategoryTheory.Sheaf.chi (divisorSheaf D') +
      CategoryTheory.Sheaf.chi (skyModule (X := X) x (jumpModule hx D)) at hchi
  rw [chi_skyModule_jump_eq_one hx D] at hchi
  exact hchi

/-! ## Iterating the increment -/

/-- Under the explicit finiteness hypothesis, `χ(𝒪(D))` is affine-linear in
the divisor degree. -/
theorem chi_divisorSheaf_eq_base_add_degree
    (hfin : HasFiniteDivisorCohomology (k := k) (X := X))
    (D : CurveDivisor k X) :
    CategoryTheory.Sheaf.chi (divisorSheaf D) =
      CategoryTheory.Sheaf.chi (divisorSheaf (X := X) (0 : CurveDivisor k X)) +
        CurveDivisor.degree D := by
  apply CurveDivisor.induction_devissage (P := fun E : CurveDivisor k X =>
    CategoryTheory.Sheaf.chi (divisorSheaf E) =
      CategoryTheory.Sheaf.chi (divisorSheaf (X := X) (0 : CurveDivisor k X)) +
        CurveDivisor.degree E) (D := D)
  · simp
  · intro x hx E
    constructor <;> intro hE
    · have hχ := chi_divisorSheaf_devissage hfin hx E
      have hdeg := CurveDivisor.degree_devissageDivisor_add_single hx E
      omega
    · have hχ := chi_divisorSheaf_devissage hfin hx E
      have hdeg := CurveDivisor.degree_devissageDivisor_add_single hx E
      omega

/-! ## The conditional product formula -/

/-- Finite-dimensional divisor-sheaf cohomology forces every principal divisor
to have degree zero.

The proof is the usual one-point dévissage argument: the exact sequence adds
one to `χ` at each closed point, while multiplication by a rational function
identifies linearly equivalent divisor sheaves. -/
theorem principalDivisorsHaveDegreeZero_of_finiteDivisorCohomology
    (hfin : HasFiniteDivisorCohomology (k := k) (X := X)) :
    PrincipalDivisorsHaveDegreeZero (k := k) (X := X) := by
  intro g
  have hχ := chi_divisorSheaf_eq_base_add_degree hfin (principalDivisor g)
  have hshift :=
    chi_divisorSheaf_sub_principalDivisor (X := X) g (principalDivisor g)
  have hχzero :
      CategoryTheory.Sheaf.chi (divisorSheaf (principalDivisor g)) =
        CategoryTheory.Sheaf.chi (divisorSheaf (X := X) (0 : CurveDivisor k X)) := by
    symm
    simpa using hshift
  omega

/-- The explicit geometric input can be stated for the structure sheaf: its
finite `H⁰` and `H¹` transport across the zero-divisor sheaf isomorphism. -/
theorem hasFiniteDivisorCohomology_of_moduleKSheaf
    (h0 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 0))
    (h1 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 1)) :
    HasFiniteDivisorCohomology (k := k) (X := X) := by
  apply hasFiniteDivisorCohomology_of_zero
  constructor
  · exact Module.Finite.equiv
      (CategoryTheory.Sheaf.HModule.mapEquiv
        (moduleKSheafDivisorSheafZeroIso (X := X)) 0)
  · exact Module.Finite.equiv
      (CategoryTheory.Sheaf.HModule.mapEquiv
        (moduleKSheafDivisorSheafZeroIso (X := X)) 1)

/-- Properness supplies the degree-zero finiteness input, so only degree one
cohomology remains explicit in this specialization. -/
theorem hasFiniteDivisorCohomology_of_moduleKSheaf_oneFinite
    (h1 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 1)) :
    HasFiniteDivisorCohomology (k := k) (X := X) :=
  hasFiniteDivisorCohomology_of_moduleKSheaf
    (moduleFinite_moduleKSheaf_zero_of_isProper (k := k) (X := X)) h1

/-- Structure-sheaf cohomology finiteness therefore suffices for the
principal-divisor degree-zero statement. -/
theorem principalDivisorsHaveDegreeZero_of_moduleKSheafCohomologyFinite
    (h0 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 0))
    (h1 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 1)) :
    PrincipalDivisorsHaveDegreeZero (k := k) (X := X) :=
  principalDivisorsHaveDegreeZero_of_finiteDivisorCohomology
    (hasFiniteDivisorCohomology_of_moduleKSheaf h0 h1)

/-- The principal-divisor degree-zero conclusion with the properness-derived
degree-zero finiteness discharged. -/
theorem principalDivisorsHaveDegreeZero_of_moduleKSheaf_oneFinite
    (h1 : Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (X.left.moduleKSheaf k) 1)) :
    PrincipalDivisorsHaveDegreeZero (k := k) (X := X) :=
  principalDivisorsHaveDegreeZero_of_moduleKSheafCohomologyFinite
    (moduleFinite_moduleKSheaf_zero_of_isProper (k := k) (X := X)) h1

end
end Hartshorne
