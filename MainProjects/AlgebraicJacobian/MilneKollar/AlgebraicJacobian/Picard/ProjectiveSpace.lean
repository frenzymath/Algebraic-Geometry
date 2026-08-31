/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.TotallySplit

/-!
# Relative projective space `ℙ(n; S)`

Mathlib v4.31 has the absolute `Proj` of a ℕ-graded ring together with the
properness package for `Proj.toSpecZero` (`ProjectiveSpectrum/Proper.lean`),
but no relative projective space over an arbitrary base scheme.  Following the
`AffineSpace` pattern (`Mathlib/AlgebraicGeometry/AffineSpace.lean`) and the
encoding settled in inbox `I-0118` (comment `C-0002`), this file defines

* `AlgebraicGeometry.ProjectiveSpace n S` (notation `ℙ(n; S)`): the relative
  projective space with homogeneous coordinates indexed by `n : Type u`, i.e.
  the pullback of the integral model
  `Proj ℤ[Xᵢ : i ∈ n] = Proj (MvPolynomial.homogeneousSubmodule n (ULift ℤ))`
  along `S ⟶ ⊤_ Scheme`;
* the structural morphism `ℙ(n; S) ↘ S` (a `CanonicallyOver` instance) with
  `IsProper` (hence `IsSeparated`, `UniversallyClosed`, `LocallyOfFiniteType`,
  `QuasiCompact`) derived by base change from the Mathlib instances on
  `Proj.toSpecZero`;
* functoriality `ProjectiveSpace.map` in the base and the base-change square
  `ProjectiveSpace.isPullback_map`.

The key observations making the transfer work: the degree-zero part of the
homogeneous coordinate ring is the copy of `ULift ℤ` given by the constants
(`MvPolynomial.homogeneousSubmodule_zero`), so `Spec (𝒜 0)` is terminal and
`terminal.from (Proj 𝒜)` factors as `Proj.toSpecZero 𝒜` followed by an
isomorphism; and for finitely many variables the coordinate ring is of finite
type over its degree-zero part, which is exactly the hypothesis of the Mathlib
properness instances.

Blueprint: `def:projective_space`, `lem:projective_space_proper`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
-/

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

universe u

/-- The total-degree grading on the homogeneous coordinate ring
`ℤ[Xᵢ : i ∈ n]` of the integral model of projective space (with `ULift ℤ`
coefficients for universe polymorphism, as in `AffineSpace`). -/
local notation3 "𝒫[" n "]" => homogeneousSubmodule n (ULift ℤ)

/-- The total-degree grading is a graded ring structure.  Mathlib deliberately
does not register `MvPolynomial.gradedAlgebra` as a global instance (other
weightings of the same polynomial ring exist); for the fixed homogeneous
coordinate ring of projective space we register it project-wide. -/
instance (n : Type u) : GradedRing 𝒫[n] :=
  MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- `ℙ(n; S)` is the projective space over `S` with homogeneous coordinates
indexed by `n : Type u` (e.g. `ULift (Fin (m + 1))` for `ℙ^m_S`).  It is the
base change to `S` of the integral model `Proj ℤ[Xᵢ : i ∈ n]`. -/
def ProjectiveSpace (n : Type u) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S)
    (terminal.from (Proj (homogeneousSubmodule n (ULift.{u} ℤ))))

namespace ProjectiveSpace

/-- `ℙ(n; S)` is the projective `n`-space over `S`. -/
scoped[AlgebraicGeometry] notation "ℙ(" n "; " S ")" => ProjectiveSpace n S

instance canonicallyOver : (ℙ(n; S)).CanonicallyOver S where
  hom := pullback.fst _ _

lemma over_eq_fst : ℙ(n; S) ↘ S = pullback.fst _ _ := rfl

/-- The projection from `ℙ(n; S)` to the integral model `Proj ℤ[Xᵢ : i ∈ n]`. -/
def toProjInt : ℙ(n; S) ⟶ Proj 𝒫[n] := pullback.snd _ _

lemma toProjInt_eq_snd : toProjInt n S = pullback.snd _ _ := rfl

@[reassoc]
lemma over_terminal_comp :
    (ℙ(n; S) ↘ S) ≫ terminal.from S = toProjInt n S ≫ terminal.from (Proj 𝒫[n]) :=
  pullback.condition

section GradeZero

/-- The degree-zero part of the homogeneous coordinate ring is the copy of
`ULift ℤ` given by the constants. -/
lemma bijective_algebraMap_gradeZero :
    Function.Bijective
      (algebraMap (ULift.{u} ℤ) (homogeneousSubmodule n (ULift.{u} ℤ) 0)) := by
  constructor
  · intro a b hab
    have := congrArg Subtype.val hab
    simpa using MvPolynomial.C_injective n (ULift.{u} ℤ) this
  · intro x
    obtain ⟨y, hy⟩ := Submodule.mem_one.mp
      ((MvPolynomial.homogeneousSubmodule_zero (σ := n) (R := ULift.{u} ℤ)).le x.2)
    exact ⟨y, Subtype.ext (by simpa using hy)⟩

/-- The degree-zero part of the homogeneous coordinate ring, as a ring, is
`ULift ℤ`. -/
def gradeZeroRingEquiv :
    ULift.{u} ℤ ≃+* homogeneousSubmodule n (ULift.{u} ℤ) 0 :=
  RingEquiv.ofBijective
    (algebraMap (ULift.{u} ℤ) (homogeneousSubmodule n (ULift.{u} ℤ) 0))
    (bijective_algebraMap_gradeZero n)

/-- `Spec` of the degree-zero part of the homogeneous coordinate ring is a
terminal scheme. -/
def specGradeZeroIsTerminal :
    IsTerminal (Spec (.of (homogeneousSubmodule n (ULift.{u} ℤ) 0))) :=
  specULiftZIsTerminal.{u}.ofIso
    (Scheme.Spec.mapIso (gradeZeroRingEquiv n).toCommRingCatIso.op).symm

instance :
    IsIso (terminal.from (Spec (.of (homogeneousSubmodule n (ULift.{u} ℤ) 0)))) :=
  isIso_of_isTerminal (specGradeZeroIsTerminal n) terminalIsTerminal _

/-- For finitely many variables, the homogeneous coordinate ring is of finite
type over its degree-zero part — the hypothesis of the Mathlib properness
package for `Proj.toSpecZero`. -/
instance [Finite n] :
    Algebra.FiniteType (homogeneousSubmodule n (ULift.{u} ℤ) 0)
      (MvPolynomial n (ULift.{u} ℤ)) := by
  haveI := IsScalarTower.of_algebraMap_eq (R := ULift.{u} ℤ)
    (S := homogeneousSubmodule n (ULift.{u} ℤ) 0)
    (A := MvPolynomial n (ULift.{u} ℤ)) fun r => rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    (R := ULift.{u} ℤ) (S := homogeneousSubmodule n (ULift.{u} ℤ) 0)
    (A := MvPolynomial n (ULift.{u} ℤ))

end GradeZero

section Instances

instance isProper_terminalFrom_proj [Finite n] :
    IsProper (terminal.from (Proj (homogeneousSubmodule n (ULift.{u} ℤ)))) := by
  rw [← terminal.comp_from (Proj.toSpecZero (homogeneousSubmodule n (ULift.{u} ℤ)))]
  infer_instance

instance isSeparated_terminalFrom_proj :
    IsSeparated (terminal.from (Proj (homogeneousSubmodule n (ULift.{u} ℤ)))) := by
  rw [← terminal.comp_from (Proj.toSpecZero (homogeneousSubmodule n (ULift.{u} ℤ)))]
  infer_instance

/-- The structural morphism of relative projective space is proper.  Its
parent classes (`IsSeparated`, `UniversallyClosed`, `LocallyOfFiniteType`,
hence also `QuasiCompact`) follow by instance projection. -/
instance isProper_over [Finite n] : IsProper (ℙ(n; S) ↘ S) :=
  MorphismProperty.pullback_fst _ _ (isProper_terminalFrom_proj n)

instance isSeparated_over : IsSeparated (ℙ(n; S) ↘ S) :=
  MorphismProperty.pullback_fst _ _ (isSeparated_terminalFrom_proj n)

end Instances

section Functorial

variable {S} {T : Scheme.{u}}

/-- `ℙ(n; S)` is functorial in the base `S`. -/
def map (f : S ⟶ T) : ℙ(n; S) ⟶ ℙ(n; T) :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma map_fst (f : S ⟶ T) :
    map n f ≫
        pullback.fst (terminal.from T)
          (terminal.from (Proj (homogeneousSubmodule n (ULift.{u} ℤ)))) =
      pullback.fst (terminal.from S)
          (terminal.from (Proj (homogeneousSubmodule n (ULift.{u} ℤ)))) ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma map_snd (f : S ⟶ T) :
    map n f ≫
        pullback.snd (terminal.from T)
          (terminal.from (Proj (homogeneousSubmodule n (ULift.{u} ℤ)))) =
      pullback.snd (terminal.from S)
        (terminal.from (Proj (homogeneousSubmodule n (ULift.{u} ℤ)))) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma map_over (f : S ⟶ T) : map n f ≫ ℙ(n; T) ↘ T = (ℙ(n; S) ↘ S) ≫ f := by
  rw [over_eq_fst, over_eq_fst]
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma map_toProjInt (f : S ⟶ T) : map n f ≫ toProjInt n T = toProjInt n S := by
  rw [toProjInt_eq_snd, toProjInt_eq_snd]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

@[simp]
lemma map_id : map n (𝟙 S) = 𝟙 ℙ(n; S) := by
  apply pullback.hom_ext
  · exact (map_fst n (𝟙 S)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  · exact (map_snd n (𝟙 S)).trans (Category.id_comp _).symm

@[reassoc, simp]
lemma map_comp {U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U) :
    map n (f ≫ g) = map n f ≫ map n g := by
  apply pullback.hom_ext
  · exact (map_fst n (f ≫ g)).trans <| ((Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ g) (map_fst n f).symm).trans <| (Category.assoc _ _ _).trans <|
        congrArg (map n f ≫ ·) (map_fst n g).symm).trans (Category.assoc _ _ _).symm
  · exact (map_snd n (f ≫ g)).trans <| ((map_snd n f).symm.trans <|
      congrArg (map n f ≫ ·) (map_snd n g).symm).trans (Category.assoc _ _ _).symm

/-- Relative projective space commutes with base change: the square

```
ℙ(n; S) ⟶ ℙ(n; T)
   |          |
   S    ⟶    T
```

is a pullback. -/
lemma isPullback_map (f : S ⟶ T) :
    IsPullback (map n f) (ℙ(n; S) ↘ S) (ℙ(n; T) ↘ T) f := by
  have hbig : IsPullback (toProjInt n S) (ℙ(n; S) ↘ S)
      (terminal.from (Proj 𝒫[n])) (terminal.from S) :=
    (IsPullback.of_hasPullback (terminal.from S) (terminal.from (Proj 𝒫[n]))).flip
  have hright : IsPullback (toProjInt n T) (ℙ(n; T) ↘ T)
      (terminal.from (Proj 𝒫[n])) (terminal.from T) :=
    (IsPullback.of_hasPullback (terminal.from T) (terminal.from (Proj 𝒫[n]))).flip
  refine IsPullback.of_right ?_ (map_over n f) hright
  rw [map_toProjInt, terminal.comp_from f]
  exact hbig

end Functorial

end ProjectiveSpace

end AlgebraicGeometry
