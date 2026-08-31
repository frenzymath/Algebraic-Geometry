/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.SemilinearAction
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Finite subsets in affine opens

`Scheme.FiniteInAffine X` is the action-free geometric condition behind the
finite-Galois quotient construction: every finite subset of `X` lies in one
affine open.  For a finite Galois extension, this immediately supplies
`SemilinearGalAction.OrbitsInAffineOpen` for every action on `X`.

The property is stated independently of Picard data.  In particular, it is a
conclusion to be proved for a representing scheme, not an additional field of
the representability datum.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits
open AlgebraicJacobian.GaloisDescent

namespace AlgebraicGeometry.Scheme

/-- Every finite subset of a scheme is contained in a single affine open. -/
def FiniteInAffine (X : Scheme.{u}) : Prop :=
  ∀ s : Set X, s.Finite → ∃ U : X.affineOpens, s ⊆ U.1

/-- An affine scheme satisfies `FiniteInAffine`. -/
theorem finiteInAffine_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    FiniteInAffine X :=
  fun _ _ ↦ ⟨⟨⊤, isAffineOpen_top X⟩, fun _ _ ↦ trivial⟩

/-- `FiniteInAffine` is invariant under isomorphism. -/
theorem finiteInAffine_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (h : FiniteInAffine X) : FiniteInAffine Y := by
  intro s hs
  obtain ⟨U, hU⟩ := h (e.hom.base ⁻¹' s)
    (hs.preimage (TopCat.homeoOfIso ((Scheme.forgetToTop).mapIso e)).injective.injOn)
  refine ⟨⟨e.hom ''ᵁ U.1, U.2.image_of_isOpenImmersion e.hom⟩, ?_⟩
  intro y hy
  exact ⟨e.inv.base y, hU (by simpa using hy), by simp⟩

/-- `FiniteInAffine` is closed under arbitrary set-indexed coproducts. -/
theorem finiteInAffine_sigma {σ : Type v} [Small.{u, v} σ] (g : σ → Scheme.{u})
    (h : ∀ i, FiniteInAffine (g i)) : FiniteInAffine (∐ g) := by
  classical
  letI : ∀ i, IsOpenImmersion (Sigma.ι g i) := fun i =>
    Scheme.IsLocallyDirected.instIsOpenImmersionι (Discrete.functor g) { as := i }
  intro s hs
  have hcomp : ∀ x : (∐ g : Scheme.{u}), ∃ i, x ∈ Set.range (Sigma.ι g i).base := by
    intro x
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover g).exists_eq x
    exact ⟨i, y, hy⟩
  choose idx hidx using hcomp
  have hpre : ∀ i : σ, ((Sigma.ι g i).base ⁻¹' s).Finite := fun i =>
    hs.preimage ((Sigma.ι g i).isOpenEmbedding.injective).injOn
  choose U hU using fun i => h i _ (hpre i)
  let J : Set σ := idx '' s
  have hJfin : J.Finite := hs.image idx
  refine ⟨⟨⨆ i ∈ J, (Sigma.ι g i) ''ᵁ (U i).1, ?_⟩, ?_⟩
  · apply IsAffineOpen.biSup_of_disjoint hJfin
    · intro i _
      exact (U i).2.image_of_isOpenImmersion _
    · intro i _ j _ hij
      exact Disjoint.mono (Scheme.Hom.image_le_opensRange _ _)
        (Scheme.Hom.image_le_opensRange _ _) (disjoint_opensRange_sigmaι g i j hij)
  · intro x hx
    obtain ⟨y, hy⟩ := hidx x
    have hyU : y ∈ (U (idx x)).1 := by
      apply hU (idx x)
      simp only [Set.mem_preimage, hy]
      exact hx
    have hmem : x ∈ (Sigma.ι g (idx x)) ''ᵁ (U (idx x)).1 := ⟨y, hyU, hy⟩
    exact (le_iSup₂ (f := fun i _ => (Sigma.ι g i) ''ᵁ (U i).1) (idx x)
      ⟨x, hx, rfl⟩) hmem

/-- `FiniteInAffine` descends along an affine morphism. -/
theorem finiteInAffine_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] (h : FiniteInAffine Y) : FiniteInAffine X := by
  intro s hs
  obtain ⟨U, hU⟩ := h (f.base '' s) (hs.image _)
  exact ⟨⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩, fun x hx ↦ hU ⟨x, hx, rfl⟩⟩

/-- An object affine over a field spectrum satisfies `FiniteInAffine`. -/
theorem finiteInAffine_left_of_isAffineHom {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffineHom X.hom] :
    FiniteInAffine X.left :=
  haveI := isAffine_of_isAffineHom X.hom
  finiteInAffine_of_isAffine _

/-- `FiniteInAffine` supplies the orbit condition for every finite-Galois
semilinear action on the scheme. -/
theorem orbitsInAffineOpen_of_finiteInAffine
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f) (h : FiniteInAffine X) :
    rho.OrbitsInAffineOpen where
  exists_affineOpen x := by
    obtain ⟨U, hU⟩ :=
      h (Set.range fun gamma : L ≃ₐ[K] L ↦ (rho.act gamma).hom.base x)
        (Set.finite_range _)
    exact ⟨U, fun gamma ↦ hU ⟨gamma, rfl⟩⟩

end AlgebraicGeometry.Scheme
