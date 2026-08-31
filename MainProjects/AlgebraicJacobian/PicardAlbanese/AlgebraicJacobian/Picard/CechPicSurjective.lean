/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.InvertibleLocalTrivialization
import AlgebraicJacobian.Algebra.LocalizationTrivialization
import AlgebraicJacobian.Picard.CechPicToPic

/-!
# Surjectivity of the Čech–Picard descent homomorphism, and the dictionary

For an affine scheme `X` this file proves surjectivity of the descent homomorphism
`CechPic.toPic : X.CechPic →* CommRing.Pic Γ(X, ⊤)` and assembles the full
**Čech–Picard dictionary**

* `AlgebraicGeometry.Scheme.cechPicEquivPic : X.CechPic ≃* CommRing.Pic Γ(X, ⊤)`

— the isomorphism between the definitional Čech Picard group on pointed Zariski covers
and mathlib's Picard group of invertible modules (the TODO of
`Mathlib.RingTheory.PicardGroup`: "exhibit isomorphism with `H¹(Spec R, 𝓞ˣ)`").

The route: an invertible module `N` over `Γ(X, ⊤)` trivializes on the basic open of
some section outside every prime, so the trivializing sections span the unit ideal
(`Module.Invertible.span_tensor_free_eq_top`) and their basic opens cover `X`.  A
choice of one trivializing basic neighborhood per point is a `TrivializingFamily`; the
transition units of its trivializations (`Module.transitionUnit`) form a unit Čech
cocycle on the associated pointed cover.  Along any finite basic refinement the
restricted cover cocycle is the transition cocycle of the pushed-forward
trivializations, so its descended module is `N` itself
(`IsLocalization.AwayCover.picClass_trivializationCocycle`), and `toPic` hits the class
of `N`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace CategoryTheory.PresheafOfGroups
open TensorProduct

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

/-! ## Trivializing families -/

/-- A pointed trivializing family for a module `N` over the global sections of `X`: one
section per point, whose basic open contains the point and carries a trivialization of
the base change of `N`.  Invertible modules over affine schemes always admit one
(`TrivializingFamily.nonempty`). -/
structure TrivializingFamily (X : Scheme.{u}) (N : Type u) [AddCommGroup N]
    [Module Γ(X, ⊤) N] : Type u where
  /-- The trivializing section at a point. -/
  sec : X → Γ(X, ⊤)
  /-- Each point lies in the basic open of its section. -/
  mem_basicOpen : ∀ x, x ∈ X.basicOpen (sec x)
  /-- The chosen trivialization of `N` over the basic open. -/
  triv : ∀ x, (Γ(X, X.basicOpen (sec x)) ⊗[Γ(X, ⊤)] N)
    ≃ₗ[Γ(X, X.basicOpen (sec x))] Γ(X, X.basicOpen (sec x))

namespace TrivializingFamily

variable {N : Type u} [AddCommGroup N] [Module Γ(X, ⊤) N]

/-- Every invertible module over the global sections of an affine scheme admits a
trivializing family: the trivializing sections span the unit ideal, so their basic
opens cover `X`. -/
theorem nonempty [IsAffine X] [Module.Invertible Γ(X, ⊤) N] :
    Nonempty (TrivializingFamily X N) := by
  have hcover :
      (⨆ f : {f : Γ(X, ⊤) | ∀ (S : Type u) [CommRing S] [Algebra Γ(X, ⊤) S],
          IsLocalization.Away f S → Module.Free S (S ⊗[Γ(X, ⊤)] N)},
        X.basicOpen f.1) = ⊤ :=
    (isAffineOpen_top X).iSup_basicOpen_eq_self_iff.mpr
      (Module.Invertible.span_tensor_free_eq_top N)
  have hex : ∀ x : X, ∃ f : Γ(X, ⊤),
      (∀ (S : Type u) [CommRing S] [Algebra Γ(X, ⊤) S],
        IsLocalization.Away f S → Module.Free S (S ⊗[Γ(X, ⊤)] N))
      ∧ x ∈ X.basicOpen f := by
    intro x
    obtain ⟨f, hf⟩ := Opens.mem_iSup.mp (hcover.ge (trivial : x ∈ (⊤ : X.Opens)))
    exact ⟨f.1, f.2, hf⟩
  choose f hfree hmem using hex
  refine ⟨⟨f, hmem, fun x ↦ ?_⟩⟩
  haveI : Module.Free Γ(X, X.basicOpen (f x)) (Γ(X, X.basicOpen (f x)) ⊗[Γ(X, ⊤)] N) :=
    hfree x Γ(X, X.basicOpen (f x)) inferInstance
  exact (Module.Invertible.free_iff_linearEquiv.mp this).some

variable (F : TrivializingFamily X N)

/-- The pointed cover underlying a trivializing family. -/
def cover : X.PointedCover where
  opens x := X.basicOpen (F.sec x)
  mem_opens := F.mem_basicOpen

@[simp]
lemma cover_opens (x : X) : F.cover.opens x = X.basicOpen (F.sec x) :=
  rfl

section transition

variable [IsAffine X]

/-- The transition cocycle of the trivializing family: on each double overlap, the
transition unit between the pushforwards of the trivializations at the two points. -/
noncomputable def transition (x y : X) : Γ(X, X.basicOpen (F.sec x * F.sec y))ˣ :=
  IsLocalization.AwayCover.trivializationCocycle F.sec
    (fun x ↦ Γ(X, X.basicOpen (F.sec x)))
    (fun x y ↦ Γ(X, X.basicOpen (F.sec x * F.sec y))) F.triv x y

/-- The transition units form a Čech cover cocycle on the (infinite) family of
trivializing basic opens. -/
lemma isCoverCocycle_transition :
    IsLocalization.AwayCover.IsCoverCocycle (A := Γ(X, ⊤)) (f := F.sec)
      (S := fun x ↦ Γ(X, X.basicOpen (F.sec x)))
      (T := fun x y ↦ Γ(X, X.basicOpen (F.sec x * F.sec y)))
      (W := fun x y z ↦ Γ(X, X.basicOpen (F.sec x * (F.sec y * F.sec z))))
      F.transition :=
  IsLocalization.AwayCover.isCoverCocycle_trivializationCocycle F.sec _ _ _ F.triv

/-- The cocycle identity for the transition units, restricted to any common open. -/
lemma transition_mul (x y z : X) {T : X.Opens}
    (hxy : T ≤ X.basicOpen (F.sec x * F.sec y))
    (hyz : T ≤ X.basicOpen (F.sec y * F.sec z))
    (hxz : T ≤ X.basicOpen (F.sec x * F.sec z)) :
    X.unitsRestrict hxy (F.transition x y) * X.unitsRestrict hyz (F.transition y z)
      = X.unitsRestrict hxz (F.transition x z) := by
  -- restrictions from the double overlaps to the triple overlap
  have h₁₂ : X.basicOpen (F.sec x * (F.sec y * F.sec z))
      ≤ X.basicOpen (F.sec x * F.sec y) :=
    X.basicOpen_le_of_dvd ⟨F.sec z, by ring⟩
  have h₂₃ : X.basicOpen (F.sec x * (F.sec y * F.sec z))
      ≤ X.basicOpen (F.sec y * F.sec z) :=
    X.basicOpen_le_of_dvd ⟨F.sec x, by ring⟩
  have h₁₃ : X.basicOpen (F.sec x * (F.sec y * F.sec z))
      ≤ X.basicOpen (F.sec x * F.sec z) :=
    X.basicOpen_le_of_dvd ⟨F.sec y, by ring⟩
  -- the common open sits inside the triple overlap
  have hT : T ≤ X.basicOpen (F.sec x * (F.sec y * F.sec z)) := by
    rw [X.basicOpen_mul, X.basicOpen_mul]
    exact le_inf (hxy.trans ((X.basicOpen_mul _ _).trans_le inf_le_left))
      (le_inf (hxy.trans ((X.basicOpen_mul _ _).trans_le inf_le_right))
        (hyz.trans ((X.basicOpen_mul _ _).trans_le inf_le_right)))
  -- the cover cocycle identity, with the face maps rewritten as restrictions
  have hc := (F.isCoverCocycle_transition).cocycle x y z
  rw [show IsLocalization.AwayCover.face₂₃ (A := Γ(X, ⊤)) (f := F.sec)
        (T := fun x y ↦ Γ(X, X.basicOpen (F.sec x * F.sec y)))
        (W := fun x y z ↦ Γ(X, X.basicOpen (F.sec x * (F.sec y * F.sec z)))) x y z
      = X.basicRes _ _ h₂₃ from X.basicOpen_algHom_ext _ _ _,
    show IsLocalization.AwayCover.face₁₂ (A := Γ(X, ⊤)) (f := F.sec)
        (T := fun x y ↦ Γ(X, X.basicOpen (F.sec x * F.sec y)))
        (W := fun x y z ↦ Γ(X, X.basicOpen (F.sec x * (F.sec y * F.sec z)))) x y z
      = X.basicRes _ _ h₁₂ from X.basicOpen_algHom_ext _ _ _,
    show IsLocalization.AwayCover.face₁₃ (A := Γ(X, ⊤)) (f := F.sec)
        (T := fun x y ↦ Γ(X, X.basicOpen (F.sec x * F.sec y)))
        (W := fun x y z ↦ Γ(X, X.basicOpen (F.sec x * (F.sec y * F.sec z)))) x y z
      = X.basicRes _ _ h₁₃ from X.basicOpen_algHom_ext _ _ _] at hc
  -- lift to units on the triple overlap
  have hu : X.unitsRestrict h₂₃ (F.transition y z) * X.unitsRestrict h₁₂ (F.transition x y)
      = X.unitsRestrict h₁₃ (F.transition x z) := Units.ext hc
  -- restrict to `T` and collapse the composed restrictions
  have e := congrArg (X.unitsRestrict hT) hu
  rw [map_mul, unitsRestrict_unitsRestrict, unitsRestrict_unitsRestrict,
    unitsRestrict_unitsRestrict] at e
  exact (mul_comm _ _).trans e

/-- The unit Čech cocycle of a trivializing family on its pointed cover: the value on
`T ≤ D(sec x) ⊓ D(sec y)` is the restriction of the transition unit. -/
noncomputable def cocycle : X.unitsCocycle F.cover where
  ev x y _ a b :=
    X.unitsRestrict ((le_inf a.le b.le).trans (X.basicOpen_mul (F.sec x) (F.sec y)).ge)
      (F.transition x y)
  ev_precomp _ _ _ _ _ _ _ := unitsRestrict_unitsRestrict _ _ _
  ev_trans x y z _ a b c :=
    F.transition_mul x y z
      ((le_inf a.le b.le).trans (X.basicOpen_mul (F.sec x) (F.sec y)).ge)
      ((le_inf b.le c.le).trans (X.basicOpen_mul (F.sec y) (F.sec z)).ge)
      ((le_inf a.le c.le).trans (X.basicOpen_mul (F.sec x) (F.sec z)).ge)

/-- The pair values of the trivializing cocycle are the restricted transition units. -/
lemma cocycle_unitsEvInf (x y : X) :
    unitsEvInf F.cocycle x y
      = X.unitsRestrict (X.basicOpen_mul (F.sec x) (F.sec y)).ge (F.transition x y) :=
  rfl

/-! ## The Picard class along a basic refinement -/

/-- The trivializations of the family, pushed forward to a basic refinement of the
trivializing cover. -/
noncomputable def refTriv (P : F.cover.BasicRefinement) (i : P.ι) :
    (Γ(X, X.basicOpen (P.r i)) ⊗[Γ(X, ⊤)] N)
      ≃ₗ[Γ(X, X.basicOpen (P.r i))] Γ(X, X.basicOpen (P.r i)) :=
  Module.trivializationPush (X.basicRes _ _ (P.basicOpen_le i)) (F.triv (P.pt i))

/-- Restricting the trivializing cocycle to a basic refinement recovers the transition
cocycle of the pushed trivializations. -/
lemma coverCocycle_eq (P : F.cover.BasicRefinement) (i j : P.ι) :
    P.coverCocycle F.cocycle i j
      = IsLocalization.AwayCover.trivializationCocycle P.r
          (fun i ↦ Γ(X, X.basicOpen (P.r i)))
          (fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j))) (F.refTriv P) i j := by
  have hle : X.basicOpen (P.r i * P.r j)
      ≤ X.basicOpen (F.sec (P.pt i) * F.sec (P.pt j)) :=
    (P.overlap_le i j).trans (X.basicOpen_mul _ _).ge
  have h₁ : P.coverCocycle F.cocycle i j
      = X.unitsRestrict hle (F.transition (P.pt i) (P.pt j)) :=
    unitsRestrict_unitsRestrict (X.basicOpen_mul (F.sec (P.pt i)) (F.sec (P.pt j))).ge
      (P.overlap_le i j) (F.transition (P.pt i) (P.pt j))
  rw [h₁, IsLocalization.AwayCover.trivializationCocycle, refTriv, refTriv,
    Module.trivializationPush_trivializationPush,
    Module.trivializationPush_trivializationPush,
    show (IsLocalization.AwayCover.inclLeft (A := Γ(X, ⊤)) (f := P.r)
        (S := fun i ↦ Γ(X, X.basicOpen (P.r i)))
        (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j))) i j).comp
          (X.basicRes _ _ (P.basicOpen_le i))
      = (X.basicRes _ _ hle).comp
          (IsLocalization.AwayCover.inclLeft (A := Γ(X, ⊤)) (f := F.sec)
            (S := fun x ↦ Γ(X, X.basicOpen (F.sec x)))
            (T := fun x y ↦ Γ(X, X.basicOpen (F.sec x * F.sec y))) (P.pt i) (P.pt j))
      from X.basicOpen_algHom_ext _ _ _,
    show (IsLocalization.AwayCover.inclRight (A := Γ(X, ⊤)) (f := P.r)
        (S := fun i ↦ Γ(X, X.basicOpen (P.r i)))
        (T := fun i j ↦ Γ(X, X.basicOpen (P.r i * P.r j))) i j).comp
          (X.basicRes _ _ (P.basicOpen_le j))
      = (X.basicRes _ _ hle).comp
          (IsLocalization.AwayCover.inclRight (A := Γ(X, ⊤)) (f := F.sec)
            (S := fun x ↦ Γ(X, X.basicOpen (F.sec x)))
            (T := fun x y ↦ Γ(X, X.basicOpen (F.sec x * F.sec y))) (P.pt i) (P.pt j))
      from X.basicOpen_algHom_ext _ _ _,
    ← Module.trivializationPush_trivializationPush,
    ← Module.trivializationPush_trivializationPush,
    Module.map_transitionUnit]
  rfl

/-- **Descent identification**: along any basic refinement, the Picard class of the
trivializing cocycle is the class of `N` itself. -/
theorem pic_cocycle [Module.Invertible Γ(X, ⊤) N] (P : F.cover.BasicRefinement) :
    P.pic F.cocycle = CommRing.Pic.mk Γ(X, ⊤) N := by
  letI := P.faithfullyFlat
  rw [P.pic_eq_picClass]
  refine (Module.IsDescentCocycle.picClass_congr _
      (IsLocalization.AwayCover.isDescentCocycle_cocycleUnit _ _ _
        (fun i j k ↦ Γ(X, X.basicOpen (P.r i * (P.r j * P.r k))))
        (IsLocalization.AwayCover.isCoverCocycle_trivializationCocycle P.r _ _
          (fun i j k ↦ Γ(X, X.basicOpen (P.r i * (P.r j * P.r k))))
          (F.refTriv P)))
      (congrArg _ (funext fun i ↦ funext fun j ↦ F.coverCocycle_eq P i j))).trans
    (IsLocalization.AwayCover.picClass_trivializationCocycle P.r _ _
      (fun i j k ↦ Γ(X, X.basicOpen (P.r i * (P.r j * P.r k)))) (F.refTriv P))

end transition

end TrivializingFamily

/-! ## Surjectivity and the dictionary -/

namespace CechPic

variable (X) [IsAffine X]

/-- **Surjectivity of the Čech–Picard descent homomorphism**: every class of invertible
modules over the global sections arises from a unit Čech cocycle on a trivializing
pointed cover. -/
theorem toPic_surjective : Function.Surjective (toPic X) := by
  intro c
  obtain ⟨F⟩ := TrivializingFamily.nonempty (X := X) (N := c.AsModule)
  obtain ⟨P⟩ := PointedCover.BasicRefinement.nonempty F.cover
  refine ⟨CechPic.mk F.cover (OneCocycle.class F.cocycle), ?_⟩
  rw [toPic_mk F.cover F.cocycle P, F.pic_cocycle P, CommRing.Pic.mk_eq_self]

/-- The Čech–Picard descent homomorphism of an affine scheme is an isomorphism. -/
theorem toPic_bijective : Function.Bijective (toPic X) :=
  ⟨toPic_injective, toPic_surjective X⟩

end CechPic

/-- **The Čech–Picard dictionary** of an affine scheme: the definitional Čech Picard
group on pointed Zariski covers is mathlib's Picard group of invertible modules over
the global sections. -/
noncomputable def cechPicEquivPic (X : Scheme.{u}) [IsAffine X] :
    X.CechPic ≃* CommRing.Pic Γ(X, ⊤) :=
  MulEquiv.ofBijective (CechPic.toPic X) (CechPic.toPic_bijective X)

@[simp]
lemma cechPicEquivPic_apply (X : Scheme.{u}) [IsAffine X] (c : X.CechPic) :
    cechPicEquivPic X c = CechPic.toPic X c :=
  rfl

end Scheme

end AlgebraicGeometry
