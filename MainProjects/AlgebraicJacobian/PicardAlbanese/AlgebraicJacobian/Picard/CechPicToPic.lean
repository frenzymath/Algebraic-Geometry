/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicAffine

/-!
# The Čech–Picard descent homomorphism of an affine scheme

Assembly of the choice-independent Picard classes of
`AlgebraicJacobian.Picard.PicAffine` into the injective group homomorphism

* `AlgebraicGeometry.Scheme.CechPic.toPic : X.CechPic →* CommRing.Pic Γ(X, ⊤)`

for an affine scheme `X` — the homomorphism half of the Čech–Picard dictionary
(mathlib's `RingTheory.PicardGroup` TODO "exhibit isomorphism with `H¹(Spec R, 𝓞ˣ)`").
Injectivity (`CechPic.toPic_injective`) is refinement injectivity: a trivial descent
class makes the descent unit a coboundary, which glues back to a coboundary on the
pointed cover itself.  Surjectivity — trivializations of an invertible module on a basic
cover — is the remaining half of the dictionary.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Opposite TopologicalSpace CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

namespace Scheme

/-! ## The descent homomorphism -/

namespace CechPic

open PointedCover

variable (X : Scheme.{u}) [IsAffine X]

/-- The underlying function of `CechPic.toPic`: descend along a chosen basic refinement
of a chosen representative. -/
noncomputable def toPicFun : X.CechPic → CommRing.Pic Γ(X, ⊤) :=
  Quotient.lift
    (fun p : Σ 𝒰 : X.PointedCover, X.unitsH1 𝒰 ↦
      (BasicRefinement.nonempty p.1).some.pic p.2.out)
    (by
      rintro ⟨𝒰, a⟩ ⟨𝒱, b⟩ ⟨𝒲, h₁, h₂, e⟩
      -- The restrictions of the chosen representatives to `𝒲` are cohomologous:
      -- their `H¹` classes are `unitsRes h₁ a = unitsRes h₂ b`.
      refine BasicRefinement.pic_congr h₁ h₂ _ _ ((OneCocycle.class_eq_iff _ _).mp ?_)
      have ha : a.out.class = a := Quot.out_eq a
      have hb : b.out.class = b := Quot.out_eq b
      calc (a.out.res fun x ↦ homOfLE (h₁ x)).class
          = unitsRes h₁ a.out.class := rfl
        _ = unitsRes h₂ b.out.class := by rw [ha, hb]; exact e
        _ = (b.out.res fun x ↦ homOfLE (h₂ x)).class := rfl)

variable {X}

@[simp]
lemma toPicFun_mk (𝒰 : X.PointedCover) (γ : X.unitsCocycle 𝒰)
    (P : 𝒰.BasicRefinement) : toPicFun X (CechPic.mk 𝒰 γ.class) = P.pic γ := by
  -- The chosen data compare to `(P, γ)` by `BasicRefinement.pic_congr` with `𝒲 := 𝒰`
  -- (the representative `Quot.out (γ.class)` is cohomologous to `γ`).
  show (BasicRefinement.nonempty 𝒰).some.pic (Quot.out γ.class) = P.pic γ
  refine BasicRefinement.pic_congr (𝒲 := 𝒰) le_rfl le_rfl _ _
    ((OneCocycle.class_eq_iff _ _).mp ?_)
  have hγ : (Quot.out γ.class).class = γ.class := Quot.out_eq γ.class
  calc ((Quot.out γ.class).res fun x ↦ homOfLE ((le_rfl : 𝒰 ≤ 𝒰) x)).class
      = unitsRes le_rfl (Quot.out γ.class).class := rfl
    _ = unitsRes le_rfl γ.class := by rw [hγ]
    _ = (γ.res fun x ↦ homOfLE ((le_rfl : 𝒰 ≤ 𝒰) x)).class := rfl

variable (X)

/-- **The Čech–Picard descent homomorphism** of an affine scheme: from the definitional
Čech Picard group to mathlib's Picard group of the global sections, by faithfully flat
descent along finite basic covers. -/
noncomputable def toPic : X.CechPic →* CommRing.Pic Γ(X, ⊤) where
  toFun := toPicFun X
  map_one' := by
    have h : (1 : X.CechPic) = CechPic.mk ⊤ (OneCocycle.class 1) := rfl
    obtain ⟨P⟩ := BasicRefinement.nonempty (⊤ : X.PointedCover)
    rw [h, toPicFun_mk _ _ P]
    exact P.pic_one
  map_mul' x y := by
    induction x using CechPic.ind with | _ 𝒰 a =>
    induction y using CechPic.ind with | _ 𝒱 b =>
    obtain ⟨P⟩ := BasicRefinement.nonempty (𝒰 ⊓ 𝒱)
    induction a using Quot.ind with | _ γ =>
    induction b using Quot.ind with | _ δ =>
    rw [CechPic.mk_mul_mk_inf]
    have hprod : (unitsRes (inf_le_left : 𝒰 ⊓ 𝒱 ≤ 𝒰) (Quot.mk _ γ)
          * unitsRes (inf_le_right : 𝒰 ⊓ 𝒱 ≤ 𝒱) (Quot.mk _ δ) : X.unitsH1 (𝒰 ⊓ 𝒱))
        = ((γ.res fun x ↦ homOfLE ((inf_le_left : 𝒰 ⊓ 𝒱 ≤ 𝒰) x))
            * (δ.res fun x ↦ homOfLE ((inf_le_right : 𝒰 ⊓ 𝒱 ≤ 𝒱) x))).class := rfl
    have h1 : (Quot.mk _ γ : X.unitsH1 𝒰) = γ.class := rfl
    have h2 : (Quot.mk _ δ : X.unitsH1 𝒱) = δ.class := rfl
    rw [hprod, h1, h2, toPicFun_mk _ _ P,
      toPicFun_mk _ _ (P.ofLE inf_le_left), toPicFun_mk _ _ (P.ofLE inf_le_right),
      BasicRefinement.pic_ofLE inf_le_left P γ, BasicRefinement.pic_ofLE inf_le_right P δ,
      BasicRefinement.pic_mul]

variable {X}

@[simp]
lemma toPic_mk (𝒰 : X.PointedCover) (γ : X.unitsCocycle 𝒰) (P : 𝒰.BasicRefinement) :
    toPic X (CechPic.mk 𝒰 γ.class) = P.pic γ :=
  toPicFun_mk 𝒰 γ P

/-- **Injectivity of the descent homomorphism**: refinement injectivity for the Čech
Picard group against mathlib's Picard group. -/
theorem toPic_injective : Function.Injective (toPic X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using CechPic.ind with | _ 𝒰 a =>
  induction a using Quot.ind with | _ γ =>
  obtain ⟨P⟩ := BasicRefinement.nonempty 𝒰
  rw [show Quot.mk _ γ = OneCocycle.class γ from rfl] at hx ⊢
  rw [toPic_mk 𝒰 γ P] at hx
  rw [BasicRefinement.class_eq_one_of_pic_eq_one P γ hx]
  exact CechPic.mk_one 𝒰

end CechPic
end Scheme

end AlgebraicGeometry
