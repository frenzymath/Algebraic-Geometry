/-
Copyright (c) 2026 The Mumford Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mumford Contributors
-/

import MumfordLib.GroupScheme

/-!
# Pointwise rigidity for proper group-scheme products

The closed-point slice step of Form-I rigidity is isolated here so it can be
kernel-checked independently of the later dense-open assembly.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace Mumford
namespace GroupScheme

section RigidityChain

open AlgebraicGeometry

variable {kbar : Type u} [Field kbar]

/-!
The geometric rigidity chain is kept in this file so the Milne project can use
the same scheme-level API as the Jacobian formalization without importing that
project.  The first step is the pointwise slice-constancy statement.
-/

theorem rigidity_eqAt_closedPoint_of_proper_into_affine
    [IsAlgClosed kbar]
    {X Y Z : Over (Spec (.of kbar))}
    [IsProper X.hom]
    [GeometricallyIrreducible (X ⊗ Y).hom]
    [LocallyOfFiniteType (X ⊗ Y).hom]
    [IsReduced (X ⊗ Y).left]
    [IsSeparated Z.hom]
    (f : (X ⊗ Y) ⟶ Z)
    (x₀ : 𝟙_ (Over (Spec (.of kbar))) ⟶ X)
    (U : (X ⊗ Y).left.Opens)
    (Vset : Set Y.left)
    (_hUV : (U : Set (X ⊗ Y).left) = (snd X Y).left.base ⁻¹' Vset)
    (U₀ : Z.left.Opens) (_hU₀ : IsAffineOpen U₀)
    (_hfU : ∀ u ∈ (U : Set (X ⊗ Y).left), f.left.base u ∈ U₀)
    (x : (U : (X ⊗ Y).left.Opens).toScheme)
    (_hx : x ∈ closedPoints (U : (X ⊗ Y).left.Opens).toScheme) :
    (U : (X ⊗ Y).left.Opens).toScheme.fromSpecResidueField x ≫
        ((U.ι : (U : (X ⊗ Y).left.Opens).toScheme ⟶ (X ⊗ Y).left) ≫ f.left) =
      (U : (X ⊗ Y).left.Opens).toScheme.fromSpecResidueField x ≫
        ((U.ι : (U : (X ⊗ Y).left.Opens).toScheme ⟶ (X ⊗ Y).left) ≫
          (lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) ≫ f).left) := by
  have hxc : IsClosed {x} := _hx
  set wU : (U : (X ⊗ Y).left.Opens).toScheme ⟶ Spec (CommRingCat.of kbar) :=
    U.ι ≫ (X ⊗ Y).hom with hwU
  set px : Spec (CommRingCat.of kbar) ⟶ (U : (X ⊗ Y).left.Opens).toScheme :=
    pointOfClosedPoint wU x hxc with hpx
  rw [← cancel_epi (Spec.map (residueFieldIsoBase wU x hxc).hom)]
  suffices h : px ≫ U.ι ≫ Over.Hom.left f =
      px ≫ U.ι ≫ Over.Hom.left (lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) ≫ f) by
    rw [hpx] at h
    simpa only [pointOfClosedPoint, Category.assoc] using h
  set q : Spec (CommRingCat.of kbar) ⟶ (X ⊗ Y).left := px ≫ U.ι with hq
  have hqsec : q ≫ (X ⊗ Y).hom = 𝟙 _ := by
    rw [hq, Category.assoc]
    exact pointOfClosedPoint_comp wU x hxc
  rw [Over.comp_left]
  set retract : X ⊗ Y ⟶ X ⊗ Y := lift (toUnit (X ⊗ Y) ≫ x₀) (snd X Y) with hretract
  have htoUnit : (toUnit X).left = X.hom := by simp
  set qhat : 𝟙_ (Over (Spec (CommRingCat.of kbar))) ⟶ X ⊗ Y :=
    Over.homMk q hqsec with hqhat
  have hqhatL : qhat.left = q := rfl
  set yhat : 𝟙_ (Over (Spec (CommRingCat.of kbar))) ⟶ Y := qhat ≫ snd X Y with hyhat
  set xq : 𝟙_ (Over (Spec (CommRingCat.of kbar))) ⟶ X := qhat ≫ fst X Y with hxq
  set sec : X ⟶ X ⊗ Y := lift (𝟙 X) (toUnit X ≫ yhat) with hsecdef
  clear_value qhat xq yhat
  have hIover : qhat = xq ≫ sec := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, hsecdef, lift_fst, Category.comp_id]
      exact hxq.symm
    · rw [Category.assoc, hsecdef, lift_snd, ← Category.assoc,
        toUnit_unique (xq ≫ toUnit X) (𝟙 _), Category.id_comp]
      exact hyhat.symm
  have hIIover : qhat ≫ retract = x₀ ≫ sec := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [hretract, hsecdef, Category.assoc, lift_fst, ← Category.assoc,
        toUnit_unique (qhat ≫ toUnit (X ⊗ Y)) (𝟙 _), Category.id_comp, Category.assoc,
        lift_fst, Category.comp_id]
    · rw [hretract, hsecdef, Category.assoc, lift_snd, Category.assoc, lift_snd,
        ← Category.assoc, toUnit_unique (x₀ ≫ toUnit X) (𝟙 _), Category.id_comp, hyhat]
  have hsecLfst : sec.left ≫ (fst X Y).left = 𝟙 X.left := by
    rw [← Over.comp_left, hsecdef, lift_fst, Over.id_left]
  have hyhatL : yhat.left = q ≫ (snd X Y).left := by
    rw [hyhat, Over.comp_left]
    exact congrArg (· ≫ Over.Hom.left (snd X Y)) hqhatL
  have hsecLsnd : sec.left ≫ (snd X Y).left = X.hom ≫ q ≫ (snd X Y).left := by
    rw [← Over.comp_left, hsecdef, lift_snd, ← hyhatL]
    simp [htoUnit]
  haveI : IsIntegral (X ⊗ Y).left := by
    haveI : IrreducibleSpace (X ⊗ Y).left :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton (X ⊗ Y).hom
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : IsIntegral X.left := isIntegral_of_retract sec.left (fst X Y).left hsecLfst
  haveI : IsAffine U₀.toScheme := _hU₀
  have hsecU : ∀ t : X.left, sec.left.base t ∈ (↑U : Set (X ⊗ Y).left) := by
    intro t
    rw [_hUV, Set.mem_preimage]
    have e1 : (snd X Y).left.base (sec.left.base t) =
        (snd X Y).left.base (q.base (X.hom.base t)) := by
      have h2 := congrArg (fun m : X.left ⟶ Y.left => m.base t) hsecLsnd
      simpa only [Scheme.Hom.comp_apply] using h2
    rw [e1]
    have hqmem : q.base (X.hom.base t) ∈ (↑U : Set (X ⊗ Y).left) := by
      rw [hq, Scheme.Hom.comp_apply, pointOfClosedPoint_apply, ← Scheme.Opens.range_ι]
      exact Set.mem_range_self x
    rw [_hUV, Set.mem_preimage] at hqmem
    exact hqmem
  have hrange : Set.range ((sec ≫ f).left).base ⊆ Set.range U₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    have hfin := _hfU (sec.left.base t) (hsecU t)
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hfin
  set g : X.left ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (sec ≫ f).left hrange with hgdef
  have hgfac : g ≫ U₀.ι = (sec ≫ f).left := IsOpenImmersion.lift_fac _ _ hrange
  have key : xq.left ≫ g = x₀.left ≫ g :=
    eq_comp_of_isAffine_of_properIntegral X.hom g xq.left x₀.left (Over.w xq) (Over.w x₀)
  have hqf : qhat ≫ f = xq ≫ sec ≫ f := by
    rw [← Category.assoc, ← hIover]
  have hqrf : qhat ≫ retract ≫ f = x₀ ≫ sec ≫ f := by
    rw [← Category.assoc, hIIover, Category.assoc]
  have hxqf : q ≫ f.left = xq.left ≫ (sec ≫ f).left := by
    have h := congrArg Over.Hom.left hqf
    simp only [Over.comp_left, hqhatL] at h
    exact h
  have hx₀f : q ≫ retract.left ≫ f.left = x₀.left ≫ (sec ≫ f).left := by
    have h := congrArg Over.Hom.left hqrf
    simp only [Over.comp_left, hqhatL] at h
    exact h
  have hbridge : xq.left ≫ (sec ≫ f).left = x₀.left ≫ (sec ≫ f).left := by
    rw [← hgfac, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ U₀.ι) key
  have hgoalq : q ≫ f.left = q ≫ retract.left ≫ f.left :=
    hxqf.trans (hbridge.trans hx₀f.symm)
  rw [hq] at hgoalq
  simpa only [Category.assoc] using hgoalq

end RigidityChain

end GroupScheme
end Mumford
