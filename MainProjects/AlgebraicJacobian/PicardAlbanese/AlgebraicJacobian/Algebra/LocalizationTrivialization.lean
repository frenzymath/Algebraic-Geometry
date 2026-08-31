/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.BaseChangeTrivialization
import AlgebraicJacobian.Algebra.LocalizationCocycle

/-!
# The transition cocycle of a locally trivialized module, and its Picard class

Let `A` be a commutative ring, `N` an `A`-module, and `f : ι → A` a finite family with
localization models `S i`, `T i j`, `W i j k` away from the single, double and triple
products as in `AlgebraicJacobian.Algebra.LocalizationCocycle`.  Given trivializations
`e i : S i ⊗[A] N ≃ₗ[S i] S i` on the members of the cover, this file:

* forms the **transition cocycle** `trivializationCocycle e i j : (T i j)ˣ` — the
  transition unit between the two pushforwards of `e i` and `e j` to the overlap — and
  shows it is a Čech cover cocycle (`isCoverCocycle_trivializationCocycle`), the diagonal
  and cocycle conditions being instances of the transition-unit calculus of
  `AlgebraicJacobian.Algebra.BaseChangeTrivialization` plus the uniqueness of `A`-algebra
  maps out of localizations;
* assembles the componentwise trivializations into one over the cover algebra
  `B := ∀ i, S i` (`Module.piTrivialization`);
* proves the **descent identification** (`picClass_trivializationCocycle`): the Picard
  class of the descent cocycle associated with the transition cocycle is the class of
  `N` itself.  The compatibility of the assembled trivialization with the twisted
  descent datum reduces, through the identification `B ⊗[A] B ≃ ∀ p, T p.1 p.2`, to the
  defining property of the transition units, and uniqueness of descent
  (`Module.DescentDatum.equivDescended`) identifies the descended module with `N`.

This is the algebraic heart of the surjectivity of the Čech–Picard descent homomorphism
(`AlgebraicGeometry.Scheme.CechPic.toPic_surjective`).
-/

universe u

open TensorProduct

/-! ## Assembling componentwise trivializations over a finite product -/

namespace Module

variable {A : Type u} [CommRing A] {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type u} [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
variable {N : Type u} [AddCommGroup N] [Module A N]

/-- The canonical `A`-linear distribution of a base change over a finite product of
`A`-algebras. -/
noncomputable def piBaseChangeDistrib :
    ((∀ i, S i) ⊗[A] N) ≃ₗ[A] ∀ i, S i ⊗[A] N :=
  (TensorProduct.comm A _ _).trans ((TensorProduct.piRight A A N S).trans
    (LinearEquiv.piCongrRight fun i ↦ TensorProduct.comm A N (S i)))

@[simp]
lemma piBaseChangeDistrib_tmul (b : ∀ i, S i) (n : N) :
    piBaseChangeDistrib (S := S) (b ⊗ₜ[A] n) = fun i ↦ b i ⊗ₜ[A] n := by
  funext i
  simp [piBaseChangeDistrib, TensorProduct.piRight_apply]

variable (e : ∀ i, (S i ⊗[A] N) ≃ₗ[S i] S i)

/-- The `A`-linear map underlying `piTrivialization`: `n ↦ (i ↦ e i (1 ⊗ₜ n))`. -/
private noncomputable def piTrivializationBase : N →ₗ[A] ∀ i, S i where
  toFun n i := e i (1 ⊗ₜ n)
  map_add' n m := by
    funext i
    simp only [Pi.add_apply, TensorProduct.tmul_add, map_add]
  map_smul' a n := by
    funext i
    simp only [RingHom.id_apply, Pi.smul_apply, TensorProduct.tmul_smul]
    exact LinearMapClass.map_smul_of_tower (e i) a _

/-- Componentwise trivializations of `N` over a finite family of `A`-algebras assemble
into a trivialization over the product algebra, sending `1 ⊗ₜ n` to
`fun i ↦ e i (1 ⊗ₜ n)` (`piTrivialization_one_tmul`). -/
noncomputable def piTrivialization :
    ((∀ i, S i) ⊗[A] N) ≃ₗ[∀ i, S i] ∀ i, S i := by
  refine LinearEquiv.ofBijective
    (LinearMap.liftBaseChange (∀ i, S i) (piTrivializationBase e)) ?_
  have key : ⇑(LinearMap.liftBaseChange (∀ i, S i) (piTrivializationBase e))
      = (fun v i ↦ e i (v i)) ∘ ⇑(piBaseChangeDistrib (S := S)) := by
    funext x
    induction x with
    | zero => exact funext fun i ↦ by simp
    | tmul b n =>
        funext i
        simp only [LinearMap.liftBaseChange_tmul, Function.comp_apply,
          piBaseChangeDistrib_tmul]
        have hb : (b i ⊗ₜ[A] n : S i ⊗[A] N) = b i • ((1 : S i) ⊗ₜ[A] n) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hb, map_smul]
        simp [piTrivializationBase, smul_eq_mul]
    | add x y hx hy =>
        rw [map_add, hx, hy]
        funext i
        simp only [Function.comp_apply, map_add, Pi.add_apply]
  rw [key]
  exact ((Equiv.piCongrRight fun i ↦ (e i).toEquiv).bijective).comp
    (piBaseChangeDistrib (S := S)).bijective

@[simp]
lemma piTrivialization_one_tmul (n : N) :
    piTrivialization e (1 ⊗ₜ n) = fun i ↦ e i (1 ⊗ₜ n) := by
  change LinearMap.liftBaseChange (∀ i, S i) (piTrivializationBase e) (1 ⊗ₜ n) = _
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end Module

/-! ## The transition cocycle on a finite localization cover -/

namespace IsLocalization.AwayCover

open Module

variable {A : Type u} [CommRing A] {ι : Type u}
variable (f : ι → A)
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
  [∀ i, IsLocalization.Away (f i) (S i)]
variable (T : ι → ι → Type u) [∀ i j, CommRing (T i j)] [∀ i j, Algebra A (T i j)]
  [∀ i j, IsLocalization.Away (f i * f j) (T i j)]
variable (W : ι → ι → ι → Type u) [∀ i j k, CommRing (W i j k)]
  [∀ i j k, Algebra A (W i j k)]
  [∀ i j k, IsLocalization.Away (f i * (f j * f k)) (W i j k)]
variable {N : Type u} [AddCommGroup N] [Module A N]

variable (e : ∀ i, (S i ⊗[A] N) ≃ₗ[S i] S i)

/-- The **transition cocycle** of a family of trivializations on a finite localization
cover: on each overlap, the transition unit between the pushforwards of the two
trivializations. -/
noncomputable def trivializationCocycle (i j : ι) : (T i j)ˣ :=
  transitionUnit (trivializationPush (inclLeft f S T i j) (e i))
    (trivializationPush (inclRight f S T i j) (e j))

/-- The defining property of the transition cocycle on the tensors `1 ⊗ₜ n`. -/
lemma trivializationCocycle_mul (i j : ι) (n : N) :
    (trivializationCocycle f S T e i j).val * inclLeft f S T i j (e i (1 ⊗ₜ n))
      = inclRight f S T i j (e j (1 ⊗ₜ n)) := by
  have h := transitionUnit_mul_apply (trivializationPush (inclLeft f S T i j) (e i))
    (trivializationPush (inclRight f S T i j) (e j)) (1 ⊗ₜ n)
  rwa [trivializationPush_one_tmul, trivializationPush_one_tmul] at h

/-- The transition cocycle is a Čech cover cocycle: the diagonal and cocycle conditions
follow from the transition-unit calculus and uniqueness of `A`-algebra maps out of
localizations. -/
theorem isCoverCocycle_trivializationCocycle :
    IsCoverCocycle (f := f) (S := S) (W := W) (trivializationCocycle f S T e) := by
  constructor
  · -- diagonal: the two pushforwards to `T i i` agree, so the transition unit is `1`
    intro i
    have hlr : inclLeft f S T i i = inclRight f S T i i :=
      (IsLocalization.algHom_subsingleton (Submonoid.powers (f i))).elim _ _
    have h1 : trivializationCocycle f S T e i i = 1 := by
      rw [trivializationCocycle, hlr, transitionUnit_self]
    rw [h1, Units.val_one, map_one]
  · -- cocycle: push all three transition units to the triple overlap and telescope
    intro i j k
    -- canonical pushforwards of the three trivializations to the triple overlap
    set ρi : S i →ₐ[A] W i j k := (face₁₂ f T W i j k).comp (inclLeft f S T i j) with hρi
    set ρj : S j →ₐ[A] W i j k := (face₁₂ f T W i j k).comp (inclRight f S T i j) with hρj
    set ρk : S k →ₐ[A] W i j k := (face₂₃ f T W i j k).comp (inclRight f S T j k) with hρk
    have key : Units.map (face₂₃ f T W i j k).toRingHom.toMonoidHom
          (trivializationCocycle f S T e j k)
        * Units.map (face₁₂ f T W i j k).toRingHom.toMonoidHom
            (trivializationCocycle f S T e i j)
        = Units.map (face₁₃ f T W i j k).toRingHom.toMonoidHom
            (trivializationCocycle f S T e i k) := by
      rw [trivializationCocycle, trivializationCocycle, trivializationCocycle,
        ← map_transitionUnit, ← map_transitionUnit, ← map_transitionUnit,
        trivializationPush_trivializationPush, trivializationPush_trivializationPush,
        trivializationPush_trivializationPush, trivializationPush_trivializationPush,
        trivializationPush_trivializationPush, trivializationPush_trivializationPush,
        show (face₂₃ f T W i j k).comp (inclLeft f S T j k) = ρj from
          (IsLocalization.algHom_subsingleton (Submonoid.powers (f j))).elim _ _,
        show (face₂₃ f T W i j k).comp (inclRight f S T j k) = ρk from rfl,
        show (face₁₂ f T W i j k).comp (inclLeft f S T i j) = ρi from rfl,
        show (face₁₂ f T W i j k).comp (inclRight f S T i j) = ρj from rfl,
        show (face₁₃ f T W i j k).comp (inclLeft f S T i k) = ρi from
          (IsLocalization.algHom_subsingleton (Submonoid.powers (f i))).elim _ _,
        show (face₁₃ f T W i j k).comp (inclRight f S T i k) = ρk from
          (IsLocalization.algHom_subsingleton (Submonoid.powers (f k))).elim _ _]
      exact transitionUnit_mul_transitionUnit _ _ _
    have hval := congrArg Units.val key
    simp only [Units.val_mul, Units.coe_map] at hval
    exact hval

/-! ## The Picard class of the transition cocycle -/

variable [Fintype ι] [DecidableEq ι]

/-- **Descent identification for locally trivialized modules**: the Picard class of the
descent cocycle associated with the transition cocycle of a family of trivializations of
`N` is the class of `N`.  The assembled trivialization over the cover algebra
intertwines the twisted descent datum of the transition cocycle with the canonical datum
on `B ⊗[A] N` — componentwise this is the defining property of the transition units —
so uniqueness of descent identifies the descended module with `N`. -/
theorem picClass_trivializationCocycle [Module.Invertible A N]
    [Module.FaithfullyFlat A (∀ i, S i)] :
    (isDescentCocycle_cocycleUnit f S T W
        (isCoverCocycle_trivializationCocycle f S T W e)).picClass
      = CommRing.Pic.mk A N := by
  set B := ∀ i, S i with hB
  set u : (B ⊗[A] B)ˣ := cocycleUnit f S T (trivializationCocycle f S T e) with hu'
  set hu := isDescentCocycle_cocycleUnit f S T W
    (isCoverCocycle_trivializationCocycle f S T W e)
  set ψ : (B ⊗[A] N) ≃ₗ[B] B := piTrivialization e with hψ
  -- the values of the assembled trivialization on `1 ⊗ₜ n` lie in the descended module
  have hkey : ∀ n : N,
      u.val * descentIncl₁ A B (ψ (1 ⊗ₜ n)) = descentIncl₂ A B (ψ (1 ⊗ₜ n)) := by
    intro n
    apply (piDoubleEquiv f S T).injective
    rw [map_mul, piDoubleEquiv_cocycleUnit_val, piDoubleEquiv_descentIncl₁,
      piDoubleEquiv_descentIncl₂]
    funext p
    rw [Pi.mul_apply]
    have hval : ψ (1 ⊗ₜ n) = fun i ↦ e i (1 ⊗ₜ n) := piTrivialization_one_tmul e n
    rw [hval]
    exact trivializationCocycle_mul f S T e p.1 p.2 n
  -- the assembled trivialization intertwines the two descent data
  have he : ∀ x : B ⊗[A] N,
      (DescentDatum.ofUnit u hu).coaction (ψ x)
        = ((ψ : B ⊗[A] N →ₗ[B] B).restrictScalars A).baseChange B
            ((DescentDatum.baseChange A B N).coaction x) := by
    intro x
    induction x with
    | zero => simp
    | tmul b n =>
        have hb : (b ⊗ₜ[A] n : B ⊗[A] N) = b • ((1 : B) ⊗ₜ[A] n) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        set s : B := ψ (1 ⊗ₜ n) with hs
        have hψb : ψ (b ⊗ₜ n) = b * s := by
          rw [hb, map_smul, smul_eq_mul]
        rw [hψb, ofUnit_coaction, unitCoaction_apply, DescentDatum.baseChange_coaction,
          LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
        have hmul : ((b * s) ⊗ₜ[A] (1 : B) : B ⊗[A] B)
            = (b ⊗ₜ[A] (1 : B)) * (s ⊗ₜ[A] (1 : B)) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        have hkey' : u.val * (s ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[A] s := hkey n
        calc u.val * (b * s) ⊗ₜ[A] (1 : B)
            = (b ⊗ₜ[A] (1 : B)) * (u.val * (s ⊗ₜ[A] (1 : B))) := by
              rw [hmul]; ring
          _ = (b ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] s) := by rw [hkey']
          _ = b ⊗ₜ[A] ψ ((1 : B) ⊗ₜ[A] n) := by
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hs]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  -- uniqueness of descent identifies the descended module with `N`
  have equivN : N ≃ₗ[A] hu.descended :=
    (DescentDatum.ofUnit u hu).equivDescended ψ he
  exact CommRing.Pic.mk_eq_mk_iff.mpr ⟨equivN.symm⟩

end IsLocalization.AwayCover
