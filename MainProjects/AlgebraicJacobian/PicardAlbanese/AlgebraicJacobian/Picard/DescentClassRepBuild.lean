/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DescentClassCocycle
import AlgebraicJacobian.Algebra.GeneratorUnit

/-!
# Construction of the Čech representative of a descended class (ζ3 brick M, part 2)

For a faithfully flat `A → B` and a global unit `w` on `Spec (B ⊗[A] B)` whose
`ΓSpecIso`-avatar is a descent cocycle, this file **constructs** a
`AlgebraicGeometry.Over.DescentClassRep w hW`: a trivializing family `F` of the
`Γ(Spec A, ⊤)`-avatar of the descended module supplies the cover and cocycle; `μ a` is
the evaluation (`Over.evalT`) of the collapsed generator `cancelN (F.triv a).symm 1` —
a unit by `Module.isUnit_map_rTensor_generator` since the evaluation factors through
the base-changed descent equivalence (`Module.descentMulEval`); `ratio` is
`Over.evalT_ratio` at `descended_tensorInr_eq`; `transition` is the transition-unit
action on generators, pushed through `cancelN` and `evalT`.

Main declaration: `AlgebraicGeometry.Over.descentClassRep`.  All data is carried in
declaration signatures — never in `variable` commands with local-notation types.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B]

set_option quotPrecheck false in
local notation "SA" => (overSpec k A).left
set_option quotPrecheck false in
local notation "SB" => (overSpec k B).left
set_option quotPrecheck false in
local notation "Sq" => (overSpec k (B ⊗[A] B)).left
set_option quotPrecheck false in
local notation "gS" => (Over.overSpecMap ((Algebra.ofId A B).restrictScalars k)).left
set_option quotPrecheck false in
local notation "q₁" => (Over.overSpecMap (tensorInl (A := A) (B := B))).left
set_option quotPrecheck false in
local notation "q₂" => (Over.overSpecMap (tensorInr (A := A) (B := B))).left

attribute [local instance] specSectionsAlgebra overSpecSectionsAlgebra
  overSpecSectionsAlgebraSq algebraA_sections isScalarTower_sections
  isScalarTower_sections_basicOpen Over.overSpecSectionsAlgebraA isAffineOverSpecA
  Over.isScalarTower_sectionsA_basicOpen

/-- The scalar tower `A → B → Γ(Spec B, U)`, re-keyed on the algebra instances active
in this file (the `WitnessAway` tower is not found at reducible transparency). -/
noncomputable local instance isScalarTower_sectionsB (U : ((overSpec k B).left).Opens) :
    IsScalarTower A B Γ((overSpec k B).left, U) :=
  IsScalarTower.of_algebraMap_eq' rfl

namespace Over

variable [Module.FaithfullyFlat A B]

/-! ## The evaluation as the base-changed descent equivalence -/

/-- The `g_S`-pullback intertwines the canonical `A`-algebra structures. -/
private lemma appLE_algebraMapA (V : (SA).Opens) (U : (SB).Opens)
    (e : U ≤ (gS) ⁻¹ᵁ V) (a : A) :
    ((gS).appLE V U e).hom (algebraMap A Γ(SA, V) a) = algebraMap A Γ(SB, U) a := by
  change ((gS).appLE V U e).hom
      (((SA).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (.of A)).inv.hom a))
    = ((SB).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (.of B)).inv.hom (algebraMap A B a))
  rw [appLE_restrict_top]
  exact congrArg _ (ΓSpecIso_inv_appTop (CommRingCat.ofHom (algebraMap A B)) a)

/-- The `g_S`-pullback of sections as an `A`-linear map. -/
private noncomputable def appLEA (V : (SA).Opens) (U : (SB).Opens)
    (e : U ≤ (gS) ⁻¹ᵁ V) : Γ(SA, V) →ₗ[A] Γ(SB, U) where
  toFun := ((gS).appLE V U e).hom
  map_add' _ _ := map_add _ _ _
  map_smul' a s := by
    simp only [RingHom.id_apply, Algebra.smul_def, map_mul, appLE_algebraMapA V U e a]

/-- The descent equivalence `B ⊗[A] Mod ≃ₗ[B] B` of the descended module. -/
private noncomputable def dEq (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w)) :
    B ⊗[A] ↥(hW.descended) ≃ₗ[B] B :=
  (Module.DescentDatum.ofUnit _ hW).descentEquiv

private lemma dEq_one_tmul (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (m : ↥(hW.descended)) :
    dEq w hW ((1 : B) ⊗ₜ[A] m) = (m : B) := by
  show (Module.DescentDatum.ofUnit _ hW).descentEquiv ((1 : B) ⊗ₜ[A] m) = (m : B)
  rw [Module.DescentDatum.descentEquiv_tmul, one_smul]

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
/-- The evaluation map is the base-changed descent equivalence applied to the
`rTensor`-pushed tensor. -/
private lemma evalT_eq_mulEval (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (V : (SA).Opens) (U : (SB).Opens) (e : U ≤ (gS) ⁻¹ᵁ V)
    (x : Γ(SA, V) ⊗[A] ↥(hW.descended)) :
    evalT (hW.descended) V U e x
      = (Module.descentMulEval (R' := Γ(SB, U)) A ↥(hW.descended)
          (dEq w hW)).toLinearMap
          (LinearMap.rTensor ↥(hW.descended) (appLEA V U e) x) := by
  induction x with
  | zero => simp only [map_zero]
  | tmul s m =>
      rw [evalT_tmul, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
        Module.descentMulEval_tmul, dEq_one_tmul w hW m, Algebra.smul_def]
      exact mul_comm _ _
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ## The trivializing units -/

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
/-- The value of the trivializing unit at `a`: the evaluation of the collapsed
generator of the trivialization. -/
private noncomputable def μval (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))) (a : SA) :
    Γ(SB, (gS) ⁻¹ᵁ (SA).basicOpen (F.sec a)) :=
  evalT (hW.descended) ((SA).basicOpen (F.sec a)) ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a))
    le_rfl (cancelN (k := k) w hW (F.sec a) ((F.triv a).symm 1))

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
private lemma isUnit_μval (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))) (a : SA) :
    IsUnit (μval w hW F a) := by
  have h := Module.isUnit_map_rTensor_generator
    (φ := ((gS).appLE ((SA).basicOpen (F.sec a))
      ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a)) le_rfl).hom)
    (φₗ := appLEA _ _ le_rfl) (fun _ => rfl)
    (F.triv a) (cancelN (k := k) w hW (F.sec a))
    (Module.descentMulEval (R' := Γ(SB, (gS) ⁻¹ᵁ (SA).basicOpen (F.sec a))) A
      ↥(hW.descended) (dEq w hW)).toLinearMap
    (Module.descentMulEval (R' := Γ(SB, (gS) ⁻¹ᵁ (SA).basicOpen (F.sec a))) A
      ↥(hW.descended) (dEq w hW)).surjective
  rw [← evalT_eq_mulEval w hW] at h
  exact h

/-- The trivializing unit at `a`. -/
private noncomputable def μunit (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))) (a : SA) :
    Γ(SB, (gS) ⁻¹ᵁ (SA).basicOpen (F.sec a))ˣ :=
  (isUnit_μval w hW F a).unit

private lemma μunit_val (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))) (a : SA) :
    (μunit w hW F a).val = μval w hW F a :=
  (isUnit_μval w hW F a).unit_spec

/-! ## The transition identity on values -/

private lemma basicOpen_mul_le_left
    (f g : Γ(SA, ⊤)) :
    (SA).basicOpen (f * g) ≤ (SA).basicOpen f :=
  ((SA).basicOpen_mul f g).trans_le inf_le_left

private lemma basicOpen_mul_le_right
    (f g : Γ(SA, ⊤)) :
    (SA).basicOpen (f * g) ≤ (SA).basicOpen g :=
  ((SA).basicOpen_mul f g).trans_le inf_le_right

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
/-- Restriction of the trivializing value to a smaller basic open is the evaluation of
the correspondingly restricted generator. -/
private lemma μval_res (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended)))
    (a : SA) (g' : Γ(SA, ⊤))
    (hle : (SA).basicOpen g' ≤ (SA).basicOpen (F.sec a)) :
    ((SB).presheaf.map (homOfLE ((gS).preimage_mono hle)).op).hom (μval w hW F a)
      = evalT (hW.descended) ((SA).basicOpen g') ((gS) ⁻¹ᵁ (SA).basicOpen g') le_rfl
          (cancelN (k := k) w hW g'
            (LinearMap.rTensor _ ((SA).basicRes (F.sec a) g' hle).toLinearMap
              ((F.triv a).symm 1))) := by
  refine (evalT_res (hW.descended) le_rfl le_rfl hle ((gS).preimage_mono hle)
    ((((SA).basicRes (F.sec a) g' hle).toLinearMap).restrictScalars A)
    (fun _ => rfl) _).trans ?_
  exact congrArg _ (cancelN_rTensor (k := k) w hW (F.sec a) g' hle ((F.triv a).symm 1))

private lemma inclLeft_eq_basicRes
    (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))) (a b : SA) :
    IsLocalization.AwayCover.inclLeft (A := Γ(SA, ⊤)) (f := F.sec)
        (S := fun x ↦ Γ(SA, (SA).basicOpen (F.sec x)))
        (T := fun x y ↦ Γ(SA, (SA).basicOpen (F.sec x * F.sec y))) a b
      = (SA).basicRes (F.sec a) (F.sec a * F.sec b)
          (basicOpen_mul_le_left (F.sec a) (F.sec b)) :=
  (SA).basicOpen_algHom_ext (F.sec a) _ _

private lemma inclRight_eq_basicRes
    (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))) (a b : SA) :
    IsLocalization.AwayCover.inclRight (A := Γ(SA, ⊤)) (f := F.sec)
        (S := fun x ↦ Γ(SA, (SA).basicOpen (F.sec x)))
        (T := fun x y ↦ Γ(SA, (SA).basicOpen (F.sec x * F.sec y))) a b
      = (SA).basicRes (F.sec b) (F.sec a * F.sec b)
          (basicOpen_mul_le_right (F.sec a) (F.sec b)) :=
  (SA).basicOpen_algHom_ext (F.sec b) _ _

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
/-- The transition cocycle, through `basicRes`-pushed trivializations. -/
private lemma transition_eq_push (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))) (a b : SA) :
    F.transition a b
      = Module.transitionUnit
          (Module.trivializationPush
            ((SA).basicRes (F.sec a) (F.sec a * F.sec b)
              (basicOpen_mul_le_left (F.sec a) (F.sec b)))
            (F.triv a))
          (Module.trivializationPush
            ((SA).basicRes (F.sec b) (F.sec a * F.sec b)
              (basicOpen_mul_le_right (F.sec a) (F.sec b)))
            (F.triv b)) := by
  have h : F.transition a b
      = Module.transitionUnit
          (Module.trivializationPush
            (IsLocalization.AwayCover.inclLeft (A := Γ(SA, ⊤)) (f := F.sec)
              (S := fun x ↦ Γ(SA, (SA).basicOpen (F.sec x)))
              (T := fun x y ↦ Γ(SA, (SA).basicOpen (F.sec x * F.sec y))) a b)
            (F.triv a))
          (Module.trivializationPush
            (IsLocalization.AwayCover.inclRight (A := Γ(SA, ⊤)) (f := F.sec)
              (S := fun x ↦ Γ(SA, (SA).basicOpen (F.sec x)))
              (T := fun x y ↦ Γ(SA, (SA).basicOpen (F.sec x * F.sec y))) a b)
            (F.triv b)) := rfl
  refine h.trans ?_
  exact congrArg₂
    (fun (φ : Γ(SA, (SA).basicOpen (F.sec a))
          →ₐ[Γ(SA, ⊤)] Γ(SA, (SA).basicOpen (F.sec a * F.sec b)))
        (ψ : Γ(SA, (SA).basicOpen (F.sec b))
          →ₐ[Γ(SA, ⊤)] Γ(SA, (SA).basicOpen (F.sec a * F.sec b))) =>
      Module.transitionUnit (Module.trivializationPush φ (F.triv a))
        (Module.trivializationPush ψ (F.triv b)))
    (inclLeft_eq_basicRes w hW F a b) (inclRight_eq_basicRes w hW F a b)

set_option maxHeartbeats 800000 in
-- the collapsed tensor lives over the composite section-ring instance stack
/-- `cancelN` commutes with scalars (explicit instantiation of `map_smul`). -/
private lemma cancelN_smul (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (g : Γ(SA, ⊤)) (c : Γ(SA, (SA).basicOpen g))
    (y : Γ(SA, (SA).basicOpen g) ⊗[Γ(SA, ⊤)] (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))) :
    cancelN (k := k) w hW g (c • y) = c • cancelN (k := k) w hW g y :=
  map_smul (cancelN (k := k) w hW g) c y

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
/-- The transition-unit action on the `basicRes`-restricted generators. -/
private lemma generator_transition (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))) (a b : SA) :
    LinearMap.rTensor _ ((SA).basicRes (F.sec a) (F.sec a * F.sec b)
        (basicOpen_mul_le_left (F.sec a) (F.sec b))).toLinearMap ((F.triv a).symm 1)
      = (F.transition a b).val
          • LinearMap.rTensor _ ((SA).basicRes (F.sec b) (F.sec a * F.sec b)
              (basicOpen_mul_le_right (F.sec a) (F.sec b))).toLinearMap
            ((F.triv b).symm 1) := by
  have h1 := Module.transitionUnit_smul_symm_one
    (Module.trivializationPush
      ((SA).basicRes (F.sec a) (F.sec a * F.sec b)
        (basicOpen_mul_le_left (F.sec a) (F.sec b)))
      (F.triv a))
    (Module.trivializationPush
      ((SA).basicRes (F.sec b) (F.sec a * F.sec b)
        (basicOpen_mul_le_right (F.sec a) (F.sec b)))
      (F.triv b))
  have h2 := congrArg
    (fun u : Γ(SA, (SA).basicOpen (F.sec a * F.sec b))ˣ =>
      u.val • (Module.trivializationPush
        ((SA).basicRes (F.sec b) (F.sec a * F.sec b)
          (basicOpen_mul_le_right (F.sec a) (F.sec b)))
        (F.triv b)).symm 1)
    (transition_eq_push w hW F a b)
  refine (Module.trivializationPush_symm_one _ (F.triv a)).symm.trans
    ((h1.trans h2.symm).trans ?_)
  exact congrArg (fun z => (F.transition a b).val • z)
    (Module.trivializationPush_symm_one _ (F.triv b))

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
/-- **The transition identity on values**: over the double overlap `D(sec a ⋅ sec b)`,
the restricted values differ by the `g_S`-pullback of the transition unit. -/
private lemma transition_val (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))) (a b : SA) :
    ((SB).presheaf.map
        (homOfLE ((gS).preimage_mono
          (basicOpen_mul_le_left (F.sec a) (F.sec b)))).op).hom
        (μval w hW F a)
      = ((gS).appLE ((SA).basicOpen (F.sec a * F.sec b))
            ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a * F.sec b)) le_rfl).hom
          ((F.transition a b).val)
        * ((SB).presheaf.map
            (homOfLE ((gS).preimage_mono
              (basicOpen_mul_le_right (F.sec a) (F.sec b)))).op).hom
            (μval w hW F b) := by
  refine (μval_res w hW F a _ (basicOpen_mul_le_left (F.sec a) (F.sec b))).trans ?_
  refine (congrArg
    (fun z => evalT (hW.descended) ((SA).basicOpen (F.sec a * F.sec b))
      ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a * F.sec b)) le_rfl
      (cancelN (k := k) w hW (F.sec a * F.sec b) z))
    (generator_transition w hW F a b)).trans ?_
  refine (congrArg
    (evalT (hW.descended) ((SA).basicOpen (F.sec a * F.sec b))
      ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a * F.sec b)) le_rfl)
    (cancelN_smul w hW (F.sec a * F.sec b) (F.transition a b).val _)).trans ?_
  refine (evalT_smul (hW.descended) ((SA).basicOpen (F.sec a * F.sec b))
    ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a * F.sec b)) le_rfl
    (F.transition a b).val _).trans ?_
  exact congrArg
    (fun z => ((gS).appLE ((SA).basicOpen (F.sec a * F.sec b))
      ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a * F.sec b)) le_rfl).hom
      ((F.transition a b).val) * z)
    (μval_res w hW F b _ (basicOpen_mul_le_right (F.sec a) (F.sec b))).symm

/-! ## Assembly -/

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
/-- The `ratio` field of the representative. -/
private lemma ratio_build (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended)))
    (a : SA) (O : (Sq).Opens)
    (e₁ : O ≤ (q₁) ⁻¹ᵁ ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a)))
    (e₂ : O ≤ (q₂) ⁻¹ᵁ ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a))) :
    (q₂).unitsAppLE ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a)) O e₂ (μunit w hW F a)
      = (Sq).unitsRestrict (le_top : O ≤ ⊤) w
        * (q₁).unitsAppLE ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a)) O e₁
            (μunit w hW F a) := by
  apply Units.ext
  show ((q₂).appLE ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a)) O e₂).hom (μunit w hW F a).val
      = ((Sq).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom w.val
        * ((q₁).appLE ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a)) O e₁).hom
            (μunit w hW F a).val
  rw [μunit_val w hW F a]
  exact evalT_ratio (hW.descended) w (fun m => descended_tensorInr_eq w hW m)
    ((SA).basicOpen (F.sec a)) ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a)) le_rfl e₁ e₂
    (cancelN (k := k) w hW (F.sec a) ((F.triv a).symm 1))

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
private lemma transition_units (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended)))
    (a b : SA) (T : (SB).Opens)
    (ha : T ≤ (gS) ⁻¹ᵁ (SA).basicOpen (F.sec a))
    (hb : T ≤ (gS) ⁻¹ᵁ (SA).basicOpen (F.sec b))
    (hT : T ≤ (gS) ⁻¹ᵁ (SA).basicOpen (F.sec a * F.sec b)) :
    (SB).unitsRestrict ha (μunit w hW F a)
      = (gS).unitsAppLE ((SA).basicOpen (F.sec a * F.sec b)) T hT (F.transition a b)
        * (SB).unitsRestrict hb (μunit w hW F b) := by
  apply Units.ext
  show ((SB).presheaf.map (homOfLE ha).op).hom (μunit w hW F a).val
      = ((gS).appLE ((SA).basicOpen (F.sec a * F.sec b)) T hT).hom
          (F.transition a b).val
        * ((SB).presheaf.map (homOfLE hb).op).hom (μunit w hW F b).val
  rw [μunit_val w hW F a, μunit_val w hW F b]
  have m1 : (SB).presheaf.map (homOfLE ((gS).preimage_mono
        (basicOpen_mul_le_left (F.sec a) (F.sec b)))).op
      ≫ (SB).presheaf.map (homOfLE hT).op
      = (SB).presheaf.map (homOfLE ha).op := by
    rw [← Functor.map_comp, ← op_comp, homOfLE_comp]
  have m2 : (SB).presheaf.map (homOfLE ((gS).preimage_mono
        (basicOpen_mul_le_right (F.sec a) (F.sec b)))).op
      ≫ (SB).presheaf.map (homOfLE hT).op
      = (SB).presheaf.map (homOfLE hb).op := by
    rw [← Functor.map_comp, ← op_comp, homOfLE_comp]
  have m3 : (gS).appLE ((SA).basicOpen (F.sec a * F.sec b))
        ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a * F.sec b)) le_rfl
      ≫ (SB).presheaf.map (homOfLE hT).op
      = (gS).appLE ((SA).basicOpen (F.sec a * F.sec b)) T hT :=
    Scheme.Hom.appLE_map _ _ _
  refine (congr($(m1).hom (μval w hW F a))).symm.trans ?_
  refine (CommRingCat.comp_apply _ _ _).trans ?_
  refine (congrArg ((SB).presheaf.map (homOfLE hT).op).hom
    (transition_val w hW F a b)).trans ?_
  refine (map_mul ((SB).presheaf.map (homOfLE hT).op).hom
    (((gS).appLE ((SA).basicOpen (F.sec a * F.sec b))
      ((gS) ⁻¹ᵁ (SA).basicOpen (F.sec a * F.sec b)) le_rfl).hom
      ((F.transition a b).val))
    (((SB).presheaf.map (homOfLE ((gS).preimage_mono
      (basicOpen_mul_le_right (F.sec a) (F.sec b)))).op).hom
      (μval w hW F b))).trans ?_
  refine congrArg₂ (· * ·) ?_ ?_
  · exact ((CommRingCat.comp_apply _ _ _).symm).trans
      (congr($(m3).hom ((F.transition a b).val)))
  · exact ((CommRingCat.comp_apply _ _ _).symm).trans
      (congr($(m2).hom (μval w hW F b)))

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
/-- The cocycle pair value as the restricted transition unit. -/
private lemma transition_mid (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended)))
    (a b : SA) (T : (SB).Opens)
    (ha : T ≤ (gS) ⁻¹ᵁ (SA).basicOpen (F.sec a))
    (hb : T ≤ (gS) ⁻¹ᵁ (SA).basicOpen (F.sec b))
    (hT : T ≤ (gS) ⁻¹ᵁ (SA).basicOpen (F.sec a * F.sec b)) :
    (gS).unitsAppLE ((SA).basicOpen (F.sec a) ⊓ (SA).basicOpen (F.sec b)) T
      ((gS).le_preimage_inf ha hb) (Scheme.unitsEvInf (F.cocycle) a b)
    = (gS).unitsAppLE ((SA).basicOpen (F.sec a * F.sec b)) T hT
        (F.transition a b) := by
  rw [show Scheme.unitsEvInf (F.cocycle) a b
      = (SA).unitsRestrict ((SA).basicOpen_mul (F.sec a) (F.sec b)).ge
          (F.transition a b)
    from F.cocycle_unitsEvInf a b]
  exact Scheme.Hom.map_unitsAppLE _ _ _ _

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
/-- The `transition` field of the representative. -/
private lemma transition_build (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended)))
    (a b : SA) (T : (SB).Opens)
    (ha : T ≤ (gS) ⁻¹ᵁ (SA).basicOpen (F.sec a))
    (hb : T ≤ (gS) ⁻¹ᵁ (SA).basicOpen (F.sec b)) :
    (SB).unitsRestrict ha (μunit w hW F a)
      = (gS).unitsAppLE ((SA).basicOpen (F.sec a) ⊓ (SA).basicOpen (F.sec b)) T
          ((gS).le_preimage_inf ha hb) (Scheme.unitsEvInf (F.cocycle) a b)
        * (SB).unitsRestrict hb (μunit w hW F b) := by
  have hT : T ≤ (gS) ⁻¹ᵁ (SA).basicOpen (F.sec a * F.sec b) := by
    rw [(SA).basicOpen_mul (F.sec a) (F.sec b)]
    exact (gS).le_preimage_inf ha hb
  exact (transition_units w hW F a b T ha hb hT).trans
    (congrArg (fun z => z * (SB).unitsRestrict hb (μunit w hW F b))
      (transition_mid w hW F a b T ha hb hT).symm)

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
/-- The construction of a `DescentClassRep` from a trivializing family. -/
noncomputable def descentClassRepOf (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w))
    (F : Scheme.TrivializingFamily (SA) (Γ(SA, ⊤) ⊗[A] ↥(hW.descended))) :
    DescentClassRep w hW where
  cover := F.cover
  cocycle := F.cocycle
  μ := μunit w hW F
  ratio := ratio_build w hW F
  transition := transition_build w hW F

set_option maxHeartbeats 1600000 in
-- the concrete section-ring instance stacks exceed the default budget
/-- **The Čech representative of a descended Picard class exists** (ζ3 brick M):
choose a trivializing family of the `Γ(Spec A, ⊤)`-avatar of the descended module. -/
noncomputable def descentClassRep (w : Γ(Sq, ⊤)ˣ)
    (hW : Module.IsDescentCocycle
      (Units.map (Scheme.ΓSpecIso (.of (B ⊗[A] B))).hom.hom.toMonoidHom w)) :
    DescentClassRep w hW :=
  descentClassRepOf w hW
    (Scheme.TrivializingFamily.nonempty
      (X := SA) (N := Γ(SA, ⊤) ⊗[A] ↥(hW.descended))).some

end Over

end AlgebraicGeometry
