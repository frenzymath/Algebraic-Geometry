/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GaloisDescent.GaloisKernelCover
import AlgebraicJacobian.Picard.GaloisDescent.GaloisQuotientUniqueness
import AlgebraicJacobian.Picard.EtaleFieldCover
import Mathlib.AlgebraicGeometry.EffectiveEpi

/-!
# Descent of finite Galois quotient morphisms

The graph charts of a finite Galois action cover the kernel pair of every
finite Galois field extension.  Consequently, an equivariant morphism followed
by an invariant quotient projection equalizes that kernel pair.  Effective
descent along the finite faithfully flat field cover then supplies the full
universal property required by `IsGaloisQuotient`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicJacobian.GaloisDescent

open AlgebraicGeometry.Scheme.PicScheme

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
  (rho : SemilinearGalAction K L X f) (q : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- Equivariance and invariance of the quotient projection imply equality on
the two projections of the field-cover kernel pair. -/
theorem kernelPair_eq_of_equivariant
    (hqinv : ∀ gamma : L ≃ₐ[K] L, (rho.act gamma).hom ≫ q = q)
    (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K))
    (h : pullback t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X)
    (_hoverh : h ≫ f =
      pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (hequivh : (pullbackSemilinearGalAction K L t).IsEquivariant rho h) :
    pullback.fst
          (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap K L))))
          (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫
        h ≫ q =
      pullback.snd
          (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap K L))))
          (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫
        h ≫ q := by
  let base : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let T' : Over (Spec (CommRingCat.of K)) := Over.mk t
  let c := coverMap (k := K) (k' := L) T'
  let E := PreservesPullback.iso (Over.forget (Spec (CommRingCat.of K))) c c
  have hc : (Over.forget (Spec (CommRingCat.of K))).map c =
      pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap K L))) := rfl
  let Ec := pullback.congrHom hc hc
  let E' := E ≪≫ Ec
  apply (cancel_epi E'.hom).1
  apply coverSelfSection_hom_ext T'
  intro gamma
  simp only [E', E, Ec, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
    Category.comp_id, PreservesPullback.iso_hom_fst_assoc,
    PreservesPullback.iso_hom_snd_assoc]
  simp only [Over.forget_map]
  dsimp only [c]
  have hfst := congrArg Over.Hom.left
    (coverSelfSection_fst (k := K) (k' := L) T' gamma)
  have hsnd := congrArg Over.Hom.left
    (coverSelfSection_snd (k := K) (k' := L) T' gamma)
  simp only [Over.comp_left, Over.id_left] at hfst hsnd
  simp only [← Category.assoc, hfst, hsnd, Category.id_comp]
  change h ≫ q = twistLeft T' gamma ≫ h ≫ q
  have htwist : twistLeft T' gamma = pullbackGalMap K L t gamma⁻¹ := rfl
  have heq : pullbackGalMap K L t gamma⁻¹ ≫ h =
      h ≫ (rho.act gamma⁻¹).hom := by
    simpa only [pullbackSemilinearGalAction_act_hom] using hequivh gamma⁻¹
  symm
  calc
    twistLeft T' gamma ≫ h ≫ q =
        pullbackGalMap K L t gamma⁻¹ ≫ h ≫ q :=
      congrArg (fun m => m ≫ h ≫ q) htwist
    _ = (pullbackGalMap K L t gamma⁻¹ ≫ h) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = (h ≫ (rho.act gamma⁻¹).hom) ≫ q :=
      congrArg (fun m => m ≫ q) heq
    _ = h ≫ ((rho.act gamma⁻¹).hom ≫ q) := Category.assoc _ _ _
    _ = h ≫ q := congrArg (fun m => h ≫ m) (hqinv gamma⁻¹)

variable {g : Y ⟶ Spec (CommRingCat.of K)}

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A kernel-pair equality descends an equivariant field-valued morphism and
gives its unique factorization through the proposed quotient. -/
theorem galoisQuotientUniversal_of_kernelPair
    (e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅ X)
    (hover : e.hom ≫ f =
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (hprojection : e.inv ≫
      pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L))) = q)
    (hkernel : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K))
      (h : pullback t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X),
      h ≫ f = pullback.snd t
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) →
      (pullbackSemilinearGalAction K L t).IsEquivariant rho h →
      pullback.fst
          (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap K L))))
          (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫
          h ≫ q =
        pullback.snd
          (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap K L))))
          (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫
          h ≫ q) :
    ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K))
      (h : pullback t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X),
      h ≫ f = pullback.snd t
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) →
      (pullbackSemilinearGalAction K L t).IsEquivariant rho h →
      ∃! v : {v : T ⟶ Y // v ≫ g = t},
        pullbackBaseChange K L g t v.1 v.2 ≫ e.hom = h := by
  intro T t h hoverh hequivh
  let base : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let TL : Scheme.{u} := pullback t base
  let p : TL ⟶ T := pullback.fst t base
  let r : TL ⟶ Y := h ≫ q
  have hkernel' : pullback.fst p p ≫ r = pullback.snd p p ≫ r := by
    exact hkernel T t h hoverh hequivh
  have hdesc : ∀ {Z : Scheme.{u}} (a b : Z ⟶ TL),
      a ≫ p = b ≫ p → a ≫ r = b ≫ r := by
    intro Z a b hab
    let z : Z ⟶ pullback p p := pullback.lift a b hab
    calc
      a ≫ r = (z ≫ pullback.fst p p) ≫ r := by rw [pullback.lift_fst]
      _ = z ≫ (pullback.fst p p ≫ r) := Category.assoc _ _ _
      _ = z ≫ (pullback.snd p p ≫ r) :=
        congrArg (fun m => z ≫ m) hkernel'
      _ = (z ≫ pullback.snd p p) ≫ r := (Category.assoc _ _ _).symm
      _ = b ≫ r := by rw [pullback.lift_snd]
  haveI : Flat p := by
    dsimp [p, TL, base]
    infer_instance
  haveI : Surjective p := by
    dsimp [p, TL, base]
    exact Scheme.surjective_pullback_fst_specMap K L T t
  let u0 : T ⟶ Y := EffectiveEpi.desc p r hdesc
  have hfac : p ≫ u0 = r := EffectiveEpi.fac p r hdesc
  have hqbase : q ≫ g = f ≫ base := by
    rw [← hprojection]
    simp only [Category.assoc]
    rw [pullback.condition]
    rw [← hover]
    simp [base]
  have huover : u0 ≫ g = t := by
    apply (cancel_epi p).1
    calc
      p ≫ (u0 ≫ g) = (p ≫ u0) ≫ g := (Category.assoc _ _ _).symm
      _ = r ≫ g := congrArg (fun m => m ≫ g) hfac
      _ = (h ≫ q) ≫ g := rfl
      _ = h ≫ (q ≫ g) := Category.assoc _ _ _
      _ = h ≫ (f ≫ base) := congrArg (fun m => h ≫ m) hqbase
      _ = (h ≫ f) ≫ base := (Category.assoc _ _ _).symm
      _ = pullback.snd t base ≫ base :=
        congrArg (fun m => m ≫ base) hoverh
      _ = p ≫ t := pullback.condition.symm
  let u : {v : T ⟶ Y // v ≫ g = t} := ⟨u0, huover⟩
  have hbc : pullbackBaseChange K L g t u.1 u.2 = h ≫ e.inv := by
    apply pullback.hom_ext
    · rw [pullbackBaseChange_fst]
      change p ≫ u0 = (h ≫ e.inv) ≫ pullback.fst g base
      calc
        p ≫ u0 = r := hfac
        _ = h ≫ q := rfl
        _ = h ≫ (e.inv ≫ pullback.fst g base) :=
          congrArg (fun m => h ≫ m) hprojection.symm
        _ = (h ≫ e.inv) ≫ pullback.fst g base :=
          (Category.assoc _ _ _).symm
    · rw [pullbackBaseChange_snd]
      change pullback.snd t base = (h ≫ e.inv) ≫ pullback.snd g base
      have hinverseSnd : e.inv ≫ pullback.snd g base = f := by
        rw [← hover]
        simp
      calc
        pullback.snd t base = h ≫ f := hoverh.symm
        _ = h ≫ (e.inv ≫ pullback.snd g base) :=
          congrArg (fun m => h ≫ m) hinverseSnd.symm
        _ = (h ≫ e.inv) ≫ pullback.snd g base :=
          (Category.assoc _ _ _).symm
  refine ⟨u, ?_, ?_⟩
  · change pullbackBaseChange K L g t u.1 u.2 ≫ e.hom = h
    rw [hbc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro v hv
    apply Subtype.ext
    apply (cancel_epi p).1
    calc
      p ≫ v.1 =
          pullbackBaseChange K L g t v.1 v.2 ≫ pullback.fst g base := by
        change pullback.fst t
            (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫ v.1 =
          pullbackBaseChange K L g t v.1 v.2 ≫ pullback.fst g
            (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        exact (pullbackBaseChange_fst K L g t v.1 v.2).symm
      _ = (pullbackBaseChange K L g t v.1 v.2 ≫ e.hom) ≫ q := by
        dsimp [base]
        rw [← hprojection]
        simp
      _ = h ≫ q := congrArg (fun m => m ≫ q) hv
      _ = r := rfl
      _ = p ≫ u.1 := hfac.symm

/-- The Galois graph cover and effective descent turn invariance into the full
quotient universal property. -/
theorem galoisQuotientUniversal_of_equivariant
    (e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅ X)
    (hover : e.hom ≫ f =
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (hprojection : e.inv ≫
      pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L))) = q)
    (hqinv : ∀ gamma : L ≃ₐ[K] L, (rho.act gamma).hom ≫ q = q) :
    ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K))
      (h : pullback t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X),
      h ≫ f = pullback.snd t
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) →
      (pullbackSemilinearGalAction K L t).IsEquivariant rho h →
      ∃! v : {v : T ⟶ Y // v ≫ g = t},
        pullbackBaseChange K L g t v.1 v.2 ≫ e.hom = h :=
  galoisQuotientUniversal_of_kernelPair rho q e hover hprojection
    (kernelPair_eq_of_equivariant rho q hqinv)

/-- Package a base-change isomorphism and invariant projection as a specified
finite Galois quotient witness. -/
noncomputable def galoisQuotientWitnessOfInvariantProjection
    (e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅ X)
    (hover : e.hom ≫ f =
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (hequiv : (pullbackSemilinearGalAction K L g).IsEquivariant rho e.hom)
    (hprojection : e.inv ≫
      pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap K L))) = q)
    (hqinv : ∀ gamma : L ≃ₐ[K] L, (rho.act gamma).hom ≫ q = q) :
    GaloisQuotientWitnessWithProjection rho Y g q :=
  ⟨⟨e, hover, hequiv,
      galoisQuotientUniversal_of_equivariant rho q e hover hprojection hqinv⟩,
    hprojection⟩

end AlgebraicJacobian.GaloisDescent
