/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAffEtaleSeparated
import AlgebraicJacobian.Picard.PicEtAffZariskiSep
import AlgebraicJacobian.Picard.RelPicCoverInjective

/-!
# Etale effectivity of the affine Picard plus construction

A class over the carrier of a singleton etale cover whose two restrictions to the
double overlap agree descends to the base.  The representative cover is composed with
the given cover.  Its raw relative-Picard descent condition is checked after restriction
to a cover of the double overlap and reflected by etale separatedness.
-/

set_option autoImplicit false

universe u

open CategoryTheory

open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

namespace PicEtAff

set_option maxHeartbeats 4000000 in
-- The nested presented-cover and tensor-product towers make elaboration heartbeat-heavy.
set_option synthInstance.maxHeartbeats 400000 in
/-- Singleton etale descent data for `PicEtAff` are effective. -/
theorem exists_map_eq_of_double_eq {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (C : Over (Spec (.of k))) [IsProper C.hom] [GeometricallyIrreducible C.hom]
    [GeometricallyReduced C.hom] (E : Algebra.EtaleCover A) (x : PicEtAff C E.Carrier)
    (h : mapAlg C (doubleInl E) x = mapAlg C (doubleInr E) x) :
    ∃ z : PicEtAff C A, map C E.Carrier z = x := by
  induction x using ind with
  | _ G xi =>
    obtain ⟨H, m₁, m₂, hm₁, hm₂, hm⟩ :=
      exists_relPicAlgMap_eq_of_mapAlg_eq C (doubleInl E) (doubleInr E) G G xi xi h
    letI : Algebra.Etale A G.Carrier :=
      Algebra.Etale.comp A E.Carrier G.Carrier
    letI : Module.FaithfullyFlat A G.Carrier :=
      Module.FaithfullyFlat.trans A E.Carrier G.Carrier
    let K : Algebra.EtaleCover A :=
      Algebra.EtaleCover.of G.Carrier
        PrimeSpectrum.comap_surjective_of_faithfullyFlat
    let e : K.Carrier ≃ₐ[A] G.Carrier :=
      Algebra.EtaleCover.ofEquiv G.Carrier
        PrimeSpectrum.comap_surjective_of_faithfullyFlat
    let j : E.Carrier →ₐ[A] K.Carrier :=
      e.symm.toAlgHom.comp
        ((Algebra.ofId E.Carrier G.Carrier).restrictScalars A)
    let phi : E.Carrier ⊗[A] E.Carrier →ₐ[A] K.Carrier ⊗[A] K.Carrier :=
      Algebra.TensorProduct.map j j
    letI : Algebra (E.Carrier ⊗[A] E.Carrier) (K.Carrier ⊗[A] K.Carrier) :=
      phi.toRingHom.toAlgebra
    haveI : IsScalarTower k (E.Carrier ⊗[A] E.Carrier)
        (K.Carrier ⊗[A] K.Carrier) :=
      .of_algebraMap_eq fun a => by
        change (algebraMap k K.Carrier a) ⊗ₜ[A] 1 =
          phi ((algebraMap k E.Carrier a) ⊗ₜ[A] 1)
        simp [phi, j]
    let L : Algebra.EtaleCover (K.Carrier ⊗[A] K.Carrier) :=
      H.baseChange (K.Carrier ⊗[A] K.Carrier)
    let eInv : G.Carrier →ₐ[k] K.Carrier := e.symm.toAlgHom.restrictScalars k
    let xiK : relPic C (overSpec k K.Carrier) := relPicAlgMap C eInv xi
    have hxiK : xiK ∈ descentClasses C K := by
      rw [mem_descentClasses_iff]
      apply relPicAlgMap_injective_of_etaleCover C L
      let incT : K.Carrier ⊗[A] K.Carrier →ₐ[k] L.Carrier :=
        (Algebra.ofId (K.Carrier ⊗[A] K.Carrier) L.Carrier).restrictScalars k
      let incH : H.Carrier →ₐ[k] L.Carrier :=
        (H.baseChangeInclude (K.Carrier ⊗[A] K.Carrier)).restrictScalars k
      let p₁ : G.Carrier →ₐ[k] L.Carrier :=
        incT.comp ((doubleInl K).comp eInv)
      let p₂ : G.Carrier →ₐ[k] L.Carrier :=
        incT.comp ((doubleInr K).comp eInv)
      let q₁ : G.Carrier →ₐ[k] L.Carrier := incH.comp m₁
      let q₂ : G.Carrier →ₐ[k] L.Carrier := incH.comp m₂
      have hpq₁ : relPicAlgMap C p₁ xi = relPicAlgMap C q₁ xi := by
        let beta : E.Carrier →ₐ[k] L.Carrier :=
          p₁.comp ((Algebra.ofId E.Carrier G.Carrier).restrictScalars k)
        letI : Algebra E.Carrier L.Carrier := beta.toRingHom.toAlgebra
        haveI : IsScalarTower k E.Carrier L.Carrier :=
          .of_algebraMap_eq fun a => (beta.commutes a).symm
        let p₁' : G.Carrier →ₐ[E.Carrier] L.Carrier :=
          { p₁.toRingHom with commutes' := fun _ => rfl }
        have hq₁ : ∀ b : E.Carrier,
            q₁ (algebraMap E.Carrier G.Carrier b) =
              p₁ (algebraMap E.Carrier G.Carrier b) := by
          intro b
          dsimp [q₁, p₁, incH, incT]
          rw [hm₁]
          rw [AlgHom.commutes]
          rw [IsScalarTower.algebraMap_apply
            (E.Carrier ⊗[A] E.Carrier) (K.Carrier ⊗[A] K.Carrier) L.Carrier]
          congr 1
          change phi (b ⊗ₜ[A] 1) =
            e.symm (algebraMap E.Carrier G.Carrier b) ⊗ₜ[A] 1
          simp [phi, j]
        let q₁' : G.Carrier →ₐ[E.Carrier] L.Carrier :=
          { q₁.toRingHom with commutes' := hq₁ }
        have hp₁' : p₁'.restrictScalars k = p₁ := AlgHom.ext fun _ => rfl
        have hq₁' : q₁'.restrictScalars k = q₁ := AlgHom.ext fun _ => rfl
        rw [← hp₁', ← hq₁']
        exact relPicAlgMap_congr C p₁' q₁' xi.2
      have hpq₂ : relPicAlgMap C p₂ xi = relPicAlgMap C q₂ xi := by
        let beta : E.Carrier →ₐ[k] L.Carrier :=
          p₂.comp ((Algebra.ofId E.Carrier G.Carrier).restrictScalars k)
        letI : Algebra E.Carrier L.Carrier := beta.toRingHom.toAlgebra
        haveI : IsScalarTower k E.Carrier L.Carrier :=
          .of_algebraMap_eq fun a => (beta.commutes a).symm
        let p₂' : G.Carrier →ₐ[E.Carrier] L.Carrier :=
          { p₂.toRingHom with commutes' := fun _ => rfl }
        have hq₂ : ∀ b : E.Carrier,
            q₂ (algebraMap E.Carrier G.Carrier b) =
              p₂ (algebraMap E.Carrier G.Carrier b) := by
          intro b
          dsimp [q₂, p₂, incH, incT]
          rw [hm₂]
          rw [AlgHom.commutes]
          rw [IsScalarTower.algebraMap_apply
            (E.Carrier ⊗[A] E.Carrier) (K.Carrier ⊗[A] K.Carrier) L.Carrier]
          congr 1
          change phi (1 ⊗ₜ[A] b) =
            1 ⊗ₜ[A] e.symm (algebraMap E.Carrier G.Carrier b)
          simp [phi, j]
        let q₂' : G.Carrier →ₐ[E.Carrier] L.Carrier :=
          { q₂.toRingHom with commutes' := hq₂ }
        have hp₂' : p₂'.restrictScalars k = p₂ := AlgHom.ext fun _ => rfl
        have hq₂' : q₂'.restrictScalars k = q₂ := AlgHom.ext fun _ => rfl
        rw [← hp₂', ← hq₂']
        exact relPicAlgMap_congr C p₂' q₂' xi.2
      have hp₁ : relPicAlgMap C incT
            (relPicAlgMap C (doubleInl K) xiK) = relPicAlgMap C p₁ xi := by
        dsimp [xiK]
        rw [← relPicAlgMap_comp, ← relPicAlgMap_comp]
        congr 2
      have hp₂ : relPicAlgMap C incT
            (relPicAlgMap C (doubleInr K) xiK) = relPicAlgMap C p₂ xi := by
        dsimp [xiK]
        rw [← relPicAlgMap_comp, ← relPicAlgMap_comp]
        congr 2
      rw [hp₁, hp₂]
      calc
        relPicAlgMap C p₁ xi = relPicAlgMap C q₁ xi := hpq₁
        _ = relPicAlgMap C q₂ xi := by
          dsimp [q₁, q₂]
          rw [relPicAlgMap_comp, relPicAlgMap_comp, hm]
        _ = relPicAlgMap C p₂ xi := hpq₂.symm
    let xiK' : descentClasses C K := ⟨xiK, hxiK⟩
    refine ⟨mk C K xiK', ?_⟩
    rw [map_mk]
    let mu : E.Carrier ⊗[A] K.Carrier →ₐ[A] G.Carrier :=
      Algebra.TensorProduct.lift
        ((Algebra.ofId E.Carrier G.Carrier).restrictScalars A) e.toAlgHom
        fun _ _ => Commute.all _ _
    let mu' : E.Carrier ⊗[A] K.Carrier →ₐ[E.Carrier] G.Carrier :=
      { mu.toRingHom with commutes' := fun b => by simp [mu] }
    let f : (K.baseChange E.Carrier).Carrier →ₐ[E.Carrier] G.Carrier :=
      mu'.comp (K.baseChangeEquiv E.Carrier).toAlgHom
    refine (mk_eq_mk_iff C).mpr ⟨G, f, AlgHom.id E.Carrier G.Carrier, ?_⟩
    apply Subtype.ext
    rw [descentMap_coe, descentMap_coe, descentBaseChange_coe]
    rw [← relPicAlgMap_comp, ← relPicAlgMap_comp]
    have hf : ((f.restrictScalars k).comp
          ((K.baseChangeInclude E.Carrier).restrictScalars k)).comp eInv =
        AlgHom.id k G.Carrier := by
      ext y
      simp [f, mu', mu, eInv, Algebra.EtaleCover.baseChangeInclude]
    have hid : (AlgHom.id E.Carrier G.Carrier).restrictScalars k =
        AlgHom.id k G.Carrier := rfl
    rw [hf, hid, relPicAlgMap_id]

end PicEtAff

end

end AlgebraicGeometry
