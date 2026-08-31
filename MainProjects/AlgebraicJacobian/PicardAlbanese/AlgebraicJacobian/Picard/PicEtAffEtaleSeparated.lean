/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAffMap

/-!
# Etale separatedness of the affine Picard plus construction

Restriction of `PicEtAff` to the carrier of an etale cover is injective.  An equality
after restriction supplies a common refinement over the covering algebra.  Its carrier
is etale and faithfully flat over the original algebra by transitivity, so it can be
presented as a cover of the original algebra and used as a common refinement there.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

noncomputable section

namespace PicEtAff

/-- Restriction to a single etale cover is injective on the affine Picard plus
construction. -/
theorem map_injective_of_etaleCover {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (C : Over (Spec (.of k))) (E : Algebra.EtaleCover A) :
    Function.Injective (map (A := A) C E.Carrier) := by
  intro x y hxy
  induction x using ind with
  | _ G x =>
    induction y using ind with
    | _ H y =>
      rw [map_mk, map_mk] at hxy
      obtain ⟨J, f, g, hfg⟩ := (mk_eq_mk_iff C).mp hxy
      letI : Algebra.Etale A J.Carrier :=
        Algebra.Etale.comp A E.Carrier J.Carrier
      letI : Module.FaithfullyFlat A J.Carrier :=
        Module.FaithfullyFlat.trans A E.Carrier J.Carrier
      let K : Algebra.EtaleCover A :=
        Algebra.EtaleCover.of J.Carrier
          PrimeSpectrum.comap_surjective_of_faithfullyFlat
      let e : K.Carrier ≃ₐ[A] J.Carrier :=
        Algebra.EtaleCover.ofEquiv J.Carrier
          PrimeSpectrum.comap_surjective_of_faithfullyFlat
      let fA : G.Carrier →ₐ[A] K.Carrier :=
        e.symm.toAlgHom.comp
          ((f.restrictScalars A).comp (G.baseChangeInclude E.Carrier))
      let gA : H.Carrier →ₐ[A] K.Carrier :=
        e.symm.toAlgHom.comp
          ((g.restrictScalars A).comp (H.baseChangeInclude E.Carrier))
      refine (mk_eq_mk_iff C).mpr ⟨K, fA, gA, ?_⟩
      apply Subtype.ext
      have hval := congrArg Subtype.val hfg
      rw [descentMap_coe, descentMap_coe, descentBaseChange_coe,
        descentBaseChange_coe, ← relPicAlgMap_comp, ← relPicAlgMap_comp] at hval
      rw [descentMap_coe, descentMap_coe]
      change relPicAlgMap C
          ((e.symm.toAlgHom.restrictScalars k).comp
            ((f.restrictScalars k).comp
              ((G.baseChangeInclude E.Carrier).restrictScalars k)))
          (x : relPic C (overSpec k G.Carrier))
        = relPicAlgMap C
          ((e.symm.toAlgHom.restrictScalars k).comp
            ((g.restrictScalars k).comp
              ((H.baseChangeInclude E.Carrier).restrictScalars k)))
          (y : relPic C (overSpec k H.Carrier))
      calc
        _ = relPicAlgMap C (e.symm.toAlgHom.restrictScalars k)
            (relPicAlgMap C
              ((f.restrictScalars k).comp
                ((G.baseChangeInclude E.Carrier).restrictScalars k))
              (x : relPic C (overSpec k G.Carrier))) :=
            relPicAlgMap_comp C _ _ _
        _ = relPicAlgMap C (e.symm.toAlgHom.restrictScalars k)
            (relPicAlgMap C
              ((g.restrictScalars k).comp
                ((H.baseChangeInclude E.Carrier).restrictScalars k))
              (y : relPic C (overSpec k H.Carrier))) := congrArg _ hval
        _ = _ := (relPicAlgMap_comp C _ _ _).symm

end PicEtAff

end

end AlgebraicGeometry
