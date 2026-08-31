/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverageAffineTest
import AlgebraicJacobian.Picard.Pic0ChartHonest

/-!
# Etale-site reduction and affine PicEt honestification

This file provides the site-theoretic and affine-plus infrastructure used to turn affine
local lifts into local surjectivity on the big etale site. It also packages the passage from
an affine `picEt` class to an honest relative Picard class after restriction to the carrier of
one of its etale presentations.

The declarations here are independent of the Abel transformation and make no representability
or quotient assertion.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-! ## Reduction to affine tests -/

/-- A sieve on a scheme is etale-covering if its pullback to every member of the canonical
affine open cover is etale-covering. -/
theorem mem_etaleTopology_of_pullback_affine {T : Scheme.{u}} (S : Sieve T)
    (h : ∀ (j : T.affineCover.I₀), S.pullback (T.affineCover.f j) ∈
      Scheme.etaleTopology (T.affineCover.X j)) :
    S ∈ Scheme.etaleTopology T := by
  have hcov : (Sieve.generate (Presieve.ofArrows T.affineCover.X T.affineCover.f))
      ∈ Scheme.etaleTopology T := by
    apply Scheme.zariskiTopology_le_etaleTopology
    exact Scheme.mem_grothendieckTopology_iff.mpr
      ⟨T.affineCover, Sieve.le_generate _⟩
  refine Scheme.etaleTopology.transitive hcov S ?_
  rintro Y g ⟨V, a, b, ⟨j⟩, rfl⟩
  rw [Sieve.pullback_comp]
  exact Scheme.etaleTopology.pullback_stable a (h j)

/-- To prove local surjectivity on the big etale site, it suffices to produce an etale cover
with local lifts over every affine test scheme. -/
theorem isLocallySurjective_etale_of_affine
    {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (h : ∀ (Y : Scheme.{u}) [IsAffine Y] (s : G.obj (op Y)),
      ∃ (cover : Y.Cover.{u} (Scheme.precoverage @Etale)),
        ∀ j : cover.I₀, ∃ x : F.obj (op (cover.X j)),
          f.app (op (cover.X j)) x = G.map (cover.f j).op s) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology f where
  imageSieve_mem {U} s := by
    apply mem_etaleTopology_of_pullback_affine
    intro j
    rw [Presheaf.pullback_imageSieve]
    obtain ⟨cover, hcover⟩ :=
      h (U.affineCover.X j) (G.map (U.affineCover.f j).op s)
    refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).mpr ⟨cover, ?_⟩
    rintro Y g ⟨i⟩
    exact hcover i

/-! ## Covers induced by affine etale presentations -/

/-- The spectrum of the carrier of an algebraic etale cover is a singleton etale cover of
the spectrum of the base algebra. -/
noncomputable def etaleSchemeCover {A : Type u} [CommRing A]
    (E : Algebra.EtaleCover A) :
    (Spec (.of A)).Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers PUnit (fun _ => Spec (.of E.Carrier))
    (fun _ => Spec.map (CommRingCat.ofHom (algebraMap A E.Carrier)))
    (fun x => by
      obtain ⟨y, hy⟩ := E.comap_surjective x
      exact ⟨PUnit.unit, y, hy⟩)
    (fun _ => by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      exact RingHom.etale_algebraMap.mpr inferInstance)

/-! ## Honestification of affine PicEt classes -/

namespace PicEtAff

/-- `mapAlg` agrees with the instance-based affine restriction map when the underlying ring
homomorphism is the chosen `A`-algebra structure on `B`. -/
theorem mapAlg_eq_map_of_toRingHom_eq_algebraMap
    {k A B : Type u} [Field k] [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (C : Over (Spec (.of k))) (phi : A →ₐ[k] B)
    (hphi : phi.toRingHom = algebraMap A B) (a : PicEtAff C A) :
    PicEtAff.mapAlg C phi a = PicEtAff.map C B a := by
  have hAlg : phi.toRingHom.toAlgebra = (inferInstance : Algebra A B) :=
    Algebra.algebra_ext _ _ fun r => by
      change phi r = algebraMap A B r
      exact DFunLike.congr_fun hphi r
  unfold PicEtAff.mapAlg
  subst hAlg
  rfl

/-- Restricting an affine PicEt presentation along the map to its own cover carrier produces
the honest class represented by its descent datum. -/
theorem mapAlg_mk_eq_unit_self
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (C : Over (Spec (.of k)))
    (E : Algebra.EtaleCover A) (x : descentClasses C E) :
    PicEtAff.mapAlg C ((Algebra.ofId A E.Carrier).restrictScalars k)
        (PicEtAff.mk C E x)
      = PicEtAff.unit C E.Carrier
          (x : relPic C (overSpec k E.Carrier)) := by
  rw [mapAlg_eq_map_of_toRingHom_eq_algebraMap C _ rfl]
  exact PicEtAff.map_mk_eq_unit_self C E x

end PicEtAff

/-- On affine tests, restricting a `picEt` class to the carrier of one of its plus
presentations agrees with the `picEt` unit of the corresponding honest relative Picard
class. -/
theorem picEtMap_eq_relPicToPicEt_of_affineRepresentative
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (C : Over (Spec (.of k)))
    [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
    (lam : picEt C (overSpec k A)) (E : Algebra.EtaleCover A)
    (x : descentClasses C E)
    (h : picEtAffineEquiv C A lam = PicEtAff.mk C E x) :
    picEtMap C
        (Over.overSpecMap ((Algebra.ofId A E.Carrier).restrictScalars k)) lam
      = relPicToPicEt C (overSpec k E.Carrier)
          (x : relPic C (overSpec k E.Carrier)) := by
  apply (picEtAffineEquiv C E.Carrier).injective
  rw [picEtAffineEquiv_naturality, h,
    picEtAffineEquiv_relPicToPicEt,
    PicEtAff.mapAlg_mk_eq_unit_self]

end

end AlgebraicGeometry
