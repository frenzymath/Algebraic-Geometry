/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FiniteGaloisQuotientAffine
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Uniqueness of finite Galois quotients

The universal `T`-points clause in `IsGaloisQuotient` determines the quotient
scheme uniquely over the base.  This file packages that observation as a
canonical comparison morphism and isomorphism.  The transitivity theorem is the
cocycle engine for gluing affine Galois quotient charts: once two restrictions
are known to be quotients of the same acted scheme, their overlap isomorphism
and every triple-overlap identity follow from uniqueness.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicJacobian.GaloisDescent

/-- The data asserted by `IsGaloisQuotient`, retained in `Type` so its universal
property can define comparison morphisms. -/
structure GaloisQuotientWitness
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of K)) where
  e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅ X
  over : e.hom ≫ f = pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  equivariant : (pullbackSemilinearGalAction K L g).IsEquivariant rho e.hom
  universal : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K))
      (h : pullback t (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ X),
      h ≫ f = pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap K L))) →
      (pullbackSemilinearGalAction K L t).IsEquivariant rho h →
      ∃! v : {v : T ⟶ Y // v ≫ g = t},
        pullbackBaseChange K L g t v.1 v.2 ≫ e.hom = h

/-- A quotient witness together with the quotient projection induced by its
pinned base-change isomorphism. -/
structure GaloisQuotientWitnessWithProjection
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of K))
    (q : X ⟶ Y) extends GaloisQuotientWitness rho Y g where
  projection : e.inv ≫ pullback.fst g
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) = q

namespace GaloisQuotientWitness

/-- The comparison morphism defined from two specified quotient witnesses. -/
noncomputable def comparison
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {rho : SemilinearGalAction K L X f}
    {Y₁ Y₂ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    (w₁ : GaloisQuotientWitness rho Y₁ g₁)
    (w₂ : GaloisQuotientWitness rho Y₂ g₂) :
    {v : Y₁ ⟶ Y₂ // v ≫ g₂ = g₁} :=
  (w₂.universal Y₁ g₁ w₁.e.hom w₁.over w₁.equivariant).choose

/-- Base change of a witness-level comparison identifies the two pinned
base-change isomorphisms. -/
theorem comparison_spec
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {rho : SemilinearGalAction K L X f}
    {Y₁ Y₂ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    (w₁ : GaloisQuotientWitness rho Y₁ g₁)
    (w₂ : GaloisQuotientWitness rho Y₂ g₂) :
    pullbackBaseChange K L g₂ g₁ (comparison w₁ w₂).1
        (comparison w₁ w₂).2 ≫ w₂.e.hom = w₁.e.hom :=
  (w₂.universal Y₁ g₁ w₁.e.hom w₁.over w₁.equivariant).choose_spec.1

/-- A witness-level comparison intertwines the quotient projections determined
by the two pinned base-change isomorphisms. -/
theorem comparison_projection
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {rho : SemilinearGalAction K L X f}
    {Y₁ Y₂ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    (w₁ : GaloisQuotientWitness rho Y₁ g₁)
    (w₂ : GaloisQuotientWitness rho Y₂ g₂) :
    (w₁.e.inv ≫ pullback.fst g₁
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫
        (comparison w₁ w₂).1 =
      w₂.e.inv ≫ pullback.fst g₂
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  let v := comparison w₁ w₂
  let bc := pullbackBaseChange K L g₂ g₁ v.1 v.2
  have hinv : w₁.e.inv ≫ bc = w₂.e.inv := by
    rw [← cancel_mono w₂.e.hom]
    dsimp only [bc, v]
    simp only [Category.assoc, comparison_spec]
    simp
  calc
    (w₁.e.inv ≫ pullback.fst g₁
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫ v.1 =
        w₁.e.inv ≫
          (pullbackBaseChange K L g₂ g₁ v.1 v.2 ≫
            pullback.fst g₂
              (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := by
      rw [pullbackBaseChange_fst]
      simp only [Category.assoc]
    _ = (w₁.e.inv ≫ bc) ≫ pullback.fst g₂
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
      rfl
    _ = w₂.e.inv ≫ pullback.fst g₂
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by rw [hinv]

/-- Comparing witnesses with specified quotient projections intertwines those
projections. -/
theorem comparison_quotientMap
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {rho : SemilinearGalAction K L X f}
    {Y₁ Y₂ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    {q₁ : X ⟶ Y₁} {q₂ : X ⟶ Y₂}
    (w₁ : GaloisQuotientWitnessWithProjection rho Y₁ g₁ q₁)
    (w₂ : GaloisQuotientWitnessWithProjection rho Y₂ g₂ q₂) :
    q₁ ≫ (comparison w₁.toGaloisQuotientWitness
      w₂.toGaloisQuotientWitness).1 = q₂ := by
  calc
    q₁ ≫ (comparison w₁.toGaloisQuotientWitness
        w₂.toGaloisQuotientWitness).1 =
        (w₁.e.inv ≫ pullback.fst g₁
          (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫
          (comparison w₁.toGaloisQuotientWitness
            w₂.toGaloisQuotientWitness).1 :=
      congrArg (fun z => z ≫ (comparison w₁.toGaloisQuotientWitness
        w₂.toGaloisQuotientWitness).1) w₁.projection.symm
    _ = w₂.e.inv ≫ pullback.fst g₂
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
      comparison_projection w₁.toGaloisQuotientWitness
        w₂.toGaloisQuotientWitness
    _ = q₂ := w₂.projection

/-- Transport a specified quotient witness along an equivariant isomorphism of
the acted source schemes. -/
noncomputable def transport
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X X' : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of L)}
    {f' : X' ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    (rho' : SemilinearGalAction K L X' f')
    (e : X ≅ X') (hef : e.hom ≫ f' = f)
    (he : rho.IsEquivariant rho' e.hom)
    {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}
    (w : GaloisQuotientWitness rho' Y g) :
    GaloisQuotientWitness rho Y g := by
  refine ⟨w.e ≪≫ e.symm, ?_, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, ← hef, Iso.symm_hom,
      Iso.inv_hom_id_assoc, w.over]
  · intro γ
    have hinv : e.inv ≫ (rho.act γ).hom = (rho'.act γ).hom ≫ e.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← he γ, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    change _ ≫ w.e.hom ≫ e.inv = (w.e.hom ≫ e.inv) ≫ _
    rw [← Category.assoc, w.equivariant γ, Category.assoc, Category.assoc, hinv]
  · intro T t h hover hequiv
    obtain ⟨v, hv, hvuniq⟩ := w.universal T t (h ≫ e.hom)
      (by rw [Category.assoc, hef, hover])
      (by
        intro γ
        rw [← Category.assoc, hequiv γ, Category.assoc, he γ, Category.assoc])
    refine ⟨v, ?_, fun y hy => hvuniq y ?_⟩
    · change _ ≫ w.e.hom ≫ e.inv = h
      rw [← Category.assoc, hv, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · change _ ≫ w.e.hom = h ≫ e.hom
      have hy' : pullbackBaseChange K L g t y.1 y.2 ≫
          w.e.hom ≫ e.inv = h := hy
      rw [← Category.assoc] at hy'
      rw [← hy', Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Comparing a specified quotient witness with itself gives the identity. -/
theorem comparison_self
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {rho : SemilinearGalAction K L X f}
    {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}
    (w : GaloisQuotientWitness rho Y g) :
    (comparison w w).1 = 𝟙 Y := by
  classical
  have hbc : pullbackBaseChange K L g g (𝟙 Y) (Category.id_comp g) = 𝟙 _ := by
    apply pullback.hom_ext <;> simp
  have hid : pullbackBaseChange K L g g (𝟙 Y) (Category.id_comp g) ≫
      w.e.hom = w.e.hom := by rw [hbc, Category.id_comp]
  have heq := (w.universal Y g w.e.hom w.over w.equivariant).unique
    (y₁ := comparison w w) (y₂ := ⟨𝟙 Y, Category.id_comp g⟩)
    (comparison_spec w w) hid
  exact congrArg Subtype.val heq

/-- Comparisons of specified quotient witnesses compose transitively. -/
theorem comparison_comp
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {rho : SemilinearGalAction K L X f}
    {Y₁ Y₂ Y₃ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    {g₃ : Y₃ ⟶ Spec (CommRingCat.of K)}
    (w₁ : GaloisQuotientWitness rho Y₁ g₁)
    (w₂ : GaloisQuotientWitness rho Y₂ g₂)
    (w₃ : GaloisQuotientWitness rho Y₃ g₃) :
    (comparison w₁ w₂).1 ≫ (comparison w₂ w₃).1 =
      (comparison w₁ w₃).1 := by
  classical
  let v₁₂ := comparison w₁ w₂
  let v₂₃ := comparison w₂ w₃
  have hbase : (v₁₂.1 ≫ v₂₃.1) ≫ g₃ = g₁ := by
    rw [Category.assoc, v₂₃.2, v₁₂.2]
  have hcomp : pullbackBaseChange K L g₃ g₁ (v₁₂.1 ≫ v₂₃.1) hbase ≫
      w₃.e.hom = w₁.e.hom := by
    rw [pullbackBaseChange_comp K L g₃ g₂ g₁ v₂₃.1 v₂₃.2 v₁₂.1 v₁₂.2,
      Category.assoc, comparison_spec w₂ w₃, comparison_spec w₁ w₂]
  have heq := (w₃.universal Y₁ g₁ w₁.e.hom w₁.over w₁.equivariant).unique
    (y₁ := ⟨v₁₂.1 ≫ v₂₃.1, hbase⟩) (y₂ := comparison w₁ w₃)
    hcomp (comparison_spec w₁ w₃)
  exact congrArg Subtype.val heq

/-- The canonical isomorphism determined by two specified quotient witnesses. -/
noncomputable def uniqueIso
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {rho : SemilinearGalAction K L X f}
    {Y₁ Y₂ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    (w₁ : GaloisQuotientWitness rho Y₁ g₁)
    (w₂ : GaloisQuotientWitness rho Y₂ g₂) : Y₁ ≅ Y₂ where
  hom := (comparison w₁ w₂).1
  inv := (comparison w₂ w₁).1
  hom_inv_id := by rw [comparison_comp, comparison_self]
  inv_hom_id := by rw [comparison_comp, comparison_self]

end GaloisQuotientWitness

namespace GaloisQuotientWitnessWithProjection

/-- The pinned quotient projection lies over the base field. -/
@[reassoc]
theorem quotientMap_comp_base
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {rho : SemilinearGalAction K L X f}
    {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}
    {q : X ⟶ Y}
    (w : GaloisQuotientWitnessWithProjection rho Y g q) :
    q ≫ g = f ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [← w.projection]
  simp only [Category.assoc]
  rw [pullback.condition]
  rw [← w.over]
  simp

/-- The inverse of the pinned base-change isomorphism has the source structure
map as its second projection. -/
@[reassoc]
theorem inverse_comp_snd
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {rho : SemilinearGalAction K L X f}
    {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}
    {q : X ⟶ Y}
    (w : GaloisQuotientWitnessWithProjection rho Y g q) :
    w.e.inv ≫ pullback.snd g
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) = f := by
  rw [← w.over]
  simp

/-- The pinned quotient projection is invariant under the Galois action. -/
@[reassoc]
theorem act_hom_comp_quotientMap
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {rho : SemilinearGalAction K L X f}
    {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}
    {q : X ⟶ Y}
    (w : GaloisQuotientWitnessWithProjection rho Y g q)
    (gamma : L ≃ₐ[K] L) :
    (rho.act gamma).hom ≫ q = q := by
  have hinv : (rho.act gamma).hom ≫ w.e.inv =
      w.e.inv ≫
        ((pullbackSemilinearGalAction K L g).act gamma).hom := by
    rw [← cancel_mono w.e.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    calc
      (rho.act gamma).hom =
          (w.e.inv ≫ w.e.hom) ≫ (rho.act gamma).hom := by simp
      _ = w.e.inv ≫ (w.e.hom ≫ (rho.act gamma).hom) :=
        Category.assoc _ _ _
      _ = w.e.inv ≫
          (((pullbackSemilinearGalAction K L g).act gamma).hom ≫
            w.e.hom) :=
        congrArg (fun z ↦ w.e.inv ≫ z) (w.equivariant gamma).symm
      _ = (w.e.inv ≫
          ((pullbackSemilinearGalAction K L g).act gamma).hom) ≫
            w.e.hom := (Category.assoc _ _ _).symm
  rw [← w.projection, ← Category.assoc, hinv, Category.assoc]
  rw [pullbackSemilinearGalAction_act_hom, pullbackGalMap_fst]

/-- The quotient projection specified by a Galois quotient witness is an
epimorphism.  It is an isomorphism followed by the flat surjective base change
of `Spec L ⟶ Spec K`. -/
theorem epi_quotientMap
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {rho : SemilinearGalAction K L X f}
    {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}
    {q : X ⟶ Y}
    (w : GaloisQuotientWitnessWithProjection rho Y g q) : Epi q := by
  let base : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI : Surjective base :=
    ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  haveI : Epi (pullback.fst g base) :=
    Flat.epi_of_flat_of_surjective _
  rw [← w.projection]
  infer_instance

/-- Transport a projection-carrying quotient witness along an equivariant
isomorphism of acted source schemes. -/
noncomputable def transport
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X X' : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of L)}
    {f' : X' ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    (rho' : SemilinearGalAction K L X' f')
    (e : X ≅ X') (hef : e.hom ≫ f' = f)
    (he : rho.IsEquivariant rho' e.hom)
    {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}
    {q : X' ⟶ Y}
    (w : GaloisQuotientWitnessWithProjection rho' Y g q) :
    GaloisQuotientWitnessWithProjection rho Y g (e.hom ≫ q) := by
  refine ⟨GaloisQuotientWitness.transport rho rho' e hef he
    w.toGaloisQuotientWitness, ?_⟩
  dsimp [GaloisQuotientWitness.transport]
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [w.projection]

end GaloisQuotientWitnessWithProjection

/-- Extract the full quotient witness from the proposition-valued predicate.
This is the sole use of choice in the comparison construction. -/
noncomputable def IsGaloisQuotient.witness
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {rho : SemilinearGalAction K L X f}
    {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}
    (h : IsGaloisQuotient rho g) : GaloisQuotientWitness rho Y g :=
  Classical.choice (show Nonempty (GaloisQuotientWitness rho Y g) from by
    obtain ⟨e, hover, hequiv, huniv⟩ := h
    exact ⟨⟨e, hover, hequiv, huniv⟩⟩)

/-- The unique morphism from one Galois quotient to another, obtained by
applying the second quotient's universal property to the first one's
base-change isomorphism. -/
noncomputable def quotientComparison
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    {Y₁ Y₂ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    (h₁ : IsGaloisQuotient rho g₁) (h₂ : IsGaloisQuotient rho g₂) :
    {v : Y₁ ⟶ Y₂ // v ≫ g₂ = g₁} :=
  ((h₂.witness).universal Y₁ g₁ (h₁.witness).e.hom
    (h₁.witness).over (h₁.witness).equivariant).choose

/-- The base change of `quotientComparison` carries the second quotient's
chosen descent isomorphism to the first one's. -/
theorem quotientComparison_spec
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    {Y₁ Y₂ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    (h₁ : IsGaloisQuotient rho g₁) (h₂ : IsGaloisQuotient rho g₂) :
    pullbackBaseChange K L g₂ g₁ (quotientComparison rho h₁ h₂).1
        (quotientComparison rho h₁ h₂).2 ≫ (h₂.witness).e.hom =
      (h₁.witness).e.hom :=
  ((h₂.witness).universal Y₁ g₁ (h₁.witness).e.hom
    (h₁.witness).over (h₁.witness).equivariant).choose_spec.1

/-- Comparing a quotient with itself gives the identity morphism. -/
theorem quotientComparison_self
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}
    (h : IsGaloisQuotient rho g) :
    (quotientComparison rho h h).1 = 𝟙 Y := by
  classical
  have hbc : pullbackBaseChange K L g g (𝟙 Y) (Category.id_comp g) = 𝟙 _ := by
    apply pullback.hom_ext <;> simp
  have hid : pullbackBaseChange K L g g (𝟙 Y) (Category.id_comp g) ≫
      (h.witness).e.hom = (h.witness).e.hom := by rw [hbc, Category.id_comp]
  have heq := ((h.witness).universal Y g (h.witness).e.hom (h.witness).over
    (h.witness).equivariant).unique
      (y₁ := quotientComparison rho h h) (y₂ := ⟨𝟙 Y, Category.id_comp g⟩)
      (quotientComparison_spec rho h h) hid
  exact congrArg Subtype.val heq

/-- Comparison morphisms compose transitively.  This is the triple-overlap
cocycle identity used by quotient gluing. -/
theorem quotientComparison_comp
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    {Y₁ Y₂ Y₃ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    {g₃ : Y₃ ⟶ Spec (CommRingCat.of K)}
    (h₁ : IsGaloisQuotient rho g₁) (h₂ : IsGaloisQuotient rho g₂)
    (h₃ : IsGaloisQuotient rho g₃) :
    (quotientComparison rho h₁ h₂).1 ≫ (quotientComparison rho h₂ h₃).1 =
      (quotientComparison rho h₁ h₃).1 := by
  classical
  let v₁₂ := quotientComparison rho h₁ h₂
  let v₂₃ := quotientComparison rho h₂ h₃
  have hbase : (v₁₂.1 ≫ v₂₃.1) ≫ g₃ = g₁ := by
    rw [Category.assoc, v₂₃.2, v₁₂.2]
  have hcomp : pullbackBaseChange K L g₃ g₁ (v₁₂.1 ≫ v₂₃.1) hbase ≫
      (h₃.witness).e.hom = (h₁.witness).e.hom := by
    rw [pullbackBaseChange_comp K L g₃ g₂ g₁ v₂₃.1 v₂₃.2 v₁₂.1 v₁₂.2,
      Category.assoc, quotientComparison_spec rho h₂ h₃,
      quotientComparison_spec rho h₁ h₂]
  have heq := ((h₃.witness).universal Y₁ g₁ (h₁.witness).e.hom (h₁.witness).over
    (h₁.witness).equivariant).unique
      (y₁ := ⟨v₁₂.1 ≫ v₂₃.1, hbase⟩) (y₂ := quotientComparison rho h₁ h₃)
      hcomp (quotientComparison_spec rho h₁ h₃)
  exact congrArg Subtype.val heq

/-- Any two schemes representing the same finite Galois quotient are
canonically isomorphic over `Spec K`. -/
noncomputable def quotientUniqueIso
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    {Y₁ Y₂ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    (h₁ : IsGaloisQuotient rho g₁) (h₂ : IsGaloisQuotient rho g₂) : Y₁ ≅ Y₂ where
  hom := (quotientComparison rho h₁ h₂).1
  inv := (quotientComparison rho h₂ h₁).1
  hom_inv_id := by rw [quotientComparison_comp, quotientComparison_self]
  inv_hom_id := by rw [quotientComparison_comp, quotientComparison_self]

@[reassoc]
theorem quotientUniqueIso_hom_base
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    {Y₁ Y₂ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    (h₁ : IsGaloisQuotient rho g₁) (h₂ : IsGaloisQuotient rho g₂) :
    (quotientUniqueIso rho h₁ h₂).hom ≫ g₂ = g₁ :=
  (quotientComparison rho h₁ h₂).2

@[reassoc]
theorem quotientUniqueIso_inv_base
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    {Y₁ Y₂ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    (h₁ : IsGaloisQuotient rho g₁) (h₂ : IsGaloisQuotient rho g₂) :
    (quotientUniqueIso rho h₁ h₂).inv ≫ g₁ = g₂ :=
  (quotientComparison rho h₂ h₁).2

/-- The hom maps of the canonical quotient isomorphisms satisfy the gluing
cocycle on triple overlaps. -/
theorem quotientUniqueIso_hom_trans
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    {Y₁ Y₂ Y₃ : Scheme.{u}}
    {g₁ : Y₁ ⟶ Spec (CommRingCat.of K)}
    {g₂ : Y₂ ⟶ Spec (CommRingCat.of K)}
    {g₃ : Y₃ ⟶ Spec (CommRingCat.of K)}
    (h₁ : IsGaloisQuotient rho g₁) (h₂ : IsGaloisQuotient rho g₂)
    (h₃ : IsGaloisQuotient rho g₃) :
    (quotientUniqueIso rho h₁ h₂).hom ≫ (quotientUniqueIso rho h₂ h₃).hom =
      (quotientUniqueIso rho h₁ h₃).hom :=
  quotientComparison_comp rho h₁ h₂ h₃

@[simp]
theorem quotientUniqueIso_self
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (rho : SemilinearGalAction K L X f)
    {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}
    (h : IsGaloisQuotient rho g) : quotientUniqueIso rho h h = Iso.refl Y := by
  ext
  exact quotientComparison_self rho h

end AlgebraicJacobian.GaloisDescent
