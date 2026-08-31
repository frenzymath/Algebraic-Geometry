/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.QuotFunctorDef
import AlgebraicJacobian.Picard.GrassmannianQuot
import AlgebraicJacobian.Picard.ZariskiDescentRepresentability
import AlgebraicJacobian.Picard.GrassmannianZariskiSheaf

/-!
# Representability of the relative Grassmannian (`thm:grassmannian_representable`)

This file states and attacks the representability of the relative Grassmannian
functor `Grass(V, d) : (Sch/S)ᵒᵖ ⥤ Type 1` (`Scheme.Grassmannian`,
`QuotFunctorDef.lean`) by an `S`-scheme, for `V` a locally free
`O_S`-module of rank `r` and `1 ≤ d ≤ r` ([Nitsure] §1, Exercise (2);
blueprint `thm:grassmannian_representable`).

The statement here **corrects** the earlier skeleton of `QuotFunctorDef.lean`,
which quantified over an arbitrary sheaf of modules `V` with no rank data:
that form is not the [Nitsure] theorem (whose hypotheses are `V` locally free
of rank `r ≥ d ≥ 1`) and is not known to be true for non-quasi-coherent `V`.
The universe is pinned to `Scheme.{0}`: the merged absolute chart construction
(`AlgebraicGeometry.Grassmannian.scheme` / `.represents`,
`GrassmannianQuot.lean`) lives over the genuinely terminal `Spec ℤ` of
`Scheme.{0}`, and the relative theorem is obtained from it.

## Contents

* `Scheme.LocallyFreeQuotient.congrModule` / `Scheme.Grassmannian.congrIso` —
  transport of the Grassmannian functor along an isomorphism `V ≅ V'` of the
  classified module (pure functoriality, no pseudofunctor coherence).
* `Scheme.LocallyFreeQuotient.toRankQuotient` / `.ofRankQuotient` /
  `Scheme.Grassmannian.freeCompare` — for the free module `V = O_S^r`, the
  comparison `Grass(O_S^r, d) ≅ (Over.forget S)ᵒᵖ ⋙ Grass(r, d)` with the
  merged absolute Grassmannian functor, re-presenting the pulled-back free
  module through `Scheme.Modules.pullbackFreeIso`.  Naturality is the free
  coherence `pullbackFreeIso_comp` of `GlueDescent.lean`.
* `Scheme.Grassmannian.prodRepresentableBy` — the absolute Grassmannian,
  pulled back to `Over S` along the forgetful functor, is representable by
  the product `S ⨯ Gr(d, r)` with its first projection (`Spec ℤ` is terminal
  in `Scheme.{0}`, so the product is the base change of `Gr(d, r)` to `S`).
* `Scheme.Grassmannian.representable_of_iso_free` — representability of
  `Grass(V, d)` for globally trivialised `V ≅ O_S^r` (complete proof).
* `Scheme.Grassmannian.representable` — the [Nitsure] statement, for `V`
  locally free of rank `r`: glue `representable_of_iso_free` over a
  trivialising cover of `(S, V)` by Zariski descent of representability
  (`Scheme.representable_of_openCover`, proved in
  `ZariskiDescentRepresentability.lean`); the remaining leaf is the sheaf
  axiom `Grassmannian.isZariskiSheaf`.

## References

Blueprint: `thm:grassmannian_representable`, `def:grassmannian_scheme`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
Source: [Nitsure], §1 (FGA Explained Ch. 5, arXiv:math/0504020).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ## §1. Transport along an isomorphism of the classified module -/

namespace LocallyFreeQuotient

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- Transport of a rank-`d` locally free quotient of `V'_T` along an
isomorphism `g : V ≅ V'` of the classified modules: precompose the quotient
map with the pulled-back isomorphism.  Underlies the invariance
`Scheme.Grassmannian.congrIso` of the Grassmannian functor. -/
noncomputable def congrModule {V V' : S.Modules} (g : V ≅ V') {d : ℕ} {T : Over S}
    (x : LocallyFreeQuotient V d T) : LocallyFreeQuotient V' d T where
  F := x.F
  q := ((Scheme.Modules.pullback T.hom).mapIso g).inv ≫ x.q
  epi :=
    @CategoryTheory.epi_comp _ _ _ _ _
      ((Scheme.Modules.pullback T.hom).mapIso g).inv inferInstance
      x.q x.epi
  locFree := x.locFree

omit [IsLocallyNoetherian S] in
/-- The module-iso transport respects the equivalence of quotients. -/
lemma congrModule_rel {V V' : S.Modules} (g : V ≅ V') {d : ℕ} {T : Over S}
    {x y : LocallyFreeQuotient V d T} (h : x.Rel y) :
    (congrModule g x).Rel (congrModule g y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, ?_⟩
  change (((Scheme.Modules.pullback T.hom).mapIso g).inv ≫ x.q) ≫ f.hom
    = ((Scheme.Modules.pullback T.hom).mapIso g).inv ≫ y.q
  rw [Category.assoc]
  exact congrArg (((Scheme.Modules.pullback T.hom).mapIso g).inv ≫ ·) hf

end LocallyFreeQuotient

set_option backward.isDefEq.respectTransparency false in
/-- **Invariance of the Grassmannian functor under isomorphism of the
classified module**: an isomorphism `g : V ≅ V'` of sheaves of modules on `S`
induces an isomorphism `Grass(V, d) ≅ Grass(V', d)` of the relative
Grassmannian functors.  Pure functoriality: the components transport a
quotient along `congrModule`, and naturality is the naturality of the
pullback pseudofunctor comparisons in the module variable. -/
noncomputable def Grassmannian.congrIso {S : Scheme.{u}} [IsLocallyNoetherian S]
    {V V' : S.Modules} (g : V ≅ V') (d : ℕ) :
    Scheme.Grassmannian V d ≅ Scheme.Grassmannian V' d :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      { toFun := Quotient.map (LocallyFreeQuotient.congrModule g)
          (fun _ _ h => LocallyFreeQuotient.congrModule_rel g h)
        invFun := Quotient.map (LocallyFreeQuotient.congrModule g.symm)
          (fun _ _ h => LocallyFreeQuotient.congrModule_rel g.symm h)
        left_inv := fun z => by
          induction z using Quotient.ind with
          | _ x =>
            refine Quotient.sound ⟨Iso.refl _, ?_⟩
            change ((((Scheme.Modules.pullback T.unop.hom).mapIso g.symm).inv ≫
                (((Scheme.Modules.pullback T.unop.hom).mapIso g).inv ≫ x.q))) ≫ 𝟙 _
              = x.q
            rw [Category.comp_id, ← Category.assoc]
            rw [show (((Scheme.Modules.pullback T.unop.hom).mapIso g.symm).inv ≫
                ((Scheme.Modules.pullback T.unop.hom).mapIso g).inv)
              = 𝟙 _ by
                rw [Functor.mapIso_inv, Functor.mapIso_inv, Iso.symm_inv,
                  ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]]
            exact Category.id_comp x.q
        right_inv := fun z => by
          induction z using Quotient.ind with
          | _ x =>
            refine Quotient.sound ⟨Iso.refl _, ?_⟩
            change ((((Scheme.Modules.pullback T.unop.hom).mapIso g).inv ≫
                (((Scheme.Modules.pullback T.unop.hom).mapIso g.symm).inv ≫ x.q))) ≫ 𝟙 _
              = x.q
            rw [Category.comp_id, ← Category.assoc]
            rw [show ((((Scheme.Modules.pullback T.unop.hom).mapIso g).inv ≫
                ((Scheme.Modules.pullback T.unop.hom).mapIso g.symm).inv))
              = 𝟙 _ by
                rw [Functor.mapIso_inv, Functor.mapIso_inv, Iso.symm_inv,
                  ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]]
            exact Category.id_comp x.q })
    (fun {T T'} ψ => by
      ext z
      induction z using Quotient.ind with
      | _ x =>
        change Quotient.mk _ (LocallyFreeQuotient.congrModule g
            (LocallyFreeQuotient.pullbackAlong ψ.unop x))
          = Quotient.mk _ (LocallyFreeQuotient.pullbackAlong ψ.unop
            (LocallyFreeQuotient.congrModule g x))
        refine Quotient.sound ⟨Iso.refl _, ?_⟩
        change (((Scheme.Modules.pullback T'.unop.hom).mapIso g).inv ≫
            (pullbackTriangleIso (Over.w ψ.unop) V).inv ≫
            (Scheme.Modules.pullback ψ.unop.left).map x.q) ≫ 𝟙 _
          = (pullbackTriangleIso (Over.w ψ.unop) V').inv ≫
            (Scheme.Modules.pullback ψ.unop.left).map
              (((Scheme.Modules.pullback T.unop.hom).mapIso g).inv ≫ x.q)
        rw [Category.comp_id, Functor.map_comp]
        rw [← Category.assoc, ← Category.assoc]
        refine congrArg (· ≫ (Scheme.Modules.pullback ψ.unop.left).map x.q) ?_
        -- naturality of the triangle comparison in the module variable at `g.inv`
        simpa only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc,
          Functor.mapIso_inv, NatTrans.comp_app, Functor.comp_map]
          using ((Scheme.Modules.pullbackCongr (Over.w ψ.unop)).inv ≫
            (Scheme.Modules.pullbackComp ψ.unop.left T.unop.hom).inv).naturality g.inv)

/-! ## §2. The free case: comparison with the merged absolute Grassmannian

For the free module `V = O_S^r` the relative Grassmannian functor agrees with
the merged absolute Grassmannian functor `Grass(r, d)`
(`AlgebraicGeometry.Grassmannian.functor`, `GrassmannianQuot.lean`) evaluated
on the underlying schemes: a quotient of `(T.hom)^* O_S^r` is re-presented as
a quotient of `O_T^r` through the free-pullback comparison
`Scheme.Modules.pullbackFreeIso`.  Naturality is the free coherence
`pullbackFreeIso_comp` (`GlueDescent.lean`). -/

namespace LocallyFreeQuotient

variable {S : Scheme.{0}} [IsLocallyNoetherian S]

/-- Re-present a rank-`d` locally free quotient of the pulled-back free module
`(T.hom)^* O_S^r` as an absolute rank-`d` quotient of `O_T^r`
(`AlgebraicGeometry.Grassmannian.RankQuotient`), through
`Scheme.Modules.pullbackFreeIso`. -/
noncomputable def toRankQuotient {r d : ℕ} {T : Over S}
    (x : LocallyFreeQuotient
      (SheafOfModules.free (R := S.ringCatSheaf) (Fin r)) d T) :
    AlgebraicGeometry.Grassmannian.RankQuotient r d T.left where
  F := x.F
  q := (Scheme.Modules.pullbackFreeIso T.hom (Fin r)).inv ≫ x.q
  epi :=
    @CategoryTheory.epi_comp _ _ _ _ _
      (Scheme.Modules.pullbackFreeIso T.hom (Fin r)).inv inferInstance
      x.q x.epi
  locFree := x.locFree

/-- Inverse re-presentation: an absolute rank-`d` quotient of `O_T^r` as a
quotient of the pulled-back free module `(T.hom)^* O_S^r`. -/
noncomputable def ofRankQuotient {r d : ℕ} {T : Over S}
    (y : AlgebraicGeometry.Grassmannian.RankQuotient r d T.left) :
    LocallyFreeQuotient (SheafOfModules.free (R := S.ringCatSheaf) (Fin r)) d T where
  F := y.F
  q := (Scheme.Modules.pullbackFreeIso T.hom (Fin r)).hom ≫ y.q
  epi :=
    @CategoryTheory.epi_comp _ _ _ _ _
      (Scheme.Modules.pullbackFreeIso T.hom (Fin r)).hom inferInstance
      y.q y.epi
  locFree := y.locFree

omit [IsLocallyNoetherian S] in
/-- `toRankQuotient` respects the equivalence of quotients. -/
lemma toRankQuotient_rel {r d : ℕ} {T : Over S}
    {x y : LocallyFreeQuotient
      (SheafOfModules.free (R := S.ringCatSheaf) (Fin r)) d T}
    (h : x.Rel y) : (toRankQuotient x).Rel (toRankQuotient y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, ?_⟩
  change ((Scheme.Modules.pullbackFreeIso T.hom (Fin r)).inv ≫ x.q) ≫ f.hom
    = (Scheme.Modules.pullbackFreeIso T.hom (Fin r)).inv ≫ y.q
  rw [Category.assoc]
  exact congrArg ((Scheme.Modules.pullbackFreeIso T.hom (Fin r)).inv ≫ ·) hf

omit [IsLocallyNoetherian S] in
/-- `ofRankQuotient` respects the equivalence of quotients. -/
lemma ofRankQuotient_rel {r d : ℕ} {T : Over S}
    {x y : AlgebraicGeometry.Grassmannian.RankQuotient r d T.left}
    (h : x.Rel y) : (ofRankQuotient (T := T) x).Rel (ofRankQuotient y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, ?_⟩
  change ((Scheme.Modules.pullbackFreeIso T.hom (Fin r)).hom ≫ x.q) ≫ f.hom
    = (Scheme.Modules.pullbackFreeIso T.hom (Fin r)).hom ≫ y.q
  rw [Category.assoc]
  exact congrArg ((Scheme.Modules.pullbackFreeIso T.hom (Fin r)).hom ≫ ·) hf

end LocallyFreeQuotient

namespace Grassmannian

variable {S : Scheme.{0}} [IsLocallyNoetherian S]

/-- The value-level comparison between the relative Grassmannian of the free
module and the merged absolute Grassmannian functor. -/
noncomputable def freeCompareEquiv (d r : ℕ) (T : Over S) :
    Quotient (Scheme.LocallyFreeQuotient.setoid
      (SheafOfModules.free (R := S.ringCatSheaf) (Fin r)) d T) ≃
    Quotient (AlgebraicGeometry.Grassmannian.rqSetoid r d T.left) where
  toFun := Quotient.map Scheme.LocallyFreeQuotient.toRankQuotient
    (fun _ _ h => Scheme.LocallyFreeQuotient.toRankQuotient_rel h)
  invFun := Quotient.map Scheme.LocallyFreeQuotient.ofRankQuotient
    (fun _ _ h => Scheme.LocallyFreeQuotient.ofRankQuotient_rel h)
  left_inv := fun z => by
    induction z using Quotient.ind with
    | _ x =>
      refine Quotient.sound ⟨Iso.refl _, ?_⟩
      change ((Scheme.Modules.pullbackFreeIso T.hom (Fin r)).hom ≫
          ((Scheme.Modules.pullbackFreeIso T.hom (Fin r)).inv ≫ x.q)) ≫ 𝟙 _
        = x.q
      rw [Category.comp_id, Iso.hom_inv_id_assoc]
  right_inv := fun z => by
    induction z using Quotient.ind with
    | _ x =>
      refine Quotient.sound ⟨Iso.refl _, ?_⟩
      change ((Scheme.Modules.pullbackFreeIso T.hom (Fin r)).inv ≫
          ((Scheme.Modules.pullbackFreeIso T.hom (Fin r)).hom ≫ x.q)) ≫ 𝟙 _
        = x.q
      rw [Category.comp_id, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- **Free-pullback coherence for the quotient re-presentation** — the
naturality core of `freeCompare`: pulling back along `ψ : T' ⟶ T` in `Over S`
commutes with the re-presentation of the source through
`Scheme.Modules.pullbackFreeIso`.  Assembled from the congruence absorptions
and the free coherence `pullbackFreeIso_comp` of `GlueDescent.lean`. -/
lemma freeCompare_naturality_core {r : ℕ} {T T' : Over S} (ψ : T' ⟶ T) :
    (Scheme.Modules.pullbackFreeIso T'.hom (Fin r)).inv ≫
      (pullbackTriangleIso (Over.w ψ)
        (SheafOfModules.free (R := S.ringCatSheaf) (Fin r))).inv
    = (Scheme.Modules.pullbackFreeIso ψ.left (Fin r)).inv ≫
      (Scheme.Modules.pullback ψ.left).map
        (Scheme.Modules.pullbackFreeIso T.hom (Fin r)).inv := by
  -- Step A: absorb the `pullbackCongr` cast into the free-pullback comparison.
  have hA : (Scheme.Modules.pullbackFreeIso T'.hom (Fin r)).inv ≫
      (Scheme.Modules.pullbackCongr (Over.w ψ)).inv.app
        (SheafOfModules.free (R := S.ringCatSheaf) (Fin r))
      = (Scheme.Modules.pullbackFreeIso (ψ.left ≫ T.hom) (Fin r)).inv := by
    rw [Scheme.Modules.pullbackCongr_inv_app (Over.w ψ)]
    rw [← Scheme.Modules.pullbackCongr_hom_app (Over.w ψ).symm]
    exact Scheme.Modules.pullbackFreeIso_inv_congr (Over.w ψ).symm (Fin r)
  -- Step B: invert the free coherence `pullbackFreeIso_comp`.
  have hB : (Scheme.Modules.pullbackFreeIso (ψ.left ≫ T.hom) (Fin r)).inv ≫
      (Scheme.Modules.pullbackComp ψ.left T.hom).inv.app
        (SheafOfModules.free (R := S.ringCatSheaf) (Fin r))
      = (Scheme.Modules.pullbackFreeIso ψ.left (Fin r)).inv ≫
        (Scheme.Modules.pullback ψ.left).map
          (Scheme.Modules.pullbackFreeIso T.hom (Fin r)).inv := by
    rw [← cancel_mono ((Scheme.Modules.pullback ψ.left).map
      (Scheme.Modules.pullbackFreeIso T.hom (Fin r)).hom)]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rw [Scheme.Modules.pullbackComp_inv_app_free_map ψ.left T.hom (Fin r)]
    exact Iso.inv_hom_id_assoc _ _
  simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv]
  rw [← Category.assoc, hA]
  exact hB

set_option backward.isDefEq.respectTransparency false in
/-- **Comparison with the absolute Grassmannian** for the free module: the
relative Grassmannian functor of `O_S^r` is naturally isomorphic to the merged
absolute Grassmannian functor `Grass(r, d)` evaluated on underlying schemes.
Components are `freeCompareEquiv`; naturality is
`freeCompare_naturality_core`. -/
noncomputable def freeCompare (d r : ℕ) :
    Scheme.Grassmannian (SheafOfModules.free (R := S.ringCatSheaf) (Fin r)) d ≅
      (Over.forget S).op ⋙ AlgebraicGeometry.Grassmannian.functor d r :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (freeCompareEquiv d r T.unop))
    (fun {T T'} ψ => by
      ext z
      induction z using Quotient.ind with
      | _ x =>
        change Quotient.mk _ (Scheme.LocallyFreeQuotient.toRankQuotient
            (Scheme.LocallyFreeQuotient.pullbackAlong ψ.unop x))
          = Quotient.mk _ (AlgebraicGeometry.Grassmannian.rqPullback ψ.unop.left
            (Scheme.LocallyFreeQuotient.toRankQuotient x))
        refine Quotient.sound ⟨Iso.refl _, ?_⟩
        change ((Scheme.Modules.pullbackFreeIso T'.unop.hom (Fin r)).inv ≫
            (pullbackTriangleIso (Over.w ψ.unop)
              (SheafOfModules.free (R := S.ringCatSheaf) (Fin r))).inv ≫
            (Scheme.Modules.pullback ψ.unop.left).map x.q) ≫ 𝟙 _
          = (Scheme.Modules.pullbackFreeIso ψ.unop.left (Fin r)).inv ≫
            (Scheme.Modules.pullback ψ.unop.left).map
              ((Scheme.Modules.pullbackFreeIso T.unop.hom (Fin r)).inv ≫ x.q)
        rw [Category.comp_id, Functor.map_comp]
        rw [← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ (Scheme.Modules.pullback ψ.unop.left).map x.q)
          (freeCompare_naturality_core ψ.unop))

/-! ## §3. Representability of the pulled-back absolute functor

`Scheme.{0}` has binary products (`Spec ℤ` is terminal, pullbacks exist), so
the forgetful functor `Over S ⥤ Sch` has the right adjoint `Over.star S`,
`Y ↦ (S ⨯ Y, fst)`.  The base change of the absolute Grassmannian to `S` is
`(Over.star S).obj Gr(d, r)`, and the adjunction transports the absolute
representability (`AlgebraicGeometry.Grassmannian.represents`) to `Over S`. -/

/-- The merged absolute Grassmannian functor, restricted to `Over S` along the
forgetful functor, is representable by the base change
`(Over.star S).obj Gr(d, r) = (S ⨯ Gr(d, r), fst)` of the absolute
Grassmannian scheme. -/
noncomputable def prodRepresentableBy (S : Scheme.{0}) (d r : ℕ)
    (hd : 1 ≤ d) (hdr : d ≤ r) :
    ((Over.forget S).op ⋙ AlgebraicGeometry.Grassmannian.functor d r).RepresentableBy
      ((Over.star S).obj (AlgebraicGeometry.Grassmannian.scheme d r)) where
  homEquiv {T} :=
    ((Over.forgetAdjStar S).homEquiv T
      (AlgebraicGeometry.Grassmannian.scheme d r)).symm.trans
      (AlgebraicGeometry.Grassmannian.represents d r hd hdr).homEquiv
  homEquiv_comp {T T'} f g := by
    change (AlgebraicGeometry.Grassmannian.represents d r hd hdr).homEquiv
        (((Over.forgetAdjStar S).homEquiv _ _).symm (f ≫ g)) = _
    rw [Adjunction.homEquiv_naturality_left_symm]
    exact (AlgebraicGeometry.Grassmannian.represents d r hd hdr).homEquiv_comp
      ((Over.forget S).map f) (((Over.forgetAdjStar S).homEquiv _ _).symm g)

/-! ## §4. Representability: trivialised and locally free cases -/

/-- **Representability of the relative Grassmannian, trivialised case**: for a
globally trivialised module `V ≅ O_S^r` on a locally noetherian `S` and
`1 ≤ d ≤ r`, the functor `Grass(V, d)` is representable by the base change
`S ⨯ Gr(d, r)` of the absolute Grassmannian.  Complete proof: transport the
representability of the pulled-back absolute functor
(`prodRepresentableBy`) along the comparisons `congrIso` and `freeCompare`. -/
theorem representable_of_iso_free {V : S.Modules} {r : ℕ}
    (e : V ≅ SheafOfModules.free (R := S.ringCatSheaf) (Fin r)) {d : ℕ}
    (hd : 1 ≤ d) (hdr : d ≤ r) :
    ∃ (Y : Over S), Nonempty ((Scheme.Grassmannian V d).RepresentableBy Y) :=
  ⟨(Over.star S).obj (AlgebraicGeometry.Grassmannian.scheme d r),
    ⟨(prodRepresentableBy S d r hd hdr).ofIso
      ((Scheme.Grassmannian.congrIso e d ≪≫ freeCompare d r).symm)⟩⟩

end Grassmannian

/-! ## §5. Zariski descent of representability (moved)

The definitions `overRes` / `overResHom` / `overResLE` / `IsZariskiSheafOver`
and the descent theorem `Scheme.representable_of_openCover`
(EGA 0_I 4.5.4; Stacks 01JJ) now live in
`AlgebraicJacobian/Picard/ZariskiDescentRepresentability.lean`, where the
theorem is **proved** (via mathlib's
`AlgebraicGeometry.Scheme.LocalRepresentability`, Stacks 01JJ, applied to the
small total functor of `F`). -/

/-! ## §6. Restriction of the Grassmannian to an open of the base

For a base morphism `j : S' ⟶ S`, restricting the relative Grassmannian
functor along `Over.map j : Over S' ⥤ Over S` classifies quotients of the
restricted module: the pseudofunctor comparison `pullbackComp` re-presents a
quotient of `(T.hom ≫ j)^* V` as a quotient of `T.hom^* (j^* V)`, naturally
in `T` (`restrictIso`).  Combined with the trivialised case this yields local
representability over each member of a trivialising cover of `(S, V)`
(`representable_restrict`), and Zariski descent closes the theorem. -/

namespace Grassmannian

variable {S : Scheme.{0}} [IsLocallyNoetherian S]

/-- Restriction of a quotient family along a base morphism `j : S' ⟶ S`: a
family over `(Over.map j).obj T` classifies quotients of `(T.hom ≫ j)^* V`,
which the pseudofunctor comparison `pullbackComp` re-presents as a quotient
of `T.hom^* (j^* V)`. -/
noncomputable def restrictBase {S' : Scheme.{0}} (j : S' ⟶ S) {V : S.Modules}
    {d : ℕ} {T : Over S'}
    (x : Scheme.LocallyFreeQuotient V d ((Over.map j).obj T)) :
    Scheme.LocallyFreeQuotient ((Scheme.Modules.pullback j).obj V) d T where
  F := x.F
  q := ((Scheme.Modules.pullbackComp T.hom j).app V).hom ≫ x.q
  epi :=
    @CategoryTheory.epi_comp _ _ _ _ _
      ((Scheme.Modules.pullbackComp T.hom j).app V).hom inferInstance
      x.q x.epi
  locFree := x.locFree

/-- Inverse of `restrictBase`: a quotient of `T.hom^* (j^* V)` re-presented
as a family over `(Over.map j).obj T`. -/
noncomputable def corestrictBase {S' : Scheme.{0}} (j : S' ⟶ S) {V : S.Modules}
    {d : ℕ} {T : Over S'}
    (y : Scheme.LocallyFreeQuotient ((Scheme.Modules.pullback j).obj V) d T) :
    Scheme.LocallyFreeQuotient V d ((Over.map j).obj T) where
  F := y.F
  q := ((Scheme.Modules.pullbackComp T.hom j).app V).inv ≫ y.q
  epi :=
    @CategoryTheory.epi_comp _ _ _ _ _
      ((Scheme.Modules.pullbackComp T.hom j).app V).inv inferInstance
      y.q y.epi
  locFree := y.locFree

omit [IsLocallyNoetherian S] in
/-- `restrictBase` respects the equivalence of families. -/
lemma restrictBase_rel {S' : Scheme.{0}} (j : S' ⟶ S) {V : S.Modules} {d : ℕ}
    {T : Over S'} {x y : Scheme.LocallyFreeQuotient V d ((Over.map j).obj T)}
    (h : x.Rel y) : (restrictBase j x).Rel (restrictBase j y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, ?_⟩
  change (((Scheme.Modules.pullbackComp T.hom j).app V).hom ≫ x.q) ≫ f.hom
    = ((Scheme.Modules.pullbackComp T.hom j).app V).hom ≫ y.q
  rw [Category.assoc]
  exact congrArg (((Scheme.Modules.pullbackComp T.hom j).app V).hom ≫ ·) hf

omit [IsLocallyNoetherian S] in
/-- `corestrictBase` respects the equivalence of families. -/
lemma corestrictBase_rel {S' : Scheme.{0}} (j : S' ⟶ S) {V : S.Modules} {d : ℕ}
    {T : Over S'}
    {x y : Scheme.LocallyFreeQuotient ((Scheme.Modules.pullback j).obj V) d T}
    (h : x.Rel y) : (corestrictBase j x).Rel (corestrictBase j y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, ?_⟩
  change (((Scheme.Modules.pullbackComp T.hom j).app V).inv ≫ x.q) ≫ f.hom
    = ((Scheme.Modules.pullbackComp T.hom j).app V).inv ≫ y.q
  rw [Category.assoc]
  exact congrArg (((Scheme.Modules.pullbackComp T.hom j).app V).inv ≫ ·) hf

/-- The value-level comparison between the Grassmannian of `V` over the image
of `T : Over S'` and the Grassmannian of the restricted module `j^* V`. -/
noncomputable def restrictEquiv {S' : Scheme.{0}} [IsLocallyNoetherian S']
    (j : S' ⟶ S) (V : S.Modules) (d : ℕ) (T : Over S') :
    Quotient (Scheme.LocallyFreeQuotient.setoid V d ((Over.map j).obj T)) ≃
    Quotient (Scheme.LocallyFreeQuotient.setoid
      ((Scheme.Modules.pullback j).obj V) d T) where
  toFun := Quotient.map (restrictBase j) (fun _ _ h => restrictBase_rel j h)
  invFun := Quotient.map (corestrictBase j) (fun _ _ h => corestrictBase_rel j h)
  left_inv := fun z => by
    induction z using Quotient.ind with
    | _ x =>
      refine Quotient.sound ⟨Iso.refl _, ?_⟩
      change (((Scheme.Modules.pullbackComp T.hom j).app V).inv ≫
          (((Scheme.Modules.pullbackComp T.hom j).app V).hom ≫ x.q)) ≫ 𝟙 _
        = x.q
      rw [Category.comp_id, Iso.inv_hom_id_assoc]
  right_inv := fun z => by
    induction z using Quotient.ind with
    | _ x =>
      refine Quotient.sound ⟨Iso.refl _, ?_⟩
      change (((Scheme.Modules.pullbackComp T.hom j).app V).hom ≫
          (((Scheme.Modules.pullbackComp T.hom j).app V).inv ≫ x.q)) ≫ 𝟙 _
        = x.q
      rw [Category.comp_id, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
omit [IsLocallyNoetherian S] in
/-- **Pseudofunctor coherence for the base restriction** — the naturality
core of `restrictIso`: the `pullbackComp` re-presentation commutes with the
pullback actions of the two Grassmannian functors.  An instance of
`Scheme.Modules.pullback_comp_app_coherence` after normalising the
`pullbackCongr` casts to `eqToHom`s. -/
lemma restrictBase_naturality_core {S' : Scheme.{0}} (j : S' ⟶ S)
    (V : S.Modules) {T T' : Over S'} (ψ : T' ⟶ T) :
    ((Scheme.Modules.pullbackComp T'.hom j).app V).hom ≫
      (pullbackTriangleIso (Over.w ((Over.map j).map ψ)) V).inv
    = (pullbackTriangleIso (Over.w ψ) ((Scheme.Modules.pullback j).obj V)).inv ≫
      (Scheme.Modules.pullback ψ.left).map
        ((Scheme.Modules.pullbackComp T.hom j).app V).hom := by
  have h₃ : ψ.left ≫ (T.hom ≫ j) = T'.hom ≫ j := by
    rw [← Category.assoc, Over.w ψ]
  have key := Scheme.Modules.pullback_comp_app_coherence ψ.left T.hom
    (Over.w ψ).symm j rfl rfl h₃ V
  -- move to the `hom`-form `map compT ≫ tri_ψ'.hom = tri_ψ.hom ≫ compT'`
  rw [eq_comm, Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  -- expand the triangle isos and normalise all casts to `eqToHom`
  simp only [pullbackTriangleIso, Iso.trans_hom, Iso.app_hom, Category.assoc,
    Scheme.Modules.pullbackCongr_hom_app, Scheme.Modules.pullbackCongr_inv_app,
    eqToHom_refl, Category.comp_id] at key ⊢
  exact key.symm

set_option backward.isDefEq.respectTransparency false in
/-- **Restriction comparison for the Grassmannian**: for a base morphism
`j : S' ⟶ S`, the relative Grassmannian of `V`, restricted along
`Over.map j`, is naturally isomorphic to the relative Grassmannian of the
restricted module `j^* V` over `S'`. -/
noncomputable def restrictIso {S' : Scheme.{0}} [IsLocallyNoetherian S']
    (j : S' ⟶ S) (V : S.Modules) (d : ℕ) :
    (Over.map j).op ⋙ Scheme.Grassmannian V d ≅
      Scheme.Grassmannian ((Scheme.Modules.pullback j).obj V) d :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (restrictEquiv j V d T.unop))
    (fun {T T'} ψ => by
      ext z
      induction z using Quotient.ind with
      | _ x =>
        change Quotient.mk _ (restrictBase j
            (Scheme.LocallyFreeQuotient.pullbackAlong ((Over.map j).map ψ.unop) x))
          = Quotient.mk _ (Scheme.LocallyFreeQuotient.pullbackAlong ψ.unop
            (restrictBase j x))
        refine Quotient.sound ⟨Iso.refl _, ?_⟩
        change (((Scheme.Modules.pullbackComp T'.unop.hom j).app V).hom ≫
            (pullbackTriangleIso (Over.w ((Over.map j).map ψ.unop)) V).inv ≫
            (Scheme.Modules.pullback ψ.unop.left).map x.q) ≫ 𝟙 _
          = (pullbackTriangleIso (Over.w ψ.unop)
              ((Scheme.Modules.pullback j).obj V)).inv ≫
            (Scheme.Modules.pullback ψ.unop.left).map
              (((Scheme.Modules.pullbackComp T.unop.hom j).app V).hom ≫ x.q)
        rw [Category.comp_id, Functor.map_comp]
        rw [← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ (Scheme.Modules.pullback ψ.unop.left).map x.q)
          (restrictBase_naturality_core j V ψ.unop))

/-- **Local representability over a trivialising open**: over an open
`U ⊆ S` on which `V` trivialises, the restriction of the Grassmannian
functor to `Sch/U` is representable.  Complete proof: compose the
restriction comparison `restrictIso` with the trivialised case
`representable_of_iso_free` (the trivialisation index is re-normalised from
`ULift (Fin r)` to `Fin r` through the free functor). -/
theorem representable_restrict {V : S.Modules} {r : ℕ} (U : S.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj V ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{0} (Fin r)))
    {d : ℕ} (hd : 1 ≤ d) (hdr : d ≤ r) :
    ∃ Y : Over U.toScheme,
      Nonempty (((Over.map U.ι).op ⋙ Scheme.Grassmannian V d).RepresentableBy Y) := by
  obtain ⟨Y, ⟨hY⟩⟩ := representable_of_iso_free
    (e ≪≫ (SheafOfModules.freeFunctor (R := U.toScheme.ringCatSheaf)).mapIso
      (Equiv.toIso Equiv.ulift)) hd hdr
  exact ⟨Y, ⟨hY.ofIso (restrictIso U.ι V d).symm⟩⟩

/-- **The Grassmannian functor is a Zariski sheaf** ([Nitsure] §1; the
implicit locality behind the chart construction).  Families of rank-`d`
locally free quotients glue along an open cover of the parameter scheme:
the target sheaves glue by descent of sheaves of modules along the cover
(the `Scheme.Modules.glue` engine of `GlueDescent.lean` at the glue datum of
the cover), the quotient maps glue through the descent-equalizer lift
`Scheme.Modules.glueLift`, local freeness and epi-ness are local, and the
glued family is unique up to the equivalence `ker q = ker q'` because an
isomorphism of quotients commuting with the epimorphisms is unique when it
exists, so the local comparison isos satisfy the descent cocycle for free.
Proved in `GrassmannianZariskiSheaf.lean`
(`Scheme.grassmannian_isZariskiSheafOver`). -/
theorem isZariskiSheaf (V : S.Modules) (d : ℕ) :
    IsZariskiSheafOver (Scheme.Grassmannian V d) :=
  Scheme.grassmannian_isZariskiSheafOver V d

/-- **Representability of the Grassmannian** (`thm:grassmannian_representable`,
[Nitsure] §1 "Construction of Grassmannian", Exercise (2)): for a locally
noetherian `S`, a locally free `O_S`-module `V` of rank `r`, and `1 ≤ d ≤ r`,
the functor `Grass(V, d)` is representable by an `S`-scheme.  Proof: `V`
trivialises on an open cover of `S`; over each member the functor is
representable (`representable_restrict`, via the merged absolute chart
construction), and representability descends along the cover
(`Scheme.representable_of_openCover`) since the Grassmannian functor is a
Zariski sheaf (`isZariskiSheaf`). -/
theorem representable {V : S.Modules} {r : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank V r) {d : ℕ}
    (hd : 1 ≤ d) (hdr : d ≤ r) :
    ∃ (Y : Over S), Nonempty ((Scheme.Grassmannian V d).RepresentableBy Y) := by
  obtain ⟨ι, U, hU, hloc⟩ := hV
  refine representable_of_openCover (Scheme.Grassmannian V d)
    (isZariskiSheaf V d) U hU (fun i => ?_)
  obtain ⟨e⟩ := hloc i
  exact representable_restrict (U i) e hd hdr

/-! ## §7. The universal quotient on the chosen representing scheme -/

/-- A chosen representing scheme for the relative Grassmannian.  This makes
the existential output of `representable` available to constructions, such as
the universal evaluation cokernel used in the divisor locus. -/
noncomputable def representingScheme {V : S.Modules} {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank V r)
    (hd : 1 ≤ d) (hdr : d ≤ r) : Over S :=
  Classical.choose (representable hV hd hdr)

/-- The chosen representation carried by `representingScheme`. -/
noncomputable def representation {V : S.Modules} {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank V r)
    (hd : 1 ≤ d) (hdr : d ≤ r) :
    (Scheme.Grassmannian V d).RepresentableBy
      (representingScheme hV hd hdr) :=
  Classical.choice (Classical.choose_spec (representable hV hd hdr))

/-- The universal Grassmannian class: the image of the identity of the chosen
representing scheme under its `RepresentableBy` equivalence. -/
noncomputable def universalClass {V : S.Modules} {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank V r)
    (hd : 1 ≤ d) (hdr : d ≤ r) :
    (Scheme.Grassmannian V d).obj
      (Opposite.op (representingScheme hV hd hdr)) :=
  (representation hV hd hdr).homEquiv (𝟙 _)

/-- A quotient representative of the universal Grassmannian class.  Choosing
the representative exposes its sheaf and quotient map to the D3 construction;
all moduli statements remain at the quotient-class level. -/
noncomputable def universalQuotient {V : S.Modules} {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank V r)
    (hd : 1 ≤ d) (hdr : d ≤ r) :
    LocallyFreeQuotient V d (representingScheme hV hd hdr) :=
  Quotient.out (universalClass hV hd hdr)

/-- The chosen universal quotient represents the universal class. -/
theorem mk_universalQuotient {V : S.Modules} {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank V r)
    (hd : 1 ≤ d) (hdr : d ≤ r) :
    Quotient.mk _ (universalQuotient hV hd hdr) =
      universalClass hV hd hdr :=
  Quotient.out_eq _

/-- Every point of the chosen representing scheme classifies the pullback of
the universal quotient.  This is the representation-facing universal-family
identity needed before forming a sheaf on `X ×_S Gr(V,d)`. -/
theorem homEquiv_eq_pullback_universalQuotient
    {V : S.Modules} {r d : ℕ}
    (hV : SheafOfModules.IsLocallyFreeOfRank V r)
    (hd : 1 ≤ d) (hdr : d ≤ r)
    {T : Over S} (f : T ⟶ representingScheme hV hd hdr) :
    (representation hV hd hdr).homEquiv f =
      Quotient.mk _ (LocallyFreeQuotient.pullbackAlong f
        (universalQuotient hV hd hdr)) := by
  calc
    (representation hV hd hdr).homEquiv f =
        (Scheme.Grassmannian V d).map f.op
          ((representation hV hd hdr).homEquiv (𝟙 _)) := by
      rw [← (representation hV hd hdr).homEquiv_comp f (𝟙 _),
        Category.comp_id]
    _ = (Scheme.Grassmannian V d).map f.op
          (Quotient.mk _ (universalQuotient hV hd hdr)) := by
      exact congrArg ((Scheme.Grassmannian V d).map f.op)
        (mk_universalQuotient hV hd hdr).symm
    _ = Quotient.mk _ (LocallyFreeQuotient.pullbackAlong f
          (universalQuotient hV hd hdr)) := rfl

end Grassmannian

end Scheme

end AlgebraicGeometry
