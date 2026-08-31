/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianPhi
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The Grassmannian glue data and glued scheme over a field (DD-3, stage 3a)

The scheme-level chart layer of the DD-3 Grassmannian port: the principal-open chart
overlaps `U^I_J = Spec R^I[1/P^I_J]`, the transition isomorphisms, the triple-overlap
`t'`-morphisms with their `t_fac` and cocycle coherences, and the assembled
`AlgebraicGeometry.Scheme.GlueData` whose `glued` is the Grassmannian scheme `Gr(d, r)`
over the base field `k` (`informal/spec-dd-3.md` §2/§3; route map: the GR-Quot-Closure
tree's `GrassmannianCells.lean` glue section).

* `AlgebraicGeometry.Grassmannian.chartOverlap`, `chartIncl`, `chartTransition`: the
  `V`/`f`/`t`-fields of the glue data.
* `AlgebraicGeometry.Grassmannian.awayPullbackIso`: the pullback of two principal opens
  `Spec R[1/x] ← Spec R → Spec R[1/y]` is `Spec R[1/(xy)]`, with its two leg lemmas.
* `AlgebraicGeometry.Grassmannian.chartTransition'`: the triple-overlap `t'`-field;
  `chartTransition'_fac`, `chartTransition'_cocycle`: the coherences (reduced to the
  ring identities `chartTransition'_ringIdentity` and `cocyclePhiId`).
* `AlgebraicGeometry.Grassmannian.glueData`, `grScheme`: **the Grassmannian glue data
  and scheme** over `k`, glued from the `Nat.choose r d` affine charts, with the
  finiteness instance on the chart index.
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Grassmannian

/-- The principal-open chart overlap `U^I_J = Spec R^I[1/P^I_J]`: the `V`-object of the
Grassmannian glue data. -/
noncomputable def chartOverlap (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) : Scheme :=
  Spec (CommRingCat.of (Localization.Away (minorDet k d r I J hI hJ)))

/-- The canonical open immersion `U^I_J → U^I` of the principal open into the chart:
the `f`-field of the Grassmannian glue data. -/
noncomputable def chartIncl (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) :
    chartOverlap k d r I J hI hJ ⟶ affineChart k d r I :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (ChartRing k d r I) (Localization.Away (minorDet k d r I J hI hJ))))

instance chartIncl_isOpenImmersion (k : Type u) [Field k] (d r : ℕ)
    (I J : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) :
    IsOpenImmersion (chartIncl k d r I J hI hJ) :=
  inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (ChartRing k d r I) (Localization.Away (minorDet k d r I J hI hJ))))))

/-- The self-inclusion `U^I_I → U^I` is an isomorphism: since `P^I_I = 1`
(`minorDet_self`) the away-localisation is the identity, so its `Spec` is an iso.
The `f_id`-field of the Grassmannian glue data. -/
theorem chartIncl_self_isIso (k : Type u) [Field k] (d r : ℕ) (I : Finset (Fin r))
    (hI : I.card = d) : IsIso (chartIncl k d r I I hI hI) := by
  have hx : IsUnit (minorDet k d r I I hI hI) := by rw [minorDet_self]; exact isUnit_one
  have e : ChartRing k d r I ≃ₐ[_] Localization.Away (minorDet k d r I I hI hI) :=
    IsLocalization.atUnit _ (Localization.Away (minorDet k d r I I hI hI)) _ hx
  have hbij : Function.Bijective
      (algebraMap (ChartRing k d r I) (Localization.Away (minorDet k d r I I hI hI))) := by
    have hfun : (⇑(algebraMap (ChartRing k d r I)
        (Localization.Away (minorDet k d r I I hI hI)))) = ⇑e := by
      funext y; simp [← e.commutes y]
    rw [hfun]; exact e.bijective
  have : IsIso (CommRingCat.ofHom
      (algebraMap (ChartRing k d r I) (Localization.Away (minorDet k d r I I hI hI)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  change IsIso (Spec.map (CommRingCat.ofHom
    (algebraMap (ChartRing k d r I) (Localization.Away (minorDet k d r I I hI hI)))))
  infer_instance

/-- The scheme-level transition `U^I_J → U^J_I`, the comorphism (`Spec.map`) of the
transition map `θ_{I,J} : R^J[1/P^J_I] →ₐ[k] R^I[1/P^I_J]`: the `t`-field of the
Grassmannian glue data. -/
noncomputable def chartTransition (k : Type u) [Field k] (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) :
    chartOverlap k d r I J hI hJ ⟶ chartOverlap k d r J I hJ hI :=
  Spec.map (CommRingCat.ofHom (transitionMap k d r I J hI hJ).toRingHom)

/-- `t_{I,I} = id`: the self-transition is the identity, from `transitionMap_self`.
The `t_id`-field of the Grassmannian glue data. -/
theorem chartTransition_self (k : Type u) [Field k] (d r : ℕ) (I : Finset (Fin r))
    (hI : I.card = d) :
    chartTransition k d r I I hI hI
      = CategoryTheory.CategoryStruct.id (chartOverlap k d r I I hI hI) := by
  rw [chartTransition, transitionMap_self]
  rw [show (AlgHom.id k (Localization.Away (minorDet k d r I I hI hI))).toRingHom
      = RingHom.id (Localization.Away (minorDet k d r I I hI hI)) from rfl,
    CommRingCat.ofHom_id, Spec.map_id]
  rfl

/-- The pullback of two principal-open inclusions
`Spec R[1/x] → Spec R ← Spec R[1/y]` is `Spec R[1/(xy)]`: combine `pullbackSpecIso`
(the pullback is `Spec` of the tensor product) with the localisation identification
`R[1/x] ⊗_R R[1/y] ≅ R[1/(xy)]`.  Stated over a general base ring so its proof term
carries the needed `IsScalarTower` instances (avoiding a typeclass timeout over the
heavy chart ring). -/
noncomputable def awayPullbackIso {A : Type*} [CommRing A] (x y : A) :
    Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x))))
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away y)))) ≅
      Spec (CommRingCat.of (Localization.Away (x * y))) :=
  letI : IsLocalization.Away (x * y)
      (TensorProduct A (Localization.Away x) (Localization.Away y)) :=
    IsLocalization.Away.mul' (Localization.Away x) _ x y
  (pullbackSpecIso A (Localization.Away x) (Localization.Away y)) ≪≫
    Scheme.Spec.mapIso
      ((IsLocalization.algEquiv (Submonoid.powers (x * y))
        (TensorProduct A (Localization.Away x) (Localization.Away y))
        (Localization.Away (x * y))).toRingEquiv.toCommRingCatIso).symm.op

/-- The first leg of `awayPullbackIso`: under the identification
`pullback ≅ Spec R[1/(xy)]`, the projection to `Spec R[1/x]` is `Spec.map` of the
left away-inclusion.  The `pullback.fst`-compatibility for the `t_fac` field. -/
theorem awayPullbackIso_inv_fst (k : Type u) [Field k] {A : Type u} [CommRing A]
    [Algebra k A] (x y : A) :
    (awayPullbackIso x y).inv ≫
        Limits.pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x))))
          (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away y))))
      = Spec.map (CommRingCat.ofHom (awayInclLeft k x y).toRingHom) := by
  letI : IsLocalization.Away (x * y)
      (TensorProduct A (Localization.Away x) (Localization.Away y)) :=
    IsLocalization.Away.mul' (Localization.Away x) _ x y
  rw [awayPullbackIso, Iso.trans_inv, Category.assoc, pullbackSpecIso_inv_fst,
    show (Scheme.Spec.mapIso ((IsLocalization.algEquiv (Submonoid.powers (x * y))
        (TensorProduct A (Localization.Away x) (Localization.Away y))
        (Localization.Away (x * y))).toRingEquiv.toCommRingCatIso).symm.op).inv
      = Spec.map ((IsLocalization.algEquiv (Submonoid.powers (x * y))
        (TensorProduct A (Localization.Away x) (Localization.Away y))
        (Localization.Away (x * y))).toRingEquiv.toCommRingCatIso).hom from rfl,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingEquiv.toCommRingCatIso_hom]
  apply IsLocalization.ringHom_ext (Submonoid.powers x)
  ext w
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeftRingHom_apply]
  rw [show (awayInclLeft k x y).toRingHom (algebraMap A (Localization.Away x) w)
      = algebraMap A (Localization.Away (x * y)) w from
    awayInclLeft_algebraMap_apply k x y w,
    ← Algebra.TensorProduct.algebraMap_apply]
  exact (IsLocalization.algEquiv (Submonoid.powers (x * y))
    (TensorProduct A (Localization.Away x) (Localization.Away y))
    (Localization.Away (x * y))).commutes w

/-- The second leg of `awayPullbackIso`: under the identification
`pullback ≅ Spec R[1/(xy)]`, the projection to `Spec R[1/y]` is `Spec.map` of the
right away-inclusion. -/
theorem awayPullbackIso_inv_snd (k : Type u) [Field k] {A : Type u} [CommRing A]
    [Algebra k A] (x y : A) :
    (awayPullbackIso x y).inv ≫
        Limits.pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x))))
          (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away y))))
      = Spec.map (CommRingCat.ofHom (awayInclRight k x y).toRingHom) := by
  letI : IsLocalization.Away (x * y)
      (TensorProduct A (Localization.Away x) (Localization.Away y)) :=
    IsLocalization.Away.mul' (Localization.Away x) _ x y
  rw [awayPullbackIso, Iso.trans_inv, Category.assoc, pullbackSpecIso_inv_snd,
    show (Scheme.Spec.mapIso ((IsLocalization.algEquiv (Submonoid.powers (x * y))
        (TensorProduct A (Localization.Away x) (Localization.Away y))
        (Localization.Away (x * y))).toRingEquiv.toCommRingCatIso).symm.op).inv
      = Spec.map ((IsLocalization.algEquiv (Submonoid.powers (x * y))
        (TensorProduct A (Localization.Away x) (Localization.Away y))
        (Localization.Away (x * y))).toRingEquiv.toCommRingCatIso).hom from rfl,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingEquiv.toCommRingCatIso_hom]
  apply IsLocalization.ringHom_ext (Submonoid.powers y)
  ext w
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply]
  rw [show (awayInclRight k x y).toRingHom (algebraMap A (Localization.Away y) w)
      = algebraMap A (Localization.Away (x * y)) w from
    awayInclRight_algebraMap_apply k x y w]
  rw [show (1 : Localization.Away x) ⊗ₜ[A] (algebraMap A (Localization.Away y) w)
      = algebraMap A (TensorProduct A (Localization.Away x) (Localization.Away y)) w from by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
          Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']]
  exact (IsLocalization.algEquiv (Submonoid.powers (x * y))
    (TensorProduct A (Localization.Away x) (Localization.Away y))
    (Localization.Away (x * y))).commutes w

/-- The triple-overlap `t'`-field of the Grassmannian glue data: the morphism
`U^I_J ×_{U^I} U^I_K ⟶ U^J_K ×_{U^J} U^J_I` reconciling the two pullbacks via the
away-pullback identification, the localised transition `Θ_{I,J}`, and the order-swap
isomorphism. -/
noncomputable def chartTransition' (k : Type u) [Field k] (d r : ℕ)
    (I J K : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    Limits.pullback (chartIncl k d r I J hI hJ) (chartIncl k d r I K hI hK) ⟶
      Limits.pullback (chartIncl k d r J K hJ hK) (chartIncl k d r J I hJ hI) :=
  (awayPullbackIso (minorDet k d r I J hI hJ) (minorDet k d r I K hI hK)).hom ≫
    Spec.map (CommRingCat.ofHom (cocycleΘIJ k d r I J K hI hJ hK).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (awayMulCommAlgEquiv k (minorDet k d r J K hJ hK)
        (minorDet k d r J I hJ hI)).toAlgHom.toRingHom) ≫
    (awayPullbackIso (minorDet k d r J K hJ hK) (minorDet k d r J I hJ hI)).inv

/-- The ring-hom identity underlying the `t_fac` coherence field: over the
triple-overlap rings, the localised transition `Θ_{I,J}` pre-composed with the
order-swap and right inclusion equals the left inclusion post-composed with the plain
transition `θ_{I,J}`.  Both reduce to `ι^L ∘ θ̃_{I,J}`. -/
theorem chartTransition'_ringIdentity (k : Type u) [Field k] (d r : ℕ)
    (I J K : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    (cocycleΘIJ k d r I J K hI hJ hK).toRingHom.comp
        ((awayMulCommAlgEquiv k (minorDet k d r J K hJ hK)
            (minorDet k d r J I hJ hI)).toAlgHom.toRingHom.comp
          (awayInclRight k (minorDet k d r J K hJ hK)
            (minorDet k d r J I hJ hI)).toRingHom)
      = (awayInclLeft k (minorDet k d r I J hI hJ)
            (minorDet k d r I K hI hK)).toRingHom.comp
          (transitionMap k d r I J hI hJ).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (minorDet k d r J I hJ hI))
  rw [RingHom.comp_assoc, RingHom.comp_assoc, awayInclRight_comp_algebraMap,
    awayMulCommAlgEquiv_comp_algebraMap, cocycleΘIJ_comp_algebraMap,
    RingHom.comp_assoc, transitionMap_comp_algebraMap]
  rfl

set_option maxHeartbeats 1600000 in
-- The `erw` through the `HasPullback` instance diamond on the heavy `MvPolynomial`
-- localisation objects is defeq-expensive; the raised limit covers it (elaboration
-- cost, not a kernel raise — the GRQ route map carries the same raise here).
/-- The `t_fac`-compatibility field of the Grassmannian glue data: the triple-overlap
transition `t'` is compatible with the projections, `t' ≫ pr₂ = pr₁ ≫ t_{I,J}`.
Reduces, both pullbacks being affine, to `chartTransition'_ringIdentity` via the leg
lemmas. -/
theorem chartTransition'_fac (k : Type u) [Field k] (d r : ℕ) (I J K : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    chartTransition' k d r I J K hI hJ hK ≫
        Limits.pullback.snd (chartIncl k d r J K hJ hK) (chartIncl k d r J I hJ hI)
      = Limits.pullback.fst (chartIncl k d r I J hI hJ) (chartIncl k d r I K hI hK) ≫
          chartTransition k d r I J hI hJ := by
  have hfstc : (awayPullbackIso (minorDet k d r I J hI hJ)
        (minorDet k d r I K hI hK)).inv ≫
        Limits.pullback.fst (chartIncl k d r I J hI hJ) (chartIncl k d r I K hI hK)
      = Spec.map (CommRingCat.ofHom
          (awayInclLeft k (minorDet k d r I J hI hJ)
            (minorDet k d r I K hI hK)).toRingHom) :=
    awayPullbackIso_inv_fst k _ _
  have hfst := (Iso.inv_comp_eq _).mp hfstc
  have hXY : Spec.map (CommRingCat.ofHom (cocycleΘIJ k d r I J K hI hJ hK).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (awayMulCommAlgEquiv k (minorDet k d r J K hJ hK)
            (minorDet k d r J I hJ hI)).toAlgHom.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (awayInclRight k (minorDet k d r J K hJ hK)
              (minorDet k d r J I hJ hI)).toRingHom)
      = Spec.map (CommRingCat.ofHom
            (awayInclLeft k (minorDet k d r I J hI hJ)
              (minorDet k d r I K hI hK)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (transitionMap k d r I J hI hJ).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, chartTransition'_ringIdentity]
  rw [hfst, chartTransition']
  simp only [Category.assoc]
  erw [awayPullbackIso_inv_snd k (minorDet k d r J K hJ hK) (minorDet k d r J I hJ hI)]
  simp only [chartTransition]
  exact congrArg (_ ≫ ·) hXY

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
-- The `simp`/`Iso.inv_hom_id_assoc` cancellation of the conjugating pullback
-- isomorphisms over the heavy localisation objects is defeq-expensive; raised limit
-- (elaboration cost — same raise as the GRQ route map).
/-- The **scheme-level cocycle** field of the Grassmannian glue data: the threefold
composite of triple-overlap transitions is the identity.  The two internal
conjugating-pullback pairs cancel, the six `Spec`-arrows collapse into a single `Spec`
of the rotated ring cocycle `Φ`, and `cocyclePhiId` (`Φ = id`) closes it. -/
theorem chartTransition'_cocycle (k : Type u) [Field k] (d r : ℕ)
    (I J K : Finset (Fin r)) (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    chartTransition' k d r I J K hI hJ hK ≫ chartTransition' k d r J K I hJ hK hI ≫
        chartTransition' k d r K I J hK hI hJ
      = CategoryTheory.CategoryStruct.id
          (Limits.pullback (chartIncl k d r I J hI hJ) (chartIncl k d r I K hI hK)) := by
  have hPhi : (cocycleΘIJ k d r I J K hI hJ hK).toRingHom.comp
        ((awayMulCommAlgEquiv k (minorDet k d r J K hJ hK)
            (minorDet k d r J I hJ hI)).toAlgHom.toRingHom.comp
          ((cocycleΘIJ k d r J K I hJ hK hI).toRingHom.comp
            ((awayMulCommAlgEquiv k (minorDet k d r K I hK hI)
                (minorDet k d r K J hK hJ)).toAlgHom.toRingHom.comp
              ((cocycleΘIJ k d r K I J hK hI hJ).toRingHom.comp
                (awayMulCommAlgEquiv k (minorDet k d r I J hI hJ)
                  (minorDet k d r I K hI hK)).toAlgHom.toRingHom))))
      = RingHom.id (Localization.Away
          (minorDet k d r I J hI hJ * minorDet k d r I K hI hK)) :=
    congrArg AlgHom.toRingHom (cocyclePhiId k d r I J K hI hJ hK)
  have h6 : Spec.map (CommRingCat.ofHom (cocycleΘIJ k d r I J K hI hJ hK).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (awayMulCommAlgEquiv k (minorDet k d r J K hJ hK)
          (minorDet k d r J I hJ hI)).toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (cocycleΘIJ k d r J K I hJ hK hI).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (awayMulCommAlgEquiv k (minorDet k d r K I hK hI)
          (minorDet k d r K J hK hJ)).toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (cocycleΘIJ k d r K I J hK hI hJ).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (awayMulCommAlgEquiv k (minorDet k d r I J hI hJ)
          (minorDet k d r I K hI hK)).toAlgHom.toRingHom)
      = CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of (Localization.Away
          (minorDet k d r I J hI hJ * minorDet k d r I K hI hK)))) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hPhi, CommRingCat.ofHom_id, Spec.map_id]
  simp only [chartTransition', Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h6, Iso.hom_inv_id]

/-- The **Grassmannian glue data** over the base field `k`: charts `affineChart`,
overlaps `chartOverlap`, inclusions `chartIncl`, transitions `chartTransition`, with
the cocycle `chartTransition'_cocycle`; indexed by the size-`d` subsets of `Fin r`. -/
noncomputable def glueData (k : Type u) [Field k] (d r : ℕ) : Scheme.GlueData.{u} where
  J := ULift.{u} {I : Finset (Fin r) // I.card = d}
  U I := affineChart k d r I.down.1
  V p := chartOverlap k d r p.1.down.1 p.2.down.1 p.1.down.2 p.2.down.2
  f I J := chartIncl k d r I.down.1 J.down.1 I.down.2 J.down.2
  f_id I := chartIncl_self_isIso k d r I.down.1 I.down.2
  f_open I J := chartIncl_isOpenImmersion k d r I.down.1 J.down.1 I.down.2 J.down.2
  t I J := chartTransition k d r I.down.1 J.down.1 I.down.2 J.down.2
  t_id I := chartTransition_self k d r I.down.1 I.down.2
  t' I J K := chartTransition' k d r I.down.1 J.down.1 K.down.1 I.down.2 J.down.2 K.down.2
  t_fac I J K := chartTransition'_fac k d r I.down.1 J.down.1 K.down.1 I.down.2 J.down.2 K.down.2
  cocycle I J K :=
    chartTransition'_cocycle k d r I.down.1 J.down.1 K.down.1 I.down.2 J.down.2 K.down.2

/-- **The Grassmannian scheme** `Gr(d, r)` over the base field `k`: the scheme glued
from the `Nat.choose r d` affine charts `U^I` along the Cramer transition
isomorphisms. -/
noncomputable def grScheme (k : Type u) [Field k] (d r : ℕ) : Scheme :=
  (glueData k d r).glued

/-- The chart index of the Grassmannian glue data is finite (the `Nat.choose r d`
subsets): the finite-atlas fact consumed by the DD-Q quasi-compactness bundle. -/
instance finite_glueData_J (k : Type u) [Field k] (d r : ℕ) :
    Finite (glueData k d r).J :=
  inferInstanceAs (Finite (ULift {I : Finset (Fin r) // I.card = d}))

/-- The Grassmannian scheme is quasi-compact: it is glued from the finitely many
affine charts `U^I`, each the spectrum of a ring. -/
instance compactSpace_grScheme (k : Type u) [Field k] (d r : ℕ) :
    CompactSpace (grScheme k d r) := by
  haveI : Finite (glueData k d r).openCover.I₀ :=
    inferInstanceAs (Finite (ULift {I : Finset (Fin r) // I.card = d}))
  haveI : ∀ i, CompactSpace ((glueData k d r).openCover.X i) := fun i =>
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of (ChartRing k d r i.down.1))))
  exact (glueData k d r).openCover.compactSpace

end AlgebraicGeometry.Grassmannian
