/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.ModulesPushforwardBaseChange

/-!
# The canonical pushforward base-change mate on base-map sections

This file identifies the action of `canonicalBaseChangeMap` on the canonical
sections supplied by the unit of `pullback ⊣ pushforward`.  The formula is
pure adjunction and pullback-pseudofunctor coherence: it has no flatness,
finiteness, affineness, or quasi-coherence hypotheses.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

private noncomputable def pullback_app_isoTensor_unitAtV
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules) (V : X.Opens) :
    Γ(N, V) →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj N), V) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).val.app (.op V)).hom

/-- The adjunction-unit base map, restricted from `g ⁻¹ᵁ V` to `U`. -/
noncomputable def pullback_app_isoTensor_baseMap
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    {U : Y.Opens} {V : X.Opens} (e : U ≤ g ⁻¹ᵁ V) :
    letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
    letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj N, U) :=
      Module.compHom _ (g.appLE V U e).hom
    Γ(N, V) →ₗ[Γ(X, V)] Γ((Scheme.Modules.pullback g).obj N, U) := by
  letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
  letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj N, U) :=
    Module.compHom _ (g.appLE V U e).hom
  let restr := (((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE e).op).hom
  let unit := pullback_app_isoTensor_unitAtV g N V
  refine
    { toFun := fun x => restr (unit x)
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    change restr (unit (x + y)) = restr (unit x) + restr (unit y)
    rw [unit.map_add]
    exact restr.map_add _ _
  · intro r x
    change restr (unit (r • x)) = (g.appLE V U e).hom r • restr (unit x)
    rw [unit.map_smul]
    exact ((Scheme.Modules.pullback g).obj N).map_smul (homOfLE e) _ _

set_option backward.isDefEq.respectTransparency false in
private lemma modules_res_res
    {Y : Scheme.{u}} (N : Y.Modules) {W₁ W₂ W₃ : Y.Opens}
    (i₁ : W₁ ≤ W₂) (i₂ : W₂ ≤ W₃) (i₃ : W₁ ≤ W₃) (x : Γ(N, W₃)) :
    (N.presheaf.map (homOfLE i₁).op).hom ((N.presheaf.map (homOfLE i₂).op).hom x) =
      (N.presheaf.map (homOfLE i₃).op).hom x := by
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp, ← op_comp]
  exact (congrArg (fun (i : W₁ ⟶ W₃) =>
    (AddCommGrpCat.Hom.hom (N.presheaf.map i.op)) x) (Subsingleton.elim _ _)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical pullback base map commutes with restriction on both the source and target
opens. -/
lemma pullback_app_isoTensor_baseMap_res
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    {V' V'' : X.Opens} {W' W'' : Y.Opens}
    (hW' : W' ≤ g ⁻¹ᵁ V') (hW'' : W'' ≤ g ⁻¹ᵁ V'')
    (hV : V'' ≤ V') (hW : W'' ≤ W') (x : Γ(N, V')) :
    (((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE hW).op).hom
        (pullback_app_isoTensor_baseMap g N hW' x) =
      pullback_app_isoTensor_baseMap g N hW''
        ((N.presheaf.map (homOfLE hV).op).hom x) := by
  have hnat := congrArg
    (fun (k : Γ(N, V') ⟶
        Γ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj N), V'')) =>
      (AddCommGrpCat.Hom.hom k) x)
    ((Scheme.Modules.Hom.mapPresheaf
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N)).naturality
      (homOfLE hV).op)
  have hL := modules_res_res ((Scheme.Modules.pullback g).obj N)
    hW hW' (hW.trans hW')
    ((Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V').hom x)
  have hR := modules_res_res ((Scheme.Modules.pullback g).obj N)
    hW'' (Scheme.Hom.preimage_mono g hV) (hW.trans hW')
    ((Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V').hom x)
  change (((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE hW).op).hom
      ((((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE hW').op).hom
        ((Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V').hom x)) =
    (((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE hW'').op).hom
      ((Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V'').hom
        ((N.presheaf.map (homOfLE hV).op).hom x))
  rw [hL]
  refine hR.symm.trans ?_
  exact (congrArg
    (fun w => (((Scheme.Modules.pullback g).obj N).presheaf.map (homOfLE hW'').op).hom w)
    hnat).symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical pullback base map is natural in the module. -/
lemma pullback_app_isoTensor_baseMap_naturality
    {X Y : Scheme.{u}} (g : Y ⟶ X) {N N' : X.Modules}
    (h : N ⟶ N') {U : Y.Opens} {V : X.Opens} (e : U ≤ g ⁻¹ᵁ V) (x : Γ(N, V)) :
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map h) U).hom
        (pullback_app_isoTensor_baseMap g N e x) =
      pullback_app_isoTensor_baseMap g N' e ((Scheme.Modules.Hom.app h V).hom x) := by
  have hb := congrArg
    (fun (k : N ⟶ (Scheme.Modules.pushforward g).obj
        ((Scheme.Modules.pullback g).obj N')) =>
      (Scheme.Modules.Hom.app k V).hom x)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality h)
  have ha := congrArg
    (fun (k : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ V) ⟶
        Γ((Scheme.Modules.pullback g).obj N', U)) =>
      (AddCommGrpCat.Hom.hom k)
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app V x))
    ((Scheme.Modules.Hom.mapPresheaf ((Scheme.Modules.pullback g).map h)).naturality
      (homOfLE e).op)
  exact ha.trans (congrArg
    (fun w => ((((Scheme.Modules.pullback g).obj N').presheaf.map (homOfLE e).op).hom) w)
    hb.symm)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical pullback base map is compatible with equality of scheme morphisms. -/
lemma pullback_app_isoTensor_baseMap_congr
    {X Y : Scheme.{u}} {g g' : Y ⟶ X} (hgg' : g = g')
    (N : X.Modules) {U : Y.Opens} {V : X.Opens} (e : U ≤ g ⁻¹ᵁ V) (e' : U ≤ g' ⁻¹ᵁ V)
    (x : Γ(N, V)) :
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hgg').hom.app N) U).hom
        (pullback_app_isoTensor_baseMap g N e x) =
      pullback_app_isoTensor_baseMap g' N e' x := by
  subst hgg'
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Expanding the composed adjunction unit traverses nested pullback transports.
/-- The canonical pullback base map is compatible with composition of scheme morphisms. -/
lemma pullback_app_isoTensor_baseMap_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules)
    {T : X.Opens} {V : Y.Opens} {U : Z.Opens}
    (eV : V ≤ g ⁻¹ᵁ U) (eT : T ≤ f ⁻¹ᵁ V) (eTU : T ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(N, U)) :
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app N) T).hom
        (pullback_app_isoTensor_baseMap f ((Scheme.Modules.pullback g).obj N) eT
          (pullback_app_isoTensor_baseMap g N eV x)) =
      pullback_app_isoTensor_baseMap (f ≫ g) N eTU x := by
  have hs1 := congrArg
    (fun (k : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ U) ⟶
        Γ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj
          ((Scheme.Modules.pullback g).obj N)), V)) =>
      (AddCommGrpCat.Hom.hom k)
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app U x))
    ((Scheme.Modules.Hom.mapPresheaf
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj N))).naturality (homOfLE eV).op)
  have hconj := Scheme.Modules.conjugateEquiv_pullbackComp_inv f g
  have hunit := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    ((Scheme.Modules.pullbackComp f g).inv) N
  rw [hconj] at hunit
  have hs2 := congrArg
    (fun (k : N ⟶ (Scheme.Modules.pushforward (f ≫ g)).obj
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N))) =>
      (Scheme.Modules.Hom.app k U).hom x) hunit
  have hs3 := congrArg
    (fun (k : Γ((Scheme.Modules.pullback (f ≫ g)).obj N, (f ≫ g) ⁻¹ᵁ U) ⟶
        Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N), T)) =>
      (AddCommGrpCat.Hom.hom k)
        (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app N).app U x))
    ((Scheme.Modules.Hom.mapPresheaf
      ((Scheme.Modules.pullbackComp f g).inv.app N)).naturality (homOfLE eTU).op)
  have hs4 : ∀ (z : Γ((Scheme.Modules.pullback (f ≫ g)).obj N, T)),
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app N) T).hom
        ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).inv.app N) T).hom z) =
        z := fun z => congrArg
    (fun (k : (Scheme.Modules.pullback (f ≫ g)).obj N ⟶
        (Scheme.Modules.pullback (f ≫ g)).obj N) =>
      (Scheme.Modules.Hom.app k T).hom z)
    (Iso.inv_hom_id_app (Scheme.Modules.pullbackComp f g) N)
  refine (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app N) T).hom
      ((((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)).presheaf.map
        (homOfLE eT).op).hom w)) hs1).trans ?_
  refine (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app N) T).hom w)
    (modules_res_res ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N))
      eT ((fun _ ha => eV ha) : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U))
      eTU (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj N)).app (g ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app U x)))).trans ?_
  refine (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app N) T).hom
      ((((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)).presheaf.map
        (homOfLE eTU).op).hom w)) hs2).trans ?_
  refine (congrArg (fun w =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f g).hom.app N) T).hom w)
    hs3.symm).trans ?_
  exact hs4 _

set_option backward.isDefEq.respectTransparency false in
/-- On the full preimage of an open, `pullback_app_isoTensor_baseMap` is exactly the component of
the pullback--pushforward adjunction unit. -/
lemma pullback_app_isoTensor_baseMap_le_refl
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules) (V : X.Opens) (x : Γ(N, V)) :
    pullback_app_isoTensor_baseMap g N (le_refl (g ⁻¹ᵁ V)) x =
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V).hom x := by
  change ((((Scheme.Modules.pullback g).obj N).presheaf.map
      (homOfLE (le_refl (g ⁻¹ᵁ V))).op).hom)
      ((Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N) V).hom x) = _
  rw [show (homOfLE (le_refl (g ⁻¹ᵁ V))).op = 𝟙 (Opposite.op (g ⁻¹ᵁ V)) from rfl,
    CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
-- The mate calculation expands two adjunctions and three pullback coherence isomorphisms.
/-- The canonical base-change mate sends the unit base-map image along `g`
to the unit base-map image along `g'` on every compatible pair of opens. -/
theorem canonicalBaseChangeMap_app_baseMap_compat
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g)
    (F : X.Modules) {V : S.Opens} {U : S'.Opens}
    (e : U ≤ g ⁻¹ᵁ V) (e' : f' ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V))
    (x : Γ((Scheme.Modules.pushforward f).obj F, V)) :
    (((canonicalBaseChangeMap sq).app F).app U).hom
        (pullback_app_isoTensor_baseMap g ((Scheme.Modules.pushforward f).obj F) e x) =
      pullback_app_isoTensor_baseMap g' F e' x := by
  have e₂ : f' ⁻¹ᵁ U ≤ (f' ≫ g) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage]
    exact fun a ha => e ha
  have e₃ : f' ⁻¹ᵁ U ≤ (g' ≫ f) ⁻¹ᵁ V := by
    rw [sq.w, Scheme.Hom.comp_preimage]
    exact fun a ha => e ha
  have h1 := pullback_app_isoTensor_baseMap_le_refl f'
    ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F)) U
    (pullback_app_isoTensor_baseMap g ((Scheme.Modules.pushforward f).obj F) e x)
  have h2 := pullback_app_isoTensor_baseMap_comp f' g
    ((Scheme.Modules.pushforward f).obj F) e (le_refl (f' ⁻¹ᵁ U)) e₂ x
  have h3 := pullback_app_isoTensor_baseMap_congr sq.w.symm
    ((Scheme.Modules.pushforward f).obj F) e₂ e₃ x
  have h4' := pullback_app_isoTensor_baseMap_comp g' f
    ((Scheme.Modules.pushforward f).obj F) (le_refl (f ⁻¹ᵁ V)) e' e₃ x
  have hcancel : ∀ z : Γ((Scheme.Modules.pullback g').obj
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj F)),
        f' ⁻¹ᵁ U),
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).inv.app
          ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
        ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).hom.app
          ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom z) = z :=
    fun z => congrArg
      (fun (k : (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g').obj
          ((Scheme.Modules.pushforward f).obj F) ⟶
          (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g').obj
          ((Scheme.Modules.pushforward f).obj F)) =>
        (Scheme.Modules.Hom.app k (f' ⁻¹ᵁ U)).hom z)
      (Iso.hom_inv_id_app (Scheme.Modules.pullbackComp g' f)
        ((Scheme.Modules.pushforward f).obj F))
  have h4 := (congrArg (fun z =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).inv.app
      ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom z) h4'.symm).trans
    (hcancel _)
  have h5 := pullback_app_isoTensor_baseMap_naturality g'
    ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F) e'
    (pullback_app_isoTensor_baseMap f ((Scheme.Modules.pushforward f).obj F)
      (le_refl (f ⁻¹ᵁ V)) x)
  have h6a := pullback_app_isoTensor_baseMap_le_refl f
    ((Scheme.Modules.pushforward f).obj F) V x
  have h6b := congrArg
    (fun (k : (Scheme.Modules.pushforward f).obj F ⟶
        (Scheme.Modules.pushforward f).obj F) =>
      (Scheme.Modules.Hom.app k V).hom x)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).right_triangle_components F)
  have h6 : (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F) (f ⁻¹ᵁ V)).hom
      (pullback_app_isoTensor_baseMap f ((Scheme.Modules.pushforward f).obj F)
        (le_refl (f ⁻¹ᵁ V)) x) = x :=
    (congrArg (fun z => (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)
      (f ⁻¹ᵁ V)).hom z) h6a).trans h6b
  change (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g').map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) (f' ⁻¹ᵁ U)).hom
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).inv.app
          ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
        ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr sq.w.symm).hom.app
            ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
          ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f' g).hom.app
              ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
            ((Scheme.Modules.Hom.app
                ((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
                  ((Scheme.Modules.pullback g).obj
                    ((Scheme.Modules.pushforward f).obj F))) U).hom
              (pullback_app_isoTensor_baseMap g
                ((Scheme.Modules.pushforward f).obj F) e x))))) =
    pullback_app_isoTensor_baseMap g' F e' x
  refine (congrArg (fun z =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g').map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) (f' ⁻¹ᵁ U)).hom
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).inv.app
          ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
        ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr sq.w.symm).hom.app
            ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
          ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f' g).hom.app
              ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom z))))
    h1.symm).trans ?_
  refine (congrArg (fun z =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g').map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) (f' ⁻¹ᵁ U)).hom
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).inv.app
          ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom
        ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr sq.w.symm).hom.app
            ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom z)))
    h2).trans ?_
  refine (congrArg (fun z =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g').map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) (f' ⁻¹ᵁ U)).hom
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g' f).inv.app
          ((Scheme.Modules.pushforward f).obj F)) (f' ⁻¹ᵁ U)).hom z))
    h3).trans ?_
  refine (congrArg (fun z =>
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g').map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F)) (f' ⁻¹ᵁ U)).hom z)
    h4).trans ?_
  exact h5.trans
    (congrArg (fun z => pullback_app_isoTensor_baseMap g' F e' z) h6)

end AlgebraicGeometry
