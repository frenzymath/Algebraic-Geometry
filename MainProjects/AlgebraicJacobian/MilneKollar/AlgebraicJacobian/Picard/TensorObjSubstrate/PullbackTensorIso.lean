/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.TensorObjSubstrate.PullbackTensorMapIso

/-!
# D4′: pullback commutes with `⊗` on locally-trivial pairs

Leaf module carrying the chart-chase upgrading the sheaf-level pullback–tensor comparison
`pullbackTensorMap` (`f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N`) to an isomorphism on locally-trivial pairs,
blueprint `lem:pullback_tensor_iso_loctriv` and its per-chart helper `lem:chart_isiso`. Imports
only `TensorObjSubstrate.PullbackTensorMapIso` (which in turn imports `TensorObjSubstrate`) —
monster-free (does NOT import `PresheafDualPullback`/`TensorObjInverse`/`DualInverse`).
-/

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

/-- **Local reproduction of the (private) four-fold "cancel the flanks" device.**
For a four-fold composite `a ≫ b ≫ c ≫ d` that is an isomorphism, if `a`, `c`, `d` are
isomorphisms then so is the middle factor `b`. The `isIso_of_isIso_comp4_mid` in
`TensorObjSubstrate.lean` is `private` (does not export across import), so we reproduce the
tiny generic `[Category C]` helper here. -/
private lemma isIso_of_isIso_comp4_mid {C : Type*} [Category C] {W₀ X₀ Y₀ Z₀ T₀ : C}
    {a : W₀ ⟶ X₀} {b : X₀ ⟶ Y₀} {c : Y₀ ⟶ Z₀} {d : Z₀ ⟶ T₀}
    (h : IsIso (a ≫ b ≫ c ≫ d)) (ha : IsIso a) (hc : IsIso c) (hd : IsIso d) : IsIso b := by
  haveI := h; haveI := ha; haveI := hc; haveI := hd
  haveI : IsIso (b ≫ c ≫ d) := IsIso.of_isIso_comp_left a (b ≫ c ≫ d)
  exact IsIso.of_isIso_comp_right b (c ≫ d)

/-- **Per-chart isomorphism obligation for the D4′ chart-chase** (blueprint `lem:chart_isiso`).

In the situation of `pullbackTensorIsoOfLocallyTrivial`, fix a chart of the common trivialising
cover: a scheme `U` with open immersion `j : U ⟶ X`, its preimage `V` with open immersion
`j' : V ⟶ Y`, and the restriction `g : V ⟶ U` of `f`, related by the two equal factorisations of
`V ⟶ X` through `j' ≫ f = g ≫ j`. Given chart-trivialisations of `M, N` along `j`
(`j^*M ≅ 𝒪_U`, `j^*N ≅ 𝒪_U`), the restriction of `pullbackTensorMap f M N` to the chart `V` (via
`restrictFunctor j'`) is an isomorphism. -/
/- Planner strategy:
  Apply the composition coherence `pullbackTensorMap_restrict` (blueprint
  `lem:pullback_tensor_map_basechange`) twice, at the two factorisations of `j' ≫ f = g ≫ j`:
    • `pullbackTensorMap_restrict j' f M N` expresses `pullbackTensorMap (j' ≫ f) M N` as
      `(pullbackComp j' f).inv ≫ (pullback j').map (pullbackTensorMap f M N) ≫
        pullbackTensorMap j' (f^*M) (f^*N) ≫
        (tensorObjIsoOfIso (pullbackComp j' f) (pullbackComp j' f)).hom`.
    • `pullbackTensorMap_restrict g j M N` expresses `pullbackTensorMap (g ≫ j) M N` as
      `(pullbackComp g j).inv ≫ (pullback g).map (pullbackTensorMap j M N) ≫
        pullbackTensorMap g (j^*M) (j^*N) ≫
        (tensorObjIsoOfIso (pullbackComp g j) (pullbackComp g j)).hom`.
    Rewrite `pullbackTensorMap (j' ≫ f) M N = pullbackTensorMap (g ≫ j) M N` via `hcomp`
    (`congrArg (pullbackTensorMap · M N) hcomp`) to equate the two decompositions. Every factor in
    that equation is an isomorphism EXCEPT the two comparisons we care about:
      - `pullbackTensorMap j' ((pullback f).obj M) ((pullback f).obj N)` is `IsIso` by K1
        `pullbackTensorMap_isIso_of_isOpenImmersion j' _ _` (`j'` is an open immersion);
      - `(pullback g).map (pullbackTensorMap j M N)` is `IsIso` since `pullbackTensorMap j M N`
        is `IsIso` by K1 `pullbackTensorMap_isIso_of_isOpenImmersion j M N` (`j` open immersion),
        hence its functor-image is `IsIso` (`Functor.map_isIso`);
      - `pullbackTensorMap g ((pullback j).obj M) ((pullback j).obj N)` is `IsIso` by the
        now-public base-case `pullbackTensorMap_isIso_of_base_unit g eM eN`
        (`lem:pullback_tensor_map_isiso_base_unit`);
      - the `pullbackComp` isos and `tensorObjIsoOfIso` factors are isomorphisms unconditionally.
    Isolate `(pullback j').map (pullbackTensorMap f M N)` as the sole non-obviously-iso factor of
    the (now all-iso) equated composite — a 4-fold-composite "cancel the flanks" argument (compare
    the project-local `isIso_of_isIso_comp4_mid`-shaped device already used for
    `pullbackTensorMap_isIso_of_base_unit` in `TensorObjSubstrate.lean`; that helper is currently
    `private` there, so either reproduce a local analogue or request it be made public). Finally,
    transport `IsIso ((pullback j').map (pullbackTensorMap f M N))` to the stated
    `IsIso ((restrictFunctor j').map (pullbackTensorMap f M N))` along the natural isomorphism
    `restrictFunctorIsoPullback j' : restrictFunctor j' ≅ pullback j'` (naturality square at
    `pullbackTensorMap f M N`, then transport isomorphism along the two flanking isos). -/
lemma chart_isIso {X Y U V : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules)
    (j : U ⟶ X) (j' : V ⟶ Y) (g : V ⟶ U)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (hcomp : j' ≫ f = g ≫ j)
    (eM : (Scheme.Modules.pullback j).obj M ≅ SheafOfModules.unit U.ringCatSheaf)
    (eN : (Scheme.Modules.pullback j).obj N ≅ SheafOfModules.unit U.ringCatSheaf) :
    IsIso ((Scheme.Modules.restrictFunctor j').map (pullbackTensorMap f M N)) := by
  -- Step A: transport the goal to the pullback world along the natural iso
  -- `restrictFunctorIsoPullback j' : restrictFunctor j' ≅ pullback j'`.
  refine (CategoryTheory.NatIso.isIso_map_iff
    (Scheme.Modules.restrictFunctorIsoPullback j') (pullbackTensorMap f M N)).mpr ?_
  -- Goal: `IsIso ((pullback j').map (pullbackTensorMap f M N))`.
  -- Step B: the whole composite `pullbackTensorMap (j' ≫ f) M N` is an iso, via the `g ≫ j`
  -- factorisation (all four factors are isos there).
  have hcompiso : IsIso (pullbackTensorMap (j' ≫ f) M N) := by
    rw [hcomp, pullbackTensorMap_restrict g j M N]
    -- The four factors of the `g ≫ j` decomposition, each an isomorphism.
    haveI hj : IsIso (pullbackTensorMap j M N) :=
      pullbackTensorMap_isIso_of_isOpenImmersion j M N
    have hb : IsIso ((Scheme.Modules.pullback g).map (pullbackTensorMap j M N)) :=
      Functor.map_isIso _ _
    have hc : IsIso (pullbackTensorMap g ((Scheme.Modules.pullback j).obj M)
        ((Scheme.Modules.pullback j).obj N)) :=
      pullbackTensorMap_isIso_of_base_unit g eM eN
    have ha : IsIso ((Scheme.Modules.pullbackComp g j).inv.app (tensorObj M N)) := by
      infer_instance
    have hd : IsIso (tensorObjIsoOfIso ((Scheme.Modules.pullbackComp g j).app M)
        ((Scheme.Modules.pullbackComp g j).app N)).hom :=
      (tensorObjIsoOfIso ((Scheme.Modules.pullbackComp g j).app M)
        ((Scheme.Modules.pullbackComp g j).app N)).isIso_hom
    -- Assemble the composite isomorphism explicitly (instance search does not chain these).
    exact IsIso.comp_isIso' ha (IsIso.comp_isIso' hb (IsIso.comp_isIso' hc hd))
  -- Step C: expand the `j' ≫ f` factorisation and cancel the three iso flanks to isolate
  -- the middle factor `(pullback j').map (pullbackTensorMap f M N)`.
  rw [pullbackTensorMap_restrict j' f M N] at hcompiso
  haveI : IsIso (pullbackTensorMap j' ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N)) :=
    pullbackTensorMap_isIso_of_isOpenImmersion j' _ _
  haveI hinv : IsIso ((Scheme.Modules.pullbackComp j' f).inv.app (tensorObj M N)) := by
    infer_instance
  exact isIso_of_isIso_comp4_mid hcompiso hinv inferInstance inferInstance

/-- **D4′ — pullback commutes with `⊗` on locally-trivial pairs** (blueprint
`lem:pullback_tensor_iso_loctriv`). For `f : Y ⟶ X` and locally-trivial `M N : X.Modules`, the
sheaf-level comparison `pullbackTensorMap f M N` is an isomorphism
`f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`, natural in `M, N`. -/
/- Planner strategy:
  By local triviality of `M, N` (`LineBundle.IsLocallyTrivial`), choose the common trivialising
  cover exactly as in `tensorObj_isLocallyTrivial`
  (blueprint `lem:tensorobj_preserves_locally_trivial`):
  for each `y : Y`, pick affine opens `U_M, U_N` of `X` trivialising `M, N` at `f.base y`
  (from `hM (f.base y)`, `hN (f.base y)`), then an affine `W ≤ U_M ⊓ U_N` containing `f.base y`
  (`exists_isAffineOpen_mem_and_subset`), giving `j : (W : Scheme) ⟶ X` (i.e. `W.ι`) with
  trivialisations of `M, N` on `W` transported down from `U_M, U_N` via `restrictIsoUnitOfLE`
  (mirroring `tensorObj_isLocallyTrivial`'s construction at `TensorObjSubstrate.lean:559`), then
  further shrink to an affine `V ≤ f ⁻¹ᵁ W` containing `y` for the chart on the `Y` side, exactly
  as `LineBundle.IsLocallyTrivial.pullback` (`lem:IsLocallyTrivial_pullback`) does at
  `LineBundlePullback.lean:156`. Set `j' := V.ι`, and `g := f.resLE W V hVW`
  (`Scheme.Hom.resLE`, with `hcomp : j' ≫ f = g ≫ j` supplied by `Scheme.Hom.resLE_comp_ι`,
  mirroring the `hg_comp` step of `IsLocallyTrivial.pullback`).
  Convert the chart trivialisations from `M.restrict W.ι ≅ unit` (the `IsLocallyTrivial` witness
  shape) to `(pullback j).obj M ≅ unit` via `restrictFunctorIsoPullback W.ι`, then feed everything
  to `chart_isIso f M N j j' g hcomp eM eN` to get, for each `y : Y`,
  `IsIso ((restrictFunctor j').map (pullbackTensorMap f M N))` on a chart `V` containing `y`.
  Assemble globally via the restriction-detects-isomorphism criterion `isIso_of_isIso_restrict`
  (blueprint `lem:isiso_of_isiso_restrict`) applied to `φ := pullbackTensorMap f M N`, with the
  open-assignment `y ↦ V y` and the per-point chart-`IsIso` hypothesis just built, concluding
  `IsIso (pullbackTensorMap f M N)`. Package as `asIso (pullbackTensorMap f M N)` for the `Iso`
  conclusion; naturality in `M, N` (if consumed downstream) is `pullbackTensorMap_natural`
  (`lem:pullback_tensor_map_natural`), already unconditional and not part of this statement's
  type. `f^*M, f^*N, f^*(M⊗N)` being locally trivial on this same cover follows from
  `LineBundle.IsLocallyTrivial.pullback` and `tensorObj_isLocallyTrivial`
  (`lem:IsLocallyTrivial_pullback`, `lem:tensorobj_preserves_locally_trivial`) — consumed
  implicitly by the chart-chase shape, not as a separate obligation of this statement. -/
noncomputable def pullbackTensorIsoOfLocallyTrivial {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M N : X.Modules) (hM : LineBundle.IsLocallyTrivial M) (hN : LineBundle.IsLocallyTrivial N) :
    (Scheme.Modules.pullback f).obj (tensorObj M N) ≅
      tensorObj ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) := by
  -- For each `y : Y`, build a chart of the common trivialising cover and feed `chart_isIso`.
  have key : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map (pullbackTensorMap f M N)) := by
    intro y
    -- Common trivialising affine `W ∋ f.base y` on `X`, refining charts of `M` and `N`.
    obtain ⟨UM, hxUM, _, ⟨eM0⟩⟩ := hM (f.base y)
    obtain ⟨UN, hxUN, _, ⟨eN0⟩⟩ := hN (f.base y)
    obtain ⟨W, _, hxW, hWsub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := f.base y) (U := UM ⊓ UN) ⟨hxUM, hxUN⟩
    have hWUM : W ≤ UM := le_trans hWsub inf_le_left
    have hWUN : W ≤ UN := le_trans hWsub inf_le_right
    -- Transport the `W`-trivialisations to the `(pullback W.ι)` shape `chart_isIso` needs.
    have eM : (Scheme.Modules.pullback W.ι).obj M ≅
        SheafOfModules.unit (W : Scheme).ringCatSheaf :=
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).symm.app M ≪≫ restrictIsoUnitOfLE hWUM eM0
    have eN : (Scheme.Modules.pullback W.ι).obj N ≅
        SheafOfModules.unit (W : Scheme).ringCatSheaf :=
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).symm.app N ≪≫ restrictIsoUnitOfLE hWUN eN0
    -- Shrink to an affine chart `V ≤ f⁻¹ W` on the `Y` side containing `y`.
    have hyW : y ∈ f ⁻¹ᵁ W := hxW
    obtain ⟨V, _, hyV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) hyW
    have hVW' : V ≤ f ⁻¹ᵁ W := hVW
    set g : (V : Scheme) ⟶ (W : Scheme) := f.resLE W V hVW' with hg_def
    have hcomp : V.ι ≫ f = g ≫ W.ι := (Scheme.Hom.resLE_comp_ι f hVW').symm
    exact ⟨V, hyV, chart_isIso f M N W.ι V.ι g hcomp eM eN⟩
  -- Assemble globally: restriction detects the isomorphism, then package as an `Iso`.
  haveI : IsIso (pullbackTensorMap f M N) :=
    isIso_of_isIso_restrict (pullbackTensorMap f M N)
      (fun y => (key y).choose)
      (fun y => (key y).choose_spec.1)
      (fun y => (key y).choose_spec.2)
  exact asIso (pullbackTensorMap f M N)

end Modules

end Scheme

end AlgebraicGeometry
