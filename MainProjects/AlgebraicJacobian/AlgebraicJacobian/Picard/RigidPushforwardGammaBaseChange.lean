/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RigidPushforwardChartBaseChange
import AlgebraicJacobian.Picard.RigidPushforwardInstance
import AlgebraicJacobian.Curve.GeometricallyReduced

/-!
# `H⁰` commutes with affine base change, in the form the B3 gate consumes

`Picard/RigidPushforwardAffineDescent.lean` reduces the second field of the campaign gate
`Scheme.HasRigidPushforward` — `Scheme.RigidPushforwardBaseChange` — to the single module-level
statement `Adelic.RigidPushforwardGammaBaseChange`: bijectivity of the canonical
`Γ(Spec A', ⊤) ⊗_{Γ(Spec A, ⊤)} Γ(C_A, L) → Γ(C_{A'}, g'^* L)`.  This file proves that
statement.

## §1, the general theorem

`exists_gammaBaseChange_of_kerPure` takes a cartesian square

```
  X' --g'--> X
  |f'        |f
  v          v
  Y' --g---> Y
```

with `Y`, `Y'` affine and `g'` affine, a bundled 2-affine cover `𝒰` of `X`, a quasi-coherent `M`,
and the Čech `H⁰`-purity hypothesis `hker` (the kernel base-change map of the two-term Čech
difference `d = 𝒰.moduleSectionDiffBase f M` is bijective for every `Γ(Y, ⊤)`-algebra `B`), and
produces the canonical comparison

`Γ(Y', ⊤) ⊗_{Γ(Y, ⊤)} Γ(f_* M, ⊤) ≅ Γ(f'_* (g'^* M), ⊤)`, `b ⊗ x ↦ b · baseMap x`.

It is a sandwich of three existing pieces: the sheaf condition on both sides
(`AffineCoverMVSquare.globalSectionsEquivKerModuleSectionDiffBase`, which identifies `Γ` with
`ker d`), the affine-base-change Čech square on kernels
(`Adelic.exists_kerChartTensorEquiv`, `Picard/RigidPushforwardChartBaseChange.lean`), and the
`pushforward`-versus-`baseSections` dictionary at the two tops
(`Scheme.Modules.pushforwardTopEquivBaseSections`).  The only computation is that the resulting
map does send `b ⊗ x` to `b · baseMap x`, which is the restriction naturality
`pullback_app_isoTensor_baseMap_res'` on each of the two charts.

Note what is *not* assumed: `f` is arbitrary — in the application it is the proper, emphatically
non-affine family `q : C_A ⟶ Spec A`, which is exactly the case
`Picard/RigidPushforwardFrontier.lean` reports as having no infrastructure.

Sources: Stacks 01HQ, 02KG at `i = 0`; Mumford, *Abelian Varieties*, II §5; EGA III 7.7.5.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

namespace Adelic

open Scheme Scheme.Modules

/-! ## §1. The `Γ`-level base-change comparison from Čech purity -/

/-- **`H⁰` commutes with an affine base change**, in the `Γ`-level form the B3 gate consumes.

For a cartesian square with affine bases `Y`, `Y'` and affine `g'`, a bundled 2-affine cover `𝒰`
of `X` and a quasi-coherent `M`, the Čech `H⁰`-purity hypothesis `hker` gives the canonical
additive comparison

`Γ(Y', ⊤) ⊗_{Γ(Y, ⊤)} Γ(f_* M, ⊤) ≅ Γ(f'_* (g'^* M), ⊤)`, `b ⊗ x ↦ b · baseMap x`.

**`f` is not assumed affine**, which is the whole point: in the application it is the proper
family `q : C_A ⟶ Spec A`.  The two-term Čech complex of `𝒰` replaces the affineness of `f`.

**Vacuity audit.**  The conclusion is `∃ s, (values of s on simple tensors) ∧ Bijective s`, and
`s` is required to be additive while simple tensors generate the source as an abelian group; so
the prescribed values determine `s` uniquely and the existential really asserts bijectivity of
the canonical map, not the existence of a convenient one. -/
theorem exists_gammaBaseChange_of_kerPure {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [IsAffine Y] [IsAffine Y'] [IsAffineHom g']
    (𝒰 : X.AffineCoverMVSquare) (M : X.Modules) [M.IsQuasicoherent]
    (hker : ∀ (B : Type u) [CommRing B] [Algebra Γ(Y, ⊤) B],
      letI := f.baseSectionsModule M 𝒰.U₁
      letI := f.baseSectionsModule M 𝒰.U₂
      letI := f.baseSectionsModule M (𝒰.U₁ ⊓ 𝒰.U₂)
      Function.Bijective
        (AlgebraicJacobian.TwoTerm.kerBaseChange (𝒰.moduleSectionDiffBase f M) B))
    (e' : f' ⁻¹ᵁ (⊤ : Y'.Opens) ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ (⊤ : Y.Opens))) :
    letI : Algebra Γ(Y, ⊤) Γ(Y', ⊤) := (g.appLE ⊤ ⊤ le_top).hom.toAlgebra
    ∃ s : TensorProduct Γ(Y, ⊤) Γ(Y', ⊤)
        Γ((Scheme.Modules.pushforward f).obj M, (⊤ : Y.Opens)) →+
      Γ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj M),
        (⊤ : Y'.Opens)),
      (∀ (b : Γ(Y', ⊤)) (x : Γ((Scheme.Modules.pushforward f).obj M, (⊤ : Y.Opens))),
        s (b ⊗ₜ[Γ(Y, ⊤)] x) =
          b • (show Γ((Scheme.Modules.pushforward f').obj
              ((Scheme.Modules.pullback g').obj M), (⊤ : Y'.Opens)) from
            pullback_app_isoTensor_baseMap g' M e' x)) ∧
      Function.Bijective s := by
  letI aAB : Algebra Γ(Y, ⊤) Γ(Y', ⊤) := (g.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI mT := f.baseSectionsModule M (⊤ : X.Opens)
  letI m1 := f.baseSectionsModule M 𝒰.U₁
  letI m2 := f.baseSectionsModule M 𝒰.U₂
  letI m0 := f.baseSectionsModule M (𝒰.U₁ ⊓ 𝒰.U₂)
  letI nT := f'.baseSectionsModule ((Scheme.Modules.pullback g').obj M) (⊤ : X'.Opens)
  letI n1 := f'.baseSectionsModule ((Scheme.Modules.pullback g').obj M) (𝒰.preimage g').U₁
  letI n2 := f'.baseSectionsModule ((Scheme.Modules.pullback g').obj M) (𝒰.preimage g').U₂
  letI n0 := f'.baseSectionsModule ((Scheme.Modules.pullback g').obj M)
    ((𝒰.preimage g').U₁ ⊓ (𝒰.preimage g').U₂)
  obtain ⟨⟨Ξ, hΞ⟩⟩ := exists_kerChartTensorEquiv h 𝒰 M hker
  let E := 𝒰.globalSectionsEquivKerModuleSectionDiffBase f M
  let E' := (𝒰.preimage g').globalSectionsEquivKerModuleSectionDiffBase f'
    ((Scheme.Modules.pullback g').obj M)
  let T := Scheme.Modules.pushforwardTopEquivBaseSections f M
  let T' := Scheme.Modules.pushforwardTopEquivBaseSections f'
    ((Scheme.Modules.pullback g').obj M)
  let s : TensorProduct Γ(Y, ⊤) Γ(Y', ⊤)
      Γ((Scheme.Modules.pushforward f).obj M, (⊤ : Y.Opens)) ≃+
      Γ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj M),
        (⊤ : Y'.Opens)) :=
    (TensorProduct.congr (LinearEquiv.refl Γ(Y, ⊤) Γ(Y', ⊤)) (T.trans E)).toAddEquiv.trans
      (Ξ.trans (E'.symm.trans T'.symm).toAddEquiv)
  refine ⟨s.toAddMonoidHom, ?_, s.bijective⟩
  intro b x
  -- the canonical base map commutes with restriction to either chart
  have hres : ∀ (W₀ : X.Opens) (hW₀ : W₀ ≤ f ⁻¹ᵁ (⊤ : Y.Opens))
      (hW'' : g' ⁻¹ᵁ W₀ ≤ f' ⁻¹ᵁ (⊤ : Y'.Opens)),
      (((Scheme.Modules.pullback g').obj M).presheaf.map (homOfLE hW'').op).hom
          (pullback_app_isoTensor_baseMap g' M e' x)
        = pullback_app_isoTensor_baseMap g' M (le_refl (g' ⁻¹ᵁ W₀))
          ((M.presheaf.map (homOfLE hW₀).op).hom x) :=
    fun W₀ hW₀ hW'' => pullback_app_isoTensor_baseMap_res' g' M e'
      (le_refl (g' ⁻¹ᵁ W₀)) hW₀ hW'' x
  have key : E' (T' (b • (show Γ((Scheme.Modules.pushforward f').obj
        ((Scheme.Modules.pullback g').obj M), (⊤ : Y'.Opens)) from
      pullback_app_isoTensor_baseMap g' M e' x))) = Ξ (b ⊗ₜ[Γ(Y, ⊤)] (E (T x))) := by
    rw [_root_.map_smul T' b, _root_.map_smul E' b]
    refine Subtype.ext ?_
    rw [hΞ b (E (T x))]
    exact Prod.ext
      (congrArg (fun z => (f'.appLE (⊤ : Y'.Opens) (g' ⁻¹ᵁ 𝒰.U₁) le_top).hom b • z)
        (hres 𝒰.U₁ le_top le_top))
      (congrArg (fun z => (f'.appLE (⊤ : Y'.Opens) (g' ⁻¹ᵁ 𝒰.U₂) le_top).hom b • z)
        (hres 𝒰.U₂ le_top le_top))
  have hsval : s.toAddMonoidHom (b ⊗ₜ[Γ(Y, ⊤)] x) =
      T'.symm (E'.symm (Ξ (b ⊗ₜ[Γ(Y, ⊤)] (E (T x))))) := rfl
  rw [hsval, ← key, E'.symm_apply_apply, T'.symm_apply_apply]

/-! ## §2. The gate's remaining statement, for an AJC curve -/

section AJC

variable {k : Type u} [Field k]

set_option maxHeartbeats 1600000 in
-- Elaborating the engine application unfolds two nested pullback squares and the full
-- `letI` dictionary of the preimage cover.
/-- **`RigidPushforwardGammaBaseChange` is a theorem.**  For the AJC curve `C/k` and every
finitely generated `k`-algebra `A`, the formation of `Γ(C_A, L)` for an invertible `L` with
fibrewise `h¹ = 0` commutes with every ring map `A → A'`.

The Čech `H⁰`-purity fed to §1 is obtained on the 2-affine cover
`(p1BaseChangeCoverSquare A).preimage π_A` of `C_A` — the preimage under the finite (hence
affine) `π_A : C_A ⟶ ℙ¹_A` of the standard 2-chart cover of `ℙ¹_A` — from two inputs:

* **surjectivity** of its Čech differential, which is the *first* conjunct of the ℙ¹ engine
  `p1Cech_h0_baseChange_of_fibrewise_h1_vanishing_of_isIntegral` applied to `(π_A)_* L`.  No
  transport is needed: `AffineCoverMVSquare.moduleSectionDiff_pushforward` is `rfl` and
  `moduleSectionDiffBase`'s underlying function *is* `moduleSectionDiff`, so the two
  surjectivity statements are the same proposition — in particular the propositional
  `q = π_A ≫ p` never has to be crossed;
* **flatness** of `Γ(L, U₁ ⊓ U₂)` over `Γ(Spec A, ⊤)`, which is `CoherentSheafFlat q L` read at
  the pair `(⊤, U₁ ⊓ U₂)` (`flat_baseSections_of_coherentSheafFlat`) — stated for `q` from the
  start, so again no transport.

`bijective_kerBaseChange_of_surjective` then gives purity at `q`'s own module structures.  (The
alternative recorded in `Picard/RigidPushforwardAffineDescent.lean` — instantiating the engine's
*fourth* conjunct instead — avoids the flatness obligation but has to move the whole `letI`
dictionary from `p` and the pushforward module to `q` and `L`; flatness is free here, so this
route is shorter.)

The ℙ¹ engine's `H⁰`-finiteness anchor is `IsIntegral (ℙ¹_k)`
(`Adelic.instIsIntegralP1OverLeft`), so the two fields of the gate are not independent — as
`Picard/RigidPushforwardAffineDescent.lean`'s dependency warning records. -/
theorem rigidPushforwardGammaBaseChange_proved
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    RigidPushforwardGammaBaseChange C A := by
  intro L hL h1 A' _ φ e'
  haveI := hL.isFinitePresentation
  haveI : IsFinite (finiteMapToP1BaseChange A C) := isFinite_finiteMapToP1BaseChange A C
  haveI := pushforward_finiteMapToP1BaseChange_isFinitePresentation A C L hL
  -- the ℙ¹ engine, applied to the finite pushforward `(π_A)_* L`
  have hengine := p1Cech_h0_baseChange_of_fibrewise_h1_vanishing_of_isIntegral A
    ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L)
    (pushforward_finiteMapToP1BaseChange_coherentSheafFlat A C L hL)
    (p1CechFibrewiseBridge_proved A
      ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) inferInstance
      (fun t => pushforward_finiteMapToP1BaseChange_fiberH1 A C L t hL (h1 t)))
  -- the module dictionary on `C_A` for the preimage cover
  letI c1 := (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule
    L ((p1BaseChangeCoverSquare A).preimage (finiteMapToP1BaseChange A C)).U₁
  letI c2 := (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule
    L ((p1BaseChangeCoverSquare A).preimage (finiteMapToP1BaseChange A C)).U₂
  letI c0 := (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule
    L (((p1BaseChangeCoverSquare A).preimage (finiteMapToP1BaseChange A C)).U₁ ⊓
      ((p1BaseChangeCoverSquare A).preimage (finiteMapToP1BaseChange A C)).U₂)
  -- surjectivity of the Čech differential of the preimage cover: the same proposition
  have hd : Function.Surjective
      ⇑(((p1BaseChangeCoverSquare A).preimage
          (finiteMapToP1BaseChange A C)).moduleSectionDiffBase
        (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) L) :=
    hengine.1
  -- flatness of the overlap sections, read off `CoherentSheafFlat q L`
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : AlgebraicGeometry.Flat C.hom := inferInstance
  haveI : AlgebraicGeometry.Flat
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) := inferInstance
  haveI : Module.Flat Γ(Spec (CommRingCat.of A), ⊤)
      Γ(L, ((p1BaseChangeCoverSquare A).preimage (finiteMapToP1BaseChange A C)).U₁ ⊓
        ((p1BaseChangeCoverSquare A).preimage (finiteMapToP1BaseChange A C)).U₂) :=
    Scheme.flat_baseSections_of_coherentSheafFlat _ L
      (Scheme.coherentSheafFlat_of_isLocallyTrivial_of_flat _ hL)
      ((p1BaseChangeCoverSquare A).preimage (finiteMapToP1BaseChange A C)).isAffineOpen_inf
  haveI : IsAffineHom (pullback.fst
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      (Spec.map (CommRingCat.ofHom φ))) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  exact exists_gammaBaseChange_of_kerPure (IsPullback.of_hasPullback _ _)
    ((p1BaseChangeCoverSquare A).preimage (finiteMapToP1BaseChange A C)) L
    (fun B _ _ => AlgebraicJacobian.TwoTerm.bijective_kerBaseChange_of_surjective hd B) e'

/-! ## §3. The gate, as an instance -/

/-- **The B3 gate is a theorem.**  For the AJC curve — smooth of relative dimension one, proper,
geometrically integral over `k` — `Scheme.HasRigidPushforward C` holds.

Both fields are now unconditional: `locallyFree` is
`Adelic.rigidPushforwardLocallyFree_proved` (`Picard/RigidPushforwardInstance.lean`) and
`baseChange` is `Adelic.rigidPushforwardBaseChange_of_gamma`
(`Picard/RigidPushforwardAffineDescent.lean`) fed by `rigidPushforwardGammaBaseChange_proved`
of §2.

This is the discharge `Picard/RigidPushforward.lean`'s class docstring anticipated; that
docstring has been corrected accordingly, and the class is kept rather than deleted so consumers
keep reading as hypotheses on the curve.  The `[HasRigidPushforward C]` binders on the three
extraction theorems now synthesize for an AJC curve, as §4 witnesses, and
`Picard/RigidPushforwardP1Witness.lean` exhibits a curve satisfying the three hypotheses, so
neither this instance nor §4 is vacuous. -/
instance instHasRigidPushforwardOfCurve
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom] :
    Scheme.HasRigidPushforward C :=
  hasRigidPushforward_of_gammaBaseChange C
    (fun A _ _ _ => rigidPushforwardGammaBaseChange_proved C A)

/-! ## §4. The B3 headlines, unconditionally

The three extraction theorems of `Picard/RigidPushforward.lean` §3–§4 carry a
`[HasRigidPushforward C]` binder.  Restated here for an AJC curve *without* that binder — the
gate is synthesized by §3, not assumed.  These are the honest "the consumers synthesize"
witnesses: if §3 were absent, none of the three would elaborate. -/

section Headlines

variable (C : Over (Spec (CommRingCat.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
variable (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
variable (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)

/-- **B3 local freeness, unconditional.**  For an invertible `L` on `C_A` with fibrewise
`h¹ = 0` at all scheme points, `q_* L` is free of rank `h⁰(C_t, L_t)` near every `t : Spec A`. -/
theorem rigidPushforward_locallyFree
    (hL : LineBundle.IsLocallyTrivial L)
    (h1 : ∀ t : Spec (CommRingCat.of A),
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t)
    (t : Spec (CommRingCat.of A)) :
    ∃ U : (Spec (CommRingCat.of A)).Opens, t ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj
          ((Scheme.Modules.pushforward
            (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj L) ≅
        _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf)
          (ULift.{u} (Fin ((pullback.snd C.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t)))) :=
  Scheme.pushforward_locallyFree_of_h1_vanishing C A L hL h1 t

/-- **B3 base change, unconditional.**  Under the same hypotheses the formation of `q_* L`
commutes with every ring map `A → A'` — no finiteness, flatness or noetherian condition on
`A'`. -/
theorem rigidPushforward_baseChange
    (hL : LineBundle.IsLocallyTrivial L)
    (h1 : ∀ t : Spec (CommRingCat.of A),
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t)
    (A' : Type u) [CommRing A'] (φ : A →+* A') :
    IsIso (pushforwardBaseChangeMap
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      (Spec.map (CommRingCat.ofHom φ))
      (pullback.snd (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
        (Spec.map (CommRingCat.ofHom φ)))
      (pullback.fst (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
        (Spec.map (CommRingCat.ofHom φ)))
      pullback.condition L) :=
  Scheme.pushforward_baseChange_of_h1_vanishing C A L hL h1 A' φ

/-- **The B3 rank-one corollary, unconditional** (Kleiman §5).  If in addition `h⁰ ≡ 1` then
`q_* L` is an invertible sheaf on `Spec A`.  This is the implemented route from a line bundle on
the family to the rigidified data the Picard campaign consumes. -/
theorem rigidPushforward_isLocallyTrivial
    (hL : LineBundle.IsLocallyTrivial L)
    (h1 : ∀ t : Spec (CommRingCat.of A),
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t)
    (h0 : ∀ t : Spec (CommRingCat.of A),
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t = 1) :
    LineBundle.IsLocallyTrivial
      ((Scheme.Modules.pushforward
        (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj L) :=
  Scheme.pushforward_isLocallyTrivial_of_h1_vanishing C A L hL h1 h0

end Headlines

end AJC

end Adelic

end AlgebraicGeometry
