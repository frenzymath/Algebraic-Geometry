/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyWindow
import AlgebraicJacobian.Picard.DivisorFamilyMapAlg

/-!
# G-2 (DD-4 Task 7), crux half — the window identification commutes with base change

The base-change triangle of the window pair (`informal/spec-w4-gates.md` §G-2): the
`k`-anchored ambient comparison `R ⊗[k] H_a → R' ⊗[k] H_a` intertwines the window
identifications `relThetaWindowEquiv` over `R` and `R'` through the relative-curve
sections comparison `relSectionsMap C R R'`.  This is the crux of both halves of
`divFamEps_mapAlg` (`AlgebraicJacobian.Picard.DivisorFamilyEpsNaturality`): it feeds the
`⊇` (formal) half by germ transport, and pins the pushed-forward window submodule for
the `⊆` (certificate) half.

**Orientation seam (recorded once, spec-dd-3 §0 discipline).**  The ambient comparison
is pinned as `AlgebraTensorModule.cancelBaseChange k R R' R' H` applied to
`1 ⊗ₜ (·)` — the SAME orientation as `ker_baseChangeMkQ_eq_map_baseChange`
(`Picard/DivCarveKit.lean`), so the DDR-9/G-5 consumers (`w4-g5-worksheet` §2 step (e))
convert `Module.Grassmannian.map`-kernels to `windowBaseChange` without a transport
lemma.

* `Sheaf.HModule.linearEquiv₀_linearEquivHModule'` — the two degree-zero section
  identifications of the site (`HModule.linearEquiv₀` vs the `HModule'`-route of
  `twoCoverH0LinearEquiv`) agree at a terminal object.
* `Scheme.TwoCoverPairData.h0Equiv_val` — the `H⁰`-carrier of a two-cover pair reads a
  cohomology class as the pair of chart restrictions of its global section.
* `relSectionsMap_relSectionsMap` — the tower law of the sections comparison,
  `relSectionsMap C R R' ∘ relSectionsMap C k R = relSectionsMap C k R'`.
* `resHom_relTwistH0BaseChange_one_tmul_fst/snd` — **the val-computation**: the rigid
  engine's `H⁰` base change `relTwistH0BaseChange C k S` reads, on `1 ⊗ y`, as the
  sections comparison `relSectionsMap C k S` of the chart components of `y`.
* `resHom_relThetaWindowEquiv_cancelBaseChange_fst/snd` — **THE TRIANGLE**: the window
  identification over `R'` of the compared ambient vector is the compared window
  identification over `R`, chart-componentwise.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

/-! ## The degree-zero compatibility of the two section identifications -/

namespace CategoryTheory

section ExtCompat

universe v u'

variable {D : Type u'} [Category.{v} D] [Abelian D] [HasExt.{v} D]
variable (R : Type v) [CommRing R] [Linear R D]

/-- Precomposition with `mk₀ f` corresponds to composition with `f` under the
degree-zero identification `Ext X Y 0 ≃ₗ[R] (X ⟶ Y)` — the universe-polymorphic form
of `Abelian.Ext.linearEquiv₀_mk₀_comp` (`Cohomology/OverOpen.lean`), applicable to the
sheaf category (objects one universe above the homs). -/
private lemma Abelian.Ext.linearEquiv₀_mk₀_comp' {X Y Z : D} (f : X ⟶ Y)
    (x : Abelian.Ext Y Z 0) :
    Abelian.Ext.linearEquiv₀ (R := R)
        ((Abelian.Ext.mk₀ f).comp x (zero_add 0)) =
      f ≫ Abelian.Ext.linearEquiv₀ (R := R) x := by
  apply (Abelian.Ext.mk₀_bijective X Z).injective
  rw [Abelian.Ext.mk₀_linearEquiv₀_apply, ← Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.mk₀_linearEquiv₀_apply]

end ExtCompat

namespace Sheaf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable {R : Type u} [CommRing R]
variable [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} R)]
variable {T : C} (hT : IsTerminal T) (F : Sheaf J (ModuleCat.{u} R))

set_option maxHeartbeats 800000 in
-- The `Ext`-level unfoldings through the sheafified free/constant sheaves are heavy.
omit [HasWeakSheafify J (Type u)] in
/-- **The two degree-zero identifications agree**: reading a degree-zero class through
the terminal-object comparison `HModule.linearEquivHModule'` and the free-sheaf
identification `HModule'.linearEquiv₀` is the constant-sheaf identification
`HModule.linearEquiv₀`. -/
theorem HModule.linearEquiv₀_linearEquivHModule' (w : HModule F 0) :
    HModule'.linearEquiv₀ F T (HModule.linearEquivHModule' hT F 0 w) =
      HModule.linearEquiv₀ J hT F w := by
  have hcomp := Abelian.Ext.linearEquiv₀_mk₀_comp' (R := R)
    (freeModuleSheafIsoConstModuleSheaf J R hT).hom
    (w : Abelian.Ext (constModuleSheaf J R) F 0)
  rw [HModule'.linearEquiv₀, LinearEquiv.trans_apply,
    HModule.linearEquivHModule'_apply, hcomp,
    HModule.linearEquiv₀, LinearEquiv.trans_apply, freeModuleSheafHomEquiv_comp,
    show freeModuleSheafHomEquiv (constModuleSheaf J R)
        (freeModuleSheafIsoConstModuleSheaf J R hT).hom = constModuleSheafGen J R hT from
      LinearEquiv.apply_symm_apply _ _]
  exact (constModuleSheafHomEquiv_eq_app_gen hT _).symm

end Sheaf

end CategoryTheory

/-! ## The `H⁰`-carrier of a two-cover pair reads as the chart restrictions -/

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

section H0Val

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable {F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} R)}
variable {U₀ U₁ : X.Opens} [Scheme.QcohOn F U₀] [Scheme.QcohOn F U₁]
variable (dat : Scheme.TwoCoverPairData F U₀ U₁)
variable (hU₀ : IsAffineOpen U₀) (hU₁ : IsAffineOpen U₁) (hcov : U₀ ⊔ U₁ = ⊤)

/-- **The `H⁰`-carrier reads as the chart restrictions**: the two-lattice-pair `H⁰`
class of a degree-zero cohomology class has, as components, the two chart restrictions
of its global section (`HModule.linearEquiv₀`). -/
theorem Scheme.TwoCoverPairData.h0Equiv_val (w : Sheaf.HModule F 0) :
    (dat.h0Equiv hU₀ hU₁ hcov w).val =
      (secRes F le_top (Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology (X : TopCat)) isTerminalTop F w),
        secRes F le_top (Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology (X : TopCat)) isTerminalTop F w)) := by
  have h1 : (dat.h0Equiv hU₀ hU₁ hcov w).val =
      ((X.twoCoverSquare U₀ U₁ hcov).sectionsKerEquiv F
        (Sheaf.HModule'.linearEquiv₀ F (X.twoCoverSquare U₀ U₁ hcov).X₄
          (Sheaf.HModule.linearEquivHModule' isTerminalTop F 0 w))).val := rfl
  rw [h1, show Sheaf.HModule'.linearEquiv₀ F (X.twoCoverSquare U₀ U₁ hcov).X₄
        (Sheaf.HModule.linearEquivHModule' isTerminalTop F 0 w) =
      Sheaf.HModule.linearEquiv₀ (Opens.grothendieckTopology (X : TopCat))
        isTerminalTop F w from
    Sheaf.HModule.linearEquiv₀_linearEquivHModule' isTerminalTop F w]
  exact (X.twoCoverSquare U₀ U₁ hcov).sectionsKerEquiv_apply_coe F _

end H0Val

/-! ## The tower law of the sections comparison -/

section Tower

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R'] [IsScalarTower k R R']

/-- `appLE` is invariant under an equality of morphisms (the inclusion witness is
proof-irrelevant). -/
private lemma appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens}
    {W : X.Opens} (e : W ≤ f ⁻¹ᵁ U) :
    f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

/-- Simultaneously transporting the morphism and source open of `appLE` does not
change the compared section. -/
private lemma cast_appLE_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g)
    {U : Y.Opens} {W W' : X.Opens} (hW : W = W')
    (e : W ≤ f ⁻¹ᵁ U) (e' : W' ≤ g ⁻¹ᵁ U) (s : Γ(Y, U)) :
    cast (congrArg (fun V : X.Opens => ↑(Γ(X, V))) hW) ((f.appLE U W e).hom s) =
      (g.appLE U W' e').hom s := by
  subst hf
  subst hW
  rfl

/-- Equality of unit values after transporting their ambient rings gives heterogeneous
equality of the units themselves. -/
private lemma units_heq_of_cast_val_eq {M N : CommRingCat} (h : M = N)
    (a : (↑M)ˣ) (b : (↑N)ˣ)
    (hab : cast (congrArg (fun A : CommRingCat => ↑A) h) (a : ↑M) = (b : ↑N)) :
    HEq a b := by
  subst h
  exact heq_of_eq (Units.ext hab)

/-- **The general tower law of the sections comparison** over `R → R' → R''`:
comparing sections in two stages is comparing them along the composite tower. -/
theorem relSectionsMap_relSectionsMap_tower
    (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R'']
    (V : C.left.Opens)
    (s : Γ(relCurve C R, (fst C (overSpec k R)).left ⁻¹ᵁ V)) :
    relSectionsMap C R' R'' V (relSectionsMap C R R' V s) =
      relSectionsMap C R R'' V s := by
  have h : (relCurveMap C R R').appLE ((fst C (overSpec k R)).left ⁻¹ᵁ V)
        ((fst C (overSpec k R')).left ⁻¹ᵁ V)
        (le_of_eq (relCurveMap_preimage C R R' V).symm) ≫
      (relCurveMap C R' R'').appLE ((fst C (overSpec k R')).left ⁻¹ᵁ V)
        ((fst C (overSpec k R'')).left ⁻¹ᵁ V)
        (le_of_eq (relCurveMap_preimage C R' R'' V).symm) =
      (relCurveMap C R R'').appLE ((fst C (overSpec k R)).left ⁻¹ᵁ V)
        ((fst C (overSpec k R'')).left ⁻¹ᵁ V)
        (le_of_eq (relCurveMap_preimage C R R'' V).symm) := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_hom (relCurveMap_comp (R' := R') (R'' := R'')) _
  exact congr($(h).hom s)

/-- **The tower law of the sections comparison** over `k → R → R'`: comparing sections
in two stages is comparing them along the composite tower,
`relSectionsMap C R R' ∘ relSectionsMap C k R = relSectionsMap C k R'`. -/
theorem relSectionsMap_relSectionsMap (V : C.left.Opens)
    (s : Γ(relCurve C k, (fst C (overSpec k k)).left ⁻¹ᵁ V)) :
    relSectionsMap C R R' V (relSectionsMap C k R V s) =
      relSectionsMap C k R' V s := by
  exact relSectionsMap_relSectionsMap_tower C k R R' V s

/-- Basic-open cover data base-changed along `R → R' → R''` agrees with direct
base change along the composite tower. -/
theorem BasicOpenCoverData.baseChange_baseChange
    {pi : C.left ⟶ P1 k} [IsAffineHom pi] (D : BasicOpenCoverData C R pi)
    (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R''] :
    (D.baseChange R').baseChange R'' = D.baseChange R'' := by
  cases D
  simp only [BasicOpenCoverData.baseChange, relSectionsMap_relSectionsMap_tower]

/-- Each piece of a basic-open cover base-changed in two stages agrees with the
corresponding piece after direct base change. -/
theorem BasicOpenCoverData.pieces_tower
    {pi : C.left ⟶ P1 k} [IsAffineHom pi] (D : BasicOpenCoverData C R pi)
    (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R'']
    (i : D.index) :
    ((D.baseChange R').baseChange R'').pieces i =
      (D.baseChange R'').pieces i := by
  rw [(D.baseChange R').pieces_baseChange R'' i, D.pieces_baseChange R' i,
    D.pieces_baseChange R'' i, ← Scheme.Hom.comp_preimage,
    relCurveMap_comp (C := C) (R := R) (R' := R') (R'' := R'')]

/-- The comparison map on a double overlap is transitive along an arbitrary tower of
coefficient rings, after transporting the target overlap along `pieces_tower`. -/
theorem BasicOpenCoverData.overlapMap_tower
    {pi : C.left ⟶ P1 k} [IsAffineHom pi] (D : BasicOpenCoverData C R pi)
    (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R'']
    (i j : D.index) (s : Γ(relCurve C R, D.pieces i ⊓ D.pieces j)) :
    let hopen := congrArg₂ (· ⊓ ·)
      (D.pieces_tower C R R' R'' i) (D.pieces_tower C R R' R'' j)
    cast (congrArg
      (fun W : (relCurve C R'').Opens => ↑(Γ(relCurve C R'', W))) hopen)
      ((D.baseChange R').overlapMap R'' i j (D.overlapMap R' i j s)) =
        D.overlapMap R'' i j s := by
  dsimp only
  simp only [BasicOpenCoverData.overlapMap]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact cast_appLE_congr
    (relCurveMap_comp (C := C) (R := R) (R' := R') (R'' := R''))
    (congrArg₂ (· ⊓ ·)
      (D.pieces_tower C R R' R'' i) (D.pieces_tower C R R' R'' j)) _ _ s

/-- Pinned cocycle data base-changed along `R → R' → R''` agrees with direct
base change. The unit field is identified by `overlapMap_tower`. -/
theorem BasicOpenCocycleDatum.baseChange_baseChange
    {pi : C.left ⟶ P1 k} [IsAffineHom pi] (D : BasicOpenCocycleDatum C R pi)
    (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R''] :
    (D.baseChange R').baseChange R'' = D.baseChange R'' := by
  rw [BasicOpenCocycleDatum.mk.injEq]
  constructor
  · exact BasicOpenCoverData.baseChange_baseChange C R R' D.toBasicOpenCoverData R''
  · apply Function.hfunext rfl
    intro i i' hi
    cases hi
    apply Function.hfunext rfl
    intro j j' hj
    cases hj
    let hopen := congrArg₂ (· ⊓ ·)
      (D.toBasicOpenCoverData.pieces_tower C R R' R'' i)
      (D.toBasicOpenCoverData.pieces_tower C R R' R'' j)
    apply units_heq_of_cast_val_eq
      (congrArg (fun W : (relCurve C R'').Opens => Γ(relCurve C R'', W)) hopen)
    simp only [BasicOpenCocycleDatum.baseChange, Units.coe_map]
    exact D.toBasicOpenCoverData.overlapMap_tower C R R' R'' i j (D.unit i j)

end Tower

/-! ## The global-sections reading of the relative twisted sheaf -/

section GlobalRead

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (S : Type u) [CommRing S] [Algebra k S] (D : C.left.AffineTwoCover)

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
/-- **Degree-zero cohomology of the relative twisted sheaf is its module of global
twisted sections** — the generic-cocycle form of `relThetaSectionsEquiv`
(`AlgebraicJacobian.Picard.DivisorFamilyWindow`). -/
noncomputable def relTwistSectionsEquiv₀
    (γ : Γ(relCurve C S, (relCover C S D).V₀ ⊓ (relCover C S D).V₁)ˣ) :
    Sheaf.HModule (relTwistSheaf C S D γ) 0 ≃ₗ[S]
      ↥(twistSubmodule S (relCover C S D).V₀ (relCover C S D).V₁ γ ⊤) :=
  Sheaf.HModule.linearEquiv₀
    (Opens.grothendieckTopology ((relCurve C S : Scheme.{u}) : TopCat))
    (isTerminalTop) (relTwistSheaf C S D γ)

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
/-- (Implementation) Transporting a degree-zero class along an equality of cocycles
does not move the underlying global section pair. -/
lemma val_relTwistSectionsEquiv₀_mapEquiv
    {γ₁ γ₂ : Γ(relCurve C S, (relCover C S D).V₀ ⊓ (relCover C S D).V₁)ˣ} (e : γ₁ = γ₂)
    (w : Sheaf.HModule (relTwistSheaf C S D γ₁) 0) :
    (relTwistSectionsEquiv₀ C S D γ₂
        (Sheaf.HModule.mapEquiv (eqToIso (congrArg (relTwistSheaf C S D) e)) 0 w)).val
      = (relTwistSectionsEquiv₀ C S D γ₁ w).val := by
  subst e
  rw [show (congrArg (relTwistSheaf C S D) (rfl : γ₁ = γ₁)) = rfl from rfl,
    eqToIso_refl, Sheaf.HModule.mapEquiv_apply, Iso.refl_hom,
    Sheaf.HModule.map_id_apply]

end GlobalRead

/-! ## The val-computation of the rigid engine's `H⁰` base change -/

section H0BaseChangeVal

open AlgebraicJacobian

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (S : Type u) [CommRing S] [Algebra k S]
variable (π : C.left ⟶ P1 k) [IsFinite π]
variable (g : Γ(relCurve C k, (relCover C k (fiberTwoCover π)).V₀ ⊓
  (relCover C k (fiberTwoCover π)).V₁)ˣ)
variable (hH1 : Subsingleton (relTwistPair C k π g).H1)

/-- (Implementation) The kernel base-change equivalence on a pure tensor, ambient
value: `r ⊗ q ↦ r ⊗ q.val`. -/
lemma kerBaseChangeEquiv_tmul_coe {A B : Type u} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [Module.Flat k B] (δ : A →ₗ[k] B)
    (hδ : Function.Surjective δ) (r : S) (q : LinearMap.ker δ) :
    ((RigidEngine.kerBaseChangeEquiv δ S hδ (r ⊗ₜ q) :
        LinearMap.ker (δ.baseChange S)) : S ⊗[k] A) = r ⊗ₜ (q : A) := by
  change ((LinearMap.ker δ).subtype.baseChange S) (r ⊗ₜ q) = _
  rw [LinearMap.baseChange_tmul, Submodule.subtype_apply]

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
/-- (Implementation) The `H⁰` base change of the theta pair, read through the `S`-side
`H⁰`-carrier: it is the kernel transport of the abstract base-change clause. -/
lemma h0Equiv_relTwistH0BaseChange (x : S ⊗[k]
    (Sheaf.HModule (relTwistSheaf C k (fiberTwoCover π) g) 0)) :
    (relTwistPairData C S π
        (relCocycleBaseChange C k S (fiberTwoCover π) g)).h0Equiv
        (relCover_isAffineOpen₀ C S (fiberTwoCover π))
        (relCover_isAffineOpen₁ C S (fiberTwoCover π))
        (relCover_sup C S (fiberTwoCover π))
        (relTwistH0BaseChange C k S π g hH1 x) =
      RigidEngine.kerCongr ((relTwistPair C k π g).diff.baseChange S)
        ((relTwistPair C S π (relCocycleBaseChange C k S (fiberTwoCover π) g)).diff)
        (relTwistDomBaseChange C k S (fiberTwoCover π) g)
        (relTwistOverlapBaseChange C k S (fiberTwoCover π) g)
        (fun a => relTwistPairDiffBaseChange C k S π g a)
        (relTwistH0BaseChangeEquiv C k π g hH1 S x) := by
  rw [relTwistH0BaseChange, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  exact LinearEquiv.apply_symm_apply _ _

end H0BaseChangeVal

section SmulHelper

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

/-- (Implementation) Restriction commutes with the `Scheme.overModule` action on the
relative curve. -/
lemma resHom_smul_rel' (S : Type u) [CommRing S] [Algebra k S]
    {W V : (relCurve C S).Opens} (h : W ≤ V) (s : S) (y : Γ(relCurve C S, V)) :
    (relCurve C S).resHom h (s • y) = s • (relCurve C S).resHom h y := by
  rw [Scheme.overModule_smul_def, map_mul, Scheme.overModule_smul_def]
  congr 1
  exact (relCurve C S).overAlgebraMap_apply_res S (homOfLE h).op s

end SmulHelper

end AlgebraicGeometry
