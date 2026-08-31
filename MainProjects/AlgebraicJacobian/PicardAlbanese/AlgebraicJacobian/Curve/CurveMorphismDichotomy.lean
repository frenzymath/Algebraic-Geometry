/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.BaseFieldTransition
import AlgebraicJacobian.RiemannRoch.ChartColength
import AlgebraicJacobian.RiemannRoch.Degree

/-!
# The curve-morphism dichotomy: finite surjective or constant (E-v Lane A)

For a morphism `h : D ⟶ E` of proper smooth geometrically irreducible curve bundles over a
field `K` (the `Over (Spec K)`-objects of the Jacobian challenge), this file proves the
**dichotomy** feeding the F-6 case split of the Picard-functor wave
(`informal/w7-ev-worksheet.md` §1.3, bricks EV-1a–EV-1d):

* **EV-1a** (`AlgebraicGeometry.isProper_left`): `h.left` is proper — cancel `E.hom` in
  `h.left ≫ E.hom = D.hom` (`IsProper.of_comp`).  Local finite type and quasi-compactness
  of `h.left` follow by instance search.
* **EV-1d** (`AlgebraicGeometry.Scheme.Hom.exists_comp_fromSpecResidueField_eq`): a
  morphism with reduced quasi-compact source whose set-range is a closed point `{x}`
  factors through `Spec κ(x) ⟶ E.left`.  The kernel comparison
  (`Scheme.Hom.ker_fromSpecResidueField_le`) is discharged on basic opens: a section
  vanishing at `x` pulls back to a section with empty basic open, which vanishes on the
  reduced source (`eq_zero_of_basicOpen_eq_bot`).
* **EV-const** (`AlgebraicGeometry.cechPicMap_eq_one_of_factorization`): through such a
  factorization every Čech Picard class pulls back trivially — the class dies already in
  `CechPic (Spec κ(x))`, which is a subsingleton group.  Combined form
  `cechPicMap_eq_one_of_range_eq_singleton`, degree form
  `classDeg_cechPicMap_eq_zero_of_range_eq_singleton`.
* **EV-1b** (`AlgebraicGeometry.finite_of_isClosed_of_notMem_genericPoint_curve`): a
  closed subset of the curve bundle avoiding the generic point is finite.  The topological
  content is the landed `Scheme.finite_of_isClosed_of_notMem_genericPoint`
  (`Curve/StalksDVR.lean`: Noetherian irreducible space with height-one specialization
  order); this brick discharges its hypotheses from the `[X.Over (Spec K)]` pack.
* **EV-1c** (`AlgebraicGeometry.curveHom_isFinite_or_constant`, the **keystone**): every
  morphism of curve bundles is finite surjective or constant.  The image is closed
  (properness) and irreducible, hence the closure of a point `ζ`; if `ζ` is a closed
  point the morphism is constant, and if `ζ = η_E` the fibers are finite (EV-1b over
  closed points; over `η_E` the fiber is `{η_D}` unless `E.left` is a one-point space, in
  which case the *constant* leg holds with `x = η_E` — the two legs of the disjunction
  overlap there by design), so `h.left` is finite by Zariski's main theorem
  (`IsFinite.of_isProper_of_locallyQuasiFinite`).

The dichotomy legs are exactly the hypotheses of the EV-main multiplicativity statement
(`[Surjective h.left] [IsFinite h.left]`, Lane B) and of the constant-leg degree collapse
above; only F-6 consumes the disjunction itself.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ## EV-1a: morphisms between proper bundles are proper -/

section Proper

variable {S : Scheme.{u}} {D E : Over S}

/-- **EV-1a.** A morphism of `Over`-bundles with proper source bundle and separated target
bundle has proper underlying morphism: cancel `E.hom` in `h.left ≫ E.hom = D.hom`.  For the
curve bundles of the challenge both hypotheses come from `[IsProper _.hom]`.  Local finite
type and quasi-compactness of `h.left` follow by instance search from this. -/
theorem isProper_left [IsProper D.hom] [IsSeparated E.hom] (h : D ⟶ E) :
    IsProper h.left := by
  haveI : IsProper (h.left ≫ E.hom) := by rw [Over.w h]; infer_instance
  exact IsProper.of_comp h.left E.hom

/-- Morphisms between proper bundles are locally of finite type (EV-1a corollary). -/
theorem locallyOfFiniteType_left [IsProper D.hom] [IsSeparated E.hom] (h : D ⟶ E) :
    LocallyOfFiniteType h.left :=
  haveI : IsProper h.left := isProper_left h
  inferInstance

/-- Morphisms between proper bundles are quasi-compact (EV-1a corollary). -/
theorem quasiCompact_left [IsProper D.hom] [IsSeparated E.hom] (h : D ⟶ E) :
    QuasiCompact h.left :=
  haveI : IsProper h.left := isProper_left h
  inferInstance

end Proper

/-! ## EV-1d: the constant-leg factorization through `Spec κ(x)` -/

section ConstantLeg

/-- **The kernel comparison of EV-1d.**  If the set-range of `f : X ⟶ Y` is the single
point `{y}` and `X` is reduced, then the kernel ideal sheaf of `Y.fromSpecResidueField y`
is contained in the kernel of `f`.  On an affine `U`: a section `s` killed by
`Spec κ(y) ⟶ Y` has `y ∉ basicOpen s` (pull the membership back through
`Spec.preimage_basicOpen` to the empty basic open of `0`), so `f ⁻¹ᵁ basicOpen s = ⊥`
because the range of `f` misses `basicOpen s`; hence `f^♯ s` has empty basic open and
vanishes on the reduced source. -/
theorem Scheme.Hom.ker_fromSpecResidueField_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsReduced X] [QuasiCompact f] {y : Y} (hrange : Set.range f.base = {y}) :
    (Y.fromSpecResidueField y).ker ≤ f.ker := by
  rw [Scheme.IdealSheafData.le_def]
  intro U s hs
  have hs0 : ((Y.fromSpecResidueField y).app U).hom s = 0 :=
    RingHom.mem_ker.mp ((Y.fromSpecResidueField y).ideal_ker_le U hs)
  -- `s` vanishes at `y`: its basic open misses `y`.
  have hyb : y ∉ Y.basicOpen s := by
    intro hyb
    have hy' : y ∈ Set.range (Y.fromSpecResidueField y).base := by
      rw [Scheme.range_fromSpecResidueField]; rfl
    obtain ⟨p, hp⟩ := hy'
    have hpmem : p ∈ (Y.fromSpecResidueField y) ⁻¹ᵁ Y.basicOpen s := by
      change (Y.fromSpecResidueField y).base p ∈ Y.basicOpen s
      rw [hp]; exact hyb
    rw [Scheme.preimage_basicOpen] at hpmem
    rw [show ((Y.fromSpecResidueField y).app U) s = 0 from hs0,
      Scheme.basicOpen_zero] at hpmem
    simp at hpmem
  -- the pulled-back section has empty basic open, hence vanishes on the reduced source
  have hpre : f ⁻¹ᵁ Y.basicOpen s = ⊥ := by
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_bot]
    refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => hyb ?_
    have hzy : f.base z = y := by
      have hmem : f.base z ∈ Set.range f.base := Set.mem_range_self z
      rw [hrange] at hmem
      exact hmem
    change y ∈ Y.basicOpen s
    rw [← hzy]
    exact hz
  have hbot : X.basicOpen ((f.app U).hom s) = ⊥ := by
    rw [show X.basicOpen ((f.app U).hom s) = X.basicOpen ((f.app U) s) from rfl,
      ← Scheme.preimage_basicOpen]
    exact hpre
  rw [f.ker_apply]
  exact RingHom.mem_ker.mpr (eq_zero_of_basicOpen_eq_bot _ hbot)

/-- **EV-1d (the constant-leg factorization).**  A morphism of schemes with reduced
quasi-compact source whose set-range is a *closed* point `{y}` factors through mathlib's
`Y.fromSpecResidueField y : Spec κ(y) ⟶ Y`, via the universal property of closed
immersions (`isClosed_singleton_iff_isClosedImmersion` + `IsClosedImmersion.lift`). -/
theorem Scheme.Hom.exists_comp_fromSpecResidueField_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsReduced X] [QuasiCompact f] {y : Y} (hy : IsClosed ({y} : Set Y))
    (hrange : Set.range f.base = {y}) :
    ∃ q : X ⟶ Spec (Y.residueField y), q ≫ Y.fromSpecResidueField y = f := by
  haveI : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  exact ⟨IsClosedImmersion.lift (Y.fromSpecResidueField y) f
      (f.ker_fromSpecResidueField_le hrange),
    IsClosedImmersion.lift_fac (Y.fromSpecResidueField y) f
      (f.ker_fromSpecResidueField_le hrange)⟩

/-- **EV-const.**  A morphism of bundles factoring through `Spec κ(x)` pulls every Čech
Picard class back to the trivial class: the class dies on the subsingleton scheme
`Spec κ(x)` already (probe EV-B: `map_comp`, `eq_one_of_subsingleton`, `map_one`). -/
theorem cechPicMap_eq_one_of_factorization {K : Type u} [Field K]
    (D E : Over (Spec (CommRingCat.of K))) (h : D ⟶ E) {x : E.left}
    (q : D.left ⟶ Spec (E.left.residueField x))
    (hfac : q ≫ E.left.fromSpecResidueField x = h.left) (Λ : E.left.CechPic) :
    Scheme.CechPic.map h.left Λ = 1 := by
  haveI : Subsingleton (Spec (E.left.residueField x)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (E.left.residueField x)))
  calc Scheme.CechPic.map h.left Λ
      = Scheme.CechPic.map q
          (Scheme.CechPic.map (E.left.fromSpecResidueField x) Λ) := by
        rw [← hfac, Scheme.CechPic.map_comp]; rfl
    _ = Scheme.CechPic.map q 1 := by
        rw [Scheme.CechPic.eq_one_of_subsingleton (Spec (E.left.residueField x))
          (Scheme.CechPic.map (E.left.fromSpecResidueField x) Λ)]
    _ = 1 := map_one _

/-- **EV-1d + EV-const combined**: a morphism of bundles whose set-range is a closed point
pulls every Čech Picard class back to the trivial class. -/
theorem cechPicMap_eq_one_of_range_eq_singleton {K : Type u} [Field K]
    (D E : Over (Spec (CommRingCat.of K))) (h : D ⟶ E) [IsReduced D.left]
    [QuasiCompact h.left] {x : E.left} (hx : IsClosed ({x} : Set E.left))
    (hrange : Set.range h.left.base = {x}) (Λ : E.left.CechPic) :
    Scheme.CechPic.map h.left Λ = 1 := by
  obtain ⟨q, hfac⟩ := h.left.exists_comp_fromSpecResidueField_eq hx hrange
  exact cechPicMap_eq_one_of_factorization D E h q hfac Λ

end ConstantLeg

/-! ## EV-1b: closed subsets avoiding the generic point are finite -/

section FiberFiniteness

/-- **EV-1b (fiber finiteness).**  On the curve bundle `X` over `K` (integral, smooth of
relative dimension one, quasi-compact), a closed subset avoiding the generic point is
finite.  The topological content is the landed
`Scheme.finite_of_isClosed_of_notMem_genericPoint` (Noetherian irreducible space with
height-one specialization order, `Curve/StalksDVR.lean`); here its hypotheses are
discharged from the standing pack: `NoetherianSpace` from local finite type over the field
(`LocallyOfFiniteType.isLocallyNoetherian`) plus compactness, and the height-one
specialization order from the Dedekind charts
(`SmoothOfRelativeDimension.specializes_eq_genericPoint_or_eq`). -/
theorem finite_of_isClosed_of_notMem_genericPoint_curve
    (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [CompactSpace X] {Z : Set X} (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) :
    Z.Finite := by
  haveI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of K))
  haveI : IsNoetherian X := ⟨⟩
  exact Scheme.finite_of_isClosed_of_notMem_genericPoint
    (fun _ _ hspec =>
      SmoothOfRelativeDimension.specializes_eq_genericPoint_or_eq
        (X ↘ Spec (CommRingCat.of K)) hspec)
    hZ hη

end FiberFiniteness

/-! ## EV-1c: the dichotomy -/

section Dichotomy

variable {K : Type u} [Field K] {D E : Over (Spec (CommRingCat.of K))}
  [IsProper D.hom] [SmoothOfRelativeDimension 1 D.hom] [GeometricallyIrreducible D.hom]
  [IsProper E.hom] [SmoothOfRelativeDimension 1 E.hom] [GeometricallyIrreducible E.hom]

/-- **EV-1c: the curve-morphism dichotomy (the Lane A keystone).**  Every morphism
`h : D ⟶ E` of proper smooth geometrically irreducible curve bundles over `K` is either
**finite surjective** or **constant** (its set-range is a single closed point of `E.left`).

The two legs may overlap when `E.left` has a one-point space; the disjunction is the
statement, not a partition.  Route: the image of `h.left` is closed (EV-1a properness) and
irreducible, hence the closure of a point `ζ`.  If `ζ ≠ η_E` it is a closed point and the
range is `{ζ}` — the constant leg.  If `ζ = η_E` then `h.left` is surjective, the fibers
over closed points are finite (EV-1b: closed, missing `η_D` since `h(η_D) = η_E`), and the
fiber over `η_E` is `{η_D}` — unless some closed point of `D.left` also maps to `η_E`, in
which case `{η_E}` is closed, `E.left` is a one-point space and the *constant* leg holds
with `x = η_E`.  Fiberwise finiteness gives local quasi-finiteness
(`locallyQuasiFinite_iff_finite_preimage_singleton`), and Zariski's main theorem
(`IsFinite.of_isProper_of_locallyQuasiFinite`) closes the finite leg. -/
theorem curveHom_isFinite_or_constant (h : D ⟶ E) :
    (Surjective h.left ∧ IsFinite h.left) ∨
      (∃ x : E.left, IsClosed ({x} : Set E.left) ∧ Set.range h.left.base = {x}) := by
  haveI : IsProper h.left := isProper_left h
  -- the image is closed and irreducible, hence the closure of a point `ζ`
  have hclosed : IsClosed (Set.range h.left.base) := h.left.isClosedMap.isClosed_range
  have hirr : IsIrreducible (Set.range h.left.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ D.left).image _
      h.left.continuous.continuousOn
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hirr hclosed
  by_cases hζη : ζ = genericPoint E.left
  · -- dominant case: the range is everything
    subst hζη
    have huniv : Set.range h.left.base = Set.univ :=
      hζ.def.symm.trans (genericPoint_spec E.left).def
    haveI : Surjective h.left := ⟨Set.range_eq_univ.mp huniv⟩
    have hη : h.left.base (genericPoint D.left) = genericPoint E.left :=
      genericPoint_eq_of_surjective h.left
    by_cases hz : ∃ z : D.left,
        z ≠ genericPoint D.left ∧ h.left.base z = genericPoint E.left
    · -- a closed point maps to `η_E`: then `E.left` is a one-point space and the
      -- constant leg holds with `x = η_E` (the legs overlap here by design)
      obtain ⟨z, hzne, hzη⟩ := hz
      have hclz : IsClosed ({z} : Set D.left) :=
        isClosed_singleton_of_ne_genericPoint D.hom hzne
      have hclη : IsClosed ({genericPoint E.left} : Set E.left) := by
        have himg : IsClosed (h.left.base '' ({z} : Set D.left)) :=
          h.left.isClosedMap _ hclz
        rwa [Set.image_singleton, hzη] at himg
      refine Or.inr ⟨genericPoint E.left, hclη, ?_⟩
      rw [huniv]
      exact (genericPoint_spec E.left).def.symm.trans hclη.closure_eq
    · -- all fibers are finite: EV-1b over closed points, `{η_D}` over `η_E`; then ZMT
      push Not at hz
      have hfib : ∀ y : E.left, (h.left ⁻¹' {y}).Finite := by
        intro y
        by_cases hyη : y = genericPoint E.left
        · subst hyη
          refine (Set.finite_singleton (genericPoint D.left)).subset fun z hz' => ?_
          rw [Set.mem_singleton_iff]
          by_contra hzne
          exact hz z hzne (Set.mem_singleton_iff.mp hz')
        · letI : D.left.Over (Spec (CommRingCat.of K)) := .ofHom D.hom
          haveI : SmoothOfRelativeDimension 1 (D.left ↘ Spec (CommRingCat.of K)) :=
            inferInstanceAs (SmoothOfRelativeDimension 1 D.hom)
          have hcl : IsClosed (h.left ⁻¹' {y} : Set D.left) :=
            (isClosed_singleton_of_ne_genericPoint E.hom hyη).preimage h.left.continuous
          have hnot : genericPoint D.left ∉ (h.left ⁻¹' {y} : Set D.left) := fun hmem =>
            hyη ((Set.mem_singleton_iff.mp hmem).symm.trans hη)
          exact finite_of_isClosed_of_notMem_genericPoint_curve K hcl hnot
      haveI : LocallyQuasiFinite h.left :=
        (locallyQuasiFinite_iff_finite_preimage_singleton).mpr hfib
      exact Or.inl ⟨‹Surjective h.left›, IsFinite.of_isProper_of_locallyQuasiFinite h.left⟩
  · -- `ζ` is a closed point: the constant leg
    have hcl : IsClosed ({ζ} : Set E.left) :=
      isClosed_singleton_of_ne_genericPoint E.hom hζη
    exact Or.inr ⟨ζ, hcl, hζ.def.symm.trans hcl.closure_eq⟩

omit [SmoothOfRelativeDimension 1 E.hom] [GeometricallyIrreducible E.hom] in
/-- **The constant-leg degree collapse on the curve** (EV-1d + EV-const at the degree
level): if the set-range of `h.left` is a closed point, the pullback of every Čech Picard
class has degree zero.  This is the form the F-6 case split consumes on the constant leg;
the finite-surjective leg is Lane B's `classDeg` multiplicativity. -/
theorem classDeg_cechPicMap_eq_zero_of_range_eq_singleton (h : D ⟶ E) {x : E.left}
    (hx : IsClosed ({x} : Set E.left)) (hrange : Set.range h.left.base = {x})
    (Λ : E.left.CechPic) :
    letI : D.left.Over (Spec (CommRingCat.of K)) := .ofHom D.hom
    haveI : SmoothOfRelativeDimension 1 (D.left ↘ Spec (CommRingCat.of K)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 D.hom)
    haveI : QuasiCompact (D.left ↘ Spec (CommRingCat.of K)) :=
      inferInstanceAs (QuasiCompact D.hom)
    haveI : Module.Finite K (Sheaf.HModule (D.left.moduleKSheaf K) 0) :=
      moduleFinite_hModule_zero D
    haveI : Module.Finite K (Sheaf.HModule (D.left.moduleKSheaf K) 1) :=
      moduleFinite_hModule_one D
    classDeg K (Scheme.CechPic.map h.left Λ) = 0 := by
  letI : D.left.Over (Spec (CommRingCat.of K)) := .ofHom D.hom
  haveI : SmoothOfRelativeDimension 1 (D.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 D.hom)
  haveI : QuasiCompact (D.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (QuasiCompact D.hom)
  haveI : Module.Finite K (Sheaf.HModule (D.left.moduleKSheaf K) 0) :=
    moduleFinite_hModule_zero D
  haveI : Module.Finite K (Sheaf.HModule (D.left.moduleKSheaf K) 1) :=
    moduleFinite_hModule_one D
  haveI : IsProper h.left := isProper_left h
  rw [cechPicMap_eq_one_of_range_eq_singleton D E h hx hrange Λ]
  exact classDeg_one K

end Dichotomy

end AlgebraicGeometry
