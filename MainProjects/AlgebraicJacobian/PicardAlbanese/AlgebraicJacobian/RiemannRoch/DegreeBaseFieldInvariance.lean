/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.LocalEquationsPullback
import AlgebraicJacobian.RiemannRoch.DegreeBaseChange

/-!
# E-iv-alg: the degree is invariant under base-field transition (gap G-D5(b), SB-5)

For the challenge curve `C : Over (Spec k)` and a `k`-algebra map `φ : K₁ →ₐ[k] K₂` of field
extensions of `k`, this file proves **E-iv-alg** (`informal/deg-d5b-worksheet.md` §2):

`classDeg K₂ (CechPic.map π L) = classDeg K₁ L`

for every Čech Picard class `L` of `C_{K₁}`, along the base-field transition
`π := (C ◁ Over.overSpecMap φ).left`.  This is the invariance equality through which the
degree of a relative Picard class becomes independent of the field of definition — the
well-definedness core of `degAt` (worksheet §1).

## The ladder (worksheet §2, steps 1–5)

1. Both sides are additive in `L`; `CurveDivisor.picClass K₁` is a surjective additive class
   map, so it suffices to treat `L = picClass K₁ (single hx' 1)` (`Finsupp.induction` plus
   `picClass_single_zpow` and `classDeg_zpow`).
2. `picClass_single` presents `L` by the tracked point equations
   `pointEquations K₁ hx' (pointUniformizerData K₁ hx')`.
3. `picClass_pullback` computes `CechPic.map π L` as the class of the pulled-back system
   `pointTransitionEquations`.  Its regularity hypothesis is discharged by
   `LocalEquations.pullbackEqn_germ_mem_nonZeroDivisors`: on **integral** schemes with `π`
   generic-to-generic, pulled equations are automatically regular — their germs at `η` are
   the injective function-field images of nonzero rational functions, and germs of nonzero
   sections on an integral scheme are nonzero.  (This subsumes the worksheet's
   flat-local-homomorphism discharge: integrality of both curves makes flatness of `π`
   unnecessary for regularity.)
4. The presentation divisor of the pulled system is supported in the fiber `π⁻¹(x')`, with
   coefficients `ord(π^♯ t)` (`pointTransitionEquations_presentation_elem_of_eq`/`_of_ne`:
   unit germs pull back to unit germs, the second chart piece's equation is `1`).
5. E-i (`classDeg_picClass`) turns both sides into divisor degrees, and the fiber-degree
   identity (†) (`sum_ordZ_residueDeg_baseFieldTransition`, SB-4) closes the computation.

## Main declarations

* `AlgebraicGeometry.Scheme.LocalEquations.pullbackEqn_germ_mem_nonZeroDivisors` — pulled
  local equations on integral schemes are regular (the `hreg` discharge).
* `AlgebraicGeometry.pointTransitionEquations`, `AlgebraicGeometry.pointTransitionUnit` —
  the pulled tracked point system and its trivializing unit `π^♯(uniformizer)`.
* `AlgebraicGeometry.classDeg_cechPicMap_baseFieldTransition` — **E-iv-alg** (the keystone).

The descent gadgets (`relPicDeg` and its invariance) are in
`AlgebraicJacobian.RiemannRoch.RelPicDegree`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-! ## Regularity of pulled-back local equations on integral schemes -/

/-- **Pulled local equations are regular on integral schemes.**  For a morphism `f : Y ⟶ X`
of integral schemes mapping the generic point to the generic point and a local-equation
system `E` on `X`, the germs of the pulled-back equations are nonzerodivisors — the
regularity hypothesis `hreg` of `LocalEquations.pullback`, discharged with no flatness:
the germ of the pulled equation at `η_Y` is the image of the germ of the equation at `η_X`
(a nonzero rational function) under the injective function-field map, and a section of an
integral scheme with one nonzero germ has all germs nonzero. -/
theorem Scheme.LocalEquations.pullbackEqn_germ_mem_nonZeroDivisors {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (hf : f.base (genericPoint Y) = genericPoint X) (E : X.LocalEquations) (y z : Y)
    (hz : z ∈ (E.cover.pullback f).opens y) :
    (Y.presheaf.germ ((E.cover.pullback f).opens y) z hz).hom
        (Scheme.LocalEquations.pullbackEqn f E y)
      ∈ nonZeroDivisors (Y.presheaf.stalk z) := by
  have hηy : genericPoint Y ∈ (E.cover.pullback f).opens y := by
    change f.base (genericPoint Y) ∈ E.cover.opens (f.base y)
    rw [hf]
    exact E.cover.genericPoint_mem_opens (f.base y)
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h0
  -- germs on an integral scheme are injective, so the pulled section vanishes
  have hsec : Scheme.LocalEquations.pullbackEqn f E y = 0 :=
    germ_injective_of_isIntegral Y z hz (by rw [h0, map_zero])
  -- but its germ at `η_Y` is the function-field image of a nonzero rational function
  have happ : Scheme.LocalEquations.pullbackEqn f E y
      = (f.app (E.cover.opens (f.base y))).hom (E.eqn (f.base y)) :=
    congr($(Scheme.Hom.appLE_eq_app f).hom (E.eqn (f.base y)))
  have hval := f.functionFieldMap_germ hf (E.cover.opens (f.base y))
    (E.cover.genericPoint_mem_opens (f.base y)) hηy (E.eqn (f.base y))
  refine E.germGeneric_eqn_ne_zero (f.base y) (f.functionFieldMap_injective hf ?_)
  rw [hval, ← happ, hsec]
  exact (map_zero _).trans (map_zero _).symm

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  {K₁ K₂ : Type u} [Field K₁] [Algebra k K₁] [Field K₂] [Algebra k K₂]

/-! ## The pulled tracked point system -/

/-- **The pulled tracked point system** (worksheet §2 step 3, an opaque named def per the
fiber-plumbing discipline): the pullback of the tracked point equations of the closed point
`x'` of `C_{K₁}` along the base-field transition `π := (C ◁ Over.overSpecMap φ).left`, with
regularity discharged by integrality of both curves. -/
noncomputable def pointTransitionEquations (φ : K₁ →ₐ[k] K₂)
    {x' : (C ⊗ overSpec k K₁).left}
    (hx' : x' ≠ genericPoint (C ⊗ overSpec k K₁).left) :
    (C ⊗ overSpec k K₂).left.LocalEquations :=
  (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')).pullback
    (C ◁ Over.overSpecMap φ).left
    (Scheme.LocalEquations.pullbackEqn_germ_mem_nonZeroDivisors
      (C ◁ Over.overSpecMap φ).left (baseFieldTransition_genericPoint C φ)
      (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')))

@[simp]
lemma pointTransitionEquations_eqn (φ : K₁ →ₐ[k] K₂) {x' : (C ⊗ overSpec k K₁).left}
    (hx' : x' ≠ genericPoint (C ⊗ overSpec k K₁).left) (z : (C ⊗ overSpec k K₂).left) :
    (pointTransitionEquations C φ hx').eqn z
      = Scheme.LocalEquations.pullbackEqn (C ◁ Over.overSpecMap φ).left
          (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')) z :=
  rfl

/-- **The trivializing unit of the pulled point system**: the pullback `π^♯` of the chosen
uniformizer at `x'`, as a unit of `K(C_{K₂})`. -/
noncomputable def pointTransitionUnit (φ : K₁ →ₐ[k] K₂) {x' : (C ⊗ overSpec k K₁).left}
    (hx' : x' ≠ genericPoint (C ⊗ overSpec k K₁).left) :
    (C ⊗ overSpec k K₂).left.functionFieldˣ :=
  (C ◁ Over.overSpecMap φ).left.functionFieldMapUnits (baseFieldTransition_genericPoint C φ)
    (Units.mk0 (uniformizer K₁ hx') (uniformizer_ne_zero K₁ hx'))

omit [IsProper C.hom] in
lemma coe_pointTransitionUnit (φ : K₁ →ₐ[k] K₂) {x' : (C ⊗ overSpec k K₁).left}
    (hx' : x' ≠ genericPoint (C ⊗ overSpec k K₁).left) :
    (pointTransitionUnit C φ hx' : (C ⊗ overSpec k K₂).left.functionField)
      = ((C ◁ Over.overSpecMap φ).left.functionFieldMap
          (baseFieldTransition_genericPoint C φ)).hom (uniformizer K₁ hx') :=
  rfl

omit [IsProper C.hom] in
/-- The germ at `η` of the tracked point equation at any index equal to `x'` is the chosen
uniformizer (index-generalized form of `germGeneric_pointEqn_self`). -/
private lemma germGeneric_pointEqn_of_eq {x' : (C ⊗ overSpec k K₁).left}
    (hx' : x' ≠ genericPoint (C ⊗ overSpec k K₁).left)
    (d : Scheme.PointUniformizerData K₁ hx') {w : (C ⊗ overSpec k K₁).left} (hw : w = x')
    (hη : genericPoint (C ⊗ overSpec k K₁).left ∈ (Scheme.pointCover K₁ hx' d).opens w) :
    ((C ⊗ overSpec k K₁).left.presheaf.germ ((Scheme.pointCover K₁ hx' d).opens w)
        (genericPoint (C ⊗ overSpec k K₁).left) hη).hom (Scheme.pointEqn K₁ hx' d w)
      = uniformizer K₁ hx' := by
  subst hw
  exact Scheme.germGeneric_pointEqn_self K₁ hx' d hη

/-- Off the fiber of `x'`, the trivializing element of the pulled point presentation is `1`:
the second chart piece's equation is `1`, and `1` pulls back to `1`. -/
lemma pointTransitionEquations_presentation_elem_of_ne (φ : K₁ →ₐ[k] K₂)
    {x' : (C ⊗ overSpec k K₁).left}
    (hx' : x' ≠ genericPoint (C ⊗ overSpec k K₁).left) {z : (C ⊗ overSpec k K₂).left}
    (hz : ((C ◁ Over.overSpecMap φ).left).base z ≠ x') :
    (pointTransitionEquations C φ hx').presentation.elem z = 1 := by
  have hηy : genericPoint (C ⊗ overSpec k K₂).left
      ∈ (C ◁ Over.overSpecMap φ).left ⁻¹ᵁ
        (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')).cover.opens
          (((C ◁ Over.overSpecMap φ).left).base z) := by
    change ((C ◁ Over.overSpecMap φ).left).base (genericPoint (C ⊗ overSpec k K₂).left)
      ∈ (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')).cover.opens
        (((C ◁ Over.overSpecMap φ).left).base z)
    rw [baseFieldTransition_genericPoint C φ]
    exact (Scheme.pointEquations K₁ hx'
      (Scheme.pointUniformizerData K₁ hx')).cover.genericPoint_mem_opens _
  have h1 : Scheme.LocalEquations.pullbackEqn (C ◁ Over.overSpecMap φ).left
      (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')) z = 1 := by
    have h2 : (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')).eqn
        (((C ◁ Over.overSpecMap φ).left).base z) = 1 := by
      rw [Scheme.pointEquations_eqn]
      exact Scheme.pointEqn_of_ne K₁ hx' (Scheme.pointUniformizerData K₁ hx') hz
    change ((C ◁ Over.overSpecMap φ).left.appLE _ _ le_rfl).hom
      ((Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')).eqn
        (((C ◁ Over.overSpecMap φ).left).base z)) = 1
    rw [h2]
    exact map_one _
  refine Units.ext ?_
  have hval0 : ((pointTransitionEquations C φ hx').presentation.elem z :
      (C ⊗ overSpec k K₂).left.functionField)
      = ((C ⊗ overSpec k K₂).left.presheaf.germ
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ
            (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')).cover.opens
              (((C ◁ Over.overSpecMap φ).left).base z))
          (genericPoint (C ⊗ overSpec k K₂).left) hηy).hom
        (Scheme.LocalEquations.pullbackEqn (C ◁ Over.overSpecMap φ).left
          (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')) z) := rfl
  rw [hval0, h1, Units.val_one]
  exact map_one _

/-- On the fiber of `x'`, the trivializing element of the pulled point presentation is the
pulled-back uniformizer `π^♯(t)` (worksheet §2 step 4, the fiber coefficient). -/
lemma pointTransitionEquations_presentation_elem_of_eq (φ : K₁ →ₐ[k] K₂)
    {x' : (C ⊗ overSpec k K₁).left}
    (hx' : x' ≠ genericPoint (C ⊗ overSpec k K₁).left) {z : (C ⊗ overSpec k K₂).left}
    (hz : ((C ◁ Over.overSpecMap φ).left).base z = x') :
    (pointTransitionEquations C φ hx').presentation.elem z
      = pointTransitionUnit C φ hx' := by
  have hηy : genericPoint (C ⊗ overSpec k K₂).left
      ∈ (C ◁ Over.overSpecMap φ).left ⁻¹ᵁ
        (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')).cover.opens
          (((C ◁ Over.overSpecMap φ).left).base z) := by
    change ((C ◁ Over.overSpecMap φ).left).base (genericPoint (C ⊗ overSpec k K₂).left)
      ∈ (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')).cover.opens
        (((C ◁ Over.overSpecMap φ).left).base z)
    rw [baseFieldTransition_genericPoint C φ]
    exact (Scheme.pointEquations K₁ hx'
      (Scheme.pointUniformizerData K₁ hx')).cover.genericPoint_mem_opens _
  refine Units.ext ?_
  have hval0 : ((pointTransitionEquations C φ hx').presentation.elem z :
      (C ⊗ overSpec k K₂).left.functionField)
      = ((C ⊗ overSpec k K₂).left.presheaf.germ
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ
            (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')).cover.opens
              (((C ◁ Over.overSpecMap φ).left).base z))
          (genericPoint (C ⊗ overSpec k K₂).left) hηy).hom
        (Scheme.LocalEquations.pullbackEqn (C ◁ Over.overSpecMap φ).left
          (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')) z) := rfl
  have happ : Scheme.LocalEquations.pullbackEqn (C ◁ Over.overSpecMap φ).left
      (Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')) z
      = ((C ◁ Over.overSpecMap φ).left.app _).hom
        ((Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')).eqn
          (((C ◁ Over.overSpecMap φ).left).base z)) :=
    congr($(Scheme.Hom.appLE_eq_app (C ◁ Over.overSpecMap φ).left).hom
      ((Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')).eqn
        (((C ◁ Over.overSpecMap φ).left).base z)))
  rw [hval0, coe_pointTransitionUnit, happ,
    ← (C ◁ Over.overSpecMap φ).left.functionFieldMap_germ
      (baseFieldTransition_genericPoint C φ) _
      ((Scheme.pointEquations K₁ hx'
        (Scheme.pointUniformizerData K₁ hx')).cover.genericPoint_mem_opens _) hηy
      ((Scheme.pointEquations K₁ hx' (Scheme.pointUniformizerData K₁ hx')).eqn
        (((C ◁ Over.overSpecMap φ).left).base z))]
  exact congrArg _ (germGeneric_pointEqn_of_eq C hx' (Scheme.pointUniformizerData K₁ hx')
    hz _)

/-! ## Order at a non-unit point (file-local copy of the deg-D1 lemma) -/

/-- If a section over an open containing `η` is not a unit at a closed point `z` of the
open, then its germ at `η` has nontrivial order at `z` (file-local restatement of the
private deg-D1 lemma, through the germ/stalk seam of `DivisorSheafZero`). -/
private lemma ord_ne_one_of_not_isUnit_germ {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X] {z : X}
    (hz : z ≠ genericPoint X) {U : X.Opens} (s : Γ(X, U)) (hη : genericPoint X ∈ U)
    (hzU : z ∈ U) (hnu : ¬ IsUnit ((X.presheaf.germ U z hzU).hom s)) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
      ((X.presheaf.germ U (genericPoint X) hη).hom s) ≠ 1 := by
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hz
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hz
  have hgs : (X.presheaf.germ U (genericPoint X) hη).hom s
      = algebraMap (X.presheaf.stalk z) X.functionField
        ((X.presheaf.germ U z hzU).hom s) :=
    Scheme.germ_generic_eq_algebraMap_germ hη hzU s
  have hord : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
      = (stalkHeightOne X z).valuation X.functionField := rfl
  rw [hgs, ne_eq, hord, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro h
  exact hnu (IsLocalRing.notMem_maximalIdeal.mp h)

/-! ## The degree of the pulled point divisor -/

/-- **The pulled point divisor has the degree of the point** (worksheet §2 steps 4–5 + (†)):
the divisor of the presentation of the pulled tracked point system has `K₂`-degree equal to
the residue degree of `x'` over `K₁`.  The support bookkeeping: the divisor is supported in
the fiber `π⁻¹(x')` with coefficients `ord(π^♯ t)`, and the fiber-degree identity (†) sums
them to `[κ(x') : K₁]`. -/
private theorem deg_presentationDivisor_pointTransition (φ : K₁ →ₐ[k] K₂)
    {x' : (C ⊗ overSpec k K₁).left}
    (hx' : x' ≠ genericPoint (C ⊗ overSpec k K₁).left) :
    Scheme.CurveDivisor.deg K₂ (Scheme.presentationDivisor K₂
        (pointTransitionEquations C φ hx').presentation)
      = ((C ⊗ overSpec k K₁).left.residueDeg K₁ x' : ℤ) := by
  classical
  have hπη : ((C ◁ Over.overSpecMap φ).left).base
        (genericPoint (C ⊗ overSpec k K₂).left)
      = genericPoint (C ⊗ overSpec k K₁).left := baseFieldTransition_genericPoint C φ
  set d := Scheme.pointUniformizerData K₁ hx' with hd
  -- the affine sub-chart of the tracked neighbourhood
  obtain ⟨V, hVaff, hx'V, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (C ⊗ overSpec k K₁).left.isBasis_affineOpens d.mem
  have hηV : genericPoint (C ⊗ overSpec k K₁).left ∈ V :=
    Scheme.genericPoint_mem_of_nonempty ⟨x', hx'V⟩
  -- the restricted tracked section and its unit
  set t := ((C ⊗ overSpec k K₁).left.presheaf.map (homOfLE hVle).op).hom d.sec with ht
  set g₁ : (C ⊗ overSpec k K₁).left.functionFieldˣ :=
    Units.mk0 (uniformizer K₁ hx') (uniformizer_ne_zero K₁ hx') with hg₁def
  have hgu : ((C ⊗ overSpec k K₁).left.presheaf.germ V
        (genericPoint (C ⊗ overSpec k K₁).left) hηV).hom t = uniformizer K₁ hx' := by
    rw [ht, (C ⊗ overSpec k K₁).left.presheaf.germ_res_apply (homOfLE hVle) _ hηV d.sec]
    exact d.germ_generic
  have hgt : (g₁ : (C ⊗ overSpec k K₁).left.functionField)
      = ((C ⊗ overSpec k K₁).left.presheaf.germ V
          (genericPoint (C ⊗ overSpec k K₁).left) hηV).hom t := hgu.symm
  have hunit : ∀ (z : (C ⊗ overSpec k K₁).left) (hz : z ∈ V), z ≠ x' →
      IsUnit (((C ⊗ overSpec k K₁).left.presheaf.germ V z hz).hom t) := by
    intro z hz hzx
    rw [ht, (C ⊗ overSpec k K₁).left.presheaf.germ_res_apply (homOfLE hVle) z hz d.sec]
    exact d.isUnit_germ z (hVle hz) hzx
  -- the coefficient description of the pulled divisor
  have hcoeff : ∀ (z : (C ⊗ overSpec k K₂).left)
      (hz : z ≠ genericPoint (C ⊗ overSpec k K₂).left),
      coeffAt hz (Scheme.presentationDivisor K₂
          (pointTransitionEquations C φ hx').presentation)
        = Multiplicative.toAdd
          (Scheme.ordZ ((C ⊗ overSpec k K₂).left ↘ Spec (CommRingCat.of K₂)) hz
            ((pointTransitionEquations C φ hx').presentation.elem z)) :=
    fun z hz => Scheme.coeffAt_presentationDivisor K₂ _ hz
  have hzero : ∀ (z : (C ⊗ overSpec k K₂).left)
      (hz : z ≠ genericPoint (C ⊗ overSpec k K₂).left),
      ((C ◁ Over.overSpecMap φ).left).base z ≠ x' →
      coeffAt hz (Scheme.presentationDivisor K₂
        (pointTransitionEquations C φ hx').presentation) = 0 := by
    intro z hz hne
    rw [hcoeff z hz, pointTransitionEquations_presentation_elem_of_ne C φ hx' hne,
      map_one, toAdd_one]
  -- the support is contained in the fiber over `x'`
  have hSfiber : ∀ p ∈ (toFinsupp (Scheme.presentationDivisor K₂
      (pointTransitionEquations C φ hx').presentation)).support,
      ((C ◁ Over.overSpecMap φ).left).base p.1 = x' := by
    intro p hp
    by_contra hne
    rw [Finsupp.mem_support_iff] at hp
    exact hp (hzero p.1 p.2 hne)
  have hSV : ∀ p ∈ (toFinsupp (Scheme.presentationDivisor K₂
      (pointTransitionEquations C φ hx').presentation)).support,
      p.1 ∈ (C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V := by
    intro p hp
    change ((C ◁ Over.overSpecMap φ).left).base p.1 ∈ V
    rw [hSfiber p hp]
    exact hx'V
  have hη₂ : genericPoint (C ⊗ overSpec k K₂).left
      ∈ (C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V := by
    change ((C ◁ Over.overSpecMap φ).left).base (genericPoint (C ⊗ overSpec k K₂).left) ∈ V
    rw [hπη]
    exact hηV
  -- the value of the pulled section at `η₂` is the pulled uniformizer
  have hg₂v : (((C ⊗ overSpec k K₂).left.presheaf.germ
        ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V)
        (genericPoint (C ⊗ overSpec k K₂).left) hη₂).hom
        (((C ◁ Over.overSpecMap φ).left.appLE V
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) le_rfl).hom t))
      = (pointTransitionUnit C φ hx' : (C ⊗ overSpec k K₂).left.functionField) := by
    have happ : (((C ◁ Over.overSpecMap φ).left.appLE V
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) le_rfl).hom t)
        = (((C ◁ Over.overSpecMap φ).left.app V).hom t) :=
      congr($(Scheme.Hom.appLE_eq_app (C ◁ Over.overSpecMap φ).left).hom t)
    rw [coe_pointTransitionUnit, happ,
      ← (C ◁ Over.overSpecMap φ).left.functionFieldMap_germ hπη V hηV hη₂ t]
    exact congrArg _ hgu
  -- the unit-outside hypothesis for (†) at the support
  have hout : ∀ (z : (C ⊗ overSpec k K₂).left)
      (hz : z ∈ (C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V)
      (hzg : z ≠ genericPoint (C ⊗ overSpec k K₂).left),
      (⟨z, hzg⟩ : {y : (C ⊗ overSpec k K₂).left //
          y ≠ genericPoint (C ⊗ overSpec k K₂).left})
        ∉ (toFinsupp (Scheme.presentationDivisor K₂
          (pointTransitionEquations C φ hx').presentation)).support →
      IsUnit (((C ⊗ overSpec k K₂).left.presheaf.germ
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) z hz).hom
        (((C ◁ Over.overSpecMap φ).left.appLE V
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) le_rfl).hom t)) := by
    intro z hz hzg hzS
    have hzV : ((C ◁ Over.overSpecMap φ).left).base z ∈ V := hz
    have happ : (((C ◁ Over.overSpecMap φ).left.appLE V
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) le_rfl).hom t)
        = (((C ◁ Over.overSpecMap φ).left.app V).hom t) :=
      congr($(Scheme.Hom.appLE_eq_app (C ◁ Over.overSpecMap φ).left).hom t)
    by_cases hfib : ((C ◁ Over.overSpecMap φ).left).base z = x'
    · -- fiber case: outside the support the order is trivial, hence the germ is a unit
      by_contra hnu
      have hord := ord_ne_one_of_not_isUnit_germ (K := K₂) hzg
        (((C ◁ Over.overSpecMap φ).left.appLE V
          ((C ◁ Over.overSpecMap φ).left ⁻¹ᵁ V) le_rfl).hom t) hη₂ hz hnu
      have hordZ : Scheme.ordZ ((C ⊗ overSpec k K₂).left ↘ Spec (CommRingCat.of K₂)) hzg
          (pointTransitionUnit C φ hx') ≠ 1 := by
        rw [ne_eq, Scheme.ordZ_eq_one_iff, ← hg₂v]
        exact hord
      apply hzS
      rw [Finsupp.mem_support_iff]
      change coeffAt hzg (Scheme.presentationDivisor K₂
        (pointTransitionEquations C φ hx').presentation) ≠ 0
      rw [hcoeff z hzg, pointTransitionEquations_presentation_elem_of_eq C φ hx' hfib]
      exact fun h0 => hordZ (toAdd_eq_zero.mp h0)
    · -- off the fiber: the tracked section is a unit there, and unit germs pull back
      rw [happ, ← (C ◁ Over.overSpecMap φ).left.germ_stalkMap_apply V z hzV t]
      exact ((hunit _ hzV hfib).map ((C ◁ Over.overSpecMap φ).left.stalkMap z).hom)
  -- the degree as the fiber sum
  have hdeg : Scheme.CurveDivisor.deg K₂ (Scheme.presentationDivisor K₂
      (pointTransitionEquations C φ hx').presentation)
      = ∑ p ∈ (toFinsupp (Scheme.presentationDivisor K₂
          (pointTransitionEquations C φ hx').presentation)).support,
        Multiplicative.toAdd
          (Scheme.ordZ ((C ⊗ overSpec k K₂).left ↘ Spec (CommRingCat.of K₂)) p.2
            (pointTransitionUnit C φ hx'))
          * ((C ⊗ overSpec k K₂).left.residueDeg K₂ p.1 : ℤ) := by
    change ∑ p ∈ (toFinsupp (Scheme.presentationDivisor K₂
        (pointTransitionEquations C φ hx').presentation)).support,
      (toFinsupp (Scheme.presentationDivisor K₂
        (pointTransitionEquations C φ hx').presentation)) p
        * ((C ⊗ overSpec k K₂).left.residueDeg K₂ p.1 : ℤ) = _
    refine Finset.sum_congr rfl fun p hp => ?_
    have hcp : (toFinsupp (Scheme.presentationDivisor K₂
        (pointTransitionEquations C φ hx').presentation)) p
        = coeffAt p.2 (Scheme.presentationDivisor K₂
          (pointTransitionEquations C φ hx').presentation) := rfl
    rw [hcp, hcoeff p.1 p.2,
      pointTransitionEquations_presentation_elem_of_eq C φ hx' (hSfiber p hp)]
  rw [hdeg]
  -- close by the fiber-degree identity (†) and `ord(uniformizer) = 1`
  have hdagger := sum_ordZ_residueDeg_baseFieldTransition C φ hVaff hηV g₁ hgt hx' hx'V
    hunit
    ((toFinsupp (Scheme.presentationDivisor K₂
      (pointTransitionEquations C φ hx').presentation)).support) hSV hout
  have hunit_eq : pointTransitionUnit C φ hx'
      = (C ◁ Over.overSpecMap φ).left.functionFieldMapUnits
        (baseFieldTransition_genericPoint C φ) g₁ := rfl
  rw [hunit_eq, hdagger,
    Scheme.ordZ_eq_ofAdd_one_of_val_eq_uniformizer K₁ hx' (g := g₁) rfl, toAdd_ofAdd,
    one_mul]

/-! ## E-iv-alg -/

/-- The single-point case of E-iv-alg: the transition preserves the degree of the class of
a one-point divisor. -/
private theorem classDeg_cechPicMap_picClass_single (φ : K₁ →ₐ[k] K₂)
    {x' : (C ⊗ overSpec k K₁).left}
    (hx' : x' ≠ genericPoint (C ⊗ overSpec k K₁).left) :
    classDeg K₂ (Scheme.CechPic.map ((C ◁ Over.overSpecMap φ).left)
        (Scheme.CurveDivisor.picClass K₁ (Scheme.CurveDivisor.single hx' 1)))
      = classDeg K₁ (Scheme.CurveDivisor.picClass K₁
          (Scheme.CurveDivisor.single hx' 1)) := by
  have h1 : Scheme.CechPic.map ((C ◁ Over.overSpecMap φ).left)
      (Scheme.CurveDivisor.picClass K₁ (Scheme.CurveDivisor.single hx' 1))
      = (pointTransitionEquations C φ hx').picClass := by
    rw [Scheme.CurveDivisor.picClass_single K₁ hx']
    exact (Scheme.LocalEquations.picClass_pullback _ _ _).symm
  have h2 : (pointTransitionEquations C φ hx').picClass
      = Scheme.CurveDivisor.picClass K₂ (Scheme.presentationDivisor K₂
          (pointTransitionEquations C φ hx').presentation) := by
    rw [Scheme.CurveDivisor.picClass_presentationDivisor,
      Scheme.LocalEquations.presentation_picClass]
  rw [h1, h2, classDeg_picClass, classDeg_picClass,
    deg_presentationDivisor_pointTransition C φ hx',
    Scheme.CurveDivisor.deg_single' K₁ hx' 1, one_mul]

/-- **E-iv-alg** (worksheet §2, the keystone): the degree of a Čech Picard class of the
base-changed curve is invariant under base-field transition — for every `k`-algebra map
`φ : K₁ →ₐ[k] K₂` of field extensions and every class `L` on `C_{K₁}`,

`classDeg K₂ (CechPic.map π L) = classDeg K₁ L`,

where `π := (C ◁ Over.overSpecMap φ).left`.  Proved by the §2 ladder: reduce along the
surjective additive class map `CurveDivisor.picClass K₁` to one-point divisors, present the
point class by the tracked point equations, pull the presentation back along `π`, and close
with the fiber-degree identity (†). -/
theorem classDeg_cechPicMap_baseFieldTransition (φ : K₁ →ₐ[k] K₂)
    (L : (C ⊗ overSpec k K₁).left.CechPic) :
    classDeg K₂ (Scheme.CechPic.map ((C ◁ Over.overSpecMap φ).left) L) = classDeg K₁ L := by
  obtain ⟨D, rfl⟩ := Scheme.CurveDivisor.exists_picClass_eq K₁ L
  suffices h : ∀ f : {p : (C ⊗ overSpec k K₁).left //
      p ≠ genericPoint (C ⊗ overSpec k K₁).left} →₀ ℤ,
      classDeg K₂ (Scheme.CechPic.map ((C ◁ Over.overSpecMap φ).left)
        (Scheme.CurveDivisor.picClass K₁ f))
        = classDeg K₁ (Scheme.CurveDivisor.picClass K₁ f) from h D
  intro f
  induction f using Finsupp.induction with
  | zero =>
    change classDeg K₂ (Scheme.CechPic.map ((C ◁ Over.overSpecMap φ).left)
      (Scheme.CurveDivisor.picClass K₁ (0 : (C ⊗ overSpec k K₁).left.CurveDivisor)))
      = classDeg K₁ (Scheme.CurveDivisor.picClass K₁
        (0 : (C ⊗ overSpec k K₁).left.CurveDivisor))
    rw [Scheme.CurveDivisor.picClass_zero, map_one, classDeg_one, classDeg_one]
  | single_add p b f hpf hb ih =>
    have key : ∀ D : (C ⊗ overSpec k K₁).left.CurveDivisor,
        classDeg K₂ (Scheme.CechPic.map ((C ◁ Over.overSpecMap φ).left)
          (Scheme.CurveDivisor.picClass K₁ D))
          = classDeg K₁ (Scheme.CurveDivisor.picClass K₁ D) →
        classDeg K₂ (Scheme.CechPic.map ((C ◁ Over.overSpecMap φ).left)
          (Scheme.CurveDivisor.picClass K₁ (Scheme.CurveDivisor.single p.2 b + D)))
          = classDeg K₁ (Scheme.CurveDivisor.picClass K₁
            (Scheme.CurveDivisor.single p.2 b + D)) := by
      intro D hD
      rw [Scheme.CurveDivisor.picClass_add, ← Scheme.picClass_single_zpow K₁ p.2 b,
        map_mul, map_zpow, classDeg_mul, classDeg_mul, classDeg_zpow, classDeg_zpow, hD,
        classDeg_cechPicMap_picClass_single C φ p.2]
    exact key f ih

end AlgebraicGeometry
