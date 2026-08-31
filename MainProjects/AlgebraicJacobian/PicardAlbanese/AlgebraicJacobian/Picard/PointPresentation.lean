/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PresentationCalculus

/-!
# The point presentation: local equations of `1 · x` with a tracked uniformizer

For the curve bundle `X` (integral, smooth of relative dimension one and quasi-compact
over a field `K`) and a closed point `x`, this file builds a local-equation system for
the effective divisor `1 · x` whose defining data is *publicly tracked*: the equation at
`x` is a spread-out uniformizer of `𝒪_{X,x}` whose germ at `η` is recorded to be
`uniformizer K hx`. This anchors the divisor of the associated meromorphic presentation:
`presentationDivisor K (pointEquations K hx d).presentation = CurveDivisor.single hx 1`.

The geometric construction is that of `AlgebraicJacobian.Picard.PointDivisor`
(deg-D1): a uniformizer is integral at `x`, hence spreads to a section over a
neighbourhood; removing its finitely many other zeros leaves an open on which it
vanishes only at `x`; the pointed cover `{V, {x}ᶜ}` carries the equations
`(spread uniformizer, 1)`. The deg-D1 constructor `Scheme.pointDivisor` seals this data
behind an existential that does not record the germ at `η` (nor even that the section
vanishes at `x`), so no property of its divisor is derivable from its public interface;
the present file re-runs the construction keeping the specification
(`Scheme.PointUniformizerData`) public. See the deviation note in the campaign report.

## Main declarations

* `AlgebraicGeometry.Scheme.PointUniformizerData`: an open `V ∋ x` with a regular
  section whose germ at `η` is `uniformizer K hx` and which is a unit away from `x`;
  `nonempty_pointUniformizerData` (the geometry) and `pointUniformizerData` (a choice).
* `AlgebraicGeometry.Scheme.pointCover`, `Scheme.pointEqn`,
  `Scheme.pointEquations`: the pointed cover `{V, {x}ᶜ}`, its equations, and the
  resulting `LocalEquations`, with public accessor lemmas (`germGeneric_pointEqn_self`,
  `pointEqn_of_ne`).
* `AlgebraicGeometry.Scheme.presentationDivisor_pointEquations`: the divisor of the
  associated meromorphic presentation is `CurveDivisor.single hx 1`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  {x : X} (hx : x ≠ genericPoint X)

/-! ## The tracked uniformizer section -/

/-- **A tracked point-uniformizer.** An open neighbourhood of the closed point `x`
carrying a regular section whose germ at the generic point is the chosen uniformizer
`uniformizer K hx` and whose germ at every other point of the neighbourhood is a unit.
This is the public form of the data underlying the point divisor `1 · x`: unlike an
existential, it lets consumers read off the orders of the section — `+1` at `x`
(a uniformizer), `0` elsewhere on the neighbourhood. -/
structure PointUniformizerData : Type u where
  /-- The neighbourhood of `x` carrying the spread-out uniformizer. -/
  opens : X.Opens
  /-- The point `x` lies in the neighbourhood. -/
  mem : x ∈ opens
  /-- The spread-out uniformizer. -/
  sec : Γ(X, opens)
  /-- The germ of the section at the generic point is the chosen uniformizer. -/
  germ_generic :
    (X.presheaf.germ opens (genericPoint X)
      (genericPoint_mem_of_nonempty ⟨x, mem⟩)).hom sec = uniformizer K hx
  /-- The section is regular: its germs are nonzerodivisors. -/
  regular : ∀ (y : X) (hy : y ∈ opens),
    (X.presheaf.germ opens y hy).hom sec ∈ nonZeroDivisors (X.presheaf.stalk y)
  /-- Away from `x`, the section is a unit. -/
  isUnit_germ : ∀ (y : X) (hy : y ∈ opens), y ≠ x →
    IsUnit ((X.presheaf.germ opens y hy).hom sec)

/-- **Order `≠ 1` at a zero of a section.** If a section over an open containing `η` and
a closed point `z` is not a unit at `z`, then its germ at `η` has nontrivial order at
`z`. Contrapositive of `Scheme.ord_eq_one_of_mem_basicOpen`. (A private copy of the
deg-D1 lemma of the same name, which is not exported.) -/
private lemma ord_ne_one_of_notMem_basicOpen {z : X} (hz : z ≠ genericPoint X)
    {U : X.Opens} (s : Γ(X, U)) (hη : genericPoint X ∈ U) (hzU : z ∈ U)
    (hzs : z ∉ X.basicOpen s) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
        ((X.presheaf.germ U (genericPoint X) hη).hom s) ≠ 1 := by
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hz
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hz
  have hnu : ¬ IsUnit ((X.presheaf.germ U z hzU).hom s) :=
    fun h => hzs ((X.mem_basicOpen s z hzU).mpr h)
  have hgs : (X.presheaf.germ U (genericPoint X) hη).hom s
      = algebraMap (X.presheaf.stalk z) X.functionField ((X.presheaf.germ U z hzU).hom s) :=
    germ_generic_eq_algebraMap_germ hη hzU s
  have hord : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hz
      = (stalkHeightOne X z).valuation X.functionField := rfl
  rw [hgs, ne_eq, hord, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro h
  exact hnu (IsLocalRing.notMem_maximalIdeal.mp h)

/-- **Existence of a tracked point-uniformizer** (the deg-D1 geometry, with the germ at
`η` kept in the specification): the chosen uniformizer at `x` is integral at `x`, hence
the germ of a section `s₀` on a neighbourhood; removing the finitely many other closed
points where the uniformizer has a zero or pole leaves an open neighbourhood on which
the restriction of `s₀` is regular, has germ `uniformizer K hx` at `η`, and is a unit
away from `x`. -/
theorem nonempty_pointUniformizerData [QuasiCompact (X ↘ Spec (CommRingCat.of K))] :
    Nonempty (PointUniformizerData K hx) := by
  set f := X ↘ Spec (CommRingCat.of K) with hf
  -- the uniformizer, as a nonzero rational function
  have ht0 : uniformizer K hx ≠ 0 := uniformizer_ne_zero K hx
  set tu : X.functionFieldˣ := Units.mk0 (uniformizer K hx) ht0 with htu
  have htuv : (tu : X.functionField) = uniformizer K hx := rfl
  -- the uniformizer is integral at `x`, hence a germ of a section near `x`
  have hord_le : Scheme.ord f hx (uniformizer K hx) ≤ 1 := by
    rw [ord_uniformizer K hx]
    rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num
  obtain ⟨y_st, hy_st⟩ := exists_stalk_of_ord_le_one K hx hord_le
  obtain ⟨W₀, hxW₀, s₀, hs₀⟩ := X.presheaf.exists_germ_eq (x := x) y_st
  have hηW₀ : genericPoint X ∈ W₀ := genericPoint_mem_of_nonempty ⟨x, hxW₀⟩
  have hgη : (X.presheaf.germ W₀ (genericPoint X) hηW₀).hom s₀ = uniformizer K hx := by
    rw [germ_generic_eq_algebraMap_germ hηW₀ hxW₀ s₀, hs₀, hy_st]
  -- the finite closed set of other zeros/poles of the uniformizer
  have hSfin : {p : {q : X // q ≠ genericPoint X} | Scheme.ordZ f p.2 tu ≠ 1}.Finite :=
    Scheme.ordZ_support_finite f tu
  set bad : Set X :=
    (Subtype.val '' {p : {q : X // q ≠ genericPoint X} | Scheme.ordZ f p.2 tu ≠ 1}) \ {x}
    with hbad
  have hbad_fin : bad.Finite := (hSfin.image Subtype.val).sdiff
  have hbad_ne : ∀ p ∈ bad, p ≠ genericPoint X := by
    rintro p ⟨⟨q, _, rfl⟩, _⟩
    exact q.2
  have hbad_closed : IsClosed bad := by
    rw [← Set.biUnion_of_singleton bad]
    exact hbad_fin.isClosed_biUnion
      (fun p hp => isClosed_singleton_of_ne_genericPoint f (hbad_ne p hp))
  -- the neighbourhood with the other zeros removed
  set V : X.Opens := ⟨(W₀ : Set X) \ bad, W₀.2.sdiff hbad_closed⟩ with hV
  have hVW₀ : V ≤ W₀ := Set.sdiff_subset
  have hxV : x ∈ V := ⟨hxW₀, fun h => h.2 rfl⟩
  have hηV : genericPoint X ∈ V := genericPoint_mem_of_nonempty ⟨x, hxV⟩
  refine ⟨⟨V, hxV, (X.presheaf.map (homOfLE hVW₀).op).hom s₀, ?_, ?_, ?_⟩⟩
  · -- the germ at `η` is the uniformizer
    exact (X.presheaf.germ_res_apply (homOfLE hVW₀) (genericPoint X) hηV s₀).trans hgη
  · -- regularity: the germs are nonzero in the domain stalks
    intro y hy
    have hgalg : algebraMap (X.presheaf.stalk y) X.functionField
        ((X.presheaf.germ W₀ y (hVW₀ hy)).hom s₀) = uniformizer K hx :=
      (germ_generic_eq_algebraMap_germ hηW₀ (hVW₀ hy) s₀).symm.trans hgη
    rw [X.presheaf.germ_res_apply (homOfLE hVW₀) y hy s₀,
      mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    rw [hzero, map_zero] at hgalg
    exact ht0 hgalg.symm
  · -- unit away from `x`
    intro y hy hyx
    rw [X.presheaf.germ_res_apply (homOfLE hVW₀) y hy s₀]
    by_cases hyη : y = genericPoint X
    · subst hyη
      rw [show (X.presheaf.germ W₀ (genericPoint X) (hVW₀ hy)).hom s₀ = uniformizer K hx
        from hgη]
      exact isUnit_iff_ne_zero.mpr ht0
    · by_contra hnu
      have hybad : y ∈ bad := by
        refine ⟨⟨⟨y, hyη⟩, ?_, rfl⟩, ?_⟩
        · change Scheme.ordZ f hyη tu ≠ 1
          rw [ne_eq, Scheme.ordZ_eq_one_iff f hyη tu, htuv]
          intro hord1
          have hne := ord_ne_one_of_notMem_basicOpen K (z := y) hyη s₀ hηW₀ (hVW₀ hy)
            (fun h => hnu ((X.mem_basicOpen s₀ y (hVW₀ hy)).mp h))
          rw [hgη] at hne
          exact hne hord1
        · exact hyx
      exact hy.2 hybad

/-- A chosen tracked point-uniformizer at the closed point `x`. -/
noncomputable def pointUniformizerData [QuasiCompact (X ↘ Spec (CommRingCat.of K))] :
    PointUniformizerData K hx :=
  (nonempty_pointUniformizerData K hx).some

/-! ## The point cover and its equations -/

/-- The complement of the closed point `x`, as an open of `X`. -/
def pointCompl : X.Opens :=
  ⟨({x} : Set X)ᶜ,
    (isClosed_singleton_of_ne_genericPoint (X ↘ Spec (CommRingCat.of K)) hx).isOpen_compl⟩

lemma mem_pointCompl {z : X} : z ∈ pointCompl K hx ↔ z ≠ x :=
  Iff.rfl

open Classical in
/-- The pointed cover `{V, {x}ᶜ}` of the point divisor at `x`: the piece at `x` is the
neighbourhood of the tracked uniformizer, every other piece is the complement of `x`. -/
noncomputable def pointCover (d : PointUniformizerData K hx) : X.PointedCover where
  opens z := if z = x then d.opens else pointCompl K hx
  mem_opens z := by
    by_cases h : z = x
    · rw [if_pos h]; subst h; exact d.mem
    · rw [if_neg h]; exact h

@[simp]
lemma pointCover_opens_self (d : PointUniformizerData K hx) :
    (pointCover K hx d).opens x = d.opens :=
  if_pos rfl

lemma pointCover_opens_of_ne (d : PointUniformizerData K hx) {z : X} (hz : z ≠ x) :
    (pointCover K hx d).opens z = pointCompl K hx :=
  if_neg hz

open Classical in
/-- The equations of the point divisor at `x`: the tracked uniformizer section on the
piece at `x`, the constant `1` on every other piece. -/
noncomputable def pointEqn (d : PointUniformizerData K hx) (z : X) :
    Γ(X, (pointCover K hx d).opens z) :=
  if h : z = x then
    (X.presheaf.map (homOfLE (le_of_eq (by rw [h, pointCover_opens_self]))).op).hom d.sec
  else 1

lemma pointEqn_self (d : PointUniformizerData K hx) :
    pointEqn K hx d x
      = (X.presheaf.map
          (homOfLE (pointCover_opens_self K hx d).le).op).hom d.sec :=
  dif_pos rfl

lemma pointEqn_of_ne (d : PointUniformizerData K hx) {z : X} (hz : z ≠ x) :
    pointEqn K hx d z = 1 :=
  dif_neg hz

/-- The germ at the generic point of the equation at `x` is the chosen uniformizer. -/
theorem germGeneric_pointEqn_self (d : PointUniformizerData K hx)
    (hη : genericPoint X ∈ (pointCover K hx d).opens x) :
    (X.presheaf.germ ((pointCover K hx d).opens x) (genericPoint X) hη).hom
        (pointEqn K hx d x)
      = uniformizer K hx := by
  rw [pointEqn_self, X.presheaf.germ_res_apply]
  exact d.germ_generic

/-! ## The local-equation system of the point divisor -/

omit [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X] hx in
/-- Restriction of sections composes (a local copy of the `DivisorClass` helper). -/
private lemma map_map_sec {W V U : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s)
      = (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- **The local-equation system of the point divisor `1 · x`**, built from a tracked
point-uniformizer: on the piece at `x` the equation is the tracked uniformizer section,
elsewhere it is `1`. Unlike the deg-D1 `Scheme.pointDivisor`, all defining data is
publicly accessible (`pointEqn_self`, `pointEqn_of_ne`, `germGeneric_pointEqn_self`). -/
noncomputable def pointEquations (d : PointUniformizerData K hx) : X.LocalEquations where
  cover := pointCover K hx d
  eqn := pointEqn K hx d
  regular := by
    intro x' y hy
    by_cases h : x' = x
    · subst h
      rw [pointEqn_self, X.presheaf.germ_res_apply]
      exact d.regular y _
    · rw [pointEqn_of_ne K hx d h, map_one]
      exact one_mem _
  ratio_isUnit := by
    intro x' y'
    by_cases h : x' = x <;> by_cases h' : y' = x
    · -- both pieces at `x`: the ratio is `1`
      subst h; subst h'
      refine ⟨1, ?_⟩
      rw [Units.val_one, one_mul]
    · -- piece at `x` against a piece away from `x`: the ratio is the unit section
      subst h
      have hle : (pointCover K hx d).opens x' ⊓ (pointCover K hx d).opens y' ≤ d.opens :=
        le_trans inf_le_left (pointCover_opens_self K hx d).le
      have hne : ∀ z ∈ (pointCover K hx d).opens x' ⊓ (pointCover K hx d).opens y',
          z ≠ x' := by
        intro z hz
        have h2 : z ∈ (pointCover K hx d).opens y' := hz.2
        rw [pointCover_opens_of_ne K hx d h'] at h2
        exact h2
      have hunit : IsUnit ((X.presheaf.map (homOfLE hle).op).hom d.sec) := by
        apply X.toRingedSpace.isUnit_of_isUnit_germ
        intro z hz
        rw [X.presheaf.germ_res_apply]
        exact d.isUnit_germ z (hle hz) (hne z hz)
      refine ⟨hunit.unit, ?_⟩
      rw [pointEqn_of_ne K hx d h', map_one, mul_one, IsUnit.unit_spec, pointEqn_self,
        map_map_sec]
    · -- piece away from `x` against the piece at `x`: the inverse unit
      subst h'
      have hle : (pointCover K hx d).opens x' ⊓ (pointCover K hx d).opens y' ≤ d.opens :=
        le_trans inf_le_right (pointCover_opens_self K hx d).le
      have hne : ∀ z ∈ (pointCover K hx d).opens x' ⊓ (pointCover K hx d).opens y',
          z ≠ y' := by
        intro z hz
        have h1 : z ∈ (pointCover K hx d).opens x' := hz.1
        rw [pointCover_opens_of_ne K hx d h] at h1
        exact h1
      have hunit : IsUnit ((X.presheaf.map (homOfLE hle).op).hom d.sec) := by
        apply X.toRingedSpace.isUnit_of_isUnit_germ
        intro z hz
        rw [X.presheaf.germ_res_apply]
        exact d.isUnit_germ z (hle hz) (hne z hz)
      refine ⟨hunit.unit⁻¹, ?_⟩
      rw [pointEqn_of_ne K hx d h, map_one, pointEqn_self, map_map_sec]
      exact (Units.inv_mul_of_eq hunit.unit_spec).symm
    · -- both pieces away from `x`: the ratio is `1`
      refine ⟨1, ?_⟩
      rw [pointEqn_of_ne K hx d h, pointEqn_of_ne K hx d h', map_one, map_one,
        Units.val_one, mul_one]

@[simp]
lemma pointEquations_cover (d : PointUniformizerData K hx) :
    (pointEquations K hx d).cover = pointCover K hx d :=
  rfl

@[simp]
lemma pointEquations_eqn (d : PointUniformizerData K hx) (z : X) :
    (pointEquations K hx d).eqn z = pointEqn K hx d z :=
  rfl

/-! ## The divisor of the point presentation -/

/-- A unit of `K(X)` whose underlying rational function is the chosen uniformizer at `x`
has order `+1` there (recall the classical sign convention of `Scheme.ordZ`). -/
lemma ordZ_eq_ofAdd_one_of_val_eq_uniformizer {g : X.functionFieldˣ}
    (hg : (g : X.functionField) = uniformizer K hx) :
    Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx g = Multiplicative.ofAdd (1 : ℤ) := by
  have h1 : (((Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx g)⁻¹ : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ))
      = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [coe_inv_ordZ K g hx, hg, ord_uniformizer K hx]
  have h2 := congrArg Inv.inv (WithZero.coe_inj.mp h1)
  rw [inv_inv, ofAdd_neg, inv_inv] at h2
  exact h2

/-- **The divisor of the point presentation is `1 · x`** (the anchor of the meromorphic
bridge): the presentation of the tracked point local equations cuts out exactly the
one-point divisor. At `x` the trivializing element is the uniformizer (order `+1`); on
every other piece it is `1` (order `0`). -/
theorem presentationDivisor_pointEquations
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] (d : PointUniformizerData K hx) :
    presentationDivisor K (pointEquations K hx d).presentation
      = CurveDivisor.single hx 1 := by
  refine CurveDivisor.ext_coeffAt fun z hz => ?_
  rw [coeffAt_presentationDivisor]
  by_cases h : z = x
  · subst h
    have hval : ((pointEquations K hx d).presentation.elem z : X.functionField)
        = uniformizer K hx := by
      rw [LocalEquations.presentation_elem_val]
      exact germGeneric_pointEqn_self K hx d _
    rw [ordZ_eq_ofAdd_one_of_val_eq_uniformizer K hx hval,
      CurveDivisor.coeffAt_single_self]
    rfl
  · have hval : (pointEquations K hx d).presentation.elem z = 1 := by
      refine Units.ext ?_
      rw [LocalEquations.presentation_elem_val, Units.val_one]
      change (X.presheaf.germ _ (genericPoint X) _).hom (pointEqn K hx d z) = 1
      rw [pointEqn_of_ne K hx d h, map_one]
    rw [hval, map_one, toAdd_one, CurveDivisor.coeffAt_single_of_ne hx hz h]

end Scheme

end AlgebraicGeometry
