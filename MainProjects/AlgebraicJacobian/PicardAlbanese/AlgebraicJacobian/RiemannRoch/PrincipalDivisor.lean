/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Divisor

/-!
# The principal divisor of a rational function on a curve

For a scheme `X` smooth of relative dimension one over a field `K` and integral (the curve
bundle of the Jacobian challenge), a nonzero rational function `g : K(X)ˣ` has a well-defined
**principal divisor** `div(g) = ∑ₓ ordₓ(g) · x`, a finitely supported `ℤ`-valued function on
the closed points:

* `AlgebraicGeometry.Scheme.ordZ`: the `ℤ`-valued order of a unit of the function field at a
  closed point, packaged as a group homomorphism `K(X)ˣ →* Multiplicative ℤ`;
* `AlgebraicGeometry.Scheme.divOf`: the principal divisor `div(g)`, whose value at a closed
  point `x` is the classical order `ordₓ(g)`, with additivity `divOf_mul` and `divOf_one`.

## Sign convention

Mathlib's `IsDedekindDomain.HeightOneSpectrum.intValuation` sends a local uniformizer `π` to
`WithZero.exp (-1) = ↑(Multiplicative.ofAdd (-1))`, i.e. the *additive* value of the valuation
of a uniformizer is `-1`.  The **classical order** used here is the negative of that additive
value: `ordZ` is defined as the inverse (in the multiplicative group `Multiplicative ℤ`) of the
units-extraction of `Scheme.ord`, so that

  `Multiplicative.toAdd (ordZ f hx π) = +1`   for `π` (the image of) a uniformizer,

a *zero* of `g` contributing a positive order and a *pole* a negative one.  Consequently
`divOf f g ⟨x, hx⟩ = Multiplicative.toAdd (ordZ f hx g)` is the classical order of vanishing.

## Finiteness

The support of `div(g)` is finite: represent `g` by a section `s` on a nonempty open `U` (the
generic point lies in every nonempty open); at every closed point of the basic open set
`X.basicOpen s` the germ of `s` is a unit, so `ordₓ(g) = 0` there.  The complement is a closed
set avoiding the generic point, hence finite on the Noetherian curve.  Finiteness of the
ambient space uses `[LocallyOfFiniteType f]` together with `[QuasiCompact f]`: a principal
divisor is only finitely supported on a quasi-compact (hence Noetherian) curve, and the proper
curve of the Jacobian challenge satisfies this.  (The bare `[LocallyOfFiniteType f]` gives only
`IsLocallyNoetherian X`, which does not force the *global* space to be Noetherian without
quasi-compactness.)
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- **The `ℤ`-valued order at a closed point.**  The order of a unit `g` of the function field
`K(X)` at a closed point `x`, as a group homomorphism `K(X)ˣ →* Multiplicative ℤ`.  With the
classical sign convention (see the module docstring): the units-extraction of the mathlib
valuation `Scheme.ord f hx` (whose additive value on a uniformizer is `-1`) is *inverted*, so
that the order of a uniformizer is `Multiplicative.ofAdd (1 : ℤ)`. -/
noncomputable def Scheme.ordZ (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X} (hx : x ≠ genericPoint X) :
    X.functionFieldˣ →* Multiplicative ℤ :=
  invMonoidHom.comp
    (WithZero.unitsWithZeroEquiv.toMonoidHom.comp
      (Units.map (Scheme.ord f hx).toMonoidWithZeroHom.toMonoidHom))

/-- The height-one prime of the DVR stalk at a closed point: its maximal ideal.  This is exactly
the prime whose adic valuation is `Scheme.ord` (see `Scheme.ord_eq_valuation`). -/
noncomputable def stalkHeightOne (X : Scheme.{u}) [IsIntegral X] (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    IsDedekindDomain.HeightOneSpectrum (X.presheaf.stalk x) where
  asIdeal := IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  isPrime := (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).isPrime
  ne_bot := IsDiscreteValuationRing.not_a_field (X.presheaf.stalk x)

/-- `Scheme.ord` is, by construction, the adic valuation of the maximal ideal of the stalk. -/
theorem Scheme.ord_eq_valuation (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X} (hx : x ≠ genericPoint X) :
    letI := isDiscreteValuationRing_stalk f hx
    Scheme.ord f hx = (stalkHeightOne X x).valuation X.functionField :=
  rfl

/-- **`ordₓ(g) = 0` where a representing section is a unit.**  If `s : Γ(X, U)` represents the
rational function `germ_η s` at the generic point and `x ∈ X.basicOpen s` (so the germ of `s` at
`x` is a unit of the stalk), then the order of `germ_η s` at `x` is trivial: `ord = 1`. -/
theorem Scheme.ord_eq_one_of_mem_basicOpen (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X} (hx : x ≠ genericPoint X)
    {U : X.Opens} (s : Γ(X, U)) (hη : genericPoint X ∈ U) (hx_mem : x ∈ X.basicOpen s) :
    Scheme.ord f hx ((X.presheaf.germ U (genericPoint X) hη).hom s) = 1 := by
  letI := isDiscreteValuationRing_stalk f hx
  letI := isDedekindDomain_stalk f hx
  have hxU : x ∈ U := X.basicOpen_le s hx_mem
  have hunit : IsUnit ((X.presheaf.germ U x hxU).hom s) := (X.mem_basicOpen s x hxU).mp hx_mem
  have hord : Scheme.ord f hx = (stalkHeightOne X x).valuation X.functionField := rfl
  have hgs : (X.presheaf.germ U (genericPoint X) hη).hom s
      = algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ U x hxU).hom s) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact (X.presheaf.germ_stalkSpecializes_apply
      hxU ((genericPoint_spec X).specializes trivial) s).symm
  rw [hgs, hord, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact IsLocalRing.notMem_maximalIdeal.mpr hunit

/-- `ordZ f hx g = 1` (trivial order) exactly when the mathlib valuation `Scheme.ord f hx` of
`g` is `1`: the units-extraction and inversion defining `ordZ` are injective homomorphisms. -/
theorem Scheme.ordZ_eq_one_iff (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {x : X} (hx : x ≠ genericPoint X)
    (g : X.functionFieldˣ) :
    Scheme.ordZ f hx g = 1 ↔ Scheme.ord f hx (g : X.functionField) = 1 := by
  rw [Scheme.ordZ]
  simp only [MonoidHom.comp_apply, invMonoidHom_apply, inv_eq_one,
    MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff, Units.ext_iff, Units.coe_map,
    Units.val_one]
  rfl

/-- **Finite support of the order.**  For a unit `g` of the function field, the closed points
where the order of `g` is nontrivial form a finite set: `g` is represented by a section `s` on a
nonempty open `U ∋ η`, and every closed point of `X.basicOpen s` has trivial order, so the
nontrivial locus lies in the closed set `(X.basicOpen s)ᶜ`, which avoids `η` and is finite on
the Noetherian curve. -/
theorem Scheme.ordZ_support_finite (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : X.functionFieldˣ) :
    {p : {x : X // x ≠ genericPoint X} | Scheme.ordZ f p.2 g ≠ 1}.Finite := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨U, hηU, s, hs⟩ := X.presheaf.exists_germ_eq (g : X.functionField)
  have hη_basic : genericPoint X ∈ X.basicOpen s := by
    rw [X.mem_basicOpen s (genericPoint X) hηU, hs]
    exact g.isUnit
  have hZ : ((X.basicOpen s : Set X)ᶜ).Finite := by
    refine Scheme.finite_of_isClosed_of_notMem_genericPoint
      (fun _ _ h => SmoothOfRelativeDimension.specializes_eq_genericPoint_or_eq f h)
      (X.basicOpen s).isOpen.isClosed_compl ?_
    simpa using hη_basic
  refine (hZ.preimage (Subtype.val_injective.injOn)).subset ?_
  intro p hp
  rw [Set.mem_preimage, Set.mem_compl_iff]
  intro hmem
  apply hp
  rw [Scheme.ordZ_eq_one_iff, ← hs]
  exact Scheme.ord_eq_one_of_mem_basicOpen f p.2 s hηU hmem

/-- **The principal divisor of a rational function.**  For a unit `g` of the function field
`K(X)`, `divOf f g = ∑ₓ ordₓ(g) · x` is the Weil divisor whose value at a closed point `x` is
the classical order of vanishing `ordₓ(g)` (positive at zeros, negative at poles); it is
finitely supported by `Scheme.ordZ_support_finite`. -/
noncomputable def Scheme.divOf (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : X.functionFieldˣ) : X.CurveDivisor :=
  Finsupp.onFinset (Scheme.ordZ_support_finite f g).toFinset
    (fun p => Multiplicative.toAdd (Scheme.ordZ f p.2 g))
    (fun p hp => by
      rw [Set.Finite.mem_toFinset]
      exact fun he => hp (by rw [he, toAdd_one]))

/-- **The value of the principal divisor at a closed point** is the classical order of vanishing
`Multiplicative.toAdd (ordZ f hx g)`: `+1` at a simple zero, `-1` at a simple pole (see the sign
convention in the module docstring). -/
theorem Scheme.divOf_apply (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : X.functionFieldˣ) {x : X} (hx : x ≠ genericPoint X) :
    @DFunLike.coe ({x : X // x ≠ genericPoint X} →₀ ℤ) _ _ _ (Scheme.divOf f g) ⟨x, hx⟩ =
      Multiplicative.toAdd (Scheme.ordZ f hx g) :=
  rfl

/-- **Additivity of the principal divisor**: `div(g · g') = div(g) + div(g')`, since `ordZ` is a
group homomorphism and `toAdd` turns multiplication into addition. -/
theorem Scheme.divOf_mul (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] [LocallyOfFiniteType f] [QuasiCompact f]
    (g g' : X.functionFieldˣ) :
    Scheme.divOf f (g * g') = Scheme.divOf f g + Scheme.divOf f g' := by
  refine Finsupp.ext fun p => ?_
  change Multiplicative.toAdd (Scheme.ordZ f p.2 (g * g'))
    = Multiplicative.toAdd (Scheme.ordZ f p.2 g) + Multiplicative.toAdd (Scheme.ordZ f p.2 g')
  rw [map_mul, toAdd_mul]

/-- **The principal divisor of the constant `1` is zero**: a unit constant has no zeros or
poles. -/
theorem Scheme.divOf_one (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] [LocallyOfFiniteType f] [QuasiCompact f] :
    Scheme.divOf f (1 : X.functionFieldˣ) = 0 := by
  refine Finsupp.ext fun p => ?_
  change Multiplicative.toAdd (Scheme.ordZ f p.2 (1 : X.functionFieldˣ)) = 0
  rw [map_one, toAdd_one]

end AlgebraicGeometry
