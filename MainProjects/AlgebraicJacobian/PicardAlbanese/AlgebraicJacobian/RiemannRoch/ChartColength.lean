/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.LocalizedColength
import AlgebraicJacobian.RiemannRoch.ChartPoints
import AlgebraicJacobian.RiemannRoch.PrincipalDivisor
import AlgebraicJacobian.RiemannRoch.ResidueDegree

/-!
# The chart colength dictionary (gap G-D5(b), SB-3 — the heart)

For the curve bundle `X` over a field `K` (integral, smooth of relative dimension one,
locally of finite type) and an affine open chart `V` containing the generic point, this file
proves the **chart colength dictionary** (`informal/deg-d5b-worksheet.md` §4 SB-3): with
`B := Γ(X, V)`,

* **SB-3a** (`AlgebraicGeometry.isDedekindDomain_section`): `B` is a Dedekind domain, for
  *every* affine chart — the upgrade of the existential
  `SmoothOfRelativeDimension.exists_isDedekindDomain_section` (domain from integrality,
  Noetherian from finite type over `K`, DVR localizations from the landed DVR stalks
  through `IsAffineOpen.primeIdealOf`/`isLocalization_stalk`).
* **SB-3b** (`AlgebraicGeometry.finrank_quotient_span_section`): for a section `f ∈ B`
  whose germ at `η` underlies the unit `g : K(X)ˣ` and which is a unit at every closed
  point of `V` outside a finite set `S`,

  `finrank K (B ⧸ (f)) = ∑_{x ∈ S} ord_x(g) · [κ(x) : K]`.

## The dictionary legs

* points ↔ primes: `IsAffineOpen.primeIdealOf_ne_bot`, `fromSpec_base_mem`,
  `primeIdealOf_fromSpec_base`, `fromSpec_base_ne_genericPoint` — closed points of `V`
  correspond to the nonzero primes of `B` through `fromSpec`/`primeIdealOf` (landed in
  `AlgebraicJacobian.RiemannRoch.ChartPoints`, split out for the 500-line discipline).
* multiplicity ↔ order (`AlgebraicGeometry.toAdd_ordZ_eq_count_factors`): the classical
  order `ord_x(g)` of `Scheme.ordZ` equals the multiplicity of the prime of `x` in
  `factors (f)` — through the stalk-is-localization identification and the multiplicity
  bridge `count_factors_span_algebraMap` (`Algebra.LocalizedColength`), **never** the false
  principal-prime route.
* residue fields (`AlgebraicGeometry.finrank_quotient_primeIdealOf`): the residue of the
  prime of `x` is `κ(x)`, `K`-linearly: `finrank K (B ⧸ p_x) = residueDeg K x`, with
  finiteness `moduleFinite_quotient_primeIdealOf` (Zariski's lemma through the chart).

The `K`-algebra structure on sections is `Scheme.overSectionsAlgebra` (restriction of
scalars along the landed `Scheme.overAlgebraMap`), a `local instance` in the house style of
`Scheme.overModule`; consumers of the `finrank` statements must activate the same instance.

This dictionary is also the engine of the deferred E-i pushforward-rank node
(`RiemannRoch/Degree.lean` docstring) and of G-D8's graph-degree certificates.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open Module (finrank)
open UniqueFactorizationMonoid

namespace AlgebraicGeometry

/-! ## The `K`-algebra of sections of a scheme over `K` -/

section SectionsAlgebra

variable (K : Type u) [CommRing K] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))]

/-- The `K`-algebra structure on `Γ(X, V)` for a scheme over `Spec K`: restriction of
scalars along the landed structure map `Scheme.overAlgebraMap`.  Deliberately **not** a
global instance (it would overlap with mathlib's `Algebra R Γ(Spec R, U)` instances through
the tautological `OverClass X X`; cf. the house rule for `Scheme.overModule`).  Activate
with `attribute [local instance] Scheme.overSectionsAlgebra`; the `finrank` statements of
this file mention it, so consumers must activate the same instance. -/
@[reducible] noncomputable def Scheme.overSectionsAlgebra (V : X.Opens) :
    Algebra K Γ(X, V) :=
  (X.overAlgebraMap K V).toAlgebra

attribute [local instance] Scheme.overSectionsAlgebra

/-- Unfolding lemma: the algebra structure map of `Scheme.overSectionsAlgebra` is the landed
`Scheme.overAlgebraMap`. -/
lemma Scheme.algebraMap_overSectionsAlgebra (V : X.Opens) :
    algebraMap K Γ(X, V) = X.overAlgebraMap K V :=
  rfl

/-- The structure map `K →+* Γ(X, V)` is of finite type on an affine chart of a scheme
locally of finite type over `K`. -/
theorem Scheme.overAlgebraMap_finiteType
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {V : X.Opens}
    (hV : IsAffineOpen V) : (X.overAlgebraMap K V).FiniteType := by
  have happ : X.overAlgebraMap K V
      = ((X ↘ Spec (CommRingCat.of K)).appLE ⊤ V le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := by
    rw [Scheme.overAlgebraMap, CommRingCat.hom_comp]
    rfl
  rw [happ]
  exact RingHom.FiniteType.comp
    ((X ↘ Spec (CommRingCat.of K)).finiteType_appLE (isAffineOpen_top _) hV le_top)
    (RingHom.FiniteType.of_surjective _
      (((ConcreteCategory.isIso_iff_bijective
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv).mp inferInstance).surjective))

end SectionsAlgebra

/-! ## SB-3a: every affine chart of the curve has Dedekind sections -/

section DedekindSections

attribute [local instance] Scheme.overSectionsAlgebra

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  {V : X.Opens} (hV : IsAffineOpen V)

include K hV in
/-- **SB-3a: Dedekind sections on every affine chart.**  For the curve bundle `X` over `K`
and any nonempty affine open `V` (equivalently, `η ∈ V`), the section ring `Γ(X, V)` is a
Dedekind domain: it is a domain by integrality of `X`, Noetherian since it is of finite type
over the field `K` (Hilbert basis through the chart), and its localizations at nonzero
primes are the DVR stalks of the smooth curve, through
`IsAffineOpen.primeIdealOf`/`isLocalization_stalk`.  This upgrades the landed existential
`SmoothOfRelativeDimension.exists_isDedekindDomain_section` from *some* chart around each
point to *every* chart. -/
theorem isDedekindDomain_section (hη : genericPoint X ∈ V) : IsDedekindDomain Γ(X, V) := by
  haveI : Nonempty V := ⟨⟨_, hη⟩⟩
  haveI : Algebra.FiniteType K Γ(X, V) := X.overAlgebraMap_finiteType K hV
  haveI : IsNoetherianRing Γ(X, V) := Algebra.FiniteType.isNoetherianRing K Γ(X, V)
  haveI : IsDedekindDomainDvr Γ(X, V) := by
    refine ⟨fun q hq0 hqp => ?_⟩
    haveI := hqp
    obtain ⟨x, hxV, hxg, hq⟩ : ∃ (x : X) (hx : x ∈ V) (_ : x ≠ genericPoint X),
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal = q :=
      ⟨hV.fromSpec.base ⟨q, hqp⟩, hV.fromSpec_base_mem _,
        hV.fromSpec_base_ne_genericPoint hq0,
        congrArg PrimeSpectrum.asIdeal (hV.primeIdealOf_fromSpec_base ⟨q, hqp⟩)⟩
    subst hq
    letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
    haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
    haveI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hxg
    haveI : IsDomain (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors _
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl_le_nonZeroDivisors
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
        (X.presheaf.stalk x)
        (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal))
  infer_instance

end DedekindSections

/-! ## The residue leg: `B ⧸ p_x ≅ κ(x)` over `K` -/

section ResidueLeg

attribute [local instance] Scheme.overSectionsAlgebra Scheme.residueFieldOverModule

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  {V : X.Opens} (hV : IsAffineOpen V)

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- Germs of the structure map through different opens agree: the `V`-chart composite
`germ_V ∘ overAlgebraMap_V` equals the global composite `germ_⊤ ∘ overAlgebraMap_⊤`. -/
private lemma germ_overAlgebraMap_congr {x : X} (hx : x ∈ V) (c : K) :
    (X.presheaf.germ V x hx).hom (X.overAlgebraMap K V c)
      = (X.presheaf.germ ⊤ x trivial).hom (X.overAlgebraMap K ⊤ c) := by
  have hgr : X.presheaf.germ ⊤ x trivial
      = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ X.presheaf.germ V x hx :=
    (X.presheaf.germ_res (homOfLE (le_top : V ≤ ⊤)) x hx).symm
  rw [hgr, CommRingCat.comp_apply, X.overAlgebraMap_apply_res K (homOfLE le_top).op c]

/-- **Finiteness of the chart residue** (Zariski's lemma through the chart): the residue
`Γ(X, V) ⧸ p_x` at a closed point `x ∈ V` is a finite `K`-module: the structure map is of
finite type into a field over the Jacobson ring `K`. -/
theorem moduleFinite_quotient_primeIdealOf {x : X} (hx : x ∈ V)
    (hxg : x ≠ genericPoint X) :
    Module.Finite K (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  haveI : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hx⟩
      (isClosed_singleton_of_ne_genericPoint (X ↘ Spec (CommRingCat.of K)) hxg)
  letI : Field (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) := Ideal.Quotient.field _
  haveI : Algebra.FiniteType K Γ(X, V) := X.overAlgebraMap_finiteType K hV
  haveI : Algebra.FiniteType K (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) :=
    Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ K (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
      (Ideal.Quotient.mkₐ_surjective K _)
  exact finite_of_finite_type_of_isJacobsonRing K _

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- **The residue leg of the dictionary**: the residue of the chart at the prime of a
closed point `x ∈ V` is the residue field of `x`, `K`-linearly —
`finrank K (Γ(X, V) ⧸ p_x) = [κ(x) : K]`. -/
theorem finrank_quotient_primeIdealOf {x : X} (hx : x ∈ V) (hxg : x ≠ genericPoint X) :
    finrank K (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) = X.residueDeg K x := by
  haveI : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hx⟩
      (isClosed_singleton_of_ne_genericPoint (X ↘ Spec (CommRingCat.of K)) hxg)
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hV.isLocalization_stalk ⟨x, hx⟩
  set e := IsLocalization.AtPrime.equivQuotMaximalIdeal
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x) with he
  have hcompat : ∀ c : K,
      e (algebraMap K (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) c)
        = X.residueOverAlgebraMap K x c := by
    intro c
    rw [← Ideal.Quotient.mk_algebraMap,
      IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
    change IsLocalRing.residue (X.presheaf.stalk x)
        ((X.presheaf.germ V x hx).hom (X.overAlgebraMap K V c)) = _
    rw [germ_overAlgebraMap_congr K hx c]
    rfl
  have hfr : finrank K (Γ(X, V) ⧸ (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
      = finrank K (X.residueField x) :=
    LinearEquiv.finrank_eq
      { e with
        map_smul' := fun c z => by
          simp only [RingHom.id_apply, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
            EquivLike.coe_coe]
          rw [Algebra.smul_def, map_mul, hcompat c]
          rfl }
  rw [hfr]
  rfl

end ResidueLeg

/-! ## The multiplicity leg: order of vanishing = multiplicity in the factorization -/

section MultiplicityLeg

attribute [local instance] Scheme.overSectionsAlgebra

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V)

/-- File-local duplicate of the germ/stalk seam `Scheme.germ_generic_eq_algebraMap_germ`
(landed in `RiemannRoch/DivisorSheafZero.lean`; kept private so this file's import cone
stays free of the divisor-sheaf chain): the germ at `η` of a chart section is the image of
its germ at `x` along the canonical map `𝒪_{X,x} → K(X)`. -/
private lemma germ_generic_eq_algebraMap_germ {x : X} (hx : x ∈ V) (f : Γ(X, V)) :
    (X.presheaf.germ V (genericPoint X) hη).hom f
      = algebraMap (X.presheaf.stalk x) X.functionField
          ((X.presheaf.germ V x hx).hom f) := by
  rw [RingHom.algebraMap_toAlgebra]
  exact (X.presheaf.germ_stalkSpecializes_apply
    hx ((genericPoint_spec X).specializes trivial) f).symm

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- File-local form of the landed bridge `coe_inv_ordZ` (`Picard/PresentationDivisor.lean`,
kept private here so the RiemannRoch layer does not import the Picard layer): the inverse
of the classical order `Scheme.ordZ` (recall the sign inversion in its definition), coerced
into `ℤᵐ⁰`, is the mathlib valuation `Scheme.ord` of the underlying rational function. -/
private lemma coe_inv_ordZ (g : X.functionFieldˣ) {x : X} (hx : x ≠ genericPoint X) :
    (((Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hx g)⁻¹ : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ))
      = Scheme.ord (X ↘ Spec (CommRingCat.of K)) hx (g : X.functionField) := by
  rw [Scheme.ordZ]
  simp only [MonoidHom.comp_apply, invMonoidHom_apply, inv_inv, MulEquiv.coe_toMonoidHom,
    WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- **The multiplicity leg of the dictionary** (the worksheet's "least-trodden bridge"):
for a closed point `x ∈ V`, a nonzero section `f` of the chart, and a unit `g` of `K(X)`
whose value is the germ of `f` at `η`, the classical order of vanishing of `g` at `x` is
the multiplicity of the prime of `x` in the factorization of `(f) ⊆ Γ(X, V)`.  Pinned
route: `ord` is the adic valuation of the maximal ideal of the DVR stalk; the stalk is the
localization of the chart at the prime of `x` (`isLocalization_stalk`); and multiplicities
are preserved by that localization (`count_factors_span_algebraMap`). -/
theorem toAdd_ordZ_eq_count_factors [IsDedekindDomain Γ(X, V)] {x : X} (hx : x ∈ V)
    (hxg : x ≠ genericPoint X) {f : Γ(X, V)} (hf : f ≠ 0) (g : X.functionFieldˣ)
    (hg : (g : X.functionField) = (X.presheaf.germ V (genericPoint X) hη).hom f) :
    Multiplicative.toAdd (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hxg g)
      = (Multiset.count (hV.primeIdealOf ⟨x, hx⟩).asIdeal
          (factors (Ideal.span {f})) : ℤ) := by
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (CommRingCat.of K)) hxg
  letI := isDedekindDomain_stalk (X ↘ Spec (CommRingCat.of K)) hxg
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hV.isLocalization_stalk ⟨x, hx⟩
  have hq0 : (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≠ ⊥ := hV.primeIdealOf_ne_bot hx hxg
  have hgerm0 : (X.presheaf.germ V x hx).hom f ≠ 0 := fun h0 =>
    hf (germ_injective_of_isIntegral X x hx (by rw [h0, map_zero]))
  -- the value of the mathlib valuation
  have hord : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hxg (g : X.functionField)
      = WithZero.exp (-(Multiset.count (hV.primeIdealOf ⟨x, hx⟩).asIdeal
          (factors (Ideal.span {f})) : ℤ)) := by
    have h1 : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hxg
        = (stalkHeightOne X x).valuation X.functionField := rfl
    rw [h1, hg, germ_generic_eq_algebraMap_germ hη hx f,
      (stalkHeightOne X x).valuation_of_algebraMap,
      intValuation_eq_exp_neg_count (stalkHeightOne X x) hgerm0,
      show (X.presheaf.germ V x hx).hom f
        = algebraMap Γ(X, V) (X.presheaf.stalk x) f from rfl,
      show (stalkHeightOne X x).asIdeal
        = IsLocalRing.maximalIdeal (X.presheaf.stalk x) from rfl,
      count_factors_span_algebraMap (X.presheaf.stalk x) hq0 hf]
  -- extract the classical order
  have h2 := coe_inv_ordZ K g hxg
  rw [hord, WithZero.exp_eq_coe_ofAdd] at h2
  have h3 := congrArg Inv.inv (WithZero.coe_inj.mp h2)
  rw [inv_inv, ← ofAdd_neg, neg_neg] at h3
  rw [h3, toAdd_ofAdd]

end MultiplicityLeg

/-! ## SB-3b: the chart colength dictionary -/

section Keystone

attribute [local instance] Scheme.overSectionsAlgebra Scheme.residueFieldOverModule

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V)

omit [IsIntegral X] in
/-- A section is a non-unit at `x` exactly when it lies in the prime of `x`: the
stalk-is-localization form of `mem_basicOpen`. -/
lemma not_isUnit_germ_iff_mem {x : X} (hx : x ∈ V) (f : Γ(X, V)) :
    ¬ IsUnit ((X.presheaf.germ V x hx).hom f)
      ↔ f ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hV.isLocalization_stalk ⟨x, hx⟩
  rw [show (X.presheaf.germ V x hx).hom f
      = algebraMap Γ(X, V) (X.presheaf.stalk x) f from rfl,
    IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal f]
  exact not_not

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- Where the section is a unit, the order vanishes. -/
lemma toAdd_ordZ_eq_zero_of_isUnit_germ {x : X} (hx : x ∈ V)
    (hxg : x ≠ genericPoint X) {f : Γ(X, V)} (g : X.functionFieldˣ)
    (hg : (g : X.functionField) = (X.presheaf.germ V (genericPoint X) hη).hom f)
    (hunit : IsUnit ((X.presheaf.germ V x hx).hom f)) :
    Multiplicative.toAdd (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hxg g) = 0 := by
  have hbasic : x ∈ X.basicOpen f := (X.mem_basicOpen f x hx).mpr hunit
  have hord : Scheme.ord (X ↘ Spec (CommRingCat.of K)) hxg (g : X.functionField) = 1 := by
    rw [hg]
    exact Scheme.ord_eq_one_of_mem_basicOpen (X ↘ Spec (CommRingCat.of K)) hxg f hη hbasic
  rw [(Scheme.ordZ_eq_one_iff (X ↘ Spec (CommRingCat.of K)) hxg g).mpr hord, toAdd_one]

/-- Membership of the prime of a closed point in the factor set of `(f)` is the vanishing
of `f` at the point. -/
lemma primeIdealOf_mem_factors_iff [IsDedekindDomain Γ(X, V)] {x : X} (hx : x ∈ V)
    (hxg : x ≠ genericPoint X) {f : Γ(X, V)} (hf : f ≠ 0) :
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal ∈ (factors (Ideal.span {f})).toFinset
      ↔ f ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  constructor
  · intro h
    exact (prime_factor_span f h).2.2
  · intro h
    rw [Multiset.mem_toFinset, ← Multiset.count_pos]
    have h1 : f ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal ^ 1 := by rwa [pow_one]
    have h2 : 1 ≤ Multiset.count (hV.primeIdealOf ⟨x, hx⟩).asIdeal
        (factors (Ideal.span {f})) :=
      (mem_pow_iff_le_count
        ⟨(hV.primeIdealOf ⟨x, hx⟩).asIdeal, (hV.primeIdealOf ⟨x, hx⟩).isPrime,
          hV.primeIdealOf_ne_bot hx hxg⟩ hf 1).mp h1
    omega

include hV hη in
/-- **Finiteness of the chart colength module**: `Γ(X, V) ⧸ (f)` is a finite `K`-module for
every nonzero section `f` of the chart. -/
theorem moduleFinite_quotient_span_section {f : Γ(X, V)} (hf : f ≠ 0) :
    Module.Finite K (Γ(X, V) ⧸ Ideal.span {f}) := by
  haveI : Nonempty V := ⟨⟨_, hη⟩⟩
  haveI hDed : IsDedekindDomain Γ(X, V) := isDedekindDomain_section K hV hη
  haveI : ∀ P : (factors (Ideal.span {f})).toFinset,
      Module.Finite K (Γ(X, V) ⧸ (P : Ideal Γ(X, V))) := by
    intro P
    obtain ⟨hPp, hP0, hfP⟩ := prime_factor_span f P.2
    haveI := hPp
    have hq : hV.primeIdealOf
        ⟨hV.fromSpec.base ⟨(P : Ideal Γ(X, V)), hPp⟩,
          hV.fromSpec_base_mem ⟨(P : Ideal Γ(X, V)), hPp⟩⟩
        = ⟨(P : Ideal Γ(X, V)), hPp⟩ :=
      hV.primeIdealOf_fromSpec_base ⟨(P : Ideal Γ(X, V)), hPp⟩
    have hfin := moduleFinite_quotient_primeIdealOf K hV
      (hV.fromSpec_base_mem ⟨(P : Ideal Γ(X, V)), hPp⟩)
      (hV.fromSpec_base_ne_genericPoint hP0)
    rwa [hq] at hfin
  exact moduleFinite_quotient_span hf

include hV in
/-- **SB-3b, the chart colength dictionary** (the heart of the fiber-degree identity): let
`f` be a section of the affine chart `V ∋ η` of the curve bundle `X/K`, `g : K(X)ˣ` a unit
whose value is the germ of `f` at `η`, and `S` a finite set of closed points of `V` outside
which `f` is a unit on `V`.  Then the colength of `(f)` in the chart counts the orders of
vanishing of `g` weighted by residue degrees:

`finrank K (Γ(X, V) ⧸ (f)) = ∑_{x ∈ S} ord_x(g) · [κ(x) : K]`.

Pinned assembly: the honest Dedekind colength formula
(`finrank_quotient_span_eq_sum_count`, CRT + per-prime localization — never the false
`hprin` route), reindexed from prime factors to closed points along
`fromSpec`/`primeIdealOf`, with the multiplicity leg (`toAdd_ordZ_eq_count_factors`) and
the residue leg (`finrank_quotient_primeIdealOf`). -/
theorem finrank_quotient_span_section {f : Γ(X, V)} (g : X.functionFieldˣ)
    (hg : (g : X.functionField) = (X.presheaf.germ V (genericPoint X) hη).hom f)
    (S : Finset {x : X // x ≠ genericPoint X}) (hSV : ∀ p ∈ S, p.1 ∈ V)
    (hout : ∀ (z : X) (hz : z ∈ V) (hzg : z ≠ genericPoint X),
      (⟨z, hzg⟩ : {x : X // x ≠ genericPoint X}) ∉ S →
        IsUnit ((X.presheaf.germ V z hz).hom f)) :
    (finrank K (Γ(X, V) ⧸ Ideal.span {f}) : ℤ)
      = ∑ p ∈ S, Multiplicative.toAdd (Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) p.2 g)
          * (X.residueDeg K p.1 : ℤ) := by
  classical
  haveI : Nonempty V := ⟨⟨_, hη⟩⟩
  haveI hDed : IsDedekindDomain Γ(X, V) := isDedekindDomain_section K hV hη
  have hf : f ≠ 0 := by
    intro h0
    apply g.ne_zero
    rw [hg, h0, map_zero]
  haveI : ∀ P : (factors (Ideal.span {f})).toFinset,
      Module.Finite K (Γ(X, V) ⧸ (P : Ideal Γ(X, V))) := by
    intro P
    obtain ⟨hPp, hP0, hfP⟩ := prime_factor_span f P.2
    haveI := hPp
    have hq := hV.primeIdealOf_fromSpec_base ⟨(P : Ideal Γ(X, V)), hPp⟩
    have hfin := moduleFinite_quotient_primeIdealOf K hV
      (hV.fromSpec_base_mem ⟨(P : Ideal Γ(X, V)), hPp⟩)
      (hV.fromSpec_base_ne_genericPoint hP0)
    rwa [hq] at hfin
  rw [finrank_quotient_span_eq_sum_count hf]
  push_cast
  rw [Finset.sum_coe_sort _ (fun P : Ideal Γ(X, V) =>
    (Multiset.count P (factors (Ideal.span {f})) : ℤ) * (finrank K (Γ(X, V) ⧸ P) : ℤ))]
  refine (Finset.sum_bij_ne_zero
    (i := fun p hp _ => (hV.primeIdealOf ⟨p.1, hSV p hp⟩).asIdeal) ?_ ?_ ?_ ?_).symm
  · -- membership: nonzero terms come from vanishing points, whose primes divide `(f)`
    intro p h₁ h₂
    rw [primeIdealOf_mem_factors_iff hV (hSV p h₁) p.2 hf,
      ← not_isUnit_germ_iff_mem hV (hSV p h₁) f]
    intro hunit
    apply h₂
    rw [toAdd_ordZ_eq_zero_of_isUnit_germ K hη (hSV p h₁) p.2 g hg hunit, zero_mul]
  · -- injectivity: distinct points have distinct primes
    intro p₁ h₁₁ h₁₂ p₂ h₂₁ h₂₂ heq
    have h1 := hV.fromSpec_primeIdealOf ⟨p₁.1, hSV p₁ h₁₁⟩
    have h2 := hV.fromSpec_primeIdealOf ⟨p₂.1, hSV p₂ h₂₁⟩
    refine Subtype.ext ?_
    rw [← h1, ← h2]
    exact congrArg hV.fromSpec.base (PrimeSpectrum.ext heq)
  · -- surjectivity: every prime factor is the prime of a closed point of `S`
    intro P hP hPne
    obtain ⟨hPp, hP0, hfP⟩ := prime_factor_span f hP
    haveI := hPp
    set y : Spec Γ(X, V) := ⟨P, hPp⟩ with hy
    have hxV : hV.fromSpec.base y ∈ V := hV.fromSpec_base_mem y
    have hxg : hV.fromSpec.base y ≠ genericPoint X :=
      hV.fromSpec_base_ne_genericPoint hP0
    have hq : hV.primeIdealOf ⟨hV.fromSpec.base y, hxV⟩ = y :=
      hV.primeIdealOf_fromSpec_base y
    have hmemP : f ∈ (hV.primeIdealOf ⟨hV.fromSpec.base y, hxV⟩).asIdeal := by
      rw [hq]
      exact hfP
    have hmemS : (⟨hV.fromSpec.base y, hxg⟩ : {x : X // x ≠ genericPoint X}) ∈ S := by
      by_contra hn
      exact (not_isUnit_germ_iff_mem hV hxV f).mpr hmemP (hout _ hxV hxg hn)
    refine ⟨⟨hV.fromSpec.base y, hxg⟩, hmemS, ?_, ?_⟩
    · -- the point's term is the prime's term, which is nonzero
      rw [toAdd_ordZ_eq_count_factors K hV hη hxV hxg hf g hg,
        ← finrank_quotient_primeIdealOf K hV hxV hxg, hq]
      exact hPne
    · exact congrArg PrimeSpectrum.asIdeal hq
  · -- values: the dictionary legs
    intro p h₁ h₂
    rw [toAdd_ordZ_eq_count_factors K hV hη (hSV p h₁) p.2 hf g hg,
      finrank_quotient_primeIdealOf K hV (hSV p h₁) p.2]

end Keystone

end AlgebraicGeometry
